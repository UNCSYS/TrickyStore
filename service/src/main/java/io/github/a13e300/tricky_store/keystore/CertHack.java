package io.github.a13e300.tricky_store.keystore;

import android.content.pm.PackageManager;
import android.hardware.security.keymint.Algorithm;
import android.hardware.security.keymint.EcCurve;
import android.hardware.security.keymint.KeyParameter;
import android.hardware.security.keymint.Tag;
import android.security.keystore.KeyProperties;
import android.system.keystore2.KeyDescriptor;
import android.util.Pair;

import androidx.annotation.Nullable;

import org.bouncycastle.asn1.ASN1Boolean;
import org.bouncycastle.asn1.ASN1Encodable;
import org.bouncycastle.asn1.ASN1EncodableVector;
import org.bouncycastle.asn1.ASN1Enumerated;
import org.bouncycastle.asn1.ASN1Integer;
import org.bouncycastle.asn1.ASN1ObjectIdentifier;
import org.bouncycastle.asn1.ASN1OctetString;
import org.bouncycastle.asn1.ASN1Sequence;
import org.bouncycastle.asn1.ASN1TaggedObject;
import org.bouncycastle.asn1.DERNull;
import org.bouncycastle.asn1.DEROctetString;
import org.bouncycastle.asn1.DERSequence;
import org.bouncycastle.asn1.DERSet;
import org.bouncycastle.asn1.DERTaggedObject;
import org.bouncycastle.asn1.x500.X500Name;
import org.bouncycastle.asn1.x509.Extension;
import org.bouncycastle.asn1.x509.KeyUsage;
import org.bouncycastle.cert.X509CertificateHolder;
import org.bouncycastle.cert.X509v3CertificateBuilder;
import org.bouncycastle.cert.jcajce.JcaX509CertificateConverter;
import org.bouncycastle.cert.jcajce.JcaX509v3CertificateBuilder;
import org.bouncycastle.jce.provider.BouncyCastleProvider;
import org.bouncycastle.openssl.PEMKeyPair;
import org.bouncycastle.openssl.PEMParser;
import org.bouncycastle.openssl.jcajce.JcaPEMKeyConverter;
import org.bouncycastle.operator.ContentSigner;
import org.bouncycastle.operator.jcajce.JcaContentSignerBuilder;
import org.bouncycastle.util.io.pem.PemReader;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.StringReader;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.MessageDigest;
import java.security.Security;
import java.security.cert.Certificate;
import java.security.cert.CertificateFactory;
import java.security.cert.CertificateParsingException;
import java.security.cert.X509Certificate;
import java.security.spec.ECGenParameterSpec;
import java.security.spec.RSAKeyGenParameterSpec;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import javax.security.auth.x500.X500Principal;

import io.github.a13e300.tricky_store.Config;
import io.github.a13e300.tricky_store.Logger;
import io.github.a13e300.tricky_store.SecurityLevelInterceptor;
import io.github.a13e300.tricky_store.UtilKt;

/**
 * 提供证书链篡改功能的工具类，用于绕过Android密钥证明验证
 * 核心功能包括：加载预置密钥盒、篡改证书链中的证明信息、生成伪造证书链
 */
public final class CertHack {
    // Android密钥证明扩展的OID标识符
    private static final ASN1ObjectIdentifier OID = new ASN1ObjectIdentifier("1.3.6.1.4.1.11129.2.1.17");

    // 应用ID结构中包信息和签名摘要的索引常量
    private static final int ATTESTATION_APPLICATION_ID_PACKAGE_INFOS_INDEX = 0;
    private static final int ATTESTATION_APPLICATION_ID_SIGNATURE_DIGESTS_INDEX = 1;
    // 存储不同算法的预置密钥盒(密钥对+证书链)
    private static final Map<String, KeyBox> keyboxes = new HashMap<>();
    // 记录每个密钥的算法类型(用于后续查找)
    private static final Map<Key, String> leafAlgorithm = new HashMap<>();
    // 包信息结构中包名和版本号的索引常量
    private static final int ATTESTATION_PACKAGE_INFO_PACKAGE_NAME_INDEX = 0;

    // 证书工厂实例(用于解析证书)
    private static final CertificateFactory certificateFactory;

    // 组合键：别名+用户ID标识唯一密钥
    public record Key(String alias, int uid) {}

    static {
        try {
            // 初始化X.509证书工厂
            certificateFactory = CertificateFactory.getInstance("X.509");
        } catch (Throwable t) {
            Logger.e("", t);
            throw new RuntimeException(t);
        }
    }

    private static final int ATTESTATION_PACKAGE_INFO_VERSION_INDEX = 1;

    /**
     * 检查是否有可用的密钥盒用于证书篡改
     * @return true表示存在预加载的密钥盒
     */
    public static boolean canHack() {
        return !keyboxes.isEmpty();
    }

    /**
     * 解析PEM格式的密钥对字符串
     * @param key PEM格式的密钥字符串
     * @return 解析后的密钥对
     */
    private static PEMKeyPair parseKeyPair(String key) throws Throwable {
        try (PEMParser parser = new PEMParser(new StringReader(UtilKt.trimLine(key)))) {
            return (PEMKeyPair) parser.readObject();
        }
    }

    /**
     * 解析PEM格式的证书字符串
     * @param cert PEM格式的证书字符串
     * @return 解析后的证书对象
     */
    private static Certificate parseCert(String cert) throws Throwable {
        try (PemReader reader = new PemReader(new StringReader(UtilKt.trimLine(cert)))) {
            return certificateFactory.generateCertificate(new ByteArrayInputStream(reader.readPemObject().getContent()));
        }
    }

    /**
     * 从ASN1编码对象中提取字节数组
     * @param asn1Encodable ASN1编码对象
     * @return 包含的字节数组
     * @throws CertificateParsingException 当对象不是DEROctetString时抛出
     */
    private static byte[] getByteArrayFromAsn1(ASN1Encodable asn1Encodable) throws CertificateParsingException {
        if (!(asn1Encodable instanceof DEROctetString derOctectString)) {
            throw new CertificateParsingException("Expected DEROctetString");
        }
        return derOctectString.getOctets();
    }

    /**
     * 从XML配置中加载密钥盒信息
     * @param data 包含密钥盒配置的XML字符串
     */
    public static void readFromXml(String data) {
        keyboxes.clear();
        if (data == null) {
            Logger.i("clear all keyboxes");
            return;
        }
        XMLParser xmlParser = new XMLParser(data);

        try {
            // 解析XML中的密钥盒数量
            int numberOfKeyboxes = Integer.parseInt(Objects.requireNonNull(xmlParser.obtainPath(
                    "AndroidAttestation.NumberOfKeyboxes").get("text")));
            for (int i = 0; i < numberOfKeyboxes; i++) {
                // 获取密钥算法类型
                String keyboxAlgorithm = xmlParser.obtainPath(
                        "AndroidAttestation.Keybox.Key[" + i + "]").get("algorithm");
                // 获取私钥内容
                String privateKey = xmlParser.obtainPath(
                        "AndroidAttestation.Keybox.Key[" + i + "].PrivateKey").get("text");
                // 获取证书链中的证书数量
                int numberOfCertificates = Integer.parseInt(Objects.requireNonNull(xmlParser.obtainPath(
                        "AndroidAttestation.Keybox.Key[" + i + "].CertificateChain.NumberOfCertificates").get("text")));

                LinkedList<Certificate> certificateChain = new LinkedList<>();

                // 解析证书链
                for (int j = 0; j < numberOfCertificates; j++) {
                    Map<String, String> certData = xmlParser.obtainPath(
                            "AndroidAttestation.Keybox.Key[" + i + "].CertificateChain.Certificate[" + j + "]");
                    certificateChain.add(parseCert(certData.get("text")));
                }
                // 标准化算法名称
                String algo;
                if (keyboxAlgorithm.toLowerCase().equals("ecdsa")) {
                    algo = KeyProperties.KEY_ALGORITHM_EC;
                } else {
                    algo = KeyProperties.KEY_ALGORITHM_RSA;
                }
                // 转换PEM密钥对为Java密钥对
                var pemKp = parseKeyPair(privateKey);
                var kp = new JcaPEMKeyConverter().getKeyPair(pemKp);
                // 存储密钥盒
                keyboxes.put(algo, new KeyBox(pemKp, kp, certificateChain));
            }
            Logger.i("update " + numberOfKeyboxes + " keyboxes");
        } catch (Throwable t) {
            Logger.e("Error loading xml file (keyboxes cleared): " + t);
        }
    }

    /**
     * 篡改证书链中的证明扩展信息
     * @param caList 原始证书链
     * @return 篡改后的证书链（包含伪造的证明信息）
     */
    public static Certificate[] hackCertificateChain(Certificate[] caList) {
        if (caList == null) throw new UnsupportedOperationException("caList is null!");
        try {
            // 解析叶子证书
            X509Certificate leaf = (X509Certificate) certificateFactory.generateCertificate(new ByteArrayInputStream(caList[0].getEncoded()));
            // 检查是否存在Android密钥证明扩展
            byte[] bytes = leaf.getExtensionValue(OID.getId());
            if (bytes == null) return caList;

            // 使用Bouncy Castle解析证书
            X509CertificateHolder leafHolder = new X509CertificateHolder(leaf.getEncoded());
            Extension ext = leafHolder.getExtension(OID);
            ASN1Sequence sequence = ASN1Sequence.getInstance(ext.getExtnValue().getOctets());
            ASN1Encodable[] encodables = sequence.toArray();
            // 提取TEE强制字段（索引7）
            ASN1Sequence teeEnforced = (ASN1Sequence) encodables[7];
            ASN1EncodableVector vector = new ASN1EncodableVector();
            ASN1Encodable rootOfTrust = null;

            // 遍历TEE强制字段，分离出RootOfTrust（标签704）
            for (ASN1Encodable asn1Encodable : teeEnforced) {
                ASN1TaggedObject taggedObject = (ASN1TaggedObject) asn1Encodable;
                if (taggedObject.getTagNo() == 704) {
                    rootOfTrust = taggedObject.getBaseObject().toASN1Primitive();
                    continue;
                }
                vector.add(taggedObject);
            }

            LinkedList<Certificate> certificates;
            X509v3CertificateBuilder builder;
            ContentSigner signer;

            // 根据算法获取预置密钥盒
            var k = keyboxes.get(leaf.getPublicKey().getAlgorithm());
            if (k == null)
                throw new UnsupportedOperationException("unsupported algorithm " + leaf.getPublicKey().getAlgorithm());
            certificates = new LinkedList<>(k.certificates);
            // 使用密钥盒中的根证书构建新证书
            builder = new X509v3CertificateBuilder(
                    new X509CertificateHolder(
                            certificates.get(0).getEncoded()
                    ).getSubject(),
                    leafHolder.getSerialNumber(),
                    leafHolder.getNotBefore(),
                    leafHolder.getNotAfter(),
                    leafHolder.getSubject(),
                    leafHolder.getSubjectPublicKeyInfo()
            );
            signer = new JcaContentSignerBuilder(leaf.getSigAlgName())
                    .build(k.keyPair.getPrivate());

            // 获取设备引导密钥和哈希（用于伪造证明）
            byte[] verifiedBootKey = UtilKt.getBootKey();
            byte[] verifiedBootHash = null;
            try {
                if (!(rootOfTrust instanceof ASN1Sequence r)) {
                    throw new CertificateParsingException("Expected sequence for root of trust, found "
                            + rootOfTrust.getClass().getName());
                }
                // 尝试从原始证书中提取verifiedBootHash（位置3）
                verifiedBootHash = getByteArrayFromAsn1(r.getObjectAt(3));
            } catch (Throwable t) {
                Logger.e("failed to get verified boot key or hash from original, use randomly generated instead", t);
            }

            // 如果提取失败，使用随机生成的哈希
            if (verifiedBootHash == null) {
                verifiedBootHash = UtilKt.getBootHash();
            }

            // 构建伪造的RootOfTrust结构
            ASN1Encodable[] rootOfTrustEnc = {
                    new DEROctetString(verifiedBootKey),  // 引导密钥
                    ASN1Boolean.TRUE,                   // 设备锁定状态
                    new ASN1Enumerated(0),              // 验证引导状态
                    new DEROctetString(verifiedBootHash) // 引导哈希
            };

            ASN1Sequence hackedRootOfTrust = new DERSequence(rootOfTrustEnc);
            ASN1TaggedObject rootOfTrustTagObj = new DERTaggedObject(704, hackedRootOfTrust);
            vector.add(rootOfTrustTagObj);

            // 重组TEE强制字段
            ASN1Sequence hackEnforced = new DERSequence(vector);
            encodables[7] = hackEnforced;
            ASN1Sequence hackedSeq = new DERSequence(encodables);

            // 创建新的证明扩展
            ASN1OctetString hackedSeqOctets = new DEROctetString(hackedSeq);
            Extension hackedExt = new Extension(OID, false, hackedSeqOctets);
            builder.addExtension(hackedExt);

            // 复制原证书的其他扩展
            for (ASN1ObjectIdentifier extensionOID : leafHolder.getExtensions().getExtensionOIDs()) {
                if (OID.getId().equals(extensionOID.getId())) continue;
                builder.addExtension(leafHolder.getExtension(extensionOID));
            }
            // 构建新证书并插入到证书链首位
            certificates.addFirst(new JcaX509CertificateConverter().getCertificate(builder.build(signer)));

            return certificates.toArray(new Certificate[0]);

        } catch (Throwable t) {
            Logger.e("", t);
        }
        return caList;
    }

    /**
     * 获取预置的CA证书链（用于密钥证明场景）
     * @param caList 原始CA证书链数据
     * @param alias 密钥别名
     * @param uid 用户ID
     * @return 预置的CA证书链字节
     */
    public static byte[] hackCertificateChainCA(byte[] caList, String alias, int uid) {
        if (caList == null) throw new UnsupportedOperationException("caList is null!");
        try {
            var key = new Key(alias, uid);
            var algorithm = leafAlgorithm.get(key);
            leafAlgorithm.remove(key);
            var k = keyboxes.get(algorithm);
            if (k == null)
                throw new UnsupportedOperationException("unsupported algorithm " + algorithm);
            // 返回预置密钥盒中的证书链
            return Utils.toBytes(k.certificates);
        } catch (Throwable t) {
            Logger.e("", t);
        }
        return caList;
    }

    /**
     * 篡改用户证书中的证明扩展信息
     * @param certificate 原始用户证书数据
     * @param alias 密钥别名
     * @param uid 用户ID
     * @return 篡改后的用户证书字节
     */
    public static byte[] hackCertificateChainUSR(byte[] certificate, String alias, int uid) {
        if (certificate == null) throw new UnsupportedOperationException("leaf is null!");
        try {
            X509Certificate leaf = (X509Certificate) certificateFactory.generateCertificate(new ByteArrayInputStream(certificate));
            byte[] bytes = leaf.getExtensionValue(OID.getId());
            if (bytes == null) return certificate;

            // 解析过程与hackCertificateChain类似
            X509CertificateHolder leafHolder = new X509CertificateHolder(leaf.getEncoded());
            Extension ext = leafHolder.getExtension(OID);
            ASN1Sequence sequence = ASN1Sequence.getInstance(ext.getExtnValue().getOctets());
            ASN1Encodable[] encodables = sequence.toArray();
            ASN1Sequence teeEnforced = (ASN1Sequence) encodables[7];
            ASN1EncodableVector vector = new ASN1EncodableVector();
            ASN1Encodable rootOfTrust = null;

            for (ASN1Encodable asn1Encodable : teeEnforced) {
                ASN1TaggedObject taggedObject = (ASN1TaggedObject) asn1Encodable;
                if (taggedObject.getTagNo() == 704) {
                    rootOfTrust = taggedObject.getBaseObject().toASN1Primitive();
                    continue;
                }
                vector.add(taggedObject);
            }

            LinkedList<Certificate> certificates;
            X509v3CertificateBuilder builder;
            ContentSigner signer;

            // 记录密钥算法用于后续CA证书获取
            leafAlgorithm.put(new Key(alias, uid), leaf.getPublicKey().getAlgorithm());
            var k = keyboxes.get(leaf.getPublicKey().getAlgorithm());
            if (k == null)
                throw new UnsupportedOperationException("unsupported algorithm " + leaf.getPublicKey().getAlgorithm());
            certificates = new LinkedList<>(k.certificates);
            builder = new X509v3CertificateBuilder(
                    new X509CertificateHolder(
                            certificates.get(0).getEncoded()
                    ).getSubject(),
                    leafHolder.getSerialNumber(),
                    leafHolder.getNotBefore(),
                    leafHolder.getNotAfter(),
                    leafHolder.getSubject(),
                    leafHolder.getSubjectPublicKeyInfo()
            );
            signer = new JcaContentSignerBuilder(leaf.getSigAlgName())
                    .build(k.keyPair.getPrivate());

            byte[] verifiedBootKey = UtilKt.getBootKey();
            byte[] verifiedBootHash = null;
            try {
                if (!(rootOfTrust instanceof ASN1Sequence r)) {
                    throw new CertificateParsingException("Expected sequence for root of trust, found "
                            + rootOfTrust.getClass().getName());
                }
                verifiedBootHash = getByteArrayFromAsn1(r.getObjectAt(3));
            } catch (Throwable t) {
                Logger.e("failed to get verified boot key or hash from original, use randomly generated instead", t);
            }

            if (verifiedBootHash == null) {
                verifiedBootHash = UtilKt.getBootHash();
            }

            ASN1Encodable[] rootOfTrustEnc = {
                    new DEROctetString(verifiedBootKey),
                    ASN1Boolean.TRUE,
                    new ASN1Enumerated(0),
                    new DEROctetString(verifiedBootHash)
            };

            ASN1Sequence hackedRootOfTrust = new DERSequence(rootOfTrustEnc);
            ASN1TaggedObject rootOfTrustTagObj = new DERTaggedObject(704, hackedRootOfTrust);
            vector.add(rootOfTrustTagObj);

            ASN1Sequence hackEnforced = new DERSequence(vector);
            encodables[7] = hackEnforced;
            ASN1Sequence hackedSeq = new DERSequence(encodables);

            ASN1OctetString hackedSeqOctets = new DEROctetString(hackedSeq);
            Extension hackedExt = new Extension(OID, false, hackedSeqOctets);
            builder.addExtension(hackedExt);

            for (ASN1ObjectIdentifier extensionOID : leafHolder.getExtensions().getExtensionOIDs()) {
                if (OID.getId().equals(extensionOID.getId())) continue;
                builder.addExtension(leafHolder.getExtension(extensionOID));
            }
            // 返回篡改后的用户证书
            return new JcaX509CertificateConverter().getCertificate(builder.build(signer)).getEncoded();

        } catch (Throwable t) {
            Logger.e("", t);
        }
        return certificate;
    }

    /**
     * 生成指定参数的密钥对
     * @param params 密钥生成参数
     * @return 生成的密钥对
     */
    public static KeyPair generateKeyPair(KeyGenParameters params){
        KeyPair kp;
        try {
            var algo = params.algorithm;
            if (algo == Algorithm.EC) {
                Logger.d("GENERATING EC KEYPAIR OF SIZE " + params.keySize);
                kp = buildECKeyPair(params);
            } else if (algo == Algorithm.RSA) {
                Logger.d("GENERATING RSA KEYPAIR OF SIZE " + params.keySize);
                kp = buildRSAKeyPair(params);
            } else {
                Logger.e("UNSUPPORTED ALGORITHM: " + algo);
                return null;
            }
            return kp;
        } catch (Throwable t) {
            Logger.e("", t);
        }
        return null;
    }

    /**
     * 为指定密钥对生成伪造的证书链
     * @param uid 用户ID
     * @param params 密钥生成参数
     * @param kp 密钥对
     * @return 证书链字节列表
     */
    public static List<byte[]> generateChain(int uid, KeyGenParameters params, KeyPair kp){
        KeyPair rootKP;
        X500Name issuer;
        KeyBox keyBox = null;
        try{
            var algo = params.algorithm;
            // 根据算法选择预置密钥盒
            if (algo == Algorithm.EC) {
                keyBox = keyboxes.get(KeyProperties.KEY_ALGORITHM_EC);
            } else if (algo == Algorithm.RSA) {
                keyBox = keyboxes.get(KeyProperties.KEY_ALGORITHM_RSA);
            }
            if (keyBox == null) {
                Logger.e("UNSUPPORTED ALGORITHM: " + algo);
                return null;
            }
            rootKP = keyBox.keyPair;
            issuer = new X509CertificateHolder(
                    keyBox.certificates.get(0).getEncoded()
            ).getSubject();

            // 构建证书
            X509v3CertificateBuilder certBuilder = new JcaX509v3CertificateBuilder(issuer,
                    new BigInteger("1"),//params.certificateSerial,
                    params.certificateNotBefore,
                    ((X509Certificate)keyBox.certificates.get(0)).getNotAfter(),//params.certificateNotAfter,
                    new X500Name("CN=Android KeyStore Key"),//params.certificateSubject,
                    kp.getPublic()
            );

            // 添加密钥用途扩展
            KeyUsage keyUsage = new KeyUsage(KeyUsage.keyCertSign);
            certBuilder.addExtension(Extension.keyUsage, true, keyUsage);
            // 添加伪造的Android密钥证明扩展
            certBuilder.addExtension(createExtension(params, uid));

            ContentSigner contentSigner;
            if (algo == Algorithm.EC) {
                contentSigner = new JcaContentSignerBuilder("SHA256withECDSA").build(rootKP.getPrivate());
            } else {
                contentSigner = new JcaContentSignerBuilder("SHA256withRSA").build(rootKP.getPrivate());
            }
            // 生成证书
            X509CertificateHolder certHolder = certBuilder.build(contentSigner);
            var leaf = new JcaX509CertificateConverter().getCertificate(certHolder);
            // 组合证书链：新证书+预置证书链
            List<Certificate> chain = new ArrayList<>(keyBox.certificates);
            chain.add(0, leaf);
            return Utils.toListBytes(chain);
        } catch (Throwable t) {
            Logger.e("", t);
        }
        return null;
    }

    /**
     * 生成密钥对及对应的伪造证书链（带详细参数）
     * @param uid 用户ID
     * @param descriptor 密钥描述符
     * @param attestKeyDescriptor 证明密钥描述符
     * @param params 密钥生成参数
     * @return 密钥对和证书链
     */
    public static Pair<KeyPair, List<Certificate>> generateKeyPair(int uid, KeyDescriptor descriptor, KeyDescriptor attestKeyDescriptor, KeyGenParameters params) {
        Logger.i("Requested KeyPair with alias: " + descriptor.alias);
        boolean attestPurpose = attestKeyDescriptor != null;
        if (attestPurpose)
            Logger.i("Requested KeyPair with attestKey: " + attestKeyDescriptor.alias);
        KeyPair rootKP;
        X500Name issuer;
        int size = params.keySize;
        KeyPair kp = null;
        KeyBox keyBox = null;
        try {
            var algo = params.algorithm;
            if (algo == Algorithm.EC) {
                Logger.d("GENERATING EC KEYPAIR OF SIZE " + size);
                kp = buildECKeyPair(params);
                keyBox = keyboxes.get(KeyProperties.KEY_ALGORITHM_EC);
            } else if (algo == Algorithm.RSA) {
                Logger.d("GENERATING RSA KEYPAIR OF SIZE " + size);
                kp = buildRSAKeyPair(params);
                keyBox = keyboxes.get(KeyProperties.KEY_ALGORITHM_RSA);
            }
            if (keyBox == null) {
                Logger.e("UNSUPPORTED ALGORITHM: " + algo);
                return null;
            }
            rootKP = keyBox.keyPair;
            issuer = new X509CertificateHolder(
                    keyBox.certificates.get(0).getEncoded()
            ).getSubject();

            // 处理证明密钥场景
            if (attestPurpose) {
                var info = SecurityLevelInterceptor.Companion.getKeyPairs(uid, attestKeyDescriptor.alias);
                if (info != null) {
                    rootKP = info.getFirst();
                    issuer = new X509CertificateHolder(
                            info.getSecond().get(0).getEncoded()
                    ).getSubject();
                }
            }

            Logger.d("certificateSubject: " + params.certificateSubject);
            // 构建证书
            X509v3CertificateBuilder certBuilder = new JcaX509v3CertificateBuilder(issuer,
                    params.certificateSerial,
                    params.certificateNotBefore,
                    params.certificateNotAfter,
                    params.certificateSubject,
                    kp.getPublic()
            );

            KeyUsage keyUsage = new KeyUsage(KeyUsage.keyCertSign);
            certBuilder.addExtension(Extension.keyUsage, true, keyUsage);
            certBuilder.addExtension(createExtension(params, uid));

            ContentSigner contentSigner;
            if (algo == Algorithm.EC) {
                contentSigner = new JcaContentSignerBuilder("SHA256withECDSA").build(rootKP.getPrivate());
            } else {
                contentSigner = new JcaContentSignerBuilder("SHA256withRSA").build(rootKP.getPrivate());
            }
            X509CertificateHolder certHolder = certBuilder.build(contentSigner);
            var leaf = new JcaX509CertificateConverter().getCertificate(certHolder);
            List<Certificate> chain;
            if (!attestPurpose) {
                chain = new ArrayList<>(keyBox.certificates);
            } else {
                chain = new ArrayList<>();
            }
            chain.add(0, leaf);
            Logger.d("Successfully generated X500 Cert for alias: " + descriptor.alias);
            return new Pair<>(kp, chain);
        } catch (Throwable t) {
            Logger.e("", t);
        }
        return null;
    }

    /**
     * 生成EC密钥对
     * @param params 密钥参数
     */
    private static KeyPair buildECKeyPair(KeyGenParameters params) throws Exception {
        // 使用Bouncy Castle提供者
        Security.removeProvider(BouncyCastleProvider.PROVIDER_NAME);
        Security.addProvider(new BouncyCastleProvider());
        ECGenParameterSpec spec = new ECGenParameterSpec(params.ecCurveName);
        KeyPairGenerator kpg = KeyPairGenerator.getInstance("ECDSA", BouncyCastleProvider.PROVIDER_NAME);
        kpg.initialize(spec);
        return kpg.generateKeyPair();
    }

    /**
     * 生成RSA密钥对
     * @param params 密钥参数
     */
    private static KeyPair buildRSAKeyPair(KeyGenParameters params) throws Exception {
        Security.removeProvider(BouncyCastleProvider.PROVIDER_NAME);
        Security.addProvider(new BouncyCastleProvider());
        RSAKeyGenParameterSpec spec = new RSAKeyGenParameterSpec(
                params.keySize, params.rsaPublicExponent);
        KeyPairGenerator kpg = KeyPairGenerator.getInstance("RSA", BouncyCastleProvider.PROVIDER_NAME);
        kpg.initialize(spec);
        return kpg.generateKeyPair();
    }

    /**
     * 将整数列表转换为ASN1Encodable数组
     * @param list 整数列表
     * @return ASN1Encodable数组
     */
    private static ASN1Encodable[] fromIntList(List<Integer> list) {
        ASN1Encodable[] result = new ASN1Encodable[list.size()];
        for (int i = 0; i < list.size(); i++) {
            result[i] = new ASN1Integer(list.get(i));
        }
        return result;
    }

    /**
     * 创建Android密钥证明扩展
     * @param params 密钥参数
     * @param uid 用户ID
     * @return 构造的扩展对象
     */
    private static Extension createExtension(KeyGenParameters params, int uid) {
        try {
            // 获取设备引导信息
            byte[] key = UtilKt.getBootKey();
            byte[] hash = UtilKt.getBootHash();

            // 构建RootOfTrust结构
            ASN1Encodable[] rootOfTrustEncodables = {new DEROctetString(key), ASN1Boolean.TRUE,
                    new ASN1Enumerated(0), new DEROctetString(hash)};
            ASN1Sequence rootOfTrustSeq = new DERSequence(rootOfTrustEncodables);

            Logger.dd("params.purpose: " + params.purpose);

            // 构建密钥描述字段
            var Apurpose = new DERSet(fromIntList(params.purpose));
            var Aalgorithm = new ASN1Integer(params.algorithm);
            var AkeySize = new ASN1Integer(params.keySize);
            var Adigest = new DERSet(fromIntList(params.digest));
            var AecCurve = new ASN1Integer(params.ecCurve);
            var AnoAuthRequired = DERNull.INSTANCE;

            // 系统信息字段
            var AosVersion = new ASN1Integer(UtilKt.getOsVersion());
            var AosPatchLevel = new ASN1Integer(UtilKt.getPatchLevel());
            var AapplicationID = createApplicationId(uid);
            var AbootPatchlevel = new ASN1Integer(UtilKt.getPatchLevelLong());
            var AvendorPatchLevel = new ASN1Integer(UtilKt.getPatchLevelLong());
            var AcreationDateTime = new ASN1Integer(System.currentTimeMillis());
            var Aorigin = new ASN1Integer(0);

            // 封装为ASN1标签对象
            var purpose = new DERTaggedObject(true, 1, Apurpose);
            var algorithm = new DERTaggedObject(true, 2, Aalgorithm);
            var keySize = new DERTaggedObject(true, 3, AkeySize);
            var digest = new DERTaggedObject(true, 5, Adigest);
            var ecCurve = new DERTaggedObject(true, 10, AecCurve);
            var noAuthRequired = new DERTaggedObject(true, 503, AnoAuthRequired);
            var creationDateTime = new DERTaggedObject(true, 701, AcreationDateTime);
            var origin = new DERTaggedObject(true, 702, Aorigin);
            var rootOfTrust = new DERTaggedObject(true, 704, rootOfTrustSeq);
            var osVersion = new DERTaggedObject(true, 705, AosVersion);
            var osPatchLevel = new DERTaggedObject(true, 706, AosPatchLevel);
            var applicationID = new DERTaggedObject(true, 709, AapplicationID);
            var vendorPatchLevel = new DERTaggedObject(true, 718, AvendorPatchLevel);
            var bootPatchLevel = new DERTaggedObject(true, 719, AbootPatchlevel);
            var AmoduleHash = new DEROctetString(UtilKt.getModuleHash());
            var moduleHash = new DERTaggedObject(true, 724 , AmoduleHash);

            // 收集所有TEE强制字段
            var arrayList = new ArrayList<>(Arrays.asList(purpose, algorithm, keySize, digest, ecCurve,
                    noAuthRequired, origin, rootOfTrust, osVersion, osPatchLevel, vendorPatchLevel,
                    bootPatchLevel, moduleHash));

            // 添加设备标识信息（如果存在）
            if (params.brand != null) {
                var Abrand = new DEROctetString(params.brand);
                var Adevice = new DEROctetString(params.device);
                var Aproduct = new DEROctetString(params.product);
                var Amanufacturer = new DEROctetString(params.manufacturer);
                var Amodel = new DEROctetString(params.model);

                var brand = new DERTaggedObject(true, 710, Abrand);
                var device = new DERTaggedObject(true, 711, Adevice);
                var product = new DERTaggedObject(true, 712, Aproduct);
                var manufacturer = new DERTaggedObject(true, 716, Amanufacturer);
                var model = new DERTaggedObject(true, 717, Amodel);

                arrayList.addAll(List.of(brand, device, product, manufacturer, model));
                arrayList.addAll(UtilKt.getTelephonyInfos());
            }

            // 按标签号排序（规范要求）
            arrayList.sort(Comparator.comparingInt(ASN1TaggedObject::getTagNo));

            // 软件强制字段
            ASN1Encodable[] softwareEnforced = {applicationID, creationDateTime};

            // 生成完整的密钥描述结构
            ASN1OctetString keyDescriptionOctetStr = getAsn1OctetString(arrayList.toArray(new ASN1Encodable[]{}), softwareEnforced, params);

            // 创建扩展对象
            return new Extension(new ASN1ObjectIdentifier("1.3.6.1.4.1.11129.2.1.17"), false, keyDescriptionOctetStr);
        } catch (Throwable t) {
            Logger.e("", t);
        }
        return null;
    }

    /**
     * 构建密钥描述ASN1结构
     * @param teeEnforcedEncodables TEE强制字段
     * @param softwareEnforcedEncodables 软件强制字段
     * @param params 密钥参数
     */
    private static ASN1OctetString getAsn1OctetString(ASN1Encodable[] teeEnforcedEncodables, ASN1Encodable[] softwareEnforcedEncodables, KeyGenParameters params) throws IOException {
        // 固定安全级别和版本号
        ASN1Integer attestationVersion = new ASN1Integer(400);
        ASN1Enumerated attestationSecurityLevel = new ASN1Enumerated(1);
        ASN1Integer keymasterVersion = new ASN1Integer(400);
        ASN1Enumerated keymasterSecurityLevel = new ASN1Enumerated(1);
        
        // 挑战值和唯一ID
        ASN1OctetString attestationChallenge = new DEROctetString(params.attestationChallenge);
        ASN1OctetString uniqueId = new DEROctetString("".getBytes());
        
        // 封装强制字段
        ASN1Encodable softwareEnforced = new DERSequence(softwareEnforcedEncodables);
        ASN1Sequence teeEnforced = new DERSequence(teeEnforcedEncodables);

        // 组合完整结构
        ASN1Encodable[] keyDescriptionEncodables = {attestationVersion, attestationSecurityLevel, keymasterVersion,
                keymasterSecurityLevel, attestationChallenge, uniqueId, softwareEnforced, teeEnforced};

        ASN1Sequence keyDescriptionHackSeq = new DERSequence(keyDescriptionEncodables);

        return new DEROctetString(keyDescriptionHackSeq);
    }

    /**
     * 创建应用ID结构（包含包名和签名信息）
     * @param uid 用户ID
     */
    private static DEROctetString createApplicationId(int uid) throws Throwable {
        var pm = Config.INSTANCE.getPm();
        if (pm == null) {
            throw new IllegalStateException("createApplicationId: pm not found!");
        }
        // 获取UID对应的所有包名
        var packages = pm.getPackagesForUid(uid);
        var size = packages.length;
        ASN1Encodable[] packageInfoAA = new ASN1Encodable[size];
        Set<Digest> signatures = new HashSet<>();
        var dg = MessageDigest.getInstance("SHA-256");
        
        // 遍历所有包
        for (int i = 0; i < size; i++) {
            var name = packages[i];
            // 获取包信息（包含签名）
            var info = UtilKt.getPackageInfoCompat(pm, name, PackageManager.GET_SIGNATURES, uid / 100000);
            ASN1Encodable[] arr = new ASN1Encodable[2];
            // 包名
            arr[ATTESTATION_PACKAGE_INFO_PACKAGE_NAME_INDEX] =
                    new DEROctetString(packages[i].getBytes(StandardCharsets.UTF_8));
            // 版本号
            arr[ATTESTATION_PACKAGE_INFO_VERSION_INDEX] = new ASN1Integer(info.getLongVersionCode());
            packageInfoAA[i] = new DERSequence(arr);
            // 计算所有签名的SHA256摘要
            for (var s : info.signatures) {
                signatures.add(new Digest(dg.digest(s.toByteArray())));
            }
        }

        // 转换签名为DEROctetString数组
        ASN1Encodable[] signaturesAA = new ASN1Encodable[signatures.size()];
        var i = 0;
        for (var d : signatures) {
            signaturesAA[i] = new DEROctetString(d.digest);
            i++;
        }

        // 构建应用ID结构
        ASN1Encodable[] applicationIdAA = new ASN1Encodable[2];
        applicationIdAA[ATTESTATION_APPLICATION_ID_PACKAGE_INFOS_INDEX] =
                new DERSet(packageInfoAA);  // 包信息集合
        applicationIdAA[ATTESTATION_APPLICATION_ID_SIGNATURE_DIGESTS_INDEX] =
                new DERSet(signaturesAA);   // 签名摘要集合

        return new DEROctetString(new DERSequence(applicationIdAA).getEncoded());
    }

    /**
     * 摘要记录类（用于签名去重）
     */
    record Digest(byte[] digest) {
        @Override
        public boolean equals(@Nullable Object o) {
            if (o instanceof Digest d)
                return Arrays.equals(digest, d.digest);
            return false;
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(digest);
        }
    }

    /**
     * 密钥盒容器（存储PEM密钥对、Java密钥对和证书链）
     */
    record KeyBox(PEMKeyPair pemKeyPair, KeyPair keyPair, List<Certificate> certificates) {
    }

    /**
     * 密钥生成参数容器类
     */
    public static class KeyGenParameters {
        public int keySize;
        public int algorithm;
        public BigInteger certificateSerial;
        public Date certificateNotBefore;
        public Date certificateNotAfter;
        public X500Name certificateSubject;

        public BigInteger rsaPublicExponent;
        public int ecCurve;
        public String ecCurveName;

        public List<Integer> purpose = new ArrayList<>();
        public List<Integer> digest = new ArrayList<>();

        public byte[] attestationChallenge;
        public byte[] brand;
        public byte[] device;
        public byte[] product;
        public byte[] manufacturer;
        public byte[] model;
        public byte[] imei1, imei2;
        public byte[] meid;

        public KeyGenParameters(){}
        
        /**
         * 从KeyParameter数组构造参数对象
         * @param params KeyMint参数数组
         */
        public KeyGenParameters(KeyParameter[] params) {
            for (var kp : params) {
                Logger.d("kp: " + kp.tag);
                var p = kp.value;
                switch (kp.tag) {
                    case Tag.KEY_SIZE -> keySize = p.getInteger();
                    case Tag.ALGORITHM -> algorithm = p.getAlgorithm();
                    case Tag.CERTIFICATE_SERIAL -> certificateSerial = new BigInteger(p.getBlob());
                    case Tag.CERTIFICATE_NOT_BEFORE ->
                            certificateNotBefore = new Date(p.getDateTime());
                    case Tag.CERTIFICATE_NOT_AFTER ->
                            certificateNotAfter = new Date(p.getDateTime());
                    case Tag.CERTIFICATE_SUBJECT ->
                            certificateSubject = new X500Name(new X500Principal(p.getBlob()).getName());
                    case Tag.RSA_PUBLIC_EXPONENT -> rsaPublicExponent = new BigInteger(p.getBlob());
                    case Tag.EC_CURVE -> {
                        ecCurve = p.getEcCurve();
                        ecCurveName = getEcCurveName(ecCurve);
                    }
                    case Tag.PURPOSE -> purpose.add(p.getKeyPurpose());
                    case Tag.DIGEST -> digest.add(p.getDigest());
                    case Tag.ATTESTATION_CHALLENGE -> attestationChallenge = p.getBlob();
                    case Tag.ATTESTATION_ID_BRAND -> brand = p.getBlob();
                    case Tag.ATTESTATION_ID_DEVICE -> device = p.getBlob();
                    case Tag.ATTESTATION_ID_PRODUCT -> product = p.getBlob();
                    case Tag.ATTESTATION_ID_MANUFACTURER -> manufacturer = p.getBlob();
                    case Tag.ATTESTATION_ID_MODEL -> model = p.getBlob();
                    case Tag.ATTESTATION_ID_IMEI -> imei1 = p.getBlob();
                    case Tag.ATTESTATION_ID_SECOND_IMEI -> imei2 = p.getBlob();
                    case Tag.ATTESTATION_ID_MEID -> meid = p.getBlob();
                }
            }
        }

        /**
         * 将椭圆曲线标识转换为标准名称
         * @param curve 曲线标识符
         * @return 标准曲线名称
         */
        private static String getEcCurveName(int curve) {
            String res;
            switch (curve) {
                case EcCurve.CURVE_25519 -> res = "CURVE_25519";
                case EcCurve.P_224 -> res = "secp224r1";
                case EcCurve.P_256 -> res = "secp256r1";
                case EcCurve.P_384 -> res = "secp384r1";
                case EcCurve.P_521 -> res = "secp521r1";
                default -> throw new IllegalArgumentException("unknown curve");
            }
            return res;
        }
        
        /**
         * 根据密钥大小设置曲线名称（兼容旧版）
         * @param curve 密钥长度
         */
        public void setEcCurveName(int curve) {
            switch (curve) {
                case 224 -> this.ecCurveName = "secp224r1";
                case 256 -> this.ecCurveName = "secp256r1";
                case 384 -> this.ecCurveName = "secp384r1";
                case 521 -> this.ecCurveName = "secp521r1";
            }
        }
    }
}