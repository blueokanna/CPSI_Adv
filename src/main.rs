//! main.rs
//! UMPSI 多方可更新式集合求交 - 基于哈希表结构的完整可部署版本

use blake3;
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT,
    ristretto::RistrettoPoint,
    scalar::Scalar,
};
use num_bigint::BigUint;
use rand::prelude::*;
use rand_core::{OsRng, TryRngCore};
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::ops::Neg;
use rand::thread_rng;
use zeroize::Zeroize;

/// Ristretto 群阶（十进制字符串）
const RISTRETTO_GROUP_ORDER_DEC: &str = "723700557733226221397318656304299424087";

/// 将标量（32字节）转换为十进制字符串
fn scalar_to_decimal(s: &Scalar) -> String {
    let bytes_le = s.to_bytes(); // 小端序
    let big = BigUint::from_bytes_le(&bytes_le);
    big.to_str_radix(10)
}

/// 将任意字节数组安全哈希映射到 Ristretto 群
fn hash_to_group(label: &[u8]) -> RistrettoPoint {
    let hash1 = blake3::hash(label);
    let mut label2 = Vec::with_capacity(label.len() + 2);
    label2.extend_from_slice(label);
    label2.extend_from_slice(b"-2");
    let hash2 = blake3::hash(&label2);

    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(hash1.as_bytes());
    wide[32..].copy_from_slice(hash2.as_bytes());

    let h = RistrettoPoint::from_uniform_bytes(&wide);
    if h == RistrettoPoint::default() {
        panic!("哈希映射结果为恒等元，极小概率冲突，请改进哈希函数。");
    }
    h
}

/// 计算候选元素的哈希键（用于哈希表索引），这里取 Blake3 哈希的 32 字节结果
fn element_hash_key(element: &[u8]) -> Vec<u8> {
    blake3::hash(element).as_bytes().to_vec()
}

/// EC-ElGamal 密文，支持同态加法
#[derive(Clone, Debug)]
struct ElGamalCiphertext {
    version: u32,      // 区分主密钥版本
    a: RistrettoPoint, // r * G
    b: RistrettoPoint, // m * H + r * master_pubkey
}

impl ElGamalCiphertext {
    /// 同态加法：分量逐项相加
    pub fn add(&self, other: &ElGamalCiphertext) -> Self {
        assert_eq!(
            self.version, other.version,
            "不同版本的密文无法同态相加"
        );
        Self {
            version: self.version,
            a: self.a + other.a,
            b: self.b + other.b,
        }
    }
}

/// 参与方
#[derive(Debug)]
struct Participant {
    index: u32,                    // 参与方序号
    secret_share: Scalar,          // 门限秘密份额
    public_share: RistrettoPoint,  // 公钥份额
    /// 该参与方持有的原始元素集合（若某个元素在集合中则视为“插入”，否则视为不更新；
    /// 若需要“删除”，则可自行对集合进行变更，然后调用更新操作，更新时使用 delta = -1）
    elements: HashSet<Vec<u8>>,
    group: Option<u32>,            // 可选分组 ID
}

impl Participant {
    pub fn new(elements: HashSet<Vec<u8>>, group: Option<u32>) -> Self {
        Self {
            index: 0,
            secret_share: Scalar::ZERO,
            public_share: RistrettoPoint::default(),
            elements,
            group,
        }
    }

    /// 针对某个候选元素进行更新（delta 为加/减的值，通常为 1 或 -1），输出 ElGamal 密文
    fn encrypt_update(
        &self,
        master_pubkey: &RistrettoPoint,
        h: &RistrettoPoint,
        element: &[u8],
        delta: Scalar,
        version: u32,
    ) -> ElGamalCiphertext {
        // 如果该参与方持有该元素，则默认增量为 +1；如果不持有，则视为 0（也可以自行对删除进行 -1 更新）
        let m = if self.elements.contains(element) { delta } else { Scalar::ZERO };
        let mut rng = OsRng;
        let mut buf = [0u8; 64];
        rng.try_fill_bytes(&mut buf).unwrap();
        let r = Scalar::from_bytes_mod_order_wide(&buf);

        let a = r * RISTRETTO_BASEPOINT_POINT;
        let b = m * (*h) + r * (*master_pubkey);
        ElGamalCiphertext { version, a, b }
    }
}

/// 离散对数求解（只需求 m=0..max_count 的值）
fn discrete_log(dec_point: RistrettoPoint, h: RistrettoPoint, max_count: u32) -> Result<u32, String> {
    // 若 max_count 不大时，可用线性搜索
    if max_count <= 1000 {
        let mut current = RistrettoPoint::default();
        for m in 0..=max_count {
            if current == dec_point {
                return Ok(m);
            }
            current += h;
        }
        return Err("线性搜索未找到对应m".to_string());
    }
    // 否则使用 Baby-step Giant-step
    let n = (max_count as f64).sqrt().ceil() as u32;
    let mut baby_steps: HashMap<[u8; 32], u32> = HashMap::new();
    let mut baby = RistrettoPoint::default();
    for j in 0..=n {
        baby_steps.insert(baby.compress().to_bytes(), j);
        baby += h;
    }
    let factor = Scalar::from(n) * h;
    let factor_neg = factor.neg();
    let mut current = dec_point;
    for i in 0..=n {
        let key = current.compress().to_bytes();
        if let Some(&j) = baby_steps.get(&key) {
            let m = i * n + j;
            if m <= max_count {
                return Ok(m);
            }
        }
        current += factor_neg;
    }
    Err("BSGS 未找到对应m".to_string())
}

/// “链式”加密时传递的哈希表结构（以候选元素哈希值为 key，每个 key 对应一个 ElGamalCiphertext）
#[derive(Clone)]
struct EncryptedHashMap {
    version: u32,
    ciphertexts: HashMap<Vec<u8>, ElGamalCiphertext>,
}

impl EncryptedHashMap {
    /// 初始化：给定候选元素集合与版本号，构造每个候选元素位置初始均为 m=0 的同态加密
    pub fn new_empty(candidate_elements: &[Vec<u8>], version: u32, master_pubkey: &RistrettoPoint) -> Self {
        let mut rng = OsRng;
        let mut ciphertexts = HashMap::new();
        for elem in candidate_elements {
            let mut buf = [0u8; 64];
            rng.try_fill_bytes(&mut buf).unwrap();
            let r = Scalar::from_bytes_mod_order_wide(&buf);
            let ct = ElGamalCiphertext {
                version,
                a: r * RISTRETTO_BASEPOINT_POINT,
                b: r * (*master_pubkey), // m=0 => b = r*master_pubkey
            };
            let key = element_hash_key(elem);
            ciphertexts.insert(key, ct);
        }
        Self { version, ciphertexts }
    }

    /// 对哈希表中所有候选元素进行同态更新（每个参与方依次调用），更新时对于每个候选元素，调用参与方加密更新操作，
    /// 并将生成的密文同态加到哈希表中对应的密文上
    pub fn chain_encrypt_update(
        &mut self,
        participant: &Participant,
        master_pubkey: &RistrettoPoint,
        h: &RistrettoPoint,
        candidate_elements: &[Vec<u8>], // 更新时使用的增量（例如 +1 或 -1）
        delta: Scalar,
    ) {
        // 对于每个候选元素，根据哈希键定位后更新
        for elem in candidate_elements {
            let key = element_hash_key(elem);
            let ct_update = participant.encrypt_update(master_pubkey, h, elem, delta, self.version);
            self.ciphertexts
                .entry(key)
                .and_modify(|ct| {
                    *ct = ct.add(&ct_update);
                })
                .or_insert(ct_update);
        }
    }
}

/// 协议引擎
struct ProtocolEngine {
    participants: Vec<Participant>,
    union_counts: HashMap<Vec<u8>, u32>,
    master_secret: Scalar,
    master_pubkey: RistrettoPoint,
    h: RistrettoPoint,

    secret_threshold: u32,              // 门限
    intersection_threshold: u32,        // 交集阈值
    exact_intersection: bool,           // 是否为精确求交
    current_version: u32,               // 当前主密钥版本
    precomputed_lagrange: Vec<Scalar>,  // 拉格朗日系数
    version_agg_secret: HashMap<u32, Scalar>, // 各版本的聚合私钥
}

impl ProtocolEngine {
    /// 创建新的协议引擎
    pub fn new(secret_threshold: u32, intersection_threshold: u32, exact_intersection: bool) -> Self {
        let h = hash_to_group(b"UMPSI-BASE-H");
        let mut rng = OsRng;
        let mut buf = [0u8; 64];
        rng.try_fill_bytes(&mut buf).unwrap();
        let master_secret = Scalar::from_bytes_mod_order_wide(&buf);

        let master_pubkey = RISTRETTO_BASEPOINT_POINT * master_secret;

        Self {
            participants: Vec::new(),
            union_counts: HashMap::new(),
            master_secret,
            master_pubkey,
            h,
            secret_threshold,
            intersection_threshold,
            exact_intersection,
            current_version: 1,
            precomputed_lagrange: Vec::new(),
            version_agg_secret: HashMap::new(),
        }
    }

    /// 添加参与方
    pub fn add_participant(&mut self, mut participant: Participant) {
        participant.index = self.participants.len() as u32 + 1;
        for elem in &participant.elements {
            *self.union_counts.entry(elem.clone()).or_insert(0) += 1;
        }
        self.participants.push(participant);
    }

    /// 分发门限份额给所有参与方
    pub fn distribute_threshold_shares(&mut self) {
        let n = self.participants.len();
        assert!(
            n as u32 >= self.secret_threshold,
            "参与方数量不足以满足门限要求"
        );

        let mut rng = OsRng;
        let mut coeffs = Vec::with_capacity(self.secret_threshold as usize);
        // 多项式常数项
        coeffs.push(self.master_secret);
        // 其余系数
        for _ in 1..self.secret_threshold {
            let mut buf = [0u8; 64];
            rng.try_fill_bytes(&mut buf).unwrap();
            let coeff = Scalar::from_bytes_mod_order_wide(&buf);
            coeffs.push(coeff);
        }

        // 计算并分发 share(i)
        for participant in self.participants.iter_mut() {
            let x = Scalar::from(participant.index);
            let mut share = Scalar::ZERO;
            let mut x_pow = Scalar::ONE;
            for coeff in &coeffs {
                share += coeff * x_pow;
                x_pow *= x;
            }
            participant.secret_share = share;
            participant.public_share = share * RISTRETTO_BASEPOINT_POINT;
        }

        // 更新系统的主公钥
        self.master_pubkey = self.master_secret * RISTRETTO_BASEPOINT_POINT;

        // 预计算拉格朗日系数
        self.precomputed_lagrange = self.compute_all_lagrange();

        // 计算当前版本的聚合密钥
        let agg_secret = self
            .participants
            .par_iter()
            .enumerate()
            .map(|(idx, p)| self.precomputed_lagrange[idx] * p.secret_share)
            .reduce(|| Scalar::ZERO, |s1, s2| s1 + s2);

        self.version_agg_secret.clear();
        self.version_agg_secret.insert(self.current_version, agg_secret);

        coeffs.zeroize();
    }

    /// 计算所有参与方对应的拉格朗日系数
    fn compute_all_lagrange(&self) -> Vec<Scalar> {
        let indices: Vec<u32> = self.participants.iter().map(|p| p.index).collect();
        indices
            .iter()
            .map(|&i| self.lagrange_coefficient(&indices, i))
            .collect()
    }

    /// 计算单个拉格朗日系数 λ_i
    fn lagrange_coefficient(&self, indices: &[u32], i: u32) -> Scalar {
        let xi = Scalar::from(i);
        indices
            .iter()
            .filter(|&&j| j != i)
            .fold(Scalar::ONE, |acc, &j| {
                // λ_i = ∏ ( -x_j / (x_i - x_j) )
                acc * (-Scalar::from(j)) * (xi - Scalar::from(j)).invert()
            })
    }

    /// 链式加密流程：给定候选元素集合，构造一个预填充的加密哈希表，然后依次让各参与方对其同态更新，
    /// 参数 delta 用于区分插入（+1）或删除（-1）
    pub fn chain_encryption_process_map(
        &mut self,
        candidate_elements: &[Vec<u8>],
        delta: Scalar,
    ) -> EncryptedHashMap {
        // 初始化空哈希表（所有候选元素初始加密为0）
        let mut enc_map = EncryptedHashMap::new_empty(candidate_elements, self.current_version, &self.master_pubkey);

        // 依次让每个参与方对该表进行同态更新
        for participant in &self.participants {
            enc_map.chain_encrypt_update(
                participant,
                &self.master_pubkey,
                &self.h,
                candidate_elements,
                delta,
            );
        }

        enc_map
    }

    /// 阈值解密：对单个 ElGamalCiphertext 解出其同态累加的计数
    pub fn decrypt_count(&self, ct: &ElGamalCiphertext) -> Result<u32, String> {
        let agg_secret = self
            .version_agg_secret
            .get(&ct.version)
            .ok_or_else(|| format!("版本{}的聚合密钥不存在", ct.version))?;
        let dec_point = ct.b - (*agg_secret * ct.a);
        let max_count = self.participants.len() as u32;
        discrete_log(dec_point, self.h, max_count)
    }

    /// 动态更新门限参数并旋转主密钥
    pub fn update_thresholds(
        &mut self,
        new_threshold: u32,
        new_intersection_threshold: u32,
        new_exact: bool,
    ) {
        self.secret_threshold = new_threshold;
        self.intersection_threshold = new_intersection_threshold;
        self.exact_intersection = new_exact;

        // 旋转主密钥
        let mut rng = OsRng;
        let mut buf = [0u8; 64];
        rng.try_fill_bytes(&mut buf).unwrap();
        self.master_secret = Scalar::from_bytes_mod_order_wide(&buf);
        self.master_pubkey = self.master_secret * RISTRETTO_BASEPOINT_POINT;

        // 清空旧聚合密钥，版本号自增
        self.version_agg_secret.clear();
        self.current_version += 1;
        // 重新分发
        self.distribute_threshold_shares();
    }
}

impl Drop for ProtocolEngine {
    fn drop(&mut self) {
        self.master_secret.zeroize();
        self.precomputed_lagrange.zeroize();
        for (_, sec) in self.version_agg_secret.iter_mut() {
            sec.zeroize();
        }
    }
}

/// 演示主函数
fn main() {
    println!("======= UMPSI Demo (Ristretto/Curve25519) =======");
    println!("[曲线阶] {}", RISTRETTO_GROUP_ORDER_DEC);

    // 1) 初始化引擎
    let mut engine = ProtocolEngine::new(3, 3, true);
    println!("[初始 master_secret] = {}", scalar_to_decimal(&engine.master_secret));

    // 2) 添加参与方（示例：5个参与方）
    let total_participants = 5;
    let possible_elems = vec![b"A".to_vec(), b"B".to_vec(), b"C".to_vec(), b"D".to_vec()];
    for _ in 0..total_participants {
        let mut rng = thread_rng();
        let mut set = HashSet::new();
        for e in &possible_elems {
            if rng.gen_bool(0.5) {
                set.insert(e.clone());
            }
        }
        engine.add_participant(Participant::new(set, None));
    }

    // 3) 分发门限份额
    engine.distribute_threshold_shares();
    println!("门限份额分发完成，共 {} 个参与方。", engine.participants.len());

    // 4) 链式加密流程：使用候选元素集合构造加密哈希表，默认更新为插入操作（delta = +1）
    let enc_map = engine.chain_encryption_process_map(&possible_elems, Scalar::ONE);

    // 5) 解密查看计数
    println!("\n[解密查看计数]：");
    for elem in &possible_elems {
        let key = element_hash_key(elem);
        if let Some(ct) = enc_map.ciphertexts.get(&key) {
            let count = engine.decrypt_count(ct).unwrap();
            println!(
                "候选元素 {:?} -> 计数 {}",
                String::from_utf8_lossy(elem),
                count
            );
        }
    }

    // 6) 动态更新门限参数（阈值=4，交集阈值=2，改为非精确），并旋转主密钥
    println!("\n[动态更新门限并旋转主密钥]...");
    engine.update_thresholds(4, 2, false);

    // 7) 再次执行链式更新流程（此处可以模拟删除操作，更新时使用 delta = -1，例如对某些候选元素进行减操作）
    //    这里示范依然用插入操作（delta = +1），实际部署时可根据需要选择更新的方向
    let enc_map2 = engine.chain_encryption_process_map(&possible_elems, Scalar::ONE);
    println!("\n[新版本下再次解密计数]：");
    for elem in &possible_elems {
        let key = element_hash_key(elem);
        if let Some(ct) = enc_map2.ciphertexts.get(&key) {
            let count = engine.decrypt_count(ct).unwrap();
            println!(
                "候选元素 {:?} -> 计数 {}",
                String::from_utf8_lossy(elem),
                count
            );
        }
    }

    println!("\n======= UMPSI Demo 结束 =======");
}
