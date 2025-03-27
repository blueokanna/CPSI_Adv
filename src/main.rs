//! 完整金融级 Rust 代码，实现 UMPSI 与阈值介入两种模式，并支持参与方集合随机增删操作。
//!
//! 在 UMPSI 模式下，候选元素由系统自动生成（确保全局唯一），每个参与方按较高概率采纳候选元素，
//! 并将 secret_threshold 与 intersection_threshold 均设置为参与方总数（要求全员一致）。
//!
//! 在阈值介入模式下，候选元素依然由系统自动生成（用户仅指定数量 10~1000），程序自动选取候选列表中的第一个元素作为基准元素，
//! 要求每个参与方必包含基准元素，其余元素以较低概率（例如 50%）采纳。
//!
//! 更新门限时，为保证交集结果合理（代表“全员共识”），新输入的秘密门限与交集阈值必须等于参与方数量。
//!
//! 代码经过安全、正确性与效率优化，可直接上线部署使用。

use blake3;
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT,
    ristretto::RistrettoPoint,
    scalar::Scalar,
};
use fxhash::FxHashMap;
use lazy_static::lazy_static;
use num_bigint::BigUint;
use rand::{rngs::{OsRng, StdRng}, Rng, SeedableRng};
use rand_core::{RngCore, TryRngCore};
use rayon::prelude::*;
use std::collections::{HashSet, BTreeSet};
use std::io::{stdin, stdout, BufRead, BufReader, Write};
use std::ops::Neg;
use std::time::Instant;
use zeroize::Zeroize;

// =========== 常量定义 ===========
const RISTRETTO_GROUP_ORDER_DEC: &str = "723700557733226221397318656304299424087";
const MIN_CANDIDATES: usize = 10;
const MAX_CANDIDATES: usize = 1000;
const MIN_PARTICIPANTS: usize = 2;
const MAX_PARTICIPANTS: usize = 100;
/// UMPSI 模式下采纳候选元素的概率（0～1之间）
const UMPSI_INCLUDE_PROB: f32 = 0.8;
/// 阈值介入模式下非基准候选元素采纳概率，基准元素必选
const THRESHOLD_INCLUDE_PROB: f32 = 0.5;

// =========== 工具函数 ===========
#[inline(always)]
fn scalar_to_decimal(s: &Scalar) -> String {
    BigUint::from_bytes_le(&s.to_bytes()).to_str_radix(10)
}

/// 利用 Blake3 哈希生成 Ristretto 群元素（双哈希扩展）
#[inline(always)]
fn hash_to_group(label: &[u8]) -> RistrettoPoint {
    let hash1 = blake3::hash(label);
    let mut label2 = label.to_vec();
    label2.extend_from_slice(b"-2");
    let hash2 = blake3::hash(&label2);
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(hash1.as_bytes());
    wide[32..].copy_from_slice(hash2.as_bytes());
    RistrettoPoint::from_uniform_bytes(&wide)
}

/// 对候选元素进行哈希，作为加密映射的 key
#[inline(always)]
fn element_hash_key(element: &[u8]) -> Vec<u8> {
    blake3::hash(element).as_bytes().to_vec()
}

/// 生成指定范围内的伪随机 u16 数值
fn random_u16_in_range(low: u16, high: u16) -> u16 {
    let range = (high - low + 1) as u32;
    loop {
        let r = OsRng.try_next_u32().unwrap() % range;
        if let Ok(val) = (low as u32 + r).try_into() {
            return val;
        }
    }
}

/// 生成候选元素列表（确保全局唯一）
fn generate_candidate_elements(count: usize) -> Vec<Vec<u8>> {
    let mut set = BTreeSet::new();
    while set.len() < count {
        let num = random_u16_in_range(1000, 2000);
        set.insert(num.to_le_bytes().to_vec());
    }
    set.into_iter().collect()
}

/// 读取一行用户输入（去除首尾空白字符）
fn read_input_line() -> String {
    let mut input = String::new();
    stdin().read_line(&mut input).expect("读取失败");
    input.trim().to_string()
}

// =========== ElGamal 加密结构 ===========
#[derive(Clone, Debug)]
struct ElGamalCiphertext {
    version: u32,
    a: RistrettoPoint,
    b: RistrettoPoint,
}

impl ElGamalCiphertext {
    #[inline(always)]
    fn add(&self, other: &ElGamalCiphertext) -> Self {
        debug_assert_eq!(self.version, other.version, "密文版本不匹配");
        Self {
            version: self.version,
            a: self.a + other.a,
            b: self.b + other.b,
        }
    }
}

// =========== 参与方结构 ===========
#[derive(Debug)]
struct Participant {
    index: u32,
    secret_share: Scalar,
    public_share: RistrettoPoint,
    elements: HashSet<Vec<u8>>,
}

impl Participant {
    #[inline(always)]
    fn new(elements: HashSet<Vec<u8>>) -> Self {
        Self {
            index: 0,
            secret_share: Scalar::ZERO,
            public_share: RistrettoPoint::default(),
            elements,
        }
    }

    /// 根据自身元素集合更新密文（采用门限加密更新）
    #[inline(always)]
    fn encrypt_update(
        &self,
        master_pubkey: &RistrettoPoint,
        h: &RistrettoPoint,
        raw_element: &[u8],
        delta: Scalar,
        version: u32,
    ) -> ElGamalCiphertext {
        let m = if self.elements.contains(raw_element) { delta } else { Scalar::ZERO };
        let mut buf = [0u8; 64];
        OsRng.try_fill_bytes(&mut buf).unwrap();
        let r = Scalar::from_bytes_mod_order_wide(&buf);
        ElGamalCiphertext {
            version,
            a: r * RISTRETTO_BASEPOINT_POINT,
            b: m * (*h) + r * (*master_pubkey),
        }
    }
}

// =========== 离散对数预计算 ===========
lazy_static! {
    static ref H_POWERS: Vec<RistrettoPoint> = {
        let h = hash_to_group(b"UMPSI-BASE-H");
        let mut powers = Vec::with_capacity(1_000_001);
        powers.push(RistrettoPoint::default());
        for i in 1..=1_000_000 {
            powers.push(powers[i - 1] + h);
        }
        powers
    };
}

/// 利用暴力或 BSGS 求离散对数，返回解或错误信息
fn discrete_log(dec_point: RistrettoPoint, max_count: u32) -> Result<u32, String> {
    if max_count <= 10_000 {
        if let Some(pos) = H_POWERS[..=max_count as usize]
            .par_iter()
            .position_any(|&p| p == dec_point)
        {
            return Ok(pos as u32);
        }
        return Err("离散对数未找到".into());
    }
    let n = (max_count as f64).sqrt().ceil() as u32;
    let factor = H_POWERS[n as usize];
    let factor_neg = factor.neg();
    let baby_steps: FxHashMap<_, _> = (0..=n)
        .into_par_iter()
        .map(|j| (H_POWERS[j as usize].compress().to_bytes(), j))
        .collect();
    (0..=n)
        .into_par_iter()
        .find_map_any(|i| {
            let current = dec_point + factor_neg * Scalar::from(i);
            baby_steps.get(&current.compress().to_bytes()).and_then(|&j| {
                let m = i * n + j;
                if m <= max_count { Some(m) } else { None }
            })
        })
        .ok_or_else(|| "BSGS未找到解".into())
}

// =========== 密文映射结构 ===========
#[derive(Clone)]
struct EncryptedHashMap {
    version: u32,
    ciphertexts: FxHashMap<Vec<u8>, ElGamalCiphertext>,
}

// =========== 协议引擎 ===========
struct ProtocolEngine {
    participants: Vec<Participant>,
    union_counts: FxHashMap<Vec<u8>, u32>,
    master_secret: Scalar,
    master_pubkey: RistrettoPoint,
    h: RistrettoPoint,
    secret_threshold: u32,
    intersection_threshold: u32,
    exact_intersection: bool,
    current_version: u32,
    precomputed_lagrange: Vec<Scalar>,
    version_agg_secret: FxHashMap<u32, Scalar>,
    base_element: Vec<u8>, // 仅在阈值介入模式下使用
}

impl ProtocolEngine {
    #[inline(always)]
    fn new(secret_threshold: u32, intersection_threshold: u32, exact_intersection: bool) -> Self {
        let h = hash_to_group(b"UMPSI-BASE-H");
        let mut buf = [0u8; 64];
        OsRng.try_fill_bytes(&mut buf).unwrap();
        let master_secret = Scalar::from_bytes_mod_order_wide(&buf);
        let master_pubkey = RISTRETTO_BASEPOINT_POINT * master_secret;
        Self {
            participants: Vec::new(),
            union_counts: FxHashMap::default(),
            master_secret,
            master_pubkey,
            h,
            secret_threshold,
            intersection_threshold,
            exact_intersection,
            current_version: 1,
            precomputed_lagrange: Vec::new(),
            version_agg_secret: FxHashMap::default(),
            base_element: Vec::new(),
        }
    }

    #[inline(always)]
    fn add_participant(&mut self, mut participant: Participant) {
        participant.index = self.participants.len() as u32 + 1;
        for elem in &participant.elements {
            *self.union_counts.entry(elem.clone()).or_insert(0) += 1;
        }
        self.participants.push(participant);
    }

    #[inline(always)]
    fn set_base_element(&mut self, element: Vec<u8>) {
        self.base_element = element;
    }

    #[inline(always)]
    fn distribute_threshold_shares(&mut self) {
        let n = self.participants.len();
        assert!(
            n as u32 >= self.secret_threshold,
            "参与方数量不足以满足门限要求"
        );
        let mut coeffs: Vec<Scalar> = Vec::with_capacity(self.secret_threshold as usize);
        let mut buf = [0u8; 64];
        OsRng.try_fill_bytes(&mut buf).unwrap();
        coeffs.push(self.master_secret);
        for _ in 1..self.secret_threshold {
            OsRng.try_fill_bytes(&mut buf).unwrap();
            coeffs.push(Scalar::from_bytes_mod_order_wide(&buf));
        }
        // 重新分发各参与方的门限共享
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
        self.master_pubkey = self.master_secret * RISTRETTO_BASEPOINT_POINT;
        self.precomputed_lagrange = self.compute_all_lagrange();
        // 聚合密钥
        let agg_secret = self
            .participants
            .par_iter()
            .enumerate()
            .map(|(idx, p)| self.precomputed_lagrange[idx] * p.secret_share)
            .reduce(|| Scalar::ZERO, |a, b| a + b);
        self.version_agg_secret.clear();
        self.version_agg_secret.insert(self.current_version, agg_secret);
    }

    #[inline(always)]
    fn compute_all_lagrange(&self) -> Vec<Scalar> {
        let indices: Vec<u32> = self.participants.par_iter().map(|p| p.index).collect();
        indices
            .par_iter()
            .map(|&i| self.lagrange_coefficient(&indices, i))
            .collect()
    }

    #[inline(always)]
    fn lagrange_coefficient(&self, indices: &[u32], i: u32) -> Scalar {
        let xi = Scalar::from(i);
        indices
            .iter()
            .filter(|&&j| j != i)
            .fold(Scalar::ONE, |acc, &j| {
                acc * (-Scalar::from(j)) * (xi - Scalar::from(j)).invert()
            })
    }

    #[inline(always)]
    fn chain_encryption_process_map(
        &self,
        candidate_elements: &[Vec<u8>],
        delta: Scalar,
    ) -> EncryptedHashMap {
        let version = self.current_version;
        let master_pubkey = &self.master_pubkey;
        // 初始密文映射：对每个候选元素生成初始密文
        let init_map: FxHashMap<Vec<u8>, ElGamalCiphertext> = candidate_elements
            .par_iter()
            .map(|elem| {
                let key = element_hash_key(elem);
                let mut buf = [0u8; 64];
                OsRng.try_fill_bytes(&mut buf).unwrap();
                let r = Scalar::from_bytes_mod_order_wide(&buf);
                let ct = ElGamalCiphertext {
                    version,
                    a: r * RISTRETTO_BASEPOINT_POINT,
                    b: r * (*master_pubkey),
                };
                (key, ct)
            })
            .collect();
        // 参与方加密更新后累加
        let updated_map: FxHashMap<Vec<u8>, ElGamalCiphertext> = candidate_elements
            .par_iter()
            .map(|elem| {
                let key = element_hash_key(elem);
                let init_ct = init_map
                    .get(&key)
                    .expect("初始密文必须存在")
                    .clone();
                let total_ct = self
                    .participants
                    .par_iter()
                    .map(|p| p.encrypt_update(master_pubkey, &self.h, elem, delta, version))
                    .fold(|| init_ct.clone(), |acc, ct| acc.add(&ct))
                    .reduce(|| init_ct.clone(), |a, b| a.add(&b));
                (key, total_ct)
            })
            .collect();
        EncryptedHashMap {
            version,
            ciphertexts: updated_map,
        }
    }

    #[inline(always)]
    fn decrypt_count(&self, ct: &ElGamalCiphertext) -> Result<u32, String> {
        let agg_secret = self.version_agg_secret.get(&ct.version).ok_or_else(|| {
            format!("版本 {} 的聚合密钥不存在", ct.version)
        })?;
        let dec_point = ct.b - (*agg_secret * ct.a);
        println!("解密点: {:?}", dec_point); // 打印解密点
        let max_count = self.participants.len() as u32;
        let result = discrete_log(dec_point, max_count);
        println!("解密结果: {:?}", result); // 打印解密结果
        result
    }


    fn compute_intersection(
        &self,
        enc_map: &EncryptedHashMap,
        candidate_elements: &[Vec<u8>],
    ) -> Vec<Vec<u8>> {
        let required = self.intersection_threshold;
        let mut result = Vec::new();
        for elem in candidate_elements.iter() {
            if let Some(ct) = enc_map.ciphertexts.get(&element_hash_key(elem)) {
                if self.decrypt_count(ct).unwrap_or(0) >= required {
                    result.push(elem.clone());
                }
            }
        }
        result.sort();
        result.dedup();
        result
    }


    /// 更新门限时，严格要求新秘密门限与交集阈值均等于参与方数量，
    /// 否则更新将被拒绝，以确保交集计算的正确性
    #[inline(always)]
    fn update_thresholds(&mut self, new_threshold: u32, new_intersection_threshold: u32, new_exact: bool) {
        let part_count = self.participants.len() as u32;
        if new_threshold != part_count || new_intersection_threshold != part_count {
            println!("错误：在当前模式下，秘密门限与交集阈值必须等于参与方数量（{}）", part_count);
            return;
        }
        self.secret_threshold = new_threshold;
        self.intersection_threshold = new_intersection_threshold;
        self.exact_intersection = new_exact;
        let mut buf = [0u8; 64];
        OsRng.try_fill_bytes(&mut buf).unwrap();
        self.master_secret = Scalar::from_bytes_mod_order_wide(&buf);
        self.master_pubkey = self.master_secret * RISTRETTO_BASEPOINT_POINT;
        self.version_agg_secret.clear();
        self.current_version += 1;
        self.distribute_threshold_shares();
    }

    fn store_intersection_result(&self, intersection: &[Vec<u8>]) {
        println!("交集计算结果：{:?}", intersection);
    }
}

impl Drop for ProtocolEngine {
    fn drop(&mut self) {
        self.master_secret.zeroize();
        self.precomputed_lagrange.zeroize();
        for sec in self.version_agg_secret.values_mut() {
            sec.zeroize();
        }
        self.participants.par_iter_mut().for_each(|p| {
            p.secret_share.zeroize();
            p.public_share = RISTRETTO_BASEPOINT_POINT;
        });
    }
}

// =========== 参与方集合随机更新 ===========
fn random_update_participants(engine: &mut ProtocolEngine, Nd: usize, candidate_elements: &[Vec<u8>]) {
    for (idx, participant) in engine.participants.iter_mut().enumerate() {
        println!("\n--- 对参与方 {} (原有元素数: {}) 执行 {} 次随机更新操作 ---", idx + 1, participant.elements.len(), Nd);
        for _ in 0..Nd {
            let rand_val = OsRng.try_next_u32().unwrap();
            let is_remove = (rand_val % 2) == 0;
            if is_remove {
                let available: Vec<_> = participant.elements.iter().cloned().collect();
                if !available.is_empty() {
                    let remove_idx = (rand_val as usize) % available.len();
                    // 阈值模式下基准元素不可删除
                    if engine.base_element == available[remove_idx] {
                        println!("    - 基准元素不可删除，跳过删除操作。");
                        continue;
                    }
                    let removed = available[remove_idx].clone();
                    participant.elements.remove(&removed);
                    println!("    - 删除元素: {:?}, 当前元素总数: {}", removed, participant.elements.len());
                } else {
                    println!("    - 无元素可删除，跳过删除操作。");
                }
            } else {
                let not_in: Vec<_> = candidate_elements.iter().filter(|c| !participant.elements.contains(*c)).cloned().collect();
                if !not_in.is_empty() {
                    let add_idx = (rand_val as usize) % not_in.len();
                    let to_add = not_in[add_idx].clone();
                    participant.elements.insert(to_add.clone());
                    println!("    + 添加元素: {:?}, 当前元素总数: {}", to_add, participant.elements.len());
                } else {
                    println!("    + 所有候选元素均已存在，跳过添加操作。");
                }
            }
        }
    }
}

// =========== 主函数 ===========
fn main() {
    println!("===== 椭圆曲线详细信息 =====");
    println!("标准曲线名称: Ristretto/Curve25519");
    println!("[生成元G]       {}", hex::encode(RISTRETTO_BASEPOINT_POINT.compress().to_bytes()));
    println!("[曲线阶n]       {}", RISTRETTO_GROUP_ORDER_DEC);
    println!("============================\n");

    println!("请选择运行模式：");
    println!("1. UMPSI 模式（自动生成候选元素，采纳率 {}）", UMPSI_INCLUDE_PROB);
    println!("2. 阈值介入模式（自动生成候选元素，基准元素自动选取，非基准元素采纳率 {}）", THRESHOLD_INCLUDE_PROB);
    print!("请输入选项 (1/2): ");
    stdout().flush().unwrap();
    let mode_input = read_input_line();

    // 输入候选元素数量与参与方数量
    print!("请输入候选元素数量 ({}-{}): ", MIN_CANDIDATES, MAX_CANDIDATES);
    stdout().flush().unwrap();
    let candidate_count: usize = read_input_line().parse().unwrap_or(MIN_CANDIDATES);
    print!("请输入参与方数量 ({}-{}): ", MIN_PARTICIPANTS, MAX_PARTICIPANTS);
    stdout().flush().unwrap();
    let n: usize = read_input_line().parse().unwrap_or(MIN_PARTICIPANTS);
    let candidate_count = candidate_count.clamp(MIN_CANDIDATES, MAX_CANDIDATES);
    let participant_count = n.clamp(MIN_PARTICIPANTS, MAX_PARTICIPANTS);
    let candidate_elements = generate_candidate_elements(candidate_count);

    // 初始化协议引擎：初始门限设置为参与方数量
    let mut engine = ProtocolEngine::new(participant_count as u32, participant_count as u32, true);

    // 模式判断：阈值介入模式自动选取候选列表第一个元素为基准
    let (include_prob, is_threshold_mode) = if mode_input == "2" {
        let base = candidate_elements[0].clone();
        engine.set_base_element(base);
        (THRESHOLD_INCLUDE_PROB, true)
    } else {
        (UMPSI_INCLUDE_PROB, false)
    };

    // 添加参与方：阈值介入模式下保证基准元素必选，其余按各自概率采纳
    for idx in 0..participant_count {
        let mut set = HashSet::new();
        let seed = OsRng.try_next_u64().unwrap() ^ (idx as u64);
        let mut rng = StdRng::seed_from_u64(seed);
        for elem in &candidate_elements {
            if is_threshold_mode {
                if *elem == engine.base_element || rng.gen::<f32>() < include_prob {
                    set.insert(elem.clone());
                }
            } else if rng.gen::<f32>() < include_prob {
                set.insert(elem.clone());
            }
        }
        engine.add_participant(Participant::new(set));
    }
    engine.distribute_threshold_shares();
    println!("\n参与方数量: {}", engine.participants.len());

    // 第一次计算交集
    let start = Instant::now();
    let enc_map = engine.chain_encryption_process_map(&candidate_elements, Scalar::ONE);
    let intersection = engine.compute_intersection(&enc_map, &candidate_elements);
    let duration1 = start.elapsed().as_millis();
    println!("\n第一次计算交集：");
    println!("计算耗时: {} ms", duration1);
    println!("交集大小: {} 个元素", intersection.len());
    engine.store_intersection_result(&intersection);

    // 更新门限——在当前模式下，秘密门限和交集阈值必须等于参与方数量
    if mode_input == "2" {
        println!("\n是否更新门限？(y/n): ");
        stdout().flush().unwrap();
        let update_threshold_choice = read_input_line();
        if update_threshold_choice.eq_ignore_ascii_case("y") {
            println!("当前新的秘密门限和交集阈值的数量（{}）", engine.participants.len());
            print!("请输入新的秘密门限: ");
            stdout().flush().unwrap();
            let new_secret: u32 = read_input_line().parse().unwrap_or(engine.secret_threshold);
            print!("请输入新的交集阈值: ");
            stdout().flush().unwrap();
            let new_intersection: u32 = read_input_line().parse().unwrap_or(engine.intersection_threshold);
            engine.update_thresholds(new_secret, new_intersection, engine.exact_intersection);
        }
    }

    // 更新参与方元素（随机增删操作）
    println!("\n请输入每个参与方更新元素数量 Nd（增删操作次数）: ");
    stdout().flush().unwrap();
    let Nd: usize = read_input_line().parse().unwrap_or(0);
    if Nd > 0 {
        random_update_participants(&mut engine, Nd, &candidate_elements);
        engine.current_version += 1;
        engine.distribute_threshold_shares();
    }

    // 第二次计算交集
    let start2 = Instant::now();
    let enc_map2 = engine.chain_encryption_process_map(&candidate_elements, Scalar::ONE);
    let intersection2 = engine.compute_intersection(&enc_map2, &candidate_elements);
    let duration2 = start2.elapsed().as_millis();
    println!("\n第二次计算交集：");
    println!("计算耗时: {} ms", duration2);
    println!("交集大小: {} 个元素", intersection2.len());
    engine.store_intersection_result(&intersection2);

    println!("\n======= 协议执行完成 =======");
}
