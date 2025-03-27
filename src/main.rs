//! 完整金融级 Rust 代码，实现 UMPSI 与阈值介入两种模式，同时允许候选元素更新（删除或替换），更新时使用伪随机数（范围1000-2000）。

use blake3;
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT,
    ristretto::RistrettoPoint,
    scalar::Scalar,
};
use fxhash::FxHashMap;
use lazy_static::lazy_static;
use num_bigint::BigUint;
use rand_core::{OsRng, RngCore, SeedableRng, TryRngCore};
use rand::rngs::StdRng;
use rayon::prelude::*;
use std::collections::HashSet;
use std::io::{stdin, stdout, BufRead, BufReader, Write};
use std::ops::Neg;
use std::time::Instant;
use zeroize::Zeroize;

const RISTRETTO_GROUP_ORDER_DEC: &str = "723700557733226221397318656304299424087";

// 安全参数
const MIN_CANDIDATES: usize = 10;
const MAX_CANDIDATES: usize = 1000;
const MIN_PARTICIPANTS: usize = 2;
const MAX_PARTICIPANTS: usize = 100;

/// 将 Scalar 转换为十进制字符串
#[inline(always)]
fn scalar_to_decimal(s: &Scalar) -> String {
    BigUint::from_bytes_le(&s.to_bytes()).to_str_radix(10)
}

/// 利用 Blake3 哈希将 label 映射到 Ristretto 群元素
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

/// 对传入的元素做 Blake3 哈希，作为索引键
#[inline(always)]
fn element_hash_key(element: &[u8]) -> Vec<u8> {
    blake3::hash(element).as_bytes().to_vec()
}

/// ElGamal 密文结构
#[derive(Clone, Debug)]
struct ElGamalCiphertext {
    version: u32,
    a: RistrettoPoint,
    b: RistrettoPoint,
}

impl ElGamalCiphertext {
    /// 同一版本下密文可直接相加
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

/// 参与方结构体，包含密钥份额、数据集等
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

    /// 对候选元素执行加密更新：包含则消息为 delta，否则为 0
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

/// 懒加载预计算 H 的累加，用于离散对数求解
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

/// 离散对数计算（暴力查找 / BSGS），上限 max_count
fn discrete_log(dec_point: RistrettoPoint, max_count: u32) -> Result<u32, String> {
    if max_count <= 10_000 {
        if let Some(pos) = H_POWERS[..=max_count as usize].par_iter().position_any(|&p| p == dec_point) {
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

/// 密文映射结构，保存候选元素对应密文
#[derive(Clone)]
struct EncryptedHashMap {
    version: u32,
    ciphertexts: FxHashMap<Vec<u8>, ElGamalCiphertext>,
}

/// 协议引擎：包含参与方、门限分发、加密/解密、交集计算等核心逻辑
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
    base_element: Vec<u8>,
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

    /// 分发 master_secret 的门限密钥份额并计算 Lagrange 系数
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

    /// 对所有候选元素执行链式加密处理
    #[inline(always)]
    fn chain_encryption_process_map(
        &self,
        candidate_elements: &[Vec<u8>],
        delta: Scalar,
    ) -> EncryptedHashMap {
        let version = self.current_version;
        let master_pubkey = &self.master_pubkey;
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

        let updated_map: FxHashMap<Vec<u8>, ElGamalCiphertext> = candidate_elements
            .par_iter()
            .map(|elem| {
                let key = element_hash_key(elem);
                let init_ct = init_map.get(&key).expect("初始密文存在").clone();
                let total_ct = self
                    .participants
                    .par_iter()
                    .map(|p| p.encrypt_update(master_pubkey, &self.h, elem, delta, version))
                    .fold(|| init_ct.clone(), |acc, ct| acc.add(&ct))
                    .reduce(|| init_ct.clone(), |a, b| a.add(&b));
                (key, total_ct)
            })
            .collect();

        EncryptedHashMap { version, ciphertexts: updated_map }
    }

    /// 解密候选元素对应的密文，返回参与方数量
    #[inline(always)]
    fn decrypt_count(&self, ct: &ElGamalCiphertext) -> Result<u32, String> {
        let agg_secret = self.version_agg_secret.get(&ct.version)
            .ok_or_else(|| format!("版本 {} 的聚合密钥不存在", ct.version))?;
        let dec_point = ct.b - (*agg_secret * ct.a);
        let max_count = self.participants.len() as u32;
        discrete_log(dec_point, max_count)
    }

    /// 交集计算：仅当解密计数达到交集阈值时计入交集；基准元素始终包含。
    fn compute_intersection(
        &self,
        enc_map: &EncryptedHashMap,
        candidate_elements: &[Vec<u8>],
    ) -> Vec<Vec<u8>> {
        let required = self.intersection_threshold;
        let mut result = Vec::new();
        for elem in candidate_elements.iter() {
            if *elem == self.base_element {
                result.push(elem.clone());
            } else if let Some(ct) = enc_map.ciphertexts.get(&element_hash_key(elem)) {
                if self.decrypt_count(ct).unwrap_or(0) >= required {
                    result.push(elem.clone());
                }
            }
        }
        result.sort();
        result.dedup();
        result
    }

    /// 更新门限与交集阈值，重新分发秘密份额
    #[inline(always)]
    fn update_thresholds(
        &mut self,
        new_threshold: u32,
        new_intersection_threshold: u32,
        new_exact: bool,
    ) {
        self.secret_threshold = new_threshold;
        self.intersection_threshold = new_intersection_threshold;
        self.exact_intersection = new_exact;
        // 更新 master_secret 使用真随机（保持密钥随机性）
        let mut buf = [0u8; 64];
        OsRng.try_fill_bytes(&mut buf).unwrap();
        self.master_secret = Scalar::from_bytes_mod_order_wide(&buf);
        self.master_pubkey = self.master_secret * RISTRETTO_BASEPOINT_POINT;
        self.version_agg_secret.clear();
        self.current_version += 1;
        self.distribute_threshold_shares();
    }

    /// 输出交集结果（部署时可替换为存储或网络传输）
    fn store_intersection_result(&self, intersection: Vec<Vec<u8>>) {
        println!("交集计算结果： {:?}", intersection);
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
            p.public_share = RistrettoPoint::default();
        });
    }
}

/// 使用伪随机数生成器，生成范围 [low, high] 内的 u16 数（闭区间）
fn pseudo_random_u16_in_range(rng: &mut StdRng, low: u16, high: u16) -> u16 {
    let range = (high - low + 1) as u32;
    let r = rng.next_u32() % range;
    low + (r as u16)
}

/// 从标准输入读取一行去掉换行
fn read_input_line() -> String {
    let mut input = String::new();
    stdin().read_line(&mut input).expect("读取失败");
    input.trim().to_string()
}

/// 当候选元素数量不足或超出范围时做相应调整
fn adjust_candidate_elements(mut elems: Vec<Vec<u8>>) -> Vec<Vec<u8>> {
    if elems.len() < MIN_CANDIDATES {
        println!("候选元素数量不足，自动补齐至 {} 个", MIN_CANDIDATES);
        while elems.len() < MIN_CANDIDATES {
            let num = random_u16_in_range(1000, 2000);
            elems.push(num.to_le_bytes().to_vec());
        }
    } else if elems.len() > MAX_CANDIDATES {
        elems.truncate(MAX_CANDIDATES);
    }
    elems
}

/// 使用真随机生成候选元素（范围1000-2000）
fn random_u16_in_range(low: u16, high: u16) -> u16 {
    let range = (high - low + 1) as u32;
    loop {
        let r = OsRng.try_next_u32().unwrap() % range;
        if let Ok(val) = (low as u32 + r).try_into() {
            return val;
        }
    }
}

/// 伪随机更新候选元素：update_mode=1 为删除（除基准元素外），update_mode=2 为替换（保持数量不变）
fn update_candidate_elements(candidate_elements: &mut Vec<Vec<u8>>, base_element: &[u8], update_mode: u8) {
    // 固定种子，保证伪随机性
    let seed: u64 = 0xdeadbeef;
    let mut rng = StdRng::seed_from_u64(seed);
    // 更新概率
    let update_prob: f32 = 0.2;
    match update_mode {
        1 => {
            // 删除候选元素（保留基准元素）
            candidate_elements.retain(|elem| {
                if elem == base_element {
                    true
                } else {
                    let r: f32 = (rng.next_u32() as f32) / (u32::MAX as f32);
                    r > update_prob
                }
            });
            // 如删除后数量不足，补齐至 MIN_CANDIDATES
            while candidate_elements.len() < MIN_CANDIDATES {
                let num = pseudo_random_u16_in_range(&mut rng, 1000, 2000);
                candidate_elements.push(num.to_le_bytes().to_vec());
            }
        }
        2 => {
            // 替换部分候选元素（保持数量不变）
            for elem in candidate_elements.iter_mut() {
                if elem == base_element {
                    continue;
                }
                let r: f32 = (rng.next_u32() as f32) / (u32::MAX as f32);
                if r < update_prob {
                    let num = pseudo_random_u16_in_range(&mut rng, 1000, 2000);
                    *elem = num.to_le_bytes().to_vec();
                }
            }
        }
        _ => println!("未知的更新模式，跳过候选元素更新。"),
    }
}

/// 主函数：支持 UMPSI 与阈值介入模式，同时可更新候选元素（删除或替换）及门限
fn main() {
    println!("===== 椭圆曲线详细信息 =====");
    println!("标准曲线名称: Ristretto/Curve25519");
    println!(
        "[生成元G]       {}",
        hex::encode(RISTRETTO_BASEPOINT_POINT.compress().to_bytes())
    );
    println!("[曲线阶n]       {}", RISTRETTO_GROUP_ORDER_DEC);
    println!("============================\n");

    println!("请选择运行模式：");
    println!("1. UMPSI 模式（自动生成候选元素）");
    println!("2. 阈值介入模式（手动输入候选元素，并允许后续更新）");
    print!("请输入选项 (1/2): ");
    stdout().flush().unwrap();
    let mode_input = read_input_line();

    // 默认参数设置
    let (mut candidate_elements, participant_count, (init_secret_threshold, init_intersection_threshold)) =
        if mode_input == "2" {
            // 阈值介入模式：候选元素手动输入
            let elems = read_candidate_elements();
            print!("请输入参与方数量 ({}-{}): ", MIN_PARTICIPANTS, MAX_PARTICIPANTS);
            stdout().flush().unwrap();
            let n: usize = read_input_line().parse().unwrap_or(MIN_PARTICIPANTS);
            (adjust_candidate_elements(elems), n.clamp(MIN_PARTICIPANTS, MAX_PARTICIPANTS), (3, 3))
        } else {
            // UMPSI 模式：候选元素自动生成
            print!("请输入候选元素数量 ({}-{}): ", MIN_CANDIDATES, MAX_CANDIDATES);
            stdout().flush().unwrap();
            let candidate_count: usize = read_input_line().parse().unwrap_or(MIN_CANDIDATES);
            print!("请输入参与方数量 ({}-{}): ", MIN_PARTICIPANTS, MAX_PARTICIPANTS);
            stdout().flush().unwrap();
            let n: usize = read_input_line().parse().unwrap_or(MIN_PARTICIPANTS);
            let mut elems = Vec::with_capacity(candidate_count);
            for _ in 0..candidate_count.clamp(MIN_CANDIDATES, MAX_CANDIDATES) {
                let num = random_u16_in_range(1000, 2000);
                elems.push(num.to_le_bytes().to_vec());
            }
            (elems, n.clamp(MIN_PARTICIPANTS, MAX_PARTICIPANTS), (3, 3))
        };

    // 初始化协议引擎
    let mut engine = ProtocolEngine::new(init_secret_threshold, init_intersection_threshold, true);

    // 选择基准元素：阈值介入模式下允许手动输入，否则随机选择
    let base_element = if mode_input == "2" {
        println!("请输入基准元素（必须为候选元素之一）：");
        let input_elem = read_input_line();
        let input_bytes = input_elem.into_bytes();
        if !candidate_elements.contains(&input_bytes) {
            println!("输入基准元素不存在于候选集合中，自动选择第一个候选元素作为基准。");
            candidate_elements[0].clone()
        } else {
            input_bytes
        }
    } else {
        let idx = OsRng.try_next_u32().unwrap() as usize % candidate_elements.len();
        candidate_elements[idx].clone()
    };
    engine.set_base_element(base_element.clone());

    // 生成参与方数据集：每个参与方包含基准元素，其余元素按概率分布添加
    for _ in 0..participant_count {
        let mut set = HashSet::new();
        set.insert(base_element.clone());
        let mid = candidate_elements.len() as f32 / 2.0;
        let prob_curve = |x: f32| -> f32 {
            0.7 * (-0.5 * ((x - mid).powi(2) / (2.0 * mid.powf(1.5)))).exp()
        };
        for (idx, elem) in candidate_elements.iter().enumerate() {
            if *elem == base_element {
                continue;
            }
            let x = idx as f32;
            let prob = prob_curve(x).clamp(0.3, 0.7);
            let threshold = (prob * 1000.0) as u32;
            if OsRng.try_next_u32().unwrap() % 1000 < threshold {
                set.insert(elem.clone());
            }
        }
        engine.add_participant(Participant::new(set));
    }
    engine.distribute_threshold_shares();
    println!("\n参与方数量: {}", engine.participants.len());

    // 首次计算交集
    let start = Instant::now();
    let enc_map = engine.chain_encryption_process_map(&candidate_elements, Scalar::ONE);
    let intersection = engine.compute_intersection(&enc_map, &candidate_elements);
    let duration1 = start.elapsed().as_millis();

    println!("\n首次计算结果：");
    println!("计算耗时: {} ms", duration1);
    println!("交集大小: {} 个元素", intersection.len());

    // 判断是否更新阈值和候选元素
    println!("\n是否更新门限？(y/n): ");
    stdout().flush().unwrap();
    let update_threshold_choice = read_input_line();
    if update_threshold_choice.eq_ignore_ascii_case("y") {
        print!("请输入新的秘密门限（>=2）: ");
        stdout().flush().unwrap();
        let new_secret: u32 = read_input_line().parse().unwrap_or(init_secret_threshold);
        print!("请输入新的交集阈值（>=2）: ");
        stdout().flush().unwrap();
        let new_intersection: u32 = read_input_line().parse().unwrap_or(init_intersection_threshold);
        engine.update_thresholds(new_secret, new_intersection, engine.exact_intersection);
    }

    println!("\n是否更新候选元素？(y/n): ");
    stdout().flush().unwrap();
    let update_candidate_choice = read_input_line();
    if update_candidate_choice.eq_ignore_ascii_case("y") {
        println!("请选择更新模式：1. 删除候选元素；2. 替换候选元素（保持数量不变）");
        print!("请输入模式 (1/2): ");
        stdout().flush().unwrap();
        let mode = read_input_line();
        let update_mode = if mode == "1" { 1 } else { 2 };
        update_candidate_elements(&mut candidate_elements, &base_element, update_mode);
        // 更新后重新分发参与方数据集（这里简单地重新构造参与方数据集）
        engine.participants.clear();
        for _ in 0..participant_count {
            let mut set = HashSet::new();
            set.insert(base_element.clone());
            let mid = candidate_elements.len() as f32 / 2.0;
            let prob_curve = |x: f32| -> f32 {
                0.7 * (-0.5 * ((x - mid).powi(2) / (2.0 * mid.powf(1.5)))).exp()
            };
            for (idx, elem) in candidate_elements.iter().enumerate() {
                if *elem == base_element { continue; }
                let x = idx as f32;
                let prob = prob_curve(x).clamp(0.3, 0.7);
                let threshold = (prob * 1000.0) as u32;
                if OsRng.try_next_u32().unwrap() % 1000 < threshold {
                    set.insert(elem.clone());
                }
            }
            engine.add_participant(Participant::new(set));
        }
        engine.distribute_threshold_shares();
    }

    // 重新计算交集
    let start2 = Instant::now();
    let enc_map2 = engine.chain_encryption_process_map(&candidate_elements, Scalar::ONE);
    let intersection2 = engine.compute_intersection(&enc_map2, &candidate_elements);
    let duration2 = start2.elapsed().as_millis();

    println!("\n更新后结果：");
    println!("计算耗时: {} ms", duration2);
    println!("交集大小: {} 个元素", intersection2.len());

    println!("\n======= 协议执行完成 =======");
}

/// 从标准输入读取候选元素，每行一个，空行结束
fn read_candidate_elements() -> Vec<Vec<u8>> {
    println!("请输入候选元素（每行一个，输入空行结束）：");
    let stdin = stdin();
    let reader = BufReader::new(stdin.lock());
    let mut elements = Vec::new();
    for line in reader.lines() {
        let l = line.expect("读取行失败").trim().to_string();
        if l.is_empty() { break; }
        elements.push(l.into_bytes());
    }
    elements
}
