//! 每个参与者独立生成自己的候选池（集合内元素全局唯一，来源于用户指定的范围）。
//! 若选择阈值介入模式，系统自动生成一个基准元素，保证各参与者候选池中均包含该基准元素。
//!
//! 协议计算时，先取所有参与者候选池的并集，再利用门限加密技术计算出在所有参与者中都出现的候选元素（交集）。

use blake3;
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT, ristretto::RistrettoPoint, scalar::Scalar,
};
use fxhash::FxHashMap;
use itertools::Itertools;
use lazy_static::lazy_static;
use rand::{rng, rngs::OsRng, seq::SliceRandom};
use rand_core::TryRngCore;
use rayon::prelude::*;
use std::collections::HashSet;
use std::io::{stdin, stdout, Write};
use std::ops::Neg;
use std::time::Instant;
use zeroize::Zeroize;

const RISTRETTO_GROUP_ORDER_DEC: &str = "723700557733226221397318656304299424087";

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

/// 从用户指定范围 [lower, upper] 内生成 count 个全局唯一的 u32 数字（转换为小端字节向量）
/// 注意：每次调用结果独立
fn generate_candidate_elements(count: usize, lower: u32, upper: u32) -> Vec<Vec<u8>> {
    let range_size = (upper - lower + 1) as usize;
    assert!(count <= range_size, "候选数量不能超过范围内数字个数");
    let mut pool: Vec<u32> = (lower..=upper).collect();
    pool.shuffle(&mut rng());
    pool.truncate(count);
    pool.into_iter().map(|n| n.to_le_bytes().to_vec()).collect()
}

/// 从指定范围随机生成一个候选元素（全局唯一表示为字节向量）
fn generate_single_candidate(lower: u32, upper: u32) -> Vec<u8> {
    let range = upper - lower + 1;
    let mut rng = OsRng;
    let num = rng.try_next_u32().unwrap() % range + lower;
    num.to_le_bytes().to_vec()
}

/// 读取一行用户输入（去除首尾空白字符）
fn read_input_line() -> String {
    let mut input = String::new();
    stdin().read_line(&mut input).expect("读取失败");
    input.trim().to_string()
}

/// ElGamal 加密结构
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

/// 参与方结构
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

    /// 根据自身候选集合更新密文（采用门限加密更新）
    #[inline(always)]
    fn encrypt_update(
        &self,
        master_pubkey: &RistrettoPoint,
        h: &RistrettoPoint,
        raw_element: &[u8],
        delta: Scalar,
        version: u32,
    ) -> ElGamalCiphertext {
        let m = if self.elements.contains(raw_element) {
            delta
        } else {
            Scalar::ZERO
        };
        let mut buf = [0u8; 64];
        // 局部生成随机数（属于数据加密计算部分）
        OsRng.try_fill_bytes(&mut buf).unwrap();
        let r = Scalar::from_bytes_mod_order_wide(&buf);
        ElGamalCiphertext {
            version,
            a: r * RISTRETTO_BASEPOINT_POINT,
            b: m * (*h) + r * (*master_pubkey),
        }
    }
}

lazy_static! {
    static ref H_POWERS: Vec<RistrettoPoint> = {
        let h = hash_to_group(b"UMPSI-BASE-H");
        // 预分配，避免多次扩容
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
            baby_steps
                .get(&current.compress().to_bytes())
                .and_then(|&j| {
                    let m = i * n + j;
                    if m <= max_count {
                        Some(m)
                    } else {
                        None
                    }
                })
        })
        .ok_or_else(|| "BSGS未找到解".into())
}

/// 密文映射结构
#[derive(Clone)]
struct EncryptedHashMap {
    ciphertexts: FxHashMap<Vec<u8>, ElGamalCiphertext>,
}

/// 协议引擎
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
    base_element: Option<Vec<u8>>, // 阈值模式下使用基准元素
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
            base_element: None,
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
    fn distribute_threshold_shares(&mut self) {
        let n = self.participants.len();
        assert!(
            n as u32 >= self.secret_threshold,
            "参与方数量不足以满足门限要求"
        );
        // 多项式系数，第一个为 master_secret，其余随机生成
        let mut coeffs: Vec<Scalar> = Vec::with_capacity(self.secret_threshold as usize);
        let mut buf = [0u8; 64];
        OsRng.try_fill_bytes(&mut buf).unwrap();
        coeffs.push(self.master_secret);
        for _ in 1..self.secret_threshold {
            OsRng.try_fill_bytes(&mut buf).unwrap();
            coeffs.push(Scalar::from_bytes_mod_order_wide(&buf));
        }
        // 并行计算各参与方密钥份额
        self.participants.par_iter_mut().for_each(|p| {
            let x = Scalar::from(p.index);
            let mut share = Scalar::ZERO;
            let mut x_pow = Scalar::ONE;
            for coeff in &coeffs {
                share += coeff * x_pow;
                x_pow *= x;
            }
            p.secret_share = share;
            p.public_share = share * RISTRETTO_BASEPOINT_POINT;
        });
        self.master_pubkey = self.master_secret * RISTRETTO_BASEPOINT_POINT;
        self.precomputed_lagrange = self.compute_all_lagrange();
        let agg_secret = self
            .participants
            .par_iter()
            .enumerate()
            .map(|(idx, p)| self.precomputed_lagrange[idx] * p.secret_share)
            .reduce(|| Scalar::ZERO, |a, b| a + b);
        self.version_agg_secret.clear();
        self.version_agg_secret
            .insert(self.current_version, agg_secret);
    }

    #[inline(always)]
    fn compute_all_lagrange(&self) -> Vec<Scalar> {
        let indices: Vec<u32> = self.participants.iter().map(|p| p.index).collect();
        indices
            .clone()
            .into_par_iter()
            .map(|i| self.lagrange_coefficient(&indices, i))
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

    /// 对候选元素（并集）生成初始密文，并由各参与方进行加密更新累加
    #[inline(always)]
    fn chain_encryption_process_map(
        &self,
        candidate_elements: &[Vec<u8>],
        delta: Scalar,
    ) -> EncryptedHashMap {
        let version = self.current_version;
        let master_pubkey = &self.master_pubkey;
        // 并行处理每个候选项（数据操作部分，包含必要的随机性属于加密计算）
        let updated_map: FxHashMap<Vec<u8>, ElGamalCiphertext> = candidate_elements
            .par_iter()
            .map(|elem| {
                let key = element_hash_key(elem);
                let mut buf = [0u8; 64];
                OsRng.try_fill_bytes(&mut buf).unwrap();
                let r = Scalar::from_bytes_mod_order_wide(&buf);
                let init_ct = ElGamalCiphertext {
                    version,
                    a: r * RISTRETTO_BASEPOINT_POINT,
                    b: r * (*master_pubkey),
                };
                let total_ct = self
                    .participants
                    .par_iter()
                    .map(|p| p.encrypt_update(master_pubkey, &self.h, elem, delta, version))
                    .reduce(|| init_ct.clone(), |a, b| a.add(&b));
                (key, total_ct)
            })
            .collect();
        EncryptedHashMap {
            ciphertexts: updated_map,
        }
    }

    #[inline(always)]
    fn decrypt_count(&self, ct: &ElGamalCiphertext) -> Result<u32, String> {
        let agg_secret = self
            .version_agg_secret
            .get(&ct.version)
            .ok_or_else(|| format!("版本 {} 的聚合密钥不存在", ct.version))?;
        let dec_point = ct.b - (*agg_secret * ct.a);
        let max_count = self.participants.len() as u32;
        discrete_log(dec_point, max_count)
    }

    /// 计算交集：以各参与者候选池的并集为候选项，选出在各参与者中出现次数达到交集门限的元素
    fn compute_intersection(
        &self,
        enc_map: &EncryptedHashMap,
        candidate_elements: &[Vec<u8>],
    ) -> Vec<Vec<u8>> {
        let required = self.intersection_threshold;
        let mut result: Vec<Vec<u8>> = candidate_elements
            .iter()
            .filter_map(|elem| {
                let key = element_hash_key(elem);
                if let Some(ct) = enc_map.ciphertexts.get(&key) {
                    if self.decrypt_count(ct).unwrap_or(0) >= required {
                        Some(elem.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();
        result.sort();
        result.dedup();
        result
    }

    /// 更新秘密门限和交集阈值，要求新值均不超过参与方数量
    #[inline(always)]
    fn update_thresholds(
        &mut self,
        new_threshold: u32,
        new_intersection_threshold: u32,
        new_exact: bool,
    ) {
        let part_count = self.participants.len() as u32;
        if new_threshold > part_count || new_intersection_threshold > part_count {
            println!(
                "错误：秘密门限和交集阈值必须小于或等于参与方数量（{}）",
                part_count
            );
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
}

impl Drop for ProtocolEngine {
    fn drop(&mut self) {
        self.master_secret.zeroize();
        self.precomputed_lagrange.zeroize();
        for sec in self.version_agg_secret.values_mut() {
            sec.zeroize();
        }
        self.participants.iter_mut().for_each(|p| {
            p.secret_share.zeroize();
            p.public_share = RISTRETTO_BASEPOINT_POINT;
        });
    }
}

/// 对参与方集合进行随机更新：对每个参与方进行 nd 次随机增删操作
fn random_update_participants(
    engine: &mut ProtocolEngine,
    choose_nd: usize,
    union_candidates: &[Vec<u8>],
) {
    // 使用局部 OsRng 实例避免重复初始化
    let mut rng = OsRng;
    engine.participants.iter_mut().for_each(|participant| {
        for _ in 0..choose_nd {
            let rand_val = rng.try_next_u32().unwrap();
            let is_remove = (rand_val % 2) == 0;
            if is_remove {
                let available: Vec<_> = participant.elements.iter().cloned().collect();
                if !available.is_empty() {
                    if let Some(base) = &engine.base_element {
                        let remove_idx = (rand_val as usize) % available.len();
                        if available[remove_idx] == *base {
                            continue;
                        }
                    }
                    let remove_idx = (rand_val as usize) % available.len();
                    let removed = available[remove_idx].clone();
                    participant.elements.remove(&removed);
                }
            } else {
                let not_in: Vec<_> = union_candidates
                    .iter()
                    .filter(|c| !participant.elements.contains(*c))
                    .cloned()
                    .collect();
                if !not_in.is_empty() {
                    let add_idx = (rand_val as usize) % not_in.len();
                    let to_add = not_in[add_idx].clone();
                    participant.elements.insert(to_add);
                }
            }
        }
    });
}

/// 主函数入口
fn main() {
    println!("===== 椭圆曲线详细信息 =====");
    println!("标准曲线名称: Ristretto/Curve25519");
    println!(
        "[生成元 G]       {}",
        hex::encode(RISTRETTO_BASEPOINT_POINT.compress().to_bytes())
    );
    println!("[曲线阶 n]       {}", RISTRETTO_GROUP_ORDER_DEC);
    println!("============================\n");

    // 读取用户参数（随机元素生成过程不计入测时）
    println!("请选择运行模式：");
    println!("1. UMPSI 模式");
    println!("2. 阈值介入模式（基准元素自动选取）");
    print!("请输入选项 (1/2): ");
    stdout().flush().unwrap();
    let mode_input = read_input_line();

    print!("请输入候选元素范围下界 (u32): ");
    stdout().flush().unwrap();
    let candidate_lower: u32 = read_input_line().parse().expect("请输入合法数字");
    print!("请输入候选元素范围上界 (u32): ");
    stdout().flush().unwrap();
    let candidate_upper: u32 = read_input_line().parse().expect("请输入合法数字");
    assert!(candidate_lower <= candidate_upper, "下界应小于等于上界");

    print!("请输入候选元素数量（每个参与者的候选池大小）: ");
    stdout().flush().unwrap();
    let candidate_count: usize = read_input_line().parse().expect("请输入合法数字");

    print!("请输入参与方数量: ");
    stdout().flush().unwrap();
    let participant_count: usize = read_input_line().parse().expect("请输入合法数字");

    // 根据模式设定阈值（仅当 mode_input 为 "2" 时提示输入，否则默认均为参与方数量）
    let (init_threshold, init_intersection) = if mode_input == "2" {
        println!("请输入初始秘密门限: ");
        let t: u32 = read_input_line().parse().expect("请输入合法数字");
        println!("请输入初始交集阈值: ");
        let i: u32 = read_input_line().parse().expect("请输入合法数字");
        (t, i)
    } else {
        (participant_count as u32, participant_count as u32)
    };

    // 初始化协议引擎
    let mut engine = ProtocolEngine::new(init_threshold, init_intersection, true);

    // 阈值模式下生成基准候选元素，保证各参与者候选池均包含；UMPSI 模式则不需要
    let base_candidate = if mode_input == "2" {
        Some(generate_single_candidate(candidate_lower, candidate_upper))
    } else {
        None
    };

    // 为每个参与者生成独立候选池（候选池生成过程不计入数据计算测时）
    for _ in 0..participant_count {
        let mut pool: HashSet<Vec<u8>> =
            generate_candidate_elements(candidate_count, candidate_lower, candidate_upper)
                .into_iter()
                .collect();
        if let Some(ref base) = base_candidate {
            pool.insert(base.clone());
        }
        engine.add_participant(Participant::new(pool));
    }

    // 计算全体候选池的并集（不计入测时）
    let union_candidates: Vec<Vec<u8>> = engine
        .participants
        .iter()
        .flat_map(|p| p.elements.iter().cloned())
        .collect::<HashSet<_>>()
        .into_iter()
        .sorted()
        .collect();

    engine.distribute_threshold_shares();
    println!("\n参与方数量: {}", engine.participants.len());
    println!("全局候选并集大小: {}", union_candidates.len());

    // 第一轮交集计算（仅计算数据操作时间，不包含候选元素生成过程）
    let start = Instant::now();
    let enc_map = engine.chain_encryption_process_map(&union_candidates, Scalar::ONE);
    let intersection = engine.compute_intersection(&enc_map, &union_candidates);
    let duration1 = start.elapsed().as_millis();
    println!("\n第一次计算交集：");
    println!("计算耗时: {} ms", duration1);
    println!("交集大小: {} 个元素", intersection.len());
    // engine.store_intersection_result(&intersection);

    // 阈值模式下支持更新门限
    if mode_input == "2" {
        println!("\n是否更新门限？(y/n): ");
        stdout().flush().unwrap();
        let update_threshold_choice = read_input_line();
        if update_threshold_choice.eq_ignore_ascii_case("y") {
            println!(
                "请输入新的秘密门限 (≤参与方数量 {}): ",
                engine.participants.len()
            );
            print!("新的秘密门限: ");
            stdout().flush().unwrap();
            let new_secret: u32 = read_input_line().parse().unwrap_or(engine.secret_threshold);
            println!(
                "请输入新的交集阈值 (≤参与方数量 {}): ",
                engine.participants.len()
            );
            print!("新的交集阈值: ");
            stdout().flush().unwrap();
            let new_intersection: u32 = read_input_line()
                .parse()
                .unwrap_or(engine.intersection_threshold);
            engine.update_thresholds(new_secret, new_intersection, engine.exact_intersection);
        }
    }

    // 更新参与者元素（随机增删操作，候选元素集合仍保持不变）
    print!("\n请输入每个参与方更新元素的次数 Nd: ");
    stdout().flush().unwrap();
    let choose_nd: usize = read_input_line().parse().unwrap_or(0);
    if choose_nd > 0 {
        random_update_participants(&mut engine, choose_nd, &union_candidates);
        engine.current_version += 1;
        engine.distribute_threshold_shares();
    }

    // 第二轮交集计算（仅计算数据操作时间）
    let start2 = Instant::now();
    let enc_map2 = engine.chain_encryption_process_map(&union_candidates, Scalar::ONE);
    let intersection2 = engine.compute_intersection(&enc_map2, &union_candidates);
    let duration2 = start2.elapsed().as_millis();
    println!("\n第二次计算交集：");
    println!("计算耗时: {} ms", duration2);
    println!("交集大小: {} 个元素", intersection2.len());
    // engine.store_intersection_result(&intersection2);

    println!("\n======= 协议执行完成 =======");
}
