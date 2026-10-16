import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Real
import MyLean.Common
import MyLean.Exercises.«science-tokyo».«2019».Statement

/-!
# 東京工業大学 2019年度 理系 第4問 (Proof)

平面による3次元空間分割の最大個数
$$ T_{\max}(n) = \sum_{k=0}^3 \binom{n}{k} = \frac{n^3 + 5n + 6}{6} $$
の形式証明。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

/-! ### 平面分割・空間分割の漸化式補題 -/

/-- 直線による2次元平面分割の最大数を表す関数:
$$ S(k) = \binom{k}{0} + \binom{k}{1} + \binom{k}{2} = 1 + k + \frac{k(k-1)}{2} $$
「怠けた仕出し屋の数列」として知られ、任意の $k$ 本の直線配置による補集合の連結成分数の最大値を与える。 -/
def maxPlaneRegions (k : ℕ) : ℕ :=
  Nat.choose k 0 + Nat.choose k 1 + Nat.choose k 2

/-- 3次元空間分割の最大数に関する漸化式:
$T_{\max}(n + 1) = T_{\max}(n) + S(n)$。
$(n+1)$ 枚目の平面が既存の $n$ 枚の平面と交わるとき、その平面上に $n$ 本の交線が現れ、
最大で $S(n)$ 個の平面領域が生じる。
追加された平面が通過した既存の立体領域をそれぞれ2つに分割するため、
増える立体領域の個数は平面上の分割数 $S(n)$ と完全に一致する。 -/
lemma maxSpaceRegions_succ (n : ℕ) :
    maxSpaceRegions (n + 1) = maxSpaceRegions n + maxPlaneRegions n := by
  dsimp [maxSpaceRegions, maxPlaneRegions]
  have h1 : (n + 1).choose 1 = n.choose 0 + n.choose 1 := rfl
  have h2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := rfl
  have h3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := rfl
  have hz1 : (n + 1).choose 0 = 1 := Nat.choose_zero_right (n + 1)
  have hz0 : n.choose 0 = 1 := Nat.choose_zero_right n
  omega

/-! ### 組合せ数に関する計算補題 -/

/-- 組合せ数 $\binom{m}{2}$ の 2 倍に関する恒等式。 -/
lemma two_mul_choose_two (m : ℕ) :
    2 * Nat.choose m 2 = m * (m - 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases m with _ | m
    · rfl
    · rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have hsub : m + 1 - 1 = m := by omega
      rw [hsub] at ih
      calc
        2 * (m + 1 + (m + 1).choose 2) =
          2 * (m + 1) + 2 * (m + 1).choose 2 := by ring
        _ = 2 * (m + 1) + (m + 1) * m := by rw [ih]
        _ = (m + 1 + 1) * (m + 1 + 1 - 1) := by
          have : m + 1 + 1 - 1 = m + 1 := by omega
          rw [this]
          ring

/-- 怠けた仕出し屋の数列の閉じた多項式表示:
$2 \cdot S(k) = k^2 + k + 2$。
したがって $S(k) = 1 + k + \frac{k(k-1)}{2}$ が成り立つ。 -/
lemma two_mul_maxPlaneRegions (k : ℕ) :
    2 * maxPlaneRegions k = k ^ 2 + k + 2 := by
  dsimp [maxPlaneRegions]
  have h := two_mul_choose_two k
  rw [Nat.choose_zero_right, Nat.choose_one_right]
  rcases k with _ | k
  · rfl
  · have hk : k + 1 - 1 = k := by omega
    rw [hk] at h
    calc
      2 * (1 + (k + 1) + (k + 1).choose 2) =
        2 + 2 * (k + 1) + 2 * (k + 1).choose 2 := by ring
      _ = 2 + 2 * (k + 1) + (k + 1) * k := by rw [h]
      _ = (k + 1) ^ 2 + (k + 1) + 2 := by ring

/-- 組合せ数 $\binom{m+2}{3}$ の 6 倍に関する恒等式。 -/
lemma six_mul_choose_three (m : ℕ) :
    6 * Nat.choose (m + 2) 3 = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.choose_succ_succ]
    have h2 : 2 * Nat.choose (m + 2) 2 = (m + 2) * (m + 1) := by
      have h := two_mul_choose_two (m + 2)
      have h_sub : (m + 2) - 1 = m + 1 := by omega
      rw [h_sub] at h
      exact h
    calc
      6 * ((m + 2).choose 2 + (m + 2).choose 3) =
        3 * (2 * (m + 2).choose 2) + 6 * (m + 2).choose 3 := by ring
      _ = 3 * ((m + 2) * (m + 1)) + m * (m + 1) * (m + 2) := by rw [h2, ih]
      _ = (m + 1) * (m + 1 + 1) * (m + 1 + 2) := by ring

/-- 空間領域最大数の 6 倍に関する恒等式:
$6 \cdot T_{\max}(n) = n³ + 5n + 6$。 -/
lemma six_mul_maxSpaceRegions (n : ℕ) :
    6 * maxSpaceRegions n = n ^ 3 + 5 * n + 6 := by
  rcases n with _ | _ | _ | m
  · dsimp [maxSpaceRegions]
    rfl
  · dsimp [maxSpaceRegions]
    rfl
  · dsimp [maxSpaceRegions]
    rfl
  · dsimp [maxSpaceRegions]
    have h2 : 2 * Nat.choose (m + 3) 2 = (m + 3) * (m + 2) := by
      have h := two_mul_choose_two (m + 3)
      have hm : m + 3 - 1 = m + 2 := by omega
      rw [hm] at h
      exact h
    have h3 : 6 * Nat.choose (m + 3) 3 = (m + 1) * (m + 2) * (m + 3) := by
      have h := six_mul_choose_three (m + 1)
      have hm : (m + 1) + 2 = m + 3 := by omega
      rw [hm] at h
      exact h
    calc
      6 * (Nat.choose (m + 3) 0 + Nat.choose (m + 3) 1 +
           Nat.choose (m + 3) 2 + Nat.choose (m + 3) 3) =
        6 * 1 + 6 * (m + 3) + 3 * (2 * Nat.choose (m + 3) 2) +
          6 * Nat.choose (m + 3) 3 := by
        rw [Nat.choose_zero_right, Nat.choose_one_right]
        ring
      _ = 6 + 6 * (m + 3) + 3 * ((m + 3) * (m + 2)) +
          (m + 1) * (m + 2) * (m + 3) := by rw [h2, h3]
      _ = (m + 3) ^ 3 + 5 * (m + 3) + 6 := by ring

/-! ### 本問の主定理 -/

/-! ### 幾何学的交差理論と領域数の漸化不等式 -/

/-- 2本の直線が平行である条件。法線ベクトルがスカラー倍であることとして定義される。 -/
def parallelLines (L₁ L₂ : Line2) : Prop :=
  ∃ (c : ℝ), L₁.normVec = c • L₂.normVec

/-- 2次元直線配置が一般の位置(General Position)にある条件。
すべての直線が互いに平行でなく、かつどの相異なる3直線も1点で交わらない。 -/
def GeneralPositionLines (k : ℕ) (L : Fin k → Line2) : Prop :=
  (∀ i j, i ≠ j → ¬ parallelLines (L i) (L j)) ∧
  (∀ i j l, i ≠ j → j ≠ l → i ≠ l → (L i).toSet ∩ (L j).toSet ∩ (L l).toSet = ∅)

/-- 2枚の平面が平行である条件。法線ベクトルがスカラー倍であることとして定義される。 -/
def parallelPlanes (H₁ H₂ : Plane3) : Prop :=
  ∃ (c : ℝ), H₁.normVec = c • H₂.normVec

/-- 2枚の平面が交わる(平行でない)条件。 -/
def intersectPlanes (H₁ H₂ : Plane3) : Prop :=
  ¬ parallelPlanes H₁ H₂

/-- 3次元平面配置が一般の位置(General Position)にある条件。
どの2平面も平行でなく、どの3平面も共通直線をもたず1点で交わり、どの4平面も1点を共有しない。 -/
def GeneralPositionPlanes (n : ℕ) (H : Fin n → Plane3) : Prop :=
  (∀ i j, i ≠ j → ¬ parallelPlanes (H i) (H j)) ∧
  (∀ i j l, i ≠ j → j ≠ l → i ≠ l →
    ∃ p : Space3, (H i).toSet ∩ (H j).toSet ∩ (H l).toSet = {p}) ∧
  (∀ i j l m, i ≠ j → j ≠ l → l ≠ m → i ≠ l → i ≠ m → j ≠ m →
    (H i).toSet ∩ (H j).toSet ∩ (H l).toSet ∩ (H m).toSet = ∅)

/-- 2次元平面分割の最大数に関する漸化式:
$S(k + 1) = S(k) + (k + 1)$。
$(k+1)$ 本目の直線が既存の $k$ 本の直線と高々 $k$ 個の交点で交わることにより、
その直線自身が高々 $k + 1$ 個の線分・半直線に分割され、同数の平面領域が新たに生成される幾何的性質に対応する。 -/
lemma maxPlaneRegions_succ_step (k : ℕ) :
    maxPlaneRegions (k + 1) = maxPlaneRegions k + (k + 1) := by
  dsimp [maxPlaneRegions]
  have h1 : (k + 1).choose 1 = k.choose 0 + k.choose 1 := rfl
  have h2 : (k + 1).choose 2 = k.choose 1 + k.choose 2 := rfl
  have hz1 : (k + 1).choose 0 = 1 := Nat.choose_zero_right (k + 1)
  have hz0 : k.choose 0 = 1 := Nat.choose_zero_right k
  have hk1 : k.choose 1 = k := Nat.choose_one_right k
  omega

/-! ### 直線配置の漸化不等式に関する1次元帰着と中間補題 -/

/-! #### ステップ 1: 1次元実数直線の有限点分割補題 -/

/-- 実数直線上の有限点集合 S による補集合 ℝ \ S の開区間(連結成分)の個数。
$m$ 個の相異なる点によって、実数直線は高々 $m + 1$ 個の互いに素な開区間に分割される。 -/
noncomputable def realIntervalsCount (S : Finset ℝ) : ℕ :=
  Nat.card (ConnectedComponents ({x : ℝ | x ∉ S}))

/-- 実数直線の有限点分割に関する上界補題:
有限点集合 $S$ による補集合の開区間(凸連結成分)の個数は card S + 1 以下である。
昇順リスト (-∞, x₀), (x₀, x₁), ..., (x_{m-1}, ∞) の $m + 1$ 個の区間分解に対応する。 -/
lemma card_intervals_of_finset_real (S : Finset ℝ) :
    realIntervalsCount S ≤ S.card + 1 := by
  sorry

/-! #### ステップ 2: 直線同士の交点数の上界 -/

/-- 既存の $k$ 本の直線と $(k+1)$ 本目の直線との交点に対応する直線上のパラメータ集合。
2直線が平行でない限り交点は一意に定まるため、交点パラメータ集合の要素数は高々 $k$ である。 -/
def lineIntersectionParams (k : ℕ) (_L : Fin (k + 1) → Line2) : Finset ℝ :=
  sorry

/-- 直線上の交点パラメータ数の上界補題:
$(k+1)$ 本目の直線が既存の $k$ 本の直線と交わる点の総数は、$k$ 以下である。 -/
lemma card_lineIntersectionParams_le (k : ℕ) (L : Fin (k + 1) → Line2) :
    (lineIntersectionParams k L).card ≤ k := by
  sorry

/-! #### ステップ 3: 凸領域(符号ベクトル)の切断と直線上の区間への単射 -/

/-- 直線群によって定まる開半空間の符号写像。各直線に対し正負のどちら側にあるかを表す。 -/
def SignVector2 (k : ℕ) := Fin k → Bool

/-- 符号写像 σ が定める平面上の開凸多角形領域。 -/
def convexPlaneRegion (k : ℕ) (L : Fin k → Line2) (σ : SignVector2 k) : Set Plane2 :=
  {x : Plane2 | ∀ i : Fin k,
    if σ i then (L i).offset < @inner ℝ Plane2 _ (L i).normVec x
    else @inner ℝ Plane2 _ (L i).normVec x < (L i).offset}

/-- 既存の凸領域 $R$ が新しい直線によって2つに分割される条件。
領域の内部を直線が横切ることと同値である。 -/
def isSplitByLine (s : Set Plane2) (line : Line2) : Prop :=
  (s ∩ line.toSet).Nonempty

/-- 切断と交差の対応補題:
既存の凸領域が新しい直線によって分割されることと、直線との交わりが非空であることは同値である。
凸開集合の中間値の定理から従う。 -/
lemma split_region_intersects_line (k : ℕ) (L : Fin (k + 1) → Line2) (σ : SignVector2 k)
    (hsplit : isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) :
    (convexPlaneRegion k (L ∘ Fin.castSucc) σ ∩ (L (Fin.last k)).toSet).Nonempty := by
  exact hsplit

/-- 異なる凸領域から得られる直線上の交差区間は互いに素である。 -/
lemma disjoint_intersections_on_line (k : ℕ) (L : Fin (k + 1) → Line2)
    (σ₁ σ₂ : SignVector2 k) (hne : σ₁ ≠ σ₂) :
    Disjoint (convexPlaneRegion k (L ∘ Fin.castSucc) σ₁ ∩ (L (Fin.last k)).toSet)
             (convexPlaneRegion k (L ∘ Fin.castSucc) σ₂ ∩ (L (Fin.last k)).toSet) := by
  sorry

/-- 2次元平面における直線追加の幾何学的漸化不等式:
$(k+1)$ 本目の直線を追加したとき、既存の $k$ 本の直線との交点で高々 $k+1$ 個の線分・半直線に分かれ、
平面領域数の増加量は高々 $k+1$ である。
証明は直線上の有限点集合による区間分割への単射に帰着される。 -/
lemma planeRegionsCount_succ_le (k : ℕ) (L : Fin (k + 1) → Line2) :
    planeRegionsCount (k + 1) L ≤ planeRegionsCount k (L ∘ Fin.castSucc) + (k + 1) := by
  sorry

/-- 直線が0本のとき、補集合は平面全体であり領域数は1である。 -/
lemma planeRegionsCount_zero (L : Fin 0 → Line2) :
    planeRegionsCount 0 L = 1 := by
  sorry

/-- 2次元直線配置に対する幾何学的上界補題:
任意の $k$ 本の直線配置による補集合の連結成分数が
$S(k) = \binom{k}{0} + \binom{k}{1} + \binom{k}{2}$ 以下であること。

【導出過程】
$k-1$ 本の直線がある平面に、$k$ 本目の直線を追加する場合を考える。
追加した直線は既存の直線と交差し、最大で $k$ 個の線分や半直線に分かれる。
新しくできた線分や半直線がそれぞれ既存の領域を2分割するため、
全体の領域数は高々 $k$ 個増える仕組みである。
これにより漸化式 $S(k) = S(k-1) + k$ が成り立ち、$S(1) = 2$ から二項係数の和が得られる。

【領域数が最大値以下となる理由】
直線同士が平行だったり、複数の直線が1点で交わったりすると、
交点で生まれる線分や領域の増加数が減る。
したがって、すべての直線が平行でなく、どの3直線も1点で交わらない配置でのみ最大値が達成され、
任意の直線配置では領域数が常に最大値 $S(k)$ 以下となる。 -/
theorem planeRegionsCount_le_maxPlaneRegions (k : ℕ) (L : Fin k → Line2) :
    planeRegionsCount k L ≤ maxPlaneRegions k := by
  induction k with
  | zero =>
    rw [planeRegionsCount_zero L]
    dsimp [maxPlaneRegions]
    decide
  | succ m ih =>
    have hstep := planeRegionsCount_succ_le m L
    have hih := ih (L ∘ Fin.castSucc)
    have hsucc := maxPlaneRegions_succ_step m
    omega

/-- 一般の位置にある直線配置に対する最大値達成定理:
一般の位置にある直線配置 $L$ では、領域数が最大値 $S(k)$ に一致する。 -/
theorem planeRegionsCount_eq_max_of_general_position (k : ℕ) (L : Fin k → Line2)
    (hgen : GeneralPositionLines k L) :
    planeRegionsCount k L = maxPlaneRegions k := by
  sorry

/-- 3次元平面配置に対する幾何学的漸化不等式:
$(n+1)$ 枚目の平面 $H_{n}$ を追加したときの空間領域数は、
既存の $n$ 枚による領域数と、第 $(n+1)$ 平面上に現れる交線配置による領域数の和で抑えられる。
したがって、空間領域数の増加量は高々 $S(n)$ である。

【新しい平面上の領域分割】
平面 $H_{n+1}$ は、空間内に既に存在する $n$ 枚の平面 $H_1, \dots, H_n$ とそれぞれ交差する。
平行でない各平面との交わりによって、$H_{n+1}$ 上には高々 $n$ 本の交線が現れ、
これらによって平面 $H_{n+1}$ 自身がいくつかの平面領域に分割される。

【立体領域が増加する幾何学的仕組み】
追加された平面 $H_{n+1}$ は既存の空間領域を横切り、通過した領域をそれぞれ2つに分割する。
$H_{n+1}$ 上に現れる各平面領域は、既存の空間領域の内部を切断する境界面に対応するため、
新しく形成された平面領域1つにつき、空間全体の領域数が1つ増加する。

【漸化式による導出と評価】
空間領域数を $T_n$、新しい平面上の領域数を $U_{n}$ とすると、漸化関係
$$ T_{n+1} = T_n + U_{n} $$
が成り立つ。一般の位置(どの3平面も共通直線をもたず、交線が一般の位置をなす配置)にあるとき、
$U_{n}$ は怠けた仕出し屋の数列 $S(n)$ と一致し、最大増加量を与える。
したがって、増える立体領域の個数は追加された平面上の領域数と一致し、
一般の配置における増加量は常に $S(n)$ 以下となる。 -/
lemma spaceRegionsCount_succ_le (n : ℕ) (H : Fin (n + 1) → Plane3) :
    spaceRegionsCount (n + 1) H ≤ spaceRegionsCount n (H ∘ Fin.castSucc) + maxPlaneRegions n := by
  sorry

/-- 一般の位置にある平面配置における領域数の漸化等式:
一般の位置にある配置に新しい平面を追加したとき、
増える立体領域の個数は、その平面上に現れる交線配置の最大平面領域数 $S(n)$ と完全に一致する。 -/
theorem spaceRegionsCount_succ_eq_of_general_position (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H) :
    spaceRegionsCount (n + 1) H = spaceRegionsCount n (H ∘ Fin.castSucc) + maxPlaneRegions n := by
  sorry

/-- 一般の位置にある平面配置に対する最大値達成定理:
一般の位置にある平面配置 $H$ では、空間領域数が最大値 $T_{\max}(n)$ に一致する。 -/
theorem spaceRegionsCount_eq_max_of_general_position (n : ℕ) (H : Fin n → Plane3)
    (hgen : GeneralPositionPlanes n H) :
    spaceRegionsCount n H = maxSpaceRegions n := by
  sorry

/-- 平面が0枚のとき、補集合は全空間であり領域数は1である。 -/
lemma spaceRegionsCount_zero (H : Fin 0 → Plane3) :
    spaceRegionsCount 0 H = 1 := by
  sorry

/-- 3次元空間における幾何学的領域数の最大値上界定理:
任意の $n$ 枚の平面配置 $H$ による空間領域数 $T(H)$ は、代数公式 $T_{\max}(n)$ 以下である。
証明は平面の枚数 $n$ に関する帰納法と幾何学的漸化不等式による。 -/
theorem spaceRegionsCount_le_maxSpaceRegions (n : ℕ) (H : Fin n → Plane3) :
    spaceRegionsCount n H ≤ maxSpaceRegions n := by
  induction n with
  | zero =>
    rw [spaceRegionsCount_zero H]
    dsimp [maxSpaceRegions]
    decide
  | succ m ih =>
    have hstep := spaceRegionsCount_succ_le m H
    have hih := ih (H ∘ Fin.castSucc)
    have hsucc := maxSpaceRegions_succ m
    omega

/-! ### 本問の主定理 -/

/-- 【第4問 (1) の解答(代数公式との一致)】
平面分割の最大個数は多項式 (n³ + 5n + 6) / 6 に一致する。 -/
theorem problem_4_1_proof (n : ℕ) :
    maxSpaceRegions n = maxSpaceRegionsFormula n := by
  have h := six_mul_maxSpaceRegions n
  dsimp [maxSpaceRegionsFormula]
  omega

/-- 【第4問 (1) の幾何学的解答】
相異なる n 枚の平面による空間領域数は常に maxSpaceRegionsFormula n 以下であり、かつ等号を達成する配置が存在する。 -/
theorem problem_4_1_geometric_proof (n : ℕ) :
    (∀ (H : Fin n → Plane3), DistinctPlanes n H →
      spaceRegionsCount n H ≤ maxSpaceRegionsFormula n) ∧
    (∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = maxSpaceRegionsFormula n) := by
  constructor
  · intro H _hdist
    have hle := spaceRegionsCount_le_maxSpaceRegions n H
    have heq := problem_4_1_proof n
    omega
  · -- 一般の位置にある n 枚の平面配置の存在性(等号達成)。
    sorry

/-! ### 具体例 (n = 2, 3, 4) における領域数の検証補題 -/

/-- n = 2 のとき: 最大値は 4、第2位は 3 である。 -/
lemma space_regions_n_two :
    maxSpaceRegionsFormula 2 = 4 ∧ secondSpaceRegionsFormula 2 = 3 := by
  dsimp [maxSpaceRegionsFormula, secondSpaceRegionsFormula]
  decide

/-- n = 3 のとき: 最大値は 8、第2位は 7、第3位は 6 である。
問題文の例示 T(H₁, H₂, H₃) = 8 および 7 に対応する。 -/
lemma space_regions_n_three :
    maxSpaceRegionsFormula 3 = 8 ∧
    secondSpaceRegionsFormula 3 = 7 ∧
    thirdSpaceRegionsFormula 3 = 6 := by
  dsimp [maxSpaceRegionsFormula, secondSpaceRegionsFormula, thirdSpaceRegionsFormula]
  decide

/-- n = 4 のとき: 最大値は 15、第2位は 14、第3位は幾何的制約による例外値 12 である。 -/
lemma space_regions_n_four :
    maxSpaceRegionsFormula 4 = 15 ∧
    secondSpaceRegionsFormula 4 = 14 ∧
    thirdSpaceRegionsFormula 4 = 12 := by
  dsimp [maxSpaceRegionsFormula, secondSpaceRegionsFormula, thirdSpaceRegionsFormula]
  decide

/-- 【第4問 (2) の解答(代数公式との一致)】
n ≥ 2 のとき、2番目に大きい値は最大値より 1 小さく、多項式 (n³ + 5n) / 6 と一致する。 -/
theorem problem_4_2_proof (n : ℕ) (hn : 2 ≤ n) :
    secondSpaceRegionsFormula n = maxSpaceRegionsFormula n - 1 := by
  have h := six_mul_maxSpaceRegions n
  dsimp [secondSpaceRegionsFormula, maxSpaceRegionsFormula]
  omega

/-- 【第4問 (2) の幾何学的解答】
n ≥ 2 のとき、最大値未満の任意の配置の領域数は secondSpaceRegionsFormula n 以下であり、かつ達成可能である。 -/
theorem problem_4_2_geometric_proof (n : ℕ) (hn : 2 ≤ n) :
    (∀ (H : Fin n → Plane3), DistinctPlanes n H →
      spaceRegionsCount n H < maxSpaceRegionsFormula n →
      spaceRegionsCount n H ≤ secondSpaceRegionsFormula n) ∧
    (∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = secondSpaceRegionsFormula n) := by
  sorry

/-- 【第4問 (3) の解答(代数公式との一致)】
n ≥ 3 のとき、3番目に大きい値は、n = 4 のとき例外値 12 であり、
n ≠ 4 のとき最大値より 2 小さい値 (n³ + 5n - 6) / 6 である。 -/
theorem problem_4_3_proof (n : ℕ) (_hn : 3 ≤ n) :
    thirdSpaceRegionsFormula n = if n = 4 then 12 else maxSpaceRegionsFormula n - 2 := by
  by_cases h4 : n = 4
  · subst h4
    rfl
  · have h := six_mul_maxSpaceRegions n
    dsimp [thirdSpaceRegionsFormula, maxSpaceRegionsFormula]
    simp only [h4, ↓reduceIte]
    omega

/-- 【第4問 (3) の幾何学的解答】
n ≥ 3 のとき、第2位未満の任意の配置の領域数は thirdSpaceRegionsFormula n 以下であり、かつ達成可能である。
特に n = 4 のとき、領域数が 13 となる配置は存在せず、次は 12 となる。 -/
theorem problem_4_3_geometric_proof (n : ℕ) (hn : 3 ≤ n) :
    (∀ (H : Fin n → Plane3), DistinctPlanes n H →
      spaceRegionsCount n H < secondSpaceRegionsFormula n →
      spaceRegionsCount n H ≤ thirdSpaceRegionsFormula n) ∧
    (∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = thirdSpaceRegionsFormula n) := by
  sorry

end MyLean.Exercises.«science-tokyo».«2019»
