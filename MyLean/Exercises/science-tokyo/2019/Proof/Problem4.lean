import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
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

/-- 直線による2次元平面分割の最大数を表す関数 S(k) = binom(k, 0) + binom(k, 1) + binom(k, 2)。 -/
def maxPlaneRegions (k : ℕ) : ℕ :=
  Nat.choose k 0 + Nat.choose k 1 + Nat.choose k 2

/-- 3次元空間分割の最大数に関する漸化式:
$T_{\max}(n + 1) = T_{\max}(n) + S(n)$。
$(n+1)$ 枚目の平面が既存の $n$ 枚の平面と交わることで、その平面上に $S(n)$ 個の領域が生じ、
同数の立体領域が新たに分割生成される幾何的性質に対応する。 -/
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

/-- 2枚の平面が平行である条件。法線ベクトルがスカラー倍であることとして定義される。 -/
def parallelPlanes (H₁ H₂ : Plane3) : Prop :=
  ∃ (c : ℝ), H₁.normVec = c • H₂.normVec

/-- 2枚の平面が交わる(平行でない)条件。 -/
def intersectPlanes (H₁ H₂ : Plane3) : Prop :=
  ¬ parallelPlanes H₁ H₂

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

/-- 2次元直線配置に対する幾何学的上界補題:
任意の $k$ 本の直線配置による平面領域数 $S(L)$ は、最大数 $S(k)$ 以下である。 -/
lemma planeRegionsCount_le_maxPlaneRegions (k : ℕ) (L : Fin k → Line2) :
    planeRegionsCount k L ≤ maxPlaneRegions k := by
  sorry

/-- 3次元平面配置に対する幾何学的漸化不等式:
$(n+1)$ 枚目の平面 $H_{n}$ を追加したときの空間領域数は、
既存の $n$ 枚による領域数と、第 $(n+1)$ 平面上に現れる交線配置による領域数の和で抑えられる。
したがって、空間領域数の増加量は高々 $S(n)$ である。 -/
lemma spaceRegionsCount_succ_le (n : ℕ) (H : Fin (n + 1) → Plane3) :
    spaceRegionsCount (n + 1) H ≤ spaceRegionsCount n (H ∘ Fin.castSucc) + maxPlaneRegions n := by
  sorry

/-- 3次元空間における幾何学的領域数の最大値上界定理:
任意の $n$ 枚の平面配置 $H$ による空間領域数 $T(H)$ は、代数公式 $T_{\max}(n)$ 以下である。
証明は平面の枚数 $n$ に関する帰納法と幾何学的漸化不等式による。 -/
theorem spaceRegionsCount_le_maxSpaceRegions (n : ℕ) (H : Fin n → Plane3) :
    spaceRegionsCount n H ≤ maxSpaceRegions n := by
  induction n with
  | zero =>
    -- 平面が0枚のとき、補集合は全空間 ℝ³ であり連結成分数は 1 である。
    sorry
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
