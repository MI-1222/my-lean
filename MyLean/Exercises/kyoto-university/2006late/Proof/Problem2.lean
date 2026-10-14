import Mathlib
import MyLean.Common
import MyLean.Exercises.«kyoto-university».«2006late».Statement

/-!
# 京都大学 2006年度後期 理系 第2問 (Proof)

確率行列 $A = \begin{pmatrix} a & 1-a \\ 1-a & a \end{pmatrix}$ と漸化式
$\begin{pmatrix} x_n \\ y_n \end{pmatrix} = A \begin{pmatrix} x_{n-1} \\ y_{n-1} \end{pmatrix}$
により定まる数列 $\{x_n\}$ が収束するための実数 $a$ の必要十分条件が $0 < a ≤ 1$ であることを示す。
-/

namespace MyLean.Exercises.«kyoto-university».«2006late»

open Filter Topology

/-! ### 漸化式と一般項に関する補題 -/

/-- ベクトル列 $(x_n, y_n)$ の成分の和と差に関する恒等式。
和は常に 1 であり、差は初項 1 に公比 $2a - 1$ を順次掛けた等比数列となる。 -/
lemma vecSeq2_sum_and_sub (a : ℝ) (n : ℕ) :
    (vecSeq2 a n).1 + (vecSeq2 a n).2 = 1 ∧
    (vecSeq2 a n).1 - (vecSeq2 a n).2 = (2 * a - 1) ^ n := by
  induction n with
  | zero =>
    simp [vecSeq2]
  | succ n ih =>
    rcases ih with ⟨ih_sum, ih_sub⟩
    dsimp [vecSeq2, step2]
    constructor
    · calc
        (a * (vecSeq2 a n).1 + (1 - a) * (vecSeq2 a n).2) +
          ((1 - a) * (vecSeq2 a n).1 + a * (vecSeq2 a n).2) =
          (vecSeq2 a n).1 + (vecSeq2 a n).2 := by ring
        _ = 1 := ih_sum
    · calc
        (a * (vecSeq2 a n).1 + (1 - a) * (vecSeq2 a n).2) -
          ((1 - a) * (vecSeq2 a n).1 + a * (vecSeq2 a n).2) =
          (2 * a - 1) * ((vecSeq2 a n).1 - (vecSeq2 a n).2) := by ring
        _ = (2 * a - 1) * (2 * a - 1) ^ n := by rw [ih_sub]
        _ = (2 * a - 1) ^ (n + 1) := by ring

/-- 数列 $\{x_n\}$ の一般項は $(1 + (2a - 1)^n) / 2$ である。 -/
lemma xSeq2_eq (a : ℝ) (n : ℕ) :
    xSeq2 a n = (1 + (2 * a - 1) ^ n) / 2 := by
  have h := vecSeq2_sum_and_sub a n
  dsimp [xSeq2]
  linarith

/-! ### 等比数列の収束に関する補題 -/

/-- 実数の等比数列 $r^n$ が実数に収束するための必要十分条件は $-1 < r ≤ 1$ である。 -/
lemma tendsto_pow_atTop_iff (r : ℝ) :
    (∃ L : ℝ, Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 L)) ↔ (-1 < r ∧ r ≤ 1) := by
  constructor
  · rintro ⟨L, hL⟩
    have hL_succ : Tendsto (fun n : ℕ => r ^ (n + 1)) atTop (𝓝 L) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have hL_mul : Tendsto (fun n : ℕ => r * r ^ n) atTop (𝓝 (r * L)) :=
      hL.const_mul r
    have h_eq_seq : (fun n : ℕ => r ^ (n + 1)) = (fun n : ℕ => r * r ^ n) := by
      ext n; ring
    rw [h_eq_seq] at hL_succ
    have h_limit_eq : L = r * L := tendsto_nhds_unique hL_succ hL_mul
    have h_factor : (1 - r) * L = 0 := by linarith
    cases mul_eq_zero.mp h_factor with
    | inl h1 =>
      have hr1 : r = 1 := by linarith
      rw [hr1]
      norm_num
    | inr h0 =>
      rw [h0] at hL
      have h_norm : ‖r‖ < 1 := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hL
      rw [Real.norm_eq_abs] at h_norm
      rw [abs_lt] at h_norm
      exact ⟨h_norm.1, h_norm.2.le⟩
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h2 with rfl | h_lt
    · use 1
      have : (fun n : ℕ => (1 : ℝ) ^ n) = (fun _ => 1) := by ext n; simp
      rw [this]
      exact tendsto_const_nhds
    · use 0
      have h_abs : |r| < 1 := abs_lt.mpr ⟨h1, h_lt⟩
      have h_norm : ‖r‖ < 1 := by
        rw [Real.norm_eq_abs]
        exact h_abs
      exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr h_norm

/-! ### 本問の主定理 -/

/-- 【第2問の解答】
数列 $\{x_n\}$ が収束するための実数 $a$ の必要十分条件は $0 < a ≤ 1$ である。 -/
theorem problem_2_proof (a : ℝ) :
    (∃ L : ℝ, Tendsto (xSeq2 a) atTop (𝓝 L)) ↔ (0 < a ∧ a ≤ 1) := by
  have h_conv_iff :
      (∃ L : ℝ, Tendsto (xSeq2 a) atTop (𝓝 L)) ↔
      (∃ L' : ℝ, Tendsto (fun n : ℕ => (2 * a - 1) ^ n) atTop (𝓝 L')) := by
    constructor
    · rintro ⟨L, hL⟩
      use 2 * L - 1
      have h_eq : (fun n : ℕ => (2 * a - 1) ^ n) = (fun n : ℕ => 2 * xSeq2 a n - 1) := by
        ext n
        rw [xSeq2_eq a n]
        ring
      rw [h_eq]
      exact (hL.const_mul 2).sub_const 1
    · rintro ⟨L', hL'⟩
      use (1 + L') / 2
      have h_eq : xSeq2 a = (fun n : ℕ => (1 + (2 * a - 1) ^ n) / 2) := by
        ext n
        exact xSeq2_eq a n
      rw [h_eq]
      exact (tendsto_const_nhds.add hL').div_const 2
  rw [h_conv_iff]
  rw [tendsto_pow_atTop_iff (2 * a - 1)]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

end MyLean.Exercises.«kyoto-university».«2006late»
