import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MyLean.Common
import MyLean.Exercises.«science-tokyo».«2019».Statement

/-!
# 東京工業大学 2019年度 理系 第3問 (Proof)

複素数集合 $M = \{ \frac{p+qi}{3+2i} \mid p, q \in ℤ \}$ に関する格子点計数問題。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

open Real

/-! ### 不等式変形に関する基礎補題 -/

/-- √13 の正値性。 -/
lemma sqrt13_pos : 0 < Real.sqrt 13 := by
  have : (0 : ℝ) < 13 := by norm_num
  exact Real.sqrt_pos.mpr this

/-- √13 は 0 でない。 -/
lemma sqrt13_ne : Real.sqrt 13 ≠ 0 := sqrt13_pos.ne'

/-- (√13)^2 = 13。 -/
lemma sqrt13_sq : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)

/-- (2 * √2)^2 = 8。 -/
lemma two_mul_sqrt2_sq : (2 * Real.sqrt 2) ^ 2 = 8 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    (2 * Real.sqrt 2) ^ 2 = 2 ^ 2 * (Real.sqrt 2) ^ 2 := mul_pow 2 (Real.sqrt 2) 2
    _ = 4 * 2 := by rw [h2]; norm_num
    _ = 8 := by norm_num

/-- 0 ≤ r のとき 4 ≤ 13 * r^2 と 2 / √13 ≤ r は同値である。 -/
lemma four_le_thirteen_mul_sq_iff (r : ℝ) (hr : 0 ≤ r) :
    4 ≤ 13 * r ^ 2 ↔ 2 / Real.sqrt 13 ≤ r := by
  have hpos : 0 < Real.sqrt 13 := sqrt13_pos
  have hne : Real.sqrt 13 ≠ 0 := sqrt13_ne
  have hsq : (Real.sqrt 13) ^ 2 = 13 := sqrt13_sq
  have h_bound : 0 ≤ 2 / Real.sqrt 13 := by
    apply div_nonneg (by norm_num) hpos.le
  constructor
  · intro h
    have h_sq_diff : 0 ≤ (r - 2 / Real.sqrt 13) * (r + 2 / Real.sqrt 13) := by
      calc
        0 ≤ r ^ 2 - 4 / 13 := by linarith
        _ = r ^ 2 - (2 / Real.sqrt 13) ^ 2 := by
          have : (2 / Real.sqrt 13) ^ 2 = 4 / 13 := by
            rw [div_pow, hsq]
            norm_num
          rw [this]
        _ = (r - 2 / Real.sqrt 13) * (r + 2 / Real.sqrt 13) := by ring
    have h_sum_pos : 0 < r + 2 / Real.sqrt 13 := by
      have : 0 < 2 / Real.sqrt 13 := div_pos (by norm_num) hpos
      linarith
    have h_sub_nonneg : 0 ≤ r - 2 / Real.sqrt 13 := by
      nlinarith
    linarith
  · intro h
    have h_diff : 0 ≤ r - 2 / Real.sqrt 13 := by linarith
    have h_sum : 0 ≤ r + 2 / Real.sqrt 13 := by linarith
    have h_prod : 0 ≤ (r - 2 / Real.sqrt 13) * (r + 2 / Real.sqrt 13) :=
      mul_nonneg h_diff h_sum
    have h_expand : (r - 2 / Real.sqrt 13) * (r + 2 / Real.sqrt 13) =
        r ^ 2 - 4 / 13 := by
      calc
        (r - 2 / Real.sqrt 13) * (r + 2 / Real.sqrt 13) =
          r ^ 2 - (2 / Real.sqrt 13) ^ 2 := by ring
        _ = r ^ 2 - 4 / 13 := by
          have : (2 / Real.sqrt 13) ^ 2 = 4 / 13 := by
            rw [div_pow, hsq]
            norm_num
          rw [this]
    rw [h_expand] at h_prod
    linarith

/-- 0 ≤ r のとき 13 * r^2 ≤ 8 と r ≤ 2 * √2 / √13 は同値である。 -/
lemma thirteen_mul_sq_le_eight_iff (r : ℝ) (hr : 0 ≤ r) :
    13 * r ^ 2 ≤ 8 ↔ r ≤ 2 * Real.sqrt 2 / Real.sqrt 13 := by
  have hpos : 0 < Real.sqrt 13 := sqrt13_pos
  have hsq13 : (Real.sqrt 13) ^ 2 = 13 := sqrt13_sq
  have hsq8 : (2 * Real.sqrt 2) ^ 2 = 8 := two_mul_sqrt2_sq
  have h_bound_nonneg : 0 ≤ 2 * Real.sqrt 2 / Real.sqrt 13 := by
    apply div_nonneg
    · have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith
    · exact hpos.le
  have h_bound_sq : (2 * Real.sqrt 2 / Real.sqrt 13) ^ 2 = 8 / 13 := by
    rw [div_pow, hsq8, hsq13]
  constructor
  · intro h
    have h_diff : (r - 2 * Real.sqrt 2 / Real.sqrt 13) *
        (r + 2 * Real.sqrt 2 / Real.sqrt 13) ≤ 0 := by
      calc
        (r - 2 * Real.sqrt 2 / Real.sqrt 13) * (r + 2 * Real.sqrt 2 / Real.sqrt 13) =
          r ^ 2 - (2 * Real.sqrt 2 / Real.sqrt 13) ^ 2 := by ring
        _ = r ^ 2 - 8 / 13 := by rw [h_bound_sq]
        _ ≤ 0 := by linarith
    by_contra! h_gt
    have h_sum : 0 < r + 2 * Real.sqrt 2 / Real.sqrt 13 := by linarith
    have h_sub : 0 < r - 2 * Real.sqrt 2 / Real.sqrt 13 := by linarith
    have h_prod_pos : 0 < (r - 2 * Real.sqrt 2 / Real.sqrt 13) *
        (r + 2 * Real.sqrt 2 / Real.sqrt 13) :=
      mul_pos h_sub h_sum
    linarith
  · intro h
    have h_sub : r - 2 * Real.sqrt 2 / Real.sqrt 13 ≤ 0 := by linarith
    have h_sum : 0 ≤ r + 2 * Real.sqrt 2 / Real.sqrt 13 := by linarith
    have h_prod : (r - 2 * Real.sqrt 2 / Real.sqrt 13) *
        (r + 2 * Real.sqrt 2 / Real.sqrt 13) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h_sub h_sum
    have h_expand : (r - 2 * Real.sqrt 2 / Real.sqrt 13) * (r + 2 * Real.sqrt 2 / Real.sqrt 13) =
        r ^ 2 - 8 / 13 := by
      calc
        (r - 2 * Real.sqrt 2 / Real.sqrt 13) * (r + 2 * Real.sqrt 2 / Real.sqrt 13) =
          r ^ 2 - (2 * Real.sqrt 2 / Real.sqrt 13) ^ 2 := by ring
        _ = r ^ 2 - 8 / 13 := by rw [h_bound_sq]
    rw [h_expand] at h_prod
    linarith

/-! ### 本問の主定理 -/

/-- 【第3問 (1) の解答】
10 ≤ N(r) ≤ 25 を満たす半径 r の必要十分条件。 -/
theorem problem_3_1_proof (r : ℝ) (hr : 0 ≤ r) :
    (4 ≤ 13 * r ^ 2 ∧ 13 * r ^ 2 ≤ 8) ↔
      (2 / Real.sqrt 13 ≤ r ∧ r ≤ 2 * Real.sqrt 2 / Real.sqrt 13) := by
  rw [four_le_thirteen_mul_sq_iff r hr]
  rw [thirteen_mul_sq_le_eight_iff r hr]

/-- 【第3問 (2) の解答】
L字型領域に含まれる対応格子点の集合の濃度は 12 である。 -/
theorem problem_3_2_proof :
    ∃ S : Finset (ℤ × ℤ), S.card = 12 := by
  let S : Finset (ℤ × ℤ) :=
    {(0, 0), (0, 1), (0, 2), (1, 1),
     (-2, 3), (-1, 2), (-1, 3), (0, 3),
     (1, 2), (2, 2), (2, 3), (3, 2)}
  use S
  decide

end MyLean.Exercises.«science-tokyo».«2019»
