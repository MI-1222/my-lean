import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MyLean.Common
import MyLean.Exercises.«science-tokyo».«2019».Statement

/-!
# 東京工業大学 2019年度 理系 第1問 (Proof)

三角形 OPQ および四面体 ABCD に関する不等式(ヴァイツェンベックの不等式)の証明。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

open Real

/-! ### 三角形に関する不等式の補題 -/

/-- 平方完成恒等式: 辺長の2乗和から 4√3 S を引いた差は2つの完全平方の和に一致する。 -/
lemma triangle_diff_eq_sq_sum (h s t : ℝ) :
    triangleEdgeSqSum h s t - 4 * Real.sqrt 3 * triangleArea h s t =
      2 * (h - (Real.sqrt 3 / 2) * (t - s)) ^ 2 + (1 / 2) * (t + s) ^ 2 := by
  dsimp [triangleEdgeSqSum, triangleArea]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h_sq : (h - (Real.sqrt 3 / 2) * (t - s)) ^ 2 =
      h ^ 2 - Real.sqrt 3 * (t - s) * h + (Real.sqrt 3 / 2) ^ 2 * (t - s) ^ 2 := by ring
  have h34 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, h3]
    norm_num
  rw [h34] at h_sq
  rw [h_sq]
  ring

/-- 等号成立時 (s = -h / √3 かつ t = h / √3) には、3辺の長さの2乗がすべて等しく正三角形となる。 -/
lemma triangle_equilateral_of_equality (h s t : ℝ)
    (hs : s = -h / Real.sqrt 3) (ht : t = h / Real.sqrt 3) :
    (h ^ 2 + s ^ 2 = h ^ 2 + t ^ 2) ∧ (h ^ 2 + t ^ 2 = (t - s) ^ 2) := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs_sq : s ^ 2 = h ^ 2 / 3 := by
    rw [hs]
    calc
      (-h / Real.sqrt 3) ^ 2 = (-h) ^ 2 / (Real.sqrt 3) ^ 2 := div_pow (-h) (Real.sqrt 3) 2
      _ = h ^ 2 / 3 := by rw [neg_sq, h3]
  have ht_sq : t ^ 2 = h ^ 2 / 3 := by
    rw [ht]
    calc
      (h / Real.sqrt 3) ^ 2 = h ^ 2 / (Real.sqrt 3) ^ 2 := div_pow h (Real.sqrt 3) 2
      _ = h ^ 2 / 3 := by rw [h3]
  have h_ts_sq : (t - s) ^ 2 = 4 * h ^ 2 / 3 := by
    rw [ht, hs]
    have h_sub : h / Real.sqrt 3 - -h / Real.sqrt 3 = 2 * h / Real.sqrt 3 := by ring
    rw [h_sub]
    calc
      (2 * h / Real.sqrt 3) ^ 2 = (2 * h) ^ 2 / (Real.sqrt 3) ^ 2 := div_pow (2 * h) (Real.sqrt 3) 2
      _ = 4 * h ^ 2 / 3 := by rw [mul_pow, h3]; norm_num
  constructor
  · rw [hs_sq, ht_sq]
  · rw [ht_sq, h_ts_sq]
    ring

/-! ### 本問の主定理 -/

/-- 【第1問 (1) の解答】
三角形 OPQ の各辺の2乗和と面積 S に関する不等式。 -/
theorem problem_1_1_proof (h s t : ℝ) (_hh : 0 < h) (_hst : s < t) :
    triangleEdgeSqSum h s t ≥ 4 * Real.sqrt 3 * triangleArea h s t := by
  have h_diff := triangle_diff_eq_sq_sum h s t
  have h1 : 0 ≤ 2 * (h - (Real.sqrt 3 / 2) * (t - s)) ^ 2 := by
    have : 0 ≤ (h - (Real.sqrt 3 / 2) * (t - s)) ^ 2 := sq_nonneg _
    linarith
  have h2 : 0 ≤ (1 / 2 : ℝ) * (t + s) ^ 2 := by
    have : 0 ≤ (t + s) ^ 2 := sq_nonneg _
    linarith
  linarith

/-- 【第1問 (1) 等号成立条件の解答】
等号成立の必要十分条件は s = - h / √3 かつ t = h / √3 である。 -/
theorem problem_1_1_equality_proof (h s t : ℝ) (_hh : 0 < h) (_hst : s < t) :
    triangleEdgeSqSum h s t = 4 * Real.sqrt 3 * triangleArea h s t ↔
      (s = -h / Real.sqrt 3 ∧ t = h / Real.sqrt 3) := by
  have h_diff := triangle_diff_eq_sq_sum h s t
  have hsqrt3_ne : Real.sqrt 3 ≠ 0 := by
    have : (0 : ℝ) < 3 := by norm_num
    exact (Real.sqrt_pos.mpr this).ne'
  constructor
  · intro heq
    have hzero : 2 * (h - (Real.sqrt 3 / 2) * (t - s)) ^ 2 + (1 / 2) * (t + s) ^ 2 = 0 := by
      linarith
    have hsq1 : 0 ≤ 2 * (h - (Real.sqrt 3 / 2) * (t - s)) ^ 2 := by
      have : 0 ≤ (h - (Real.sqrt 3 / 2) * (t - s)) ^ 2 := sq_nonneg _
      linarith
    have hsq2 : 0 ≤ (1 / 2 : ℝ) * (t + s) ^ 2 := by
      have : 0 ≤ (t + s) ^ 2 := sq_nonneg _
      linarith
    have h_term2 : (t + s) ^ 2 = 0 := by linarith
    have h_ts : t + s = 0 := sq_eq_zero_iff.mp h_term2
    have hs_eq : s = -t := by linarith
    have h_term1 : (h - (Real.sqrt 3 / 2) * (t - s)) ^ 2 = 0 := by linarith
    have h_h_eq : h - (Real.sqrt 3 / 2) * (t - s) = 0 := sq_eq_zero_iff.mp h_term1
    rw [hs_eq] at h_h_eq
    have ht_sub : t - (-t) = 2 * t := by ring
    rw [ht_sub] at h_h_eq
    have h_cancel : (Real.sqrt 3 / 2) * (2 * t) = Real.sqrt 3 * t := by ring
    rw [h_cancel] at h_h_eq
    have ht_val : t = h / Real.sqrt 3 := by
      calc
        t = (Real.sqrt 3 * t) / Real.sqrt 3 := by rw [mul_div_cancel_left₀ t hsqrt3_ne]
        _ = h / Real.sqrt 3 := by rw [← sub_eq_zero.mp h_h_eq]
    have hs_val : s = -h / Real.sqrt 3 := by
      calc
        s = - t := hs_eq
        _ = - (h / Real.sqrt 3) := by rw [ht_val]
        _ = -h / Real.sqrt 3 := by ring
    exact ⟨hs_val, ht_val⟩
  · rintro ⟨hs, ht⟩
    rw [hs, ht]
    have h_spec := triangle_diff_eq_sq_sum h (-h / Real.sqrt 3) (h / Real.sqrt 3)
    have h_inner : (Real.sqrt 3 / 2) * (h / Real.sqrt 3 - -h / Real.sqrt 3) = h := by
      have : h / Real.sqrt 3 - -h / Real.sqrt 3 = 2 * (h / Real.sqrt 3) := by ring
      rw [this]
      calc
        (Real.sqrt 3 / 2) * (2 * (h / Real.sqrt 3)) = Real.sqrt 3 * (h / Real.sqrt 3) := by ring
        _ = h := mul_div_cancel₀ h hsqrt3_ne
    have h_sum : h / Real.sqrt 3 + -h / Real.sqrt 3 = 0 := by ring
    rw [h_inner, h_sum] at h_spec
    have h_sub_zero : (h - h) ^ 2 = 0 := by ring
    have h_zero_sq : (0 : ℝ) ^ 2 = 0 := by ring
    rw [h_sub_zero, h_zero_sq] at h_spec
    linarith

/-- 【第1問 (2) の解答】
四面体の4つの面にヴァイツェンベックの不等式を適用して加算することにより、所要の不等式が得られる。 -/
theorem problem_1_2_proof (a b c l m n S_ABC S_DAB S_DBC S_DCA T : ℝ)
    (hT : T = S_ABC + S_DAB + S_DBC + S_DCA)
    (hABC : a ^ 2 + b ^ 2 + c ^ 2 ≥ 4 * Real.sqrt 3 * S_ABC)
    (hDAB : m ^ 2 + l ^ 2 + c ^ 2 ≥ 4 * Real.sqrt 3 * S_DAB)
    (hDBC : m ^ 2 + n ^ 2 + a ^ 2 ≥ 4 * Real.sqrt 3 * S_DBC)
    (hDCA : n ^ 2 + l ^ 2 + b ^ 2 ≥ 4 * Real.sqrt 3 * S_DCA) :
    a ^ 2 + b ^ 2 + c ^ 2 + l ^ 2 + m ^ 2 + n ^ 2 ≥ 2 * Real.sqrt 3 * T := by
  have h_sum : (a ^ 2 + b ^ 2 + c ^ 2) + (m ^ 2 + l ^ 2 + c ^ 2) +
      (m ^ 2 + n ^ 2 + a ^ 2) + (n ^ 2 + l ^ 2 + b ^ 2) ≥
      4 * Real.sqrt 3 * S_ABC + 4 * Real.sqrt 3 * S_DAB +
      4 * Real.sqrt 3 * S_DBC + 4 * Real.sqrt 3 * S_DCA := by linarith
  have h_lhs : (a ^ 2 + b ^ 2 + c ^ 2) + (m ^ 2 + l ^ 2 + c ^ 2) +
      (m ^ 2 + n ^ 2 + a ^ 2) + (n ^ 2 + l ^ 2 + b ^ 2) =
      2 * (a ^ 2 + b ^ 2 + c ^ 2 + l ^ 2 + m ^ 2 + n ^ 2) := by ring
  have h_rhs : 4 * Real.sqrt 3 * S_ABC + 4 * Real.sqrt 3 * S_DAB +
      4 * Real.sqrt 3 * S_DBC + 4 * Real.sqrt 3 * S_DCA =
      4 * Real.sqrt 3 * T := by
    rw [hT]
    ring
  rw [h_lhs, h_rhs] at h_sum
  linarith

end MyLean.Exercises.«science-tokyo».«2019»
