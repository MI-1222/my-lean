import Mathlib
import MyLean.Common
import MyLean.Exercises.«kyoto-university».«2006late».Statement

/-!
# 京都大学 2006年度後期 理系 第1問 (Proof)

1次式 $A(x), B(x), C(x)$ に対して $\{A(x)\}^2 + \{B(x)\}^2 = \{C(x)\}^2$ が成り立つとき、
$A(x)$ と $B(x)$ はともに $C(x)$ の定数倍であることを示す。
-/

namespace MyLean.Exercises.«kyoto-university».«2006late»

open Polynomial

/-- 次数が 1 の多項式は $C(P_0) + C(P_1) * X$ の形に展開できる。 -/
lemma eq_C_add_C_mul_X_of_natDegree_eq_one (P : ℝ[X]) (hP : P.natDegree = 1) :
    P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := by
  ext n
  match n with
  | 0 => simp [coeff_C]
  | 1 => simp [coeff_C]
  | n + 2 =>
    have hn : P.natDegree < n + 2 := by rw [hP]; omega
    rw [coeff_eq_zero_of_natDegree_lt hn]
    simp

/-- 【第1問の解答】
1次式 A, B, C が A^2 + B^2 = C^2 を満たすとき、A と B はともに C の実数定数倍である。 -/
theorem problem_1_proof (A B C : ℝ[X])
    (hA : IsDegreeOne A) (hB : IsDegreeOne B) (hC : IsDegreeOne C)
    (h_eq : A ^ 2 + B ^ 2 = C ^ 2) :
    (∃ k₁ : ℝ, A = Polynomial.C k₁ * C) ∧ (∃ k₂ : ℝ, B = Polynomial.C k₂ * C) := by
  dsimp [IsDegreeOne] at hA hB hC
  set a0 := A.coeff 0
  set a1 := A.coeff 1
  set b0 := B.coeff 0
  set b1 := B.coeff 1
  set c0 := C.coeff 0
  set c1 := C.coeff 1
  -- 1次多項式を係数により標準展開する。
  have hA_dec : A = Polynomial.C a0 + Polynomial.C a1 * Polynomial.X :=
    eq_C_add_C_mul_X_of_natDegree_eq_one A hA
  have hB_dec : B = Polynomial.C b0 + Polynomial.C b1 * Polynomial.X :=
    eq_C_add_C_mul_X_of_natDegree_eq_one B hB
  have hC_dec : C = Polynomial.C c0 + Polynomial.C c1 * Polynomial.X :=
    eq_C_add_C_mul_X_of_natDegree_eq_one C hC
  -- x = 0, 1, -1 での評価値を計算する。
  have h_eval0 : eval 0 A ^ 2 + eval 0 B ^ 2 = eval 0 C ^ 2 := by
    have h := congr_arg (eval 0) h_eq
    simp only [eval_add, eval_pow] at h
    exact h
  have h_eval1 : eval 1 A ^ 2 + eval 1 B ^ 2 = eval 1 C ^ 2 := by
    have h := congr_arg (eval 1) h_eq
    simp only [eval_add, eval_pow] at h
    exact h
  have h_evalm1 : eval (-1) A ^ 2 + eval (-1) B ^ 2 = eval (-1) C ^ 2 := by
    have h := congr_arg (eval (-1)) h_eq
    simp only [eval_add, eval_pow] at h
    exact h
  rw [hA_dec, hB_dec, hC_dec] at h_eval0 h_eval1 h_evalm1
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero,
             mul_one, mul_neg_one] at h_eval0 h_eval1 h_evalm1
  -- 係数の 2 次関係式を導く。
  have h0 : a0 ^ 2 + b0 ^ 2 = c0 ^ 2 := h_eval0
  have h_sq : a1 ^ 2 + b1 ^ 2 = c1 ^ 2 := by linarith
  have h_cross : a0 * a1 + b0 * b1 = c0 * c1 := by linarith
  -- Lagrange の恒等式を用いて比例関係 c1 * a0 = c0 * a1 を導出する。
  have hA_prop : c1 * a0 = c0 * a1 := by
    have hA : (c1 * a0 - c0 * a1) ^ 2 = 0 := by
      calc
        (c1 * a0 - c0 * a1) ^ 2 =
          (c1 * c0 - a1 * a0) ^ 2 - (c1 ^ 2 - a1 ^ 2) * (c0 ^ 2 - a0 ^ 2) := by ring
        _ = (b1 * b0) ^ 2 - (b1 ^ 2) * (b0 ^ 2) := by
          have hb1 : c1 ^ 2 - a1 ^ 2 = b1 ^ 2 := by linarith
          have hb0 : c0 ^ 2 - a0 ^ 2 = b0 ^ 2 := by linarith
          have hbc : c1 * c0 - a1 * a0 = b1 * b0 := by linarith
          rw [hb1, hb0, hbc]
        _ = 0 := by ring
    have hA_sub : c1 * a0 - c0 * a1 = 0 := sq_eq_zero_iff.mp hA
    linarith
  -- 同様に c1 * b0 = c0 * b1 を導出する。
  have hB_prop : c1 * b0 = c0 * b1 := by
    have hB : (c1 * b0 - c0 * b1) ^ 2 = 0 := by
      calc
        (c1 * b0 - c0 * b1) ^ 2 =
          (c1 * c0 - b1 * b0) ^ 2 - (c1 ^ 2 - b1 ^ 2) * (c0 ^ 2 - b0 ^ 2) := by ring
        _ = (a1 * a0) ^ 2 - (a1 ^ 2) * (a0 ^ 2) := by
          have ha1 : c1 ^ 2 - b1 ^ 2 = a1 ^ 2 := by linarith
          have ha0 : c0 ^ 2 - b0 ^ 2 = a0 ^ 2 := by linarith
          have hac : c1 * c0 - b1 * b0 = a1 * a0 := by linarith
          rw [ha1, ha0, hac]
        _ = 0 := by ring
    have hB_sub : c1 * b0 - c0 * b1 = 0 := sq_eq_zero_iff.mp hB
    linarith
  -- C は 1 次式であるため最高次係数 c1 は 0 でない。
  have hc1_ne : c1 ≠ 0 := by
    intro hc0
    have h_ne : C ≠ 0 := by
      intro hC0
      rw [hC0, natDegree_zero] at hC
      contradiction
    have h_lc := leadingCoeff_ne_zero.mpr h_ne
    rw [leadingCoeff, hC] at h_lc
    exact h_lc hc0
  -- 定数倍 k1 = a1 / c1 および k2 = b1 / c1 を構成する。
  have ha1_eq : a1 = (a1 / c1) * c1 := by
    rw [div_mul_cancel₀ a1 hc1_ne]
  have ha0_eq : a0 = (a1 / c1) * c0 := by
    calc
      a0 = (c1 * a0) / c1 := by rw [mul_div_cancel_left₀ a0 hc1_ne]
      _ = (c0 * a1) / c1 := by rw [hA_prop]
      _ = (a1 / c1) * c0 := by ring
  have hb1_eq : b1 = (b1 / c1) * c1 := by
    rw [div_mul_cancel₀ b1 hc1_ne]
  have hb0_eq : b0 = (b1 / c1) * c0 := by
    calc
      b0 = (c1 * b0) / c1 := by rw [mul_div_cancel_left₀ b0 hc1_ne]
      _ = (c0 * b1) / c1 := by rw [hB_prop]
      _ = (b1 / c1) * c0 := by ring
  have hA_eq : A = Polynomial.C (a1 / c1) * C := by
    rw [hA_dec, hC_dec]
    have h1 : Polynomial.C a0 = Polynomial.C (a1 / c1) * Polynomial.C c0 := by
      rw [congr_arg Polynomial.C ha0_eq, map_mul]
    have h2 : Polynomial.C a1 * Polynomial.X =
        Polynomial.C (a1 / c1) * (Polynomial.C c1 * Polynomial.X) := by
      have h : Polynomial.C a1 = Polynomial.C (a1 / c1) * Polynomial.C c1 := by
        rw [congr_arg Polynomial.C ha1_eq, map_mul]
      rw [h, mul_assoc]
    rw [h1, h2, ← mul_add]
  have hB_eq : B = Polynomial.C (b1 / c1) * C := by
    rw [hB_dec, hC_dec]
    have h1 : Polynomial.C b0 = Polynomial.C (b1 / c1) * Polynomial.C c0 := by
      rw [congr_arg Polynomial.C hb0_eq, map_mul]
    have h2 : Polynomial.C b1 * Polynomial.X =
        Polynomial.C (b1 / c1) * (Polynomial.C c1 * Polynomial.X) := by
      have h : Polynomial.C b1 = Polynomial.C (b1 / c1) * Polynomial.C c1 := by
        rw [congr_arg Polynomial.C hb1_eq, map_mul]
      rw [h, mul_assoc]
    rw [h1, h2, ← mul_add]
  exact ⟨⟨a1 / c1, hA_eq⟩, ⟨b1 / c1, hB_eq⟩⟩

end MyLean.Exercises.«kyoto-university».«2006late»
