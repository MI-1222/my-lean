import Mathlib
import MyLean.Common
import MyLean.Exercises.«kyoto-university».«2006late».exercise.Statement

/-!
# 演習・課題の解答 (Proof)

大学名: 京都大学
入試年度: 2006年度後期
対象科目: 数学(理系)

このモジュールでは、京都大学2006年度後期入試(理系)の各問題の形式証明を記述する。

-/

namespace MyLean.Exercises.«kyoto-university».«2006late».exercise

open Real
open Polynomial

/-!
## 第1問の証明
1次式 $A(x), B(x), C(x)$ に対して $\{A(x)\}^2 + \{B(x)\}^2 = \{C(x)\}^2$ が成り立つとき、
$A(x)$ と $B(x)$ はともに $C(x)$ の定数倍であることを示す。
-/

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

/-!
## 第6問の証明
$\tan 1^\circ$ は有理数ではない（背理法による証明）。
-/

/-! ### 有理数に関する基礎補題 -/

/-- 有理数同士の和は有理数である。 -/
lemma isRat_add {x y : ℝ} (hx : IsRat x) (hy : IsRat y) : IsRat (x + y) := by
  rcases hx with ⟨qx, rfl⟩
  rcases hy with ⟨qy, rfl⟩
  exact ⟨qx + qy, by push_cast; rfl⟩

/-- 有理数同士の差は有理数である。 -/
lemma isRat_sub {x y : ℝ} (hx : IsRat x) (hy : IsRat y) : IsRat (x - y) := by
  rcases hx with ⟨qx, rfl⟩
  rcases hy with ⟨qy, rfl⟩
  exact ⟨qx - qy, by push_cast; rfl⟩

/-- 有理数同士の積は有理数である。 -/
lemma isRat_mul {x y : ℝ} (hx : IsRat x) (hy : IsRat y) : IsRat (x * y) := by
  rcases hx with ⟨qx, rfl⟩
  rcases hy with ⟨qy, rfl⟩
  exact ⟨qx * qy, by push_cast; rfl⟩

/-- 有理数同士の商は有理数である。 -/
lemma isRat_div {x y : ℝ} (hx : IsRat x) (hy : IsRat y) : IsRat (x / y) := by
  rcases hx with ⟨qx, rfl⟩
  rcases hy with ⟨qy, rfl⟩
  exact ⟨qx / qy, by push_cast; rfl⟩

/-- 1 は有理数である。 -/
lemma isRat_one : IsRat 1 := ⟨1, by push_cast; rfl⟩

/-! ### 三角関数の定義域と加法定理に関する補題 -/

/-- 開区間 (0, π / 2) 内の実数は、π / 2 の奇数倍にならない。 -/
lemma ne_odd_pi_div_two {x : ℝ} (h_pos : 0 < x) (h_lt : x < π / 2) (k : ℤ) :
    x ≠ (2 * (k : ℝ) + 1) * π / 2 := by
  intro hk
  rw [mul_div_assoc] at hk
  have hpi2 : 0 < π / 2 := by linarith [Real.pi_pos]
  have h_low : 0 < (2 * (k : ℝ) + 1) * (π / 2) := by
    rw [← hk]
    exact h_pos
  have h_high : (2 * (k : ℝ) + 1) * (π / 2) < 1 * (π / 2) := by
    rw [← hk, one_mul]
    exact h_lt
  have h1 : 0 < 2 * (k : ℝ) + 1 := by
    nlinarith [h_low, hpi2]
  have h2 : 2 * (k : ℝ) + 1 < 1 := by
    nlinarith [h_high, hpi2]
  have hk_int1 : 0 < 2 * k + 1 := by
    exact_mod_cast h1
  have hk_int2 : 2 * k + 1 < 1 := by
    exact_mod_cast h2
  omega

/-- 両角が開区間 (0, π / 2) に属する場合の正接の加法定理である。 -/
lemma tan_add_of_Ioo {x y : ℝ} (hx1 : 0 < x) (hx2 : x < π / 2)
    (hy1 : 0 < y) (hy2 : y < π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  apply Real.tan_add'
  constructor
  · exact ne_odd_pi_div_two hx1 hx2
  · exact ne_odd_pi_div_two hy1 hy2

/-- 有理数となる正接の和角における正接も有理数となる。 -/
lemma isRat_tan_add {x y : ℝ} (hx1 : 0 < x) (hx2 : x < π / 2)
    (hy1 : 0 < y) (hy2 : y < π / 2)
    (hx : IsRat (tan x)) (hy : IsRat (tan y)) :
    IsRat (tan (x + y)) := by
  rw [tan_add_of_Ioo hx1 hx2 hy1 hy2]
  exact isRat_div (isRat_add hx hy) (isRat_sub isRat_one (isRat_mul hx hy))

/-- 【第6問の解答】tan 1° は無理数(有理数ではない)である。 -/
theorem problem_6_proof : ¬ IsRat (tan oneDeg) := by
  intro h1
  have hpi : 0 < π := Real.pi_pos
  have h_one_pos : 0 < oneDeg := by
    dsimp [oneDeg]
    linarith
  have h_one_lt : oneDeg < π / 2 := by
    dsimp [oneDeg]
    linarith
  -- 加法定理により順次生成する角度を定義する。
  let θ1 : ℝ := oneDeg
  let θ2 : ℝ := θ1 + θ1
  let θ3 : ℝ := θ2 + θ1
  let θ6 : ℝ := θ3 + θ3
  let θ12 : ℝ := θ6 + θ6
  let θ24 : ℝ := θ12 + θ12
  let θ30 : ℝ := θ24 + θ6
  let θ60 : ℝ := θ30 + θ30
  -- θ1 (1°) の正値性と有理数性。
  have hθ1_pos : 0 < θ1 := h_one_pos
  have hθ1_lt : θ1 < π / 2 := h_one_lt
  have hθ1_rat : IsRat (tan θ1) := h1
  -- θ2 (2°) の正値性と有理数性。
  have hθ2_pos : 0 < θ2 := by dsimp [θ2]; linarith
  have hθ2_lt : θ2 < π / 2 := by dsimp [θ2, θ1, oneDeg]; linarith
  have hθ2_rat : IsRat (tan θ2) :=
    isRat_tan_add hθ1_pos hθ1_lt hθ1_pos hθ1_lt hθ1_rat hθ1_rat
  -- θ3 (3°) の正値性と有理数性。
  have hθ3_pos : 0 < θ3 := by dsimp [θ3]; linarith
  have hθ3_lt : θ3 < π / 2 := by dsimp [θ3, θ2, θ1, oneDeg]; linarith
  have hθ3_rat : IsRat (tan θ3) :=
    isRat_tan_add hθ2_pos hθ2_lt hθ1_pos hθ1_lt hθ2_rat hθ1_rat
  -- θ6 (6°) の正値性と有理数性。
  have hθ6_pos : 0 < θ6 := by dsimp [θ6]; linarith
  have hθ6_lt : θ6 < π / 2 := by dsimp [θ6, θ3, θ2, θ1, oneDeg]; linarith
  have hθ6_rat : IsRat (tan θ6) :=
    isRat_tan_add hθ3_pos hθ3_lt hθ3_pos hθ3_lt hθ3_rat hθ3_rat
  -- θ12 (12°) の正値性と有理数性。
  have hθ12_pos : 0 < θ12 := by dsimp [θ12]; linarith
  have hθ12_lt : θ12 < π / 2 := by dsimp [θ12, θ6, θ3, θ2, θ1, oneDeg]; linarith
  have hθ12_rat : IsRat (tan θ12) :=
    isRat_tan_add hθ6_pos hθ6_lt hθ6_pos hθ6_lt hθ6_rat hθ6_rat
  -- θ24 (24°) の正値性と有理数性。
  have hθ24_pos : 0 < θ24 := by dsimp [θ24]; linarith
  have hθ24_lt : θ24 < π / 2 := by dsimp [θ24, θ12, θ6, θ3, θ2, θ1, oneDeg]; linarith
  have hθ24_rat : IsRat (tan θ24) :=
    isRat_tan_add hθ12_pos hθ12_lt hθ12_pos hθ12_lt hθ12_rat hθ12_rat
  -- θ30 (30°) の正値性と有理数性。
  have hθ30_pos : 0 < θ30 := by dsimp [θ30]; linarith
  have hθ30_lt : θ30 < π / 2 := by dsimp [θ30, θ24, θ12, θ6, θ3, θ2, θ1, oneDeg]; linarith
  have hθ30_rat : IsRat (tan θ30) :=
    isRat_tan_add hθ24_pos hθ24_lt hθ6_pos hθ6_lt hθ24_rat hθ6_rat
  -- θ60 (60°) の正値性と有理数性。
  have hθ60_pos : 0 < θ60 := by dsimp [θ60]; linarith
  have hθ60_lt : θ60 < π / 2 := by dsimp [θ60, θ30, θ24, θ12, θ6, θ3, θ2, θ1, oneDeg]; linarith
  have hθ60_rat : IsRat (tan θ60) :=
    isRat_tan_add hθ30_pos hθ30_lt hθ30_pos hθ30_lt hθ30_rat hθ30_rat
  -- θ60 が π / 3 に一致することを示す。
  have hθ60_eq : θ60 = π / 3 := by
    dsimp [θ60, θ30, θ24, θ12, θ6, θ3, θ2, θ1, oneDeg]
    ring
  -- tan (π / 3) = √3 の無理数性により矛盾を導く。
  rw [hθ60_eq] at hθ60_rat
  rw [Real.tan_pi_div_three] at hθ60_rat
  have h_irr : Irrational √3 := Nat.Prime.irrational_sqrt (by norm_num)
  rcases hθ60_rat with ⟨q, hq⟩
  apply h_irr
  use q
  exact hq.symm

end MyLean.Exercises.«kyoto-university».«2006late».exercise
