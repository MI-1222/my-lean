import Mathlib
import MyLean.Common
import MyLean.Exercises.«kyoto-university».«2006late».Statement

/-!
# 京都大学 2006年度後期 理系 第6問 (Proof)

$\tan 1^\circ$ は有理数か(背理法による証明)。
-/

namespace MyLean.Exercises.«kyoto-university».«2006late»

open Real

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

end MyLean.Exercises.«kyoto-university».«2006late»
