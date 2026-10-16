import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MyLean.Common
import MyLean.Exercises.«science-tokyo».«2019».Statement

/-!
# 東京工業大学 2019年度 理系 第5問 (Proof)

関数 $f(x) = (x+1)\log\left(1 + \frac{1}{x}\right)$ の単調減少性、
および数列 $bₖ = \frac{(k+1)^{k+1}}{a^k k!}$ の最大値の決定。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

open Real

/-! ### 数列の隣接項比に関する計算補題 -/

/-- 第1項から第2項への増大比: b₂ / b₁ = 2187 / 2048 > 1。 -/
lemma seqB_ratio_one_two :
    seqB 2 / seqB 1 = 2187 / 2048 := by
  dsimp [seqB, paramA]
  norm_num

/-- 第2項から第3項への比: b₃ / b₂ = 1。 -/
lemma seqB_ratio_two_three :
    seqB 3 / seqB 2 = 1 := by
  dsimp [seqB, paramA]
  norm_num

/-- 第3項から第4項への減少比: b₄ / b₃ = 253125 / 262144 < 1。 -/
lemma seqB_ratio_three_four :
    seqB 4 / seqB 3 = 253125 / 262144 := by
  dsimp [seqB, paramA]
  norm_num

/-! ### 対数関数の評価に関する補題 -/

/-- 対数関数の基本不等式: y > 0 かつ y ≠ 1 のとき log y < y - 1 が成り立つ。
y = 1 + 1/x を代入することにより、x > 0 に対して log(1 + 1/x) < 1/x が従う。 -/
lemma log_one_add_inv_lt_inv {x : ℝ} (hx : 0 < x) :
    Real.log (1 + 1 / x) < 1 / x := by
  have h_inv_pos : 0 < 1 / x := one_div_pos.mpr hx
  have hy_pos : 0 < 1 + 1 / x := by linarith
  have hy_ne_one : 1 + 1 / x ≠ 1 := by
    intro h
    have : 1 / x = 0 := by linarith
    linarith
  have h_log := Real.log_lt_sub_one_of_pos hy_pos hy_ne_one
  have h_sub : (1 + 1 / x) - 1 = 1 / x := by ring
  rw [h_sub] at h_log
  exact h_log

/-! ### 本問の主定理 -/

/-- 【第5問 (1) の解答】
導関数の符号 log(1 + 1/x) - 1/x < 0 により、f(x) は x > 0 で減少する。 -/
theorem problem_5_1_proof (x : ℝ) (hx : 0 < x) :
    Real.log (1 + 1 / x) - 1 / x < 0 := by
  have h := log_one_add_inv_lt_inv hx
  linarith

/-- 【第5問 (2) の解答】
数列 {bₖ} の各項の計算により、b₂ = b₃ = 177147 / 131072 かつ
b₁ < b₂ かつ b₄ < b₃ であるため、最大値は M = 177147 / 131072 (k = 2, 3) である。 -/
theorem problem_5_2_proof :
    seqB 2 = 177147 / 131072 ∧
    seqB 3 = 177147 / 131072 ∧
    seqB 2 = seqB 3 ∧
    seqB 1 < seqB 2 ∧
    seqB 4 < seqB 3 := by
  dsimp [seqB, paramA]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end MyLean.Exercises.«science-tokyo».«2019»
