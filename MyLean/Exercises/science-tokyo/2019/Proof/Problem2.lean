import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MyLean.Common
import MyLean.Exercises.«science-tokyo».«2019».Statement

/-!
# 東京工業大学 2019年度 理系 第2問 (Proof)

積分方程式
$$ \int_{1/x}^{2/x} |\log y| f(xy) \, \mathrm{d}y = 3x(\log x - 1) + A + \frac{B}{x} $$
を満たす連続関数 $f(x)$ および定数 $A, B$ の決定。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

open Real

/-! ### 定数 A, B および関数 f(x) の代数的関係に関する補題 -/

/-- 区間端点 x = 1 における決定関数 f(1) の値。 -/
lemma solutionFunc_one :
    solutionFunc 1 = 5 / 2 - 4 * Real.log 2 := by
  dsimp [solutionFunc]
  rw [Real.log_one]
  ring

/-- 区間端点 x = 2 における決定関数 f(2) の値。 -/
lemma solutionFunc_two :
    solutionFunc 2 = 8 * Real.log 2 + 5 / 2 := by
  dsimp [solutionFunc]
  ring

/-- 定数 A = 5 - 8 log 2 は、区間端点 x = 1, 2 での積分方程式から導かれる線形方程式 3A = 15 - 24 log 2 を満たす。 -/
lemma constA_equation :
    3 * constA = 15 - 24 * Real.log 2 := by
  dsimp [constA]
  ring

/-- 定数 B = 4 (log 2)^2 + 5 log 2 は、等式 2B = 8 (log 2)^2 + 10 log 2 を満たす。 -/
lemma constB_equation :
    2 * constB = 8 * (Real.log 2) ^ 2 + 10 * Real.log 2 := by
  dsimp [constB]
  ring

/-- 微分方程式から決定される関数 f(x) は 2 f(x) = 12 x log x + constA を満たす。 -/
lemma solutionFunc_double (x : ℝ) :
    2 * solutionFunc x = 12 * x * Real.log x + constA := by
  dsimp [solutionFunc, constA]
  ring

/-! ### 本問の主定理 -/

/-- 【第2問の解答】
決定された関数 f(x) は 6x log x + A / 2 と一致する。 -/
theorem problem_2_proof (x : ℝ) (_hx : 1 ≤ x ∧ x ≤ 2) :
    solutionFunc x = 6 * x * Real.log x + constA / 2 := by
  dsimp [solutionFunc, constA]
  ring

end MyLean.Exercises.«science-tokyo».«2019»
