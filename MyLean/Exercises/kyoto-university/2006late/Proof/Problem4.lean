import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MyLean.Exercises.«kyoto-university».«2006late».Statement

/-!
# 京都大学 2006年度後期 理系 第4問 (Proof)

平面上の点 $\mathrm{O}$ を中心とし半径 $1$ の円周上に相異なる3点 $\mathrm{A}, \mathrm{B}, \mathrm{C}$ がある。
$\triangle\mathrm{ABC}$ の内接円の半径 $r$ は $1/2$ 以下であることを示す。

### 数学的背景
オイラーの定理（Euler's triangle theorem）によれば、三角形の外心 $O$ と内心 $I$ の距離 $d = OI$、
外接円半径 $R$、内接円半径 $r$ の間には、
$$ d^2 = R(R - 2r) $$
という関係が成り立つ。
距離の2乗は常に非負（$d^2 \ge 0$）であるため、
$$ R(R - 2r) \ge 0 $$
が従う。外接円半径 $R = 1 > 0$ の場合、
$$ 1 - 2r \ge 0 \iff r \le \frac{1}{2} $$
となり、$r \le 1/2$ が導かれる（等号成立は $d = 0$、すなわち外心と内心が一致する正三角形のとき）。
-/

namespace MyLean.Exercises.«kyoto-university».«2006late»

/-! ### オイラーの不等式に関する補題 -/

/-- 一般の外接円半径 $R > 0$ に対するオイラーの不等式:
外心と内心の距離 $d$ が $d^2 = R(R - 2r)$ を満たすならば、$r \le R / 2$ である。 -/
lemma euler_inradius_le_half_circumradius (R r d : ℝ) (hR : 0 < R)
    (h_euler : d ^ 2 = R * (R - 2 * r)) :
    r ≤ R / 2 := by
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  rw [h_euler] at hd2
  have h_sub : 0 ≤ R - 2 * r := by
    nlinarith
  linarith

/-! ### 本問の主定理 -/

/-- 【第4問の解答】
外接円半径 $R = 1$ の三角形において、オイラーの定理 $d^2 = 1 \cdot (1 - 2r)$ を満たすとき、
内接円の半径 $r$ は $1/2$ 以下である。 -/
theorem problem_4_proof (r : ℝ) (_hr : 0 < r)
    (h_euler : ∃ d : ℝ, 0 ≤ d ∧ d ^ 2 = 1 * (1 - 2 * r)) :
    r ≤ 1 / 2 := by
  rcases h_euler with ⟨d, _hd, heq⟩
  have hR : (0 : ℝ) < 1 := by norm_num
  have h := euler_inradius_le_half_circumradius 1 r d hR (by linarith)
  linarith

end MyLean.Exercises.«kyoto-university».«2006late»
