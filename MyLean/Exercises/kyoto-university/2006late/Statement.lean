import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# 演習・課題ステートメント (Statement)

大学名: 京都大学
入試年度: 2006年度後期
対象科目: 数学(理系)

このモジュールでは、京都大学2006年度後期入試(理系）の全6問の数学的ステートメント(問題の定義および主張)を記述する。
各問題の完全な証明や解法は対応する解答ファイルにて形式化される。
-/

namespace MyLean.Exercises.«kyoto-university».«2006late»

open Real
open Polynomial

/-!
## 【第1問】
1次式 $A(x), B(x), C(x)$ に対して $\{A(x)\}^2 + \{B(x)\}^2 = \{C(x)\}^2$ が成り立つとする。
このとき $A(x)$ と $B(x)$ はともに $C(x)$ の定数倍であることを示せ。
-/

/-- 実数係数1変数多項式が1次式(次数が1)であることを表す述語。 -/
def IsDegreeOne (P : ℝ[X]) : Prop := P.natDegree = 1

/-- 【第1問】
1次式 A, B, C が A^2 + B^2 = C^2 を満たすとき、A と B はともに C の実数定数倍である。 -/
theorem problem_1 (A B C : ℝ[X])
    (hA : IsDegreeOne A) (hB : IsDegreeOne B) (hC : IsDegreeOne C)
    (h_eq : A ^ 2 + B ^ 2 = C ^ 2) :
    (∃ k₁ : ℝ, A = Polynomial.C k₁ * C) ∧ (∃ k₂ : ℝ, B = Polynomial.C k₂ * C) := by
  sorry

/-!
## 【第2問】
$a$ を実数として、行列 $A = \begin{pmatrix} a & 1-a \\ 1-a & a \end{pmatrix}$ と定める。
$\begin{pmatrix} x_0 \\ y_0 \end{pmatrix} = \begin{pmatrix} 1 \\ 0 \end{pmatrix}$ とし、
$\begin{pmatrix} x_n \\ y_n \end{pmatrix} = A \begin{pmatrix} x_{n-1} \\ y_{n-1} \end{pmatrix}$
($n=1,2,\dots$) で数列 $\{x_n\}, \{y_n\}$ を定める。
数列 $\{x_n\}$ が収束するための $a$ の必要十分条件を求めよ。
-/

/-- 漸化式の1ステップの行列演算を表す関数。 -/
def step2 (a : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (a * v.1 + (1 - a) * v.2, (1 - a) * v.1 + a * v.2)

/-- ベクトル列 $(x_n, y_n)$ を定める数列。 -/
def vecSeq2 (a : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => step2 a (vecSeq2 a n)

/-- 数列 $\{x_n\}$ を表す関数。 -/
def xSeq2 (a : ℝ) (n : ℕ) : ℝ := (vecSeq2 a n).1

/-- 【第2問】
数列 $\{x_n\}$ が収束するための実数 $a$ の必要十分条件は $0 < a \le 1$ である。 -/
theorem problem_2 (a : ℝ) :
    (∃ L : ℝ, Filter.Tendsto (xSeq2 a) Filter.atTop (nhds L)) ↔ (0 < a ∧ a ≤ 1) := by
  sorry

/-!
## 【第3問】
さいころを $n$ 個同時に投げるとき、出た目の数の和が $n+3$ になる確率を求めよ。
-/

/-- サイコロ $n$ 個の出目の和が $n+3$ になる確率を求める問題の解。 -/
def problem_3_prob (n : ℕ) : ℚ :=
  (n * (n + 1) * (n + 2) : ℚ) / (6 ^ (n + 1) : ℚ)

/-- 【第3問】
出目の和が $n+3$ となる非負整数の組の組合せ数に関する命題。
サイコロの目を $X_i \in \{1, \dots, 6\}$ とし $Y_i = X_i - 1$ とおくとき、
$\sum_{i=1}^n Y_i = 3$ を満たす非負整数解の個数は $\binom{n+2}{3}$ である。 -/
theorem problem_3_count (n : ℕ) (hn : 1 ≤ n) :
    Nat.choose (n + 2) 3 = (n * (n + 1) * (n + 2)) / 6 := by
  sorry

/-!
## 【第4問】
平面上の点 $\mathrm{O}$ を中心とし半径 $1$ の円周上に相異なる3点 $\mathrm{A}, \mathrm{B}, \mathrm{C}$ がある。
$\triangle\mathrm{ABC}$ の内接円の半径 $r$ は $1/2$ 以下であることを示せ。
-/

/-- 【第4問】
外心を $O$、内心を $I$、外接円半径を $R$、内接円半径を $r$ とするとき、
オイラーの定理 $OI^2 = R(R - 2r)$ が成り立つ。
外接円半径 $R = 1$ のとき、内接円半径 $r$ は $1/2$ 以下である。 -/
theorem problem_4 (r : ℝ) (hr : 0 < r)
    (h_euler : ∃ d : ℝ, 0 ≤ d ∧ d ^ 2 = 1 * (1 - 2 * r)) :
    r ≤ 1 / 2 := by
  sorry

/-!
## 【第5問】
原点 $\mathrm{O}$ と点 $\mathrm{P}(R, 0, H)$ を結ぶ線分を $z$ 軸のまわりに回転させてできる円錐容器に水を満たし、
原点からの水面の高さが $h$ のとき単位時間あたりの排水量が $\sqrt{h}$ となるように排水する。
すべての水を排出するのに要する時間を求めよ。
-/

/-- 【第5問】
高さ $h$ における円錐容器の水平断面積は $S(h) = \pi (R h / H)^2$ である。
排水微分方程式 $dt = (S(h) / \sqrt{h}) dh$ を $0$ から $H$ まで積分することにより、
全排水所要時間 $T = \frac{2}{5} \pi R^2 \sqrt{H}$ が導かれる。 -/
theorem problem_5 (R H : ℝ) (hR : 0 < R) (hH : 0 < H) :
    ∫ h in (0 : ℝ)..H, (π * (R / H * h) ^ 2 / Real.sqrt h) =
      (2 / 5) * π * R ^ 2 * Real.sqrt H := by
  sorry

/-!
## 【第6問】
$\tan 1^{\circ}$ は有理数か(有理数ではない)。
-/

/-- 実数が有理数であることを表す述語。 -/
def IsRat (x : ℝ) : Prop := ∃ q : ℚ, x = (q : ℝ)

/-- 度数法の 1 度をラジアン単位で表した定数。 -/
noncomputable def oneDeg : ℝ := π / 180

/-- 【第6問】
$\tan 1^{\circ}$ は有理数か(有理数ではない)。 -/
theorem problem_6 : ¬ IsRat (tan oneDeg) := by
  sorry

end MyLean.Exercises.«kyoto-university».«2006late»
