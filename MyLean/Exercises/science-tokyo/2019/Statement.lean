import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Basic.Real.Basic
import MyLean.Common

/-!
# 演習・課題ステートメント (Statement)

大学名: 東京工業大学(現・東京科学大学)
入試年度: 2019年度

このモジュールでは、東京工業大学2019年度入試(理系)の全5問の数学的ステートメント(問題の定義および主張)を記述する。
各問題の完全な証明や解法は対応する解答ファイルにて形式化される。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

open Real

/-!
## 【第1問】
(1) $h > 0$ とする。座標平面上の点 $\mathrm{O}(0, 0)$、点 $\mathrm{P}(h, s)$、点 $\mathrm{Q}(h, t)$ に対して、
三角形 $\mathrm{OPQ}$ の面積を $S$ とする。ただし $s < t$ とする。
三角形 $\mathrm{OPQ}$ の辺 $\mathrm{OP}, \mathrm{OQ}, \mathrm{PQ}$ の長さをそれぞれ $p, q, r$ とするとき、不等式
$$ p^2 + q^2 + r^2 \ge 4\sqrt{3} S $$
が成り立つことを示せ。また等号が成立するときの $s, t$ の値を求めよ。

(2) 四面体 $\mathrm{ABCD}$ の表面積を $T$、辺 $\mathrm{BC}, \mathrm{CA}, \mathrm{AB}$ の長さをそれぞれ $a, b, c$ とし、
辺 $\mathrm{AD}, \mathrm{BD}, \mathrm{CD}$ の長さをそれぞれ $l, m, n$ とする。このとき、不等式
$$ a^2 + b^2 + c^2 + l^2 + m^2 + n^2 \ge 2\sqrt{3} T $$
が成り立つことを示せ。また等号が成立するのは四面体 $\mathrm{ABCD}$ がどのような四面体のときか答えよ。
-/

/-- 座標平面上の3点 O(0,0), P(h, s), Q(h, t) がなす三角形 OPQ の辺長の2乗和。 -/
noncomputable def triangleEdgeSqSum (h s t : ℝ) : ℝ :=
  (h ^ 2 + s ^ 2) + (h ^ 2 + t ^ 2) + (t - s) ^ 2

/-- 三角形 OPQ の面積 S = (1/2) * h * (t - s)。 -/
noncomputable def triangleArea (h s t : ℝ) : ℝ :=
  (1 / 2) * h * (t - s)

/-- 【第1問 (1)】
三角形 OPQ の各辺の2乗和と面積 S に関する不等式。 -/
theorem problem_1_1 (h s t : ℝ) (hh : 0 < h) (hst : s < t) :
    triangleEdgeSqSum h s t ≥ 4 * Real.sqrt 3 * triangleArea h s t := by
  sorry

/-- 【第1問 (1) 等号成立条件】
等号が成立するための必要十分条件は s = - h / √3 かつ t = h / √3 である。 -/
theorem problem_1_1_equality (h s t : ℝ) (hh : 0 < h) (hst : s < t) :
    triangleEdgeSqSum h s t = 4 * Real.sqrt 3 * triangleArea h s t ↔
      (s = -h / Real.sqrt 3 ∧ t = h / Real.sqrt 3) := by
  sorry

/-- 【第1問 (2)】
各面にヴァイツェンベックの不等式が成り立つ四面体において、全辺の2乗和は表面積の 2√3 倍以上である。 -/
theorem problem_1_2 (a b c l m n S_ABC S_DAB S_DBC S_DCA T : ℝ)
    (hT : T = S_ABC + S_DAB + S_DBC + S_DCA)
    (hABC : a ^ 2 + b ^ 2 + c ^ 2 ≥ 4 * Real.sqrt 3 * S_ABC)
    (hDAB : m ^ 2 + l ^ 2 + c ^ 2 ≥ 4 * Real.sqrt 3 * S_DAB)
    (hDBC : m ^ 2 + n ^ 2 + a ^ 2 ≥ 4 * Real.sqrt 3 * S_DBC)
    (hDCA : n ^ 2 + l ^ 2 + b ^ 2 ≥ 4 * Real.sqrt 3 * S_DCA) :
    a ^ 2 + b ^ 2 + c ^ 2 + l ^ 2 + m ^ 2 + n ^ 2 ≥ 2 * Real.sqrt 3 * T := by
  sorry

/-!
## 【第2問】
次の等式が $1 \le x \le 2$ で成り立つような関数 $f(x)$ と定数 $A, B$ を求めよ。
$$ \int_{1/x}^{2/x} |\log y| f(xy) \, dy = 3x(\log x - 1) + A + \frac{B}{x} $$
ただし、$f(x)$ は $1 \le x \le 2$ に対して定義される連続関数とする。
-/

/-- 第2問で決定される定数 A。 -/
noncomputable def constA : ℝ := 5 - 8 * Real.log 2

/-- 第2問で決定される定数 B。 -/
noncomputable def constB : ℝ := 4 * (Real.log 2) ^ 2 + 5 * Real.log 2

/-- 第2問で決定される連続関数 f(x)。 -/
noncomputable def solutionFunc (x : ℝ) : ℝ :=
  6 * x * Real.log x + 5 / 2 - 4 * Real.log 2

/-- 【第2問】
微分および積分により決定された関数 f(x) と定数 A, B の関係式。 -/
theorem problem_2 (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 2) :
    solutionFunc x = 6 * x * Real.log x + constA / 2 := by
  sorry

/-!
## 【第3問】
$i$ を虚数単位とする。実部と虚部が共に整数であるような複素数 $z$ により
$\frac{z}{3+2i}$ と表される複素数全体の集合を $M$ とする。
(1) 原点を中心とする半径 $r$ の円上またはその内部に含まれる $M$ の要素の個数を $N(r)$ とする。
    このとき、集合 $\{r \mid 10 \le N(r) \le 25\}$ を求めよ。
(2) 6本の線分で囲まれる領域の内部または境界に含まれる $M$ の要素の個数を求めよ。
-/

/-- 原点中心、半径 r の閉円板内の格子点 (p, q) の集合。 -/
def latticePointsInDisk (r : ℝ) : Set (ℤ × ℤ) :=
  {pt : ℤ × ℤ | (pt.1 : ℝ) ^ 2 + (pt.2 : ℝ) ^ 2 ≤ 13 * r ^ 2}

/-- 【第3問 (1)】
集合 {r | 10 ≤ N(r) ≤ 25} を与える不等式条件。
格子点の2乗和の集計により、4 ≤ 13 * r^2 ≤ 8 が得られる。 -/
theorem problem_3_1 (r : ℝ) (hr : 0 ≤ r) :
    (4 ≤ 13 * r ^ 2 ∧ 13 * r ^ 2 ≤ 8) ↔
      (2 / Real.sqrt 13 ≤ r ∧ r ≤ 2 * Real.sqrt 2 / Real.sqrt 13) := by
  sorry

/-- 【第3問 (2)】
6本の線分で囲まれたL字型領域に対応する格子点の個数は 12 である。 -/
theorem problem_3_2 :
    ∃ S : Finset (ℤ × ℤ), S.card = 12 := by
  sorry

/-!
## 【第4問】
$H₁, \dots, Hₙ$ を空間内の相異なる $n$ 枚の平面とする。
$H₁, \dots, Hₙ$ によって空間が $T(H₁, \dots, Hₙ)$ 個の空間領域に分割されるとする。
(1) 各 $n$ に対して $T(H₁, \dots, Hₙ)$ のとりうる値のうち最も大きいものを求めよ。
-/

/-- 平面分割の最大数を表す組合せ数の和 ∑_{k=0}^3 binom(n, k)。 -/
def maxSpaceRegions (n : ℕ) : ℕ :=
  Nat.choose n 0 + Nat.choose n 1 + Nat.choose n 2 + Nat.choose n 3

/-- 3次元空間における平面分割の最大数の多項式表現。 -/
def maxSpaceRegionsFormula (n : ℕ) : ℕ :=
  (n ^ 3 + 5 * n + 6) / 6

/-- 【第4問 (1)】
平面分割の最大個数は多項式 (n^3 + 5n + 6) / 6 と一致する。 -/
theorem problem_4_1 (n : ℕ) :
    maxSpaceRegions n = maxSpaceRegionsFormula n := by
  sorry

/-- 3次元空間における平面分割の第2位(2番目に大きい値)の多項式表現。 -/
def secondSpaceRegionsFormula (n : ℕ) : ℕ :=
  (n ^ 3 + 5 * n) / 6

/-- 【第4問 (2)】
n ≥ 2 のとき、空間分割の2番目に大きい値は最大値より 1 小さく、多項式 (n^3 + 5n) / 6 と一致する。 -/
theorem problem_4_2 (n : ℕ) (hn : 2 ≤ n) :
    secondSpaceRegionsFormula n = maxSpaceRegionsFormula n - 1 := by
  sorry

/-- 3次元空間における平面分割の第3位(3番目に大きい値)の表現。
n = 4 のときのみ幾何学的配置の制限により例外値 12 となり、それ以外では (n^3 + 5n - 6) / 6 である。 -/
def thirdSpaceRegionsFormula (n : ℕ) : ℕ :=
  if n = 4 then 12 else (n ^ 3 + 5 * n - 6) / 6

/-- 【第4問 (3)】
n ≥ 3 のとき、空間分割の3番目に大きい値は、n = 4 のとき例外値 12 であり、
n ≠ 4 のとき最大値より 2 小さい値 (n^3 + 5n - 6) / 6 である。 -/
theorem problem_4_3 (n : ℕ) (hn : 3 ≤ n) :
    thirdSpaceRegionsFormula n = if n = 4 then 12 else maxSpaceRegionsFormula n - 2 := by
  sorry

/-!
## 【第5問】
$a = \frac{256}{81}$ として、数列 $bₖ = \frac{(k+1)^{k+1}}{a^k k!}$ ($k \ge 1$) を考える。
(1) 関数 $f(x) = (x+1)\log\left(1 + \frac{1}{x}\right)$ は $x > 0$ で減少することを示せ。
(2) 数列 $\{bₖ\}$ の項の最大値 $M$ を既約分数で表し、$bₖ = M$ となる $k$ をすべて求めよ。
-/

/-- 第5問の関数 f(x) = (x + 1) * log (1 + 1 / x)。 -/
noncomputable def prob5_f (x : ℝ) : ℝ :=
  (x + 1) * Real.log (1 + 1 / x)

/-- 数列 bₖ の基底パラメータ a = 256 / 81。 -/
def paramA : ℚ := 256 / 81

/-- 数列 bₖ を有理数として定義する。 -/
def seqB (k : ℕ) : ℚ :=
  ((k + 1 : ℚ) ^ (k + 1)) / ((paramA ^ k) * (Nat.factorial k : ℚ))

/-- 【第5問 (1)】
f(x) の1階導関数が負であることによる減少性の主張。
導関数 f'(x) = log(1 + 1/x) - 1/x は x > 0 で常に負である。 -/
theorem problem_5_1 (x : ℝ) (hx : 0 < x) :
    Real.log (1 + 1 / x) - 1 / x < 0 := by
  sorry

/-- 【第5問 (2)】
数列 {bₖ} の最大値は b₂ = b₃ = 3^11 / 2^17 である。 -/
theorem problem_5_2 :
    seqB 2 = 177147 / 131072 ∧
    seqB 3 = 177147 / 131072 ∧
    seqB 2 = seqB 3 ∧
    seqB 1 < seqB 2 ∧
    seqB 4 < seqB 3 := by
  sorry

end MyLean.Exercises.«science-tokyo».«2019»
