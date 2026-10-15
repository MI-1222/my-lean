import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MyLean.Exercises.«kyoto-university».«2006late».Statement

/-!
# 京都大学 2006年度後期 理系 第3問 (Proof)

さいころを $n$ 個同時に投げるとき、出た目の数の和が $n+3$ になる確率を求める。
出目を $X_i \in \{1, \dots, 6\}$ とし、$Y_i = X_i - 1$ とおくとき、
$\sum_{i=1}^n Y_i = 3$ を満たす非負整数解の個数は $\binom{n+2}{3}$ である。
本問では、組合せ数の計算公式 $\binom{n+2}{3} = \frac{n(n+1)(n+2)}{6}$
および確率公式の整合性を証明する。
-/

namespace MyLean.Exercises.«kyoto-university».«2006late»

/-! ### 組合せ数に関する補題 -/

/-- 組合せ数 $\binom{m}{2}$ の 2 倍に関する恒等式。 -/
lemma two_mul_choose_two (m : ℕ) :
    2 * Nat.choose m 2 = m * (m - 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases m with _ | m
    · rfl
    · rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have hsub : m + 1 - 1 = m := by omega
      rw [hsub] at ih
      calc
        2 * (m + 1 + (m + 1).choose 2) =
          2 * (m + 1) + 2 * (m + 1).choose 2 := by ring
        _ = 2 * (m + 1) + (m + 1) * m := by rw [ih]
        _ = (m + 1 + 1) * (m + 1 + 1 - 1) := by
          have : m + 1 + 1 - 1 = m + 1 := by omega
          rw [this]
          ring

/-- 組合せ数 $\binom{n+2}{3}$ の 6 倍に関する恒等式。 -/
lemma six_mul_choose_three (n : ℕ) :
    6 * Nat.choose (n + 2) 3 = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ]
    have h2 : 2 * Nat.choose (n + 2) 2 = (n + 2) * (n + 1) := by
      have := two_mul_choose_two (n + 2)
      have h_sub : (n + 2) - 1 = n + 1 := by omega
      rw [h_sub] at this
      exact this
    calc
      6 * ((n + 2).choose 2 + (n + 2).choose 3) =
        3 * (2 * (n + 2).choose 2) + 6 * (n + 2).choose 3 := by ring
      _ = 3 * ((n + 2) * (n + 1)) + n * (n + 1) * (n + 2) := by rw [h2, ih]
      _ = (n + 1) * (n + 1 + 1) * (n + 1 + 2) := by ring

/-! ### 本問の主定理 -/

/-- 【第3問の解答（場合の数）】
$n$ 個のサイコロの目の和が $n+3$ となる組合せ数は $\binom{n+2}{3} = \frac{n(n+1)(n+2)}{6}$ である。 -/
theorem problem_3_proof (n : ℕ) (_hn : 1 ≤ n) :
    Nat.choose (n + 2) 3 = (n * (n + 1) * (n + 2)) / 6 := by
  have h := six_mul_choose_three n
  omega

/-- 確率の式との整合性: 場合の数を全事象の数 $6^n$ で割ることで、求める確率が得られる。 -/
theorem problem_3_prob_eq (n : ℕ) (_hn : 1 ≤ n) :
    (Nat.choose (n + 2) 3 : ℚ) / (6 ^ n : ℚ) = problem_3_prob n := by
  have h := six_mul_choose_three n
  dsimp [problem_3_prob]
  have h6 : (6 : ℚ) ≠ 0 := by norm_num
  have hpow : (6 ^ (n + 1) : ℚ) = 6 * 6 ^ n := by ring
  rw [hpow]
  have h_eq : (Nat.choose (n + 2) 3 : ℚ) = (n * (n + 1) * (n + 2) : ℚ) / 6 := by
    have h_cast : ((6 * Nat.choose (n + 2) 3 : ℕ) : ℚ) = ((n * (n + 1) * (n + 2) : ℕ) : ℚ) := by
      rw [h]
    push_cast at h_cast
    linarith
  rw [h_eq]
  ring

end MyLean.Exercises.«kyoto-university».«2006late»
