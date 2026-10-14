import Mathlib
import MyLean.Common

/-!
# 演習・課題ステートメント (Statement)

大学名: 京都大学
入試年度: 2006年度後期
問題: 理系第6問(文系第5問)

このモジュールでは、京都大学2006年度後期入試の出題内容(問題定義および主張)を記述する。
第6問の証明は初期状態では `sorry` とし、完全な解答は `Proof.lean` に記述する。
-/

namespace MyLean.Exercises.«kyoto-university».«2006late».exercise

open Real

/-- 実数が有理数であることを表す述語である。 -/
def IsRat (x : ℝ) : Prop := ∃ q : ℚ, x = (q : ℝ)

/-- 度数法の 1 度をラジアン単位で表した定数である。 -/
noncomputable def oneDeg : ℝ := π / 180

/-- 【第6問】tan 1° は有理数か(有理数ではない)。 -/
theorem problem_6 : ¬ IsRat (tan oneDeg) := by
  sorry

end MyLean.Exercises.«kyoto-university».«2006late».exercise
