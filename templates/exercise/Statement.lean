-- 必要な Mathlib モジュールを個別にインポートする（例: import Mathlib.Data.Real.Basic）
import MyLean.Common

/-!
# 演習・課題ステートメント (Statement)

科目名: {SubjectName}
課題名: {AssignmentName}

このモジュールでは、講義課題・試験の出題内容(前提定義および各小問の主張)を記述する。
初期状態では各問題の証明を `sorry` としておき、解答は `Proof.lean` に記述する。
-/

namespace MyLean.Exercises.Template

/- 問題の前提となる局所的な定義をここに記述する。 -/

/-- 【問1】問題の主張。 -/
theorem problem_1 : True := by
  sorry

/-- 【問2】問題の主張。 -/
theorem problem_2 : True := by
  sorry

end MyLean.Exercises.Template
