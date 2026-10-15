-- 必要な Mathlib モジュールを個別にインポートする（例: import Mathlib.Data.Real.Basic）
import MyLean.Common

/-!
# 定理ステートメント (Statement)

このモジュールでは、証明対象となる定理の主張と、その主張に固有の前提定義を記述する。
実際の証明は `Proof.lean` で行う。
-/

namespace MyLean.Template

/- 定理の前提となる局所的な定義をここに記述する。 -/

/-- 主定理の主張。初期段階では `sorry` で定義しておく。 -/
theorem main_theorem : True := by
  sorry

end MyLean.Template
