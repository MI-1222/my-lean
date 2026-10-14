import Mathlib
import MyLean.Common
import MyLean.Exercises.«kyoto-university».«2006late».Statement

/-!
# 京都大学 2006年度後期 理系 第5問 (Proof)

原点 $\mathrm{O}$ と点 $\mathrm{P}(R, 0, H)$ を結ぶ線分を $z$ 軸のまわりに回転させてできる円錐容器に水を満たし、
原点からの水面の高さが $h$ のとき単位時間あたりの排水量が $\sqrt{h}$ となるように排水する。
すべての水を排出するのに要する時間を求める。

### 数学的背景
- 高さ $h$ における円錐容器の断面は半径 $\frac{R}{H} h$ の円であり、断面積は
  $$ S(h) = \pi \left(\frac{R}{H} h\right)^2 $$
  である。
- 時刻 $t$ における水面の高さを $h(t)$ とすると、体積変化率は
  $$ \frac{dV}{dt} = S(h) \frac{dh}{dt} = -\sqrt{h} $$
  を満たす（排水のため負符号）。
- 変数分離形として整理すると、
  $$ dt = -\frac{S(h)}{\sqrt{h}} dh $$
- 満水時 $h = H$ から空 $h = 0$ までの全所要時間 $T$ は、
  $$ T = \int_0^H \frac{S(h)}{\sqrt{h}} \, dh
       = \int_0^H \frac{\pi (R h / H)^2}{\sqrt{h}} \, dh
       = \frac{2}{5} \pi R^2 \sqrt{H} $$
  となる。
-/

namespace MyLean.Exercises.«kyoto-university».«2006late»

open Real intervalIntegral

/-! ### 断面積と被積分関数に関する補題 -/

/-- 水面の高さ $h \in (0, H]$ において、被積分関数は定数倍とベキ関数 $h^{3/2}$ の積に一致する。 -/
lemma integrand_eq_on_Ioc (R H : ℝ) (_hH : 0 < H) {h : ℝ} (hh : h ∈ Set.Ioc 0 H) :
    π * (R / H * h) ^ 2 / Real.sqrt h = (π * (R / H) ^ 2) * h ^ (3 / 2 : ℝ) := by
  have hpos : 0 < h := hh.1
  rw [Real.sqrt_eq_rpow]
  have h_rpow : h ^ (3 / 2 : ℝ) = h ^ 2 / h ^ (1 / 2 : ℝ) := by
    have h_sub : (3 / 2 : ℝ) = 2 - 1 / 2 := by ring
    rw [h_sub, Real.rpow_sub hpos 2 (1 / 2), Real.rpow_two]
  rw [h_rpow]
  have h_mul_pow : (R / H * h) ^ 2 = (R / H) ^ 2 * h ^ 2 := mul_pow (R / H) h 2
  rw [h_mul_pow]
  ring

/-! ### 本問の主定理 -/

/-- 【第5問の解答】
排水微分方程式から導かれる所要時間の積分は $\frac{2}{5} \pi R^2 \sqrt{H}$ に等しい。 -/
theorem problem_5_proof (R H : ℝ) (_hR : 0 < R) (hH : 0 < H) :
    ∫ h in (0 : ℝ)..H, (π * (R / H * h) ^ 2 / Real.sqrt h) =
      (2 / 5) * π * R ^ 2 * Real.sqrt H := by
  have huIoc : Set.uIoc (0 : ℝ) H = Set.Ioc 0 H := Set.uIoc_of_le hH.le
  have h_congr : (∫ h in (0 : ℝ)..H, (π * (R / H * h) ^ 2 / Real.sqrt h)) =
      ∫ h in (0 : ℝ)..H, (π * (R / H) ^ 2) * h ^ (3 / 2 : ℝ) := by
    apply integral_congr_ae
    filter_upwards with h hh
    rw [huIoc] at hh
    exact integrand_eq_on_Ioc R H hH hh
  rw [h_congr]
  rw [integral_const_mul]
  have hr : (-1 : ℝ) < (3 / 2 : ℝ) := by norm_num
  have h_rpow_int := @integral_rpow (0 : ℝ) H (3 / 2 : ℝ) (Or.inl hr)
  have h32 : (3 / 2 : ℝ) + 1 = 5 / 2 := by ring
  rw [h32] at h_rpow_int
  rw [h_rpow_int]
  have hzero : (0 : ℝ) ^ (5 / 2 : ℝ) = 0 := by
    apply zero_rpow
    norm_num
  rw [hzero, sub_zero]
  have hH_rpow : H ^ (5 / 2 : ℝ) = H ^ 2 * Real.sqrt H := by
    rw [Real.sqrt_eq_rpow]
    have : (5 / 2 : ℝ) = 2 + 1 / 2 := by ring
    rw [this, Real.rpow_add hH, Real.rpow_two]
  rw [hH_rpow]
  have hHne : H ≠ 0 := hH.ne'
  have : (R / H) ^ 2 = R ^ 2 / H ^ 2 := div_pow R H 2
  rw [this]
  calc
    (π * (R ^ 2 / H ^ 2)) * (H ^ 2 * Real.sqrt H / (5 / 2)) =
      (π * (R ^ 2 / H ^ 2) * H ^ 2) * (Real.sqrt H / (5 / 2)) := by ring
    _ = (π * R ^ 2) * (Real.sqrt H / (5 / 2)) := by
      have : (R ^ 2 / H ^ 2) * H ^ 2 = R ^ 2 := by
        exact div_mul_cancel₀ (R ^ 2) (pow_ne_zero 2 hHne)
      rw [mul_assoc π, this]
    _ = (2 / 5) * π * R ^ 2 * Real.sqrt H := by ring

end MyLean.Exercises.«kyoto-university».«2006late»
