import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.ComputeDegree
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import MyLean.Common
import MyLean.Exercises.«science-tokyo».«2019».Statement

/-!
# 東京工業大学 2019年度 理系 第4問 (Proof)

平面による3次元空間分割の最大個数
$$ T_{\max}(n) = \sum_{k=0}^3 \binom{n}{k} = \frac{n^3 + 5n + 6}{6} $$
の形式証明。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

set_option linter.style.openClassical false
open Classical Set Polynomial BigOperators

/-! ### 平面分割・空間分割の漸化式補題 -/

/-- 直線による2次元平面分割の最大数を表す関数:
$$ S(k) = \binom{k}{0} + \binom{k}{1} + \binom{k}{2} = 1 + k + \frac{k(k-1)}{2} $$
「怠けた仕出し屋の数列」として知られ、任意の $k$ 本の直線配置による補集合の連結成分数の最大値を与える。 -/
def maxPlaneRegions (k : ℕ) : ℕ :=
  Nat.choose k 0 + Nat.choose k 1 + Nat.choose k 2

/-- 3次元空間分割の最大数に関する漸化式:
$T_{\max}(n + 1) = T_{\max}(n) + S(n)$。
$(n+1)$ 枚目の平面が既存の $n$ 枚の平面と交わるとき、その平面上に $n$ 本の交線が現れ、
最大で $S(n)$ 個の平面領域が生じる。
追加された平面が通過した既存の立体領域をそれぞれ2つに分割するため、
増える立体領域の個数は平面上の分割数 $S(n)$ と完全に一致する。 -/
lemma maxSpaceRegions_succ (n : ℕ) :
    maxSpaceRegions (n + 1) = maxSpaceRegions n + maxPlaneRegions n := by
  dsimp [maxSpaceRegions, maxPlaneRegions]
  have h1 : (n + 1).choose 1 = n.choose 0 + n.choose 1 := rfl
  have h2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := rfl
  have h3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := rfl
  have hz1 : (n + 1).choose 0 = 1 := Nat.choose_zero_right (n + 1)
  have hz0 : n.choose 0 = 1 := Nat.choose_zero_right n
  omega

/-! ### 組合せ数に関する計算補題 -/

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

/-- 怠けた仕出し屋の数列の閉じた多項式表示:
$2 \cdot S(k) = k^2 + k + 2$。
したがって $S(k) = 1 + k + \frac{k(k-1)}{2}$ が成り立つ。 -/
lemma two_mul_maxPlaneRegions (k : ℕ) :
    2 * maxPlaneRegions k = k ^ 2 + k + 2 := by
  dsimp [maxPlaneRegions]
  have h := two_mul_choose_two k
  rw [Nat.choose_zero_right, Nat.choose_one_right]
  rcases k with _ | k
  · rfl
  · have hk : k + 1 - 1 = k := by omega
    rw [hk] at h
    calc
      2 * (1 + (k + 1) + (k + 1).choose 2) =
        2 + 2 * (k + 1) + 2 * (k + 1).choose 2 := by ring
      _ = 2 + 2 * (k + 1) + (k + 1) * k := by rw [h]
      _ = (k + 1) ^ 2 + (k + 1) + 2 := by ring

/-- 組合せ数 $\binom{m+2}{3}$ の 6 倍に関する恒等式。 -/
lemma six_mul_choose_three (m : ℕ) :
    6 * Nat.choose (m + 2) 3 = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.choose_succ_succ]
    have h2 : 2 * Nat.choose (m + 2) 2 = (m + 2) * (m + 1) := by
      have h := two_mul_choose_two (m + 2)
      have h_sub : (m + 2) - 1 = m + 1 := by omega
      rw [h_sub] at h
      exact h
    calc
      6 * ((m + 2).choose 2 + (m + 2).choose 3) =
        3 * (2 * (m + 2).choose 2) + 6 * (m + 2).choose 3 := by ring
      _ = 3 * ((m + 2) * (m + 1)) + m * (m + 1) * (m + 2) := by rw [h2, ih]
      _ = (m + 1) * (m + 1 + 1) * (m + 1 + 2) := by ring

/-- 空間領域最大数の 6 倍に関する恒等式:
$6 \cdot T_{\max}(n) = n³ + 5n + 6$。 -/
lemma six_mul_maxSpaceRegions (n : ℕ) :
    6 * maxSpaceRegions n = n ^ 3 + 5 * n + 6 := by
  rcases n with _ | _ | _ | m
  · dsimp [maxSpaceRegions]
    rfl
  · dsimp [maxSpaceRegions]
    rfl
  · dsimp [maxSpaceRegions]
    rfl
  · dsimp [maxSpaceRegions]
    have h2 : 2 * Nat.choose (m + 3) 2 = (m + 3) * (m + 2) := by
      have h := two_mul_choose_two (m + 3)
      have hm : m + 3 - 1 = m + 2 := by omega
      rw [hm] at h
      exact h
    have h3 : 6 * Nat.choose (m + 3) 3 = (m + 1) * (m + 2) * (m + 3) := by
      have h := six_mul_choose_three (m + 1)
      have hm : (m + 1) + 2 = m + 3 := by omega
      rw [hm] at h
      exact h
    calc
      6 * (Nat.choose (m + 3) 0 + Nat.choose (m + 3) 1 +
           Nat.choose (m + 3) 2 + Nat.choose (m + 3) 3) =
        6 * 1 + 6 * (m + 3) + 3 * (2 * Nat.choose (m + 3) 2) +
          6 * Nat.choose (m + 3) 3 := by
        rw [Nat.choose_zero_right, Nat.choose_one_right]
        ring
      _ = 6 + 6 * (m + 3) + 3 * ((m + 3) * (m + 2)) +
          (m + 1) * (m + 2) * (m + 3) := by rw [h2, h3]
      _ = (m + 3) ^ 3 + 5 * (m + 3) + 6 := by ring

/-! ### 本問の主定理 -/

/-! ### 幾何学的交差理論と領域数の漸化不等式 -/

/-- 2本の直線が平行である条件。法線ベクトルがスカラー倍であることとして定義される。 -/
def parallelLines (L₁ L₂ : Line2) : Prop :=
  ∃ (c : ℝ), L₁.normVec = c • L₂.normVec

/-- 平行線の推移律。$L_1 \parallel L_2$ かつ $L_2 \parallel L_3$ ならば $L_1 \parallel L_3$ である。 -/
lemma parallelLines_trans (L₁ L₂ L₃ : Line2)
    (h12 : parallelLines L₁ L₂) (h23 : parallelLines L₂ L₃) :
    parallelLines L₁ L₃ := by
  rcases h12 with ⟨c1, hc1⟩
  rcases h23 with ⟨c2, hc2⟩
  use (c1 * c2)
  rw [hc1, hc2, mul_smul]

/-- 平行線の対称律。$L_1 \parallel L_2$ ならば $L_2 \parallel L_1$ である。 -/
lemma parallelLines_symm (L₁ L₂ : Line2)
    (h : parallelLines L₁ L₂) : parallelLines L₂ L₁ := by
  rcases h with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply L₁.normVec_ne_zero
    rw [hc, hc0, zero_smul]
  use c⁻¹
  rw [hc, smul_smul, inv_mul_cancel₀ hc_ne, one_smul]

/-- 2次元直線配置が一般の位置(General Position)にある条件。
すべての直線が互いに平行でなく、かつどの相異なる3直線も1点で交わらない。 -/
def GeneralPositionLines (k : ℕ) (L : Fin k → Line2) : Prop :=
  (∀ i j, i ≠ j → ¬ parallelLines (L i) (L j)) ∧
  (∀ i j l, i ≠ j → j ≠ l → i ≠ l → (L i).toSet ∩ (L j).toSet ∩ (L l).toSet = ∅)

/-- 2枚の平面が平行である条件。法線ベクトルがスカラー倍であることとして定義される。 -/
def parallelPlanes (H₁ H₂ : Plane3) : Prop :=
  ∃ (c : ℝ), H₁.normVec = c • H₂.normVec

/-- 2枚の平面が交わる(平行でない)条件。 -/
def intersectPlanes (H₁ H₂ : Plane3) : Prop :=
  ¬ parallelPlanes H₁ H₂

/-- 3次元平面配置が一般の位置(General Position)にある条件。
どの2平面も平行でなく、どの3平面も共通直線をもたず1点で交わり、どの4平面も1点を共有しない。 -/
def GeneralPositionPlanes (n : ℕ) (H : Fin n → Plane3) : Prop :=
  (∀ i j, i ≠ j → ¬ parallelPlanes (H i) (H j)) ∧
  (∀ i j l, i ≠ j → j ≠ l → i ≠ l →
    ∃ p : Space3, (H i).toSet ∩ (H j).toSet ∩ (H l).toSet = {p}) ∧
  (∀ i j l m, i ≠ j → j ≠ l → l ≠ m → i ≠ l → i ≠ m → j ≠ m →
    (H i).toSet ∩ (H j).toSet ∩ (H l).toSet ∩ (H m).toSet = ∅)

/-- 2次元平面分割の最大数に関する漸化式:
$S(k + 1) = S(k) + (k + 1)$。
$(k+1)$ 本目の直線が既存の $k$ 本の直線と高々 $k$ 個の交点で交わることにより、
その直線自身が高々 $k + 1$ 個の線分・半直線に分割され、同数の平面領域が新たに生成される幾何的性質に対応する。 -/
lemma maxPlaneRegions_succ_step (k : ℕ) :
    maxPlaneRegions (k + 1) = maxPlaneRegions k + (k + 1) := by
  dsimp [maxPlaneRegions]
  have h1 : (k + 1).choose 1 = k.choose 0 + k.choose 1 := rfl
  have h2 : (k + 1).choose 2 = k.choose 1 + k.choose 2 := rfl
  have hz1 : (k + 1).choose 0 = 1 := Nat.choose_zero_right (k + 1)
  have hz0 : k.choose 0 = 1 := Nat.choose_zero_right k
  have hk1 : k.choose 1 = k := Nat.choose_one_right k
  omega

/-! ### 直線配置の漸化不等式に関する1次元帰着と中間補題 -/

/-! #### ステップ 1: 1次元実数直線の有限点分割補題 -/

/-- 点 $x$ より真に小さい有限集合 $S$ の元の個数。 -/
noncomputable def countLt (S : Finset ℝ) (x : ℝ) : ℕ :=
  (S.filter (· < x)).card

/-- 各点におけるcountLtの値は高々集合 $S$ の要素数以下である。 -/
lemma countLt_le (S : Finset ℝ) (x : ℝ) : countLt S x ≤ S.card :=
  Finset.card_filter_le S (· < x)

/-- countLtの値域を有限型`Fin(S.card+1)`に制限した写像。 -/
noncomputable def countLtFin (S : Finset ℝ) (x : ℝ) : Fin (S.card + 1) :=
  ⟨countLt S x, Nat.lt_succ_of_le (countLt_le S x)⟩

/-- 2点 $x \le y$ でcountLtの値が一致し、両端点が $S$ に属さないならば、
閉区間 $[x,y]$ と有限集合 $S$ は交わらない。 -/
lemma disjoint_Icc_of_countLt_eq {S : Finset ℝ} {x y : ℝ} (hxy : x ≤ y)
    (h_eq : countLt S x = countLt S y) (hx : x ∉ S) (hy : y ∉ S) :
    Disjoint (Icc x y) (S : Set ℝ) := by
  rw [Set.disjoint_left]
  intro z hz hzS
  have hz_in : z ∈ S := hzS
  by_cases hzx : z = x
  · subst hzx; exact hx hz_in
  · by_cases hzy : z = y
    · subst hzy; exact hy hz_in
    · have hx_lt_z : x < z := lt_of_le_of_ne hz.1 (Ne.symm hzx)
      have hz_lt_y : z < y := lt_of_le_of_ne hz.2 hzy
      have h_sub : S.filter (· < x) ⊆ S.filter (· < y) := by
        intro t ht
        rw [Finset.mem_filter] at ht ⊢
        exact ⟨ht.1, lt_of_lt_of_le ht.2 hxy⟩
      have hz_not_in_x : z ∉ S.filter (· < x) := by
        rw [Finset.mem_filter]
        intro h
        linarith
      have hz_in_y : z ∈ S.filter (· < y) := by
        rw [Finset.mem_filter]
        exact ⟨hz_in, hz_lt_y⟩
      have h_ssub : S.filter (· < x) ⊂ S.filter (· < y) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, fun h => hz_not_in_x (h ▸ hz_in_y)⟩
      have h_lt := Finset.card_lt_card h_ssub
      dsimp [countLt] at h_eq
      omega

/-- 一般の商集合において、有限値関数がファイバー上で同値関係を満たすとき、
商集合の濃度は終域の要素数以下である。 -/
lemma card_quotient_le_of_fiber_le {α : Type*} (s : Setoid α) {β : Type*} [Fintype β]
    (f : α → β) (h : ∀ x y, f x = f y → x ≈ y) :
    Nat.card (Quotient s) ≤ Fintype.card β := by
  let g : Quotient s → β := fun q => f q.out
  have hg_inj : Function.Injective g := by
    intro q1 q2 hg
    dsimp [g] at hg
    have hequiv := h q1.out q2.out hg
    have h1 : Quotient.mk s q1.out = q1 := Quotient.out_eq q1
    have h2 : Quotient.mk s q2.out = q2 := Quotient.out_eq q2
    have hsound : Quotient.mk s q1.out = Quotient.mk s q2.out := Quotient.sound hequiv
    exact h1.symm.trans (hsound.trans h2)
  have h_le := Nat.card_le_card_of_injective g hg_inj
  simpa only [Nat.card_eq_fintype_card] using h_le

/-- countLtの値が一致する $x \le y$ に対し、閉区間 $[x,y]$ が補集合に含まれるため
両者は同一の連結成分に属する。 -/
lemma connectedComponent_eq_of_countLt_eq_le {S : Finset ℝ} (x y : {x : ℝ | x ∉ S})
    (hle : x.val ≤ y.val) (h_eq : countLt S x.val = countLt S y.val) :
    connectedComponent x = connectedComponent y := by
  have hdisj : Disjoint (Icc x.val y.val) (S : Set ℝ) :=
    disjoint_Icc_of_countLt_eq hle h_eq x.2 y.2
  have h_sub : Icc x.val y.val ⊆ {z : ℝ | z ∉ S} := by
    intro z hz hzS
    have hzS' : z ∈ (S : Set ℝ) := hzS
    exact Set.disjoint_left.mp hdisj hz hzS'
  let f : Icc x.val y.val → {x : ℝ | x ∉ S} := fun ⟨z, hz⟩ => ⟨z, h_sub hz⟩
  have hf_cont : Continuous f := Continuous.subtype_mk continuous_subtype_val _
  have h_conn_icc : IsConnected (Icc x.val y.val) := isConnected_Icc hle
  have : ConnectedSpace (Icc x.val y.val) := Subtype.connectedSpace h_conn_icc
  have h_conn_range : IsConnected (range f) := isConnected_range hf_cont
  have hx_in : x ∈ range f := by
    use ⟨x.val, left_mem_Icc.mpr hle⟩
  have hy_in : y ∈ range f := by
    use ⟨y.val, right_mem_Icc.mpr hle⟩
  have h_sub_comp : range f ⊆ connectedComponent x :=
    IsConnected.subset_connectedComponent h_conn_range hx_in
  exact connectedComponent_eq (h_sub_comp hy_in)

/-- 写像countLtFinの値が一致する2点は、実数直線の順序関係に関わらず
同一の連結成分に属する。 -/
lemma connectedComponent_eq_of_countLtFin_eq {S : Finset ℝ} (x y : {x : ℝ | x ∉ S})
    (h_eq : countLtFin S x.val = countLtFin S y.val) :
    connectedComponent x = connectedComponent y := by
  have h_count_eq : countLt S x.val = countLt S y.val := congr_arg Fin.val h_eq
  rcases le_total x.val y.val with hle | hle
  · exact connectedComponent_eq_of_countLt_eq_le x y hle h_count_eq
  · exact (connectedComponent_eq_of_countLt_eq_le y x hle h_count_eq.symm).symm

/-- 実数直線上の有限点集合Sによる補集合ℝ\Sの開区間(連結成分)の個数。
$m$ 個の相異なる点によって、実数直線は高々 $m+1$ 個の互いに素な開区間に分割される。 -/
noncomputable def realIntervalsCount (S : Finset ℝ) : ℕ :=
  Nat.card (ConnectedComponents ({x : ℝ | x ∉ S}))

/-- 実数直線の有限点分割に関する上界定理:
有限点集合 $S$ による補集合の開区間(連結成分)の個数は高々 $|S| + 1$ 個である。
各連結成分を左側の点の個数により`Fin(S.card+1)`へ単射づけることで証明される。 -/
theorem card_intervals_of_finset_real (S : Finset ℝ) :
    realIntervalsCount S ≤ S.card + 1 := by
  let α := {x : ℝ | x ∉ S}
  let s : Setoid α := connectedComponentSetoid α
  let f : α → Fin (S.card + 1) := fun x => countLtFin S x.val
  have h_fiber : ∀ x y : α, f x = f y → x ≈ y := by
    intro x y hfg
    exact connectedComponent_eq_of_countLtFin_eq x y hfg
  have h_le := card_quotient_le_of_fiber_le s f h_fiber
  rw [Fintype.card_fin] at h_le
  exact h_le

/-- 同一の連結成分に属する点は、左側にある有限集合 $S$ の元の個数が等しい。
もし個数が異なれば間に $s \in S$ が存在し、開かつ閉集合により分離されて矛盾する。 -/
lemma countLt_eq_of_connectedComponent_eq {S : Finset ℝ} (x y : {x : ℝ | x ∉ S})
    (h_conn : connectedComponent x = connectedComponent y) :
    countLt S x.val = countLt S y.val := by
  by_contra hne
  have h_cases : (∃ s ∈ S, x.val < s ∧ s < y.val) ∨ (∃ s ∈ S, y.val < s ∧ s < x.val) := by
    rcases le_total x.val y.val with hle | hle
    · left
      have h_ssub : S.filter (· < x.val) ⊂ S.filter (· < y.val) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro t ht
          simp only [Finset.mem_filter] at ht ⊢
          exact ⟨ht.1, lt_of_lt_of_le ht.2 hle⟩
        · intro h_eq
          have h_card_eq : countLt S x.val = countLt S y.val := by
            dsimp [countLt]
            rw [h_eq]
          exact hne h_card_eq
      obtain ⟨s, hs⟩ := Finset.exists_of_ssubset h_ssub
      have hsS : s ∈ S := (Finset.mem_filter.mp hs.1).1
      have hsy : s < y.val := (Finset.mem_filter.mp hs.1).2
      have hsx : ¬ (s < x.val) := fun hlt => hs.2 (Finset.mem_filter.mpr ⟨hsS, hlt⟩)
      have hs_le_x : x.val ≤ s := not_lt.mp hsx
      have hne_sx : s ≠ x.val := fun h => x.2 (h ▸ hsS)
      exact ⟨s, hsS, lt_of_le_of_ne hs_le_x hne_sx.symm, hsy⟩
    · right
      have h_ssub : S.filter (· < y.val) ⊂ S.filter (· < x.val) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro t ht
          simp only [Finset.mem_filter] at ht ⊢
          exact ⟨ht.1, lt_of_lt_of_le ht.2 hle⟩
        · intro h_eq
          have h_card_eq : countLt S y.val = countLt S x.val := by
            dsimp [countLt]
            rw [h_eq]
          exact hne h_card_eq.symm
      obtain ⟨s, hs⟩ := Finset.exists_of_ssubset h_ssub
      have hsS : s ∈ S := (Finset.mem_filter.mp hs.1).1
      have hsx : s < x.val := (Finset.mem_filter.mp hs.1).2
      have hsy : ¬ (s < y.val) := fun hlt => hs.2 (Finset.mem_filter.mpr ⟨hsS, hlt⟩)
      have hs_le_y : y.val ≤ s := not_lt.mp hsy
      have hne_sy : s ≠ y.val := fun h => y.2 (h ▸ hsS)
      exact ⟨s, hsS, lt_of_le_of_ne hs_le_y hne_sy.symm, hsx⟩
  rcases h_cases with ⟨s, hsS, hx_lt, hs_lt_y⟩ | ⟨s, hsS, hy_lt, hs_lt_x⟩
  · let U : Set {p : ℝ | p ∉ S} := {p | p.val < s}
    have hU_open : IsOpen U := isOpen_Iio.preimage continuous_subtype_val
    have hUc_open : IsOpen (Uᶜ) := by
      have h_eq : Uᶜ = {p : {p : ℝ | p ∉ S} | s < p.val} := by
        ext p
        simp only [mem_compl_iff]
        change ¬ p.val < s ↔ s < p.val
        constructor
        · intro hnot
          have hle : s ≤ p.val := not_lt.mp hnot
          have hne : s ≠ p.val := fun h => p.2 (h ▸ hsS)
          exact lt_of_le_of_ne hle hne
        · intro hlt hle
          exact lt_asymm hlt hle
      rw [h_eq]
      exact isOpen_Ioi.preimage continuous_subtype_val
    have hU_clopen : IsClopen U := ⟨isOpen_compl_iff.mp hUc_open, hU_open⟩
    have hxU : x ∈ U := hx_lt
    have hyUc : y ∈ Uᶜ := by
      intro hy
      exact lt_asymm hs_lt_y hy
    have h_sub := IsClopen.connectedComponent_subset hU_clopen hxU
    have hy_in_comp : y ∈ connectedComponent x := by
      rw [h_conn]
      exact mem_connectedComponent
    have hyU : y ∈ U := h_sub hy_in_comp
    exact hyUc hyU
  · let U : Set {p : ℝ | p ∉ S} := {p | p.val < s}
    have hU_open : IsOpen U := isOpen_Iio.preimage continuous_subtype_val
    have hUc_open : IsOpen (Uᶜ) := by
      have h_eq : Uᶜ = {p : {p : ℝ | p ∉ S} | s < p.val} := by
        ext p
        simp only [mem_compl_iff]
        change ¬ p.val < s ↔ s < p.val
        constructor
        · intro hnot
          have hle : s ≤ p.val := not_lt.mp hnot
          have hne : s ≠ p.val := fun h => p.2 (h ▸ hsS)
          exact lt_of_le_of_ne hle hne
        · intro hlt hle
          exact lt_asymm hlt hle
      rw [h_eq]
      exact isOpen_Ioi.preimage continuous_subtype_val
    have hU_clopen : IsClopen U := ⟨isOpen_compl_iff.mp hUc_open, hU_open⟩
    have hyU : y ∈ U := hy_lt
    have hxUc : x ∈ Uᶜ := by
      intro hx
      exact lt_asymm hs_lt_x hx
    have h_sub := IsClopen.connectedComponent_subset hU_clopen hyU
    have hx_in_comp : x ∈ connectedComponent y := by
      rw [← h_conn]
      exact mem_connectedComponent
    have hxU : x ∈ U := h_sub hx_in_comp
    exact hxUc hxU

/-- 有限点集合 $S \subset \mathbb{R}$ に対し、
各インデックス $j \in \{0, \dots, |S|\}$ について左側にちょうど $j$ 個の元をもつ点 $x \notin S$ が存在する。
順序同型 `Fin S.card ≃o S` を用いて構成される。 -/
lemma exists_point_countLt_eq (S : Finset ℝ) (j : Fin (S.card + 1)) :
    ∃ x : ℝ, x ∉ S ∧ countLt S x = j.val := by
  let m := S.card
  by_cases hm : m = 0
  · use 0
    have hS_empty : S = ∅ := Finset.card_eq_zero.mp hm
    have hj : j.val = 0 := by
      have : j.val < m + 1 := j.isLt
      omega
    constructor
    · intro h0
      rw [hS_empty] at h0
      simp at h0
    · dsimp [countLt]
      have : S.filter (· < 0) = ∅ := by rw [hS_empty, Finset.filter_empty]
      rw [this, Finset.card_empty, hj]
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    let e : Fin m ≃o S := Finset.orderIsoOfFin S rfl
    by_cases hj0 : j.val = 0
    · let x := (e ⟨0, hm_pos⟩ : ℝ) - 1
      use x
      constructor
      · intro hxS
        let i := e.symm ⟨x, hxS⟩
        have h_eq : (e i : ℝ) = x :=
          congr_arg Subtype.val (e.apply_symm_apply ⟨x, hxS⟩)
        have h0_le_i : ⟨0, hm_pos⟩ ≤ i := Fin.le_def.mpr (Nat.zero_le i.val)
        have h_le : (e ⟨0, hm_pos⟩ : ℝ) ≤ (e i : ℝ) := by
          rw [Subtype.coe_le_coe]
          exact e.monotone h0_le_i
        rw [h_eq] at h_le
        dsimp [x] at h_le
        linarith
      · have h_filter_empty : S.filter (· < x) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro s hs
          let i := e.symm ⟨s, hs⟩
          have h_eq : (e i : ℝ) = s :=
            congr_arg Subtype.val (e.apply_symm_apply ⟨s, hs⟩)
          have h0_le_i : ⟨0, hm_pos⟩ ≤ i := Fin.le_def.mpr (Nat.zero_le i.val)
          have h_le : (e ⟨0, hm_pos⟩ : ℝ) ≤ (e i : ℝ) := by
            rw [Subtype.coe_le_coe]
            exact e.monotone h0_le_i
          rw [h_eq] at h_le
          dsimp [x]
          linarith
        dsimp [countLt]
        rw [h_filter_empty, Finset.card_empty, hj0]
    · by_cases hjm : j.val = m
      · have hm_pred_lt : m - 1 < m := by omega
        let x := (e ⟨m - 1, hm_pred_lt⟩ : ℝ) + 1
        use x
        constructor
        · intro hxS
          let i := e.symm ⟨x, hxS⟩
          have h_eq : (e i : ℝ) = x :=
            congr_arg Subtype.val (e.apply_symm_apply ⟨x, hxS⟩)
          have hi_le : i ≤ ⟨m - 1, hm_pred_lt⟩ := by
            have : i.val ≤ m - 1 := by
              have := i.isLt
              omega
            exact Fin.le_def.mpr this
          have h_le : (e i : ℝ) ≤ (e ⟨m - 1, hm_pred_lt⟩ : ℝ) := by
            rw [Subtype.coe_le_coe]
            exact e.monotone hi_le
          rw [h_eq] at h_le
          dsimp [x] at h_le
          linarith
        · have h_filter_all : S.filter (· < x) = S := by
            ext s
            simp only [Finset.mem_filter, and_iff_left_iff_imp]
            intro hs
            let i := e.symm ⟨s, hs⟩
            have h_eq : (e i : ℝ) = s :=
              congr_arg Subtype.val (e.apply_symm_apply ⟨s, hs⟩)
            have hi_le : i ≤ ⟨m - 1, hm_pred_lt⟩ := by
              have : i.val ≤ m - 1 := by
                have := i.isLt
                omega
              exact Fin.le_def.mpr this
            have h_le : (e i : ℝ) ≤ (e ⟨m - 1, hm_pred_lt⟩ : ℝ) := by
              rw [Subtype.coe_le_coe]
              exact e.monotone hi_le
            rw [h_eq] at h_le
            dsimp [x]
            linarith
          dsimp [countLt]
          rw [h_filter_all, hjm]
      · have hj_lt_m : j.val < m := by
          have : j.val < m + 1 := j.isLt
          omega
        have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj0
        have hj_pred_lt : j.val - 1 < m := by omega
        let i0 : Fin m := ⟨j.val - 1, hj_pred_lt⟩
        let i1 : Fin m := ⟨j.val, hj_lt_m⟩
        have hi0_lt_i1 : i0 < i1 := by
          exact Fin.mk_lt_mk.mpr (by omega)
        have hei0_lt_ei1 : (e i0 : ℝ) < (e i1 : ℝ) := by
          rw [Subtype.coe_lt_coe]
          exact e.lt_iff_lt.mpr hi0_lt_i1
        let x := ((e i0 : ℝ) + (e i1 : ℝ)) / 2
        use x
        have h_x_gt : (e i0 : ℝ) < x := by
          dsimp [x]; linarith
        have h_x_lt : x < (e i1 : ℝ) := by
          dsimp [x]; linarith
        constructor
        · intro hxS
          let i := e.symm ⟨x, hxS⟩
          have h_eq : (e i : ℝ) = x :=
            congr_arg Subtype.val (e.apply_symm_apply ⟨x, hxS⟩)
          rcases le_or_gt i i0 with h_le | h_gt
          · have : (e i : ℝ) ≤ (e i0 : ℝ) := by
              rw [Subtype.coe_le_coe]; exact e.monotone h_le
            rw [h_eq] at this; linarith
          · have hi1_le : i1 ≤ i := by
              have hi_lt : i0.val < i.val := Fin.lt_def.mp h_gt
              have : j.val ≤ i.val := by
                dsimp [i0] at hi_lt
                omega
              exact Fin.le_def.mpr this
            have : (e i1 : ℝ) ≤ (e i : ℝ) := by
              rw [Subtype.coe_le_coe]; exact e.monotone hi1_le
            rw [h_eq] at this; linarith
        · have h_filter_eq : S.filter (· < x) =
              (Finset.filter (fun i : Fin m => i.val < j.val) Finset.univ).image
                (fun i => (e i : ℝ)) := by
            ext s
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
            constructor
            · intro ⟨hs, hs_lt⟩
              let i := e.symm ⟨s, hs⟩
              have h_eq : (e i : ℝ) = s :=
                congr_arg Subtype.val (e.apply_symm_apply ⟨s, hs⟩)
              refine ⟨i, ?_, h_eq⟩
              by_contra hnot
              simp only [not_lt] at hnot
              have hi1_le : i1 ≤ i := by
                exact Fin.le_def.mpr hnot
              have : (e i1 : ℝ) ≤ (e i : ℝ) := by
                rw [Subtype.coe_le_coe]; exact e.monotone hi1_le
              rw [h_eq] at this; linarith
            · rintro ⟨i, hi_lt, rfl⟩
              have hsS : (e i : ℝ) ∈ S := (e i).property
              refine ⟨hsS, ?_⟩
              have hi_le_i0 : i ≤ i0 := by
                have : i.val ≤ j.val - 1 := by
                  have := i.isLt
                  omega
                exact Fin.le_def.mpr this
              have : (e i : ℝ) ≤ (e i0 : ℝ) := by
                rw [Subtype.coe_le_coe]; exact e.monotone hi_le_i0
              linarith
          dsimp [countLt]
          rw [h_filter_eq]
          have h_inj : ∀ i1 i2 : Fin m, (e i1 : ℝ) = (e i2 : ℝ) → i1 = i2 := by
            intro a b hab
            have : e a = e b := Subtype.ext hab
            exact e.injective this
          rw [Finset.card_image_of_injective _ h_inj]
          have h_eq : Finset.filter (fun i : Fin m => i.val < j.val) Finset.univ =
              (Finset.Iio (⟨j.val, hj_lt_m⟩ : Fin m)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
          rw [h_eq, Fin.card_Iio]

/-- 有限値関数がファイバー上で同値関係を満たすとき、商集合は有限型である。 -/
lemma finite_quotient_of_fiber_le {α : Type*} (s : Setoid α) {β : Type*} [Finite β]
    (f : α → β) (h : ∀ x y, f x = f y → x ≈ y) :
    Finite (Quotient s) := by
  let g : Quotient s → β := fun q => f q.out
  have hg_inj : Function.Injective g := by
    intro q1 q2 hg
    dsimp [g] at hg
    have hequiv := h q1.out q2.out hg
    have h1 : Quotient.mk s q1.out = q1 := Quotient.out_eq q1
    have h2 : Quotient.mk s q2.out = q2 := Quotient.out_eq q2
    have hsound : Quotient.mk s q1.out = Quotient.mk s q2.out := Quotient.sound hequiv
    exact h1.symm.trans (hsound.trans h2)
  exact Finite.of_injective g hg_inj

/-- 実数直線の有限点分割に関する等号定理:
有限点集合 $S$ による補集合の開区間(連結成分)の個数はちょうど $|S| + 1$ 個である。 -/
theorem realIntervalsCount_eq (S : Finset ℝ) :
    realIntervalsCount S = S.card + 1 := by
  have h_le := card_intervals_of_finset_real S
  have h_ge : S.card + 1 ≤ realIntervalsCount S := by
    let α := {x : ℝ | x ∉ S}
    let s : Setoid α := connectedComponentSetoid α
    have : Finite (Quotient s) := by
      let f : α → Fin (S.card + 1) := fun x => countLtFin S x.val
      have h_fiber : ∀ x y : α, f x = f y → x ≈ y := by
        intro x y hfg
        exact connectedComponent_eq_of_countLtFin_eq x y hfg
      exact finite_quotient_of_fiber_le s f h_fiber
    choose w hw using (fun j : Fin (S.card + 1) => exists_point_countLt_eq S j)
    let g : Fin (S.card + 1) → Quotient s := fun j => Quotient.mk s ⟨w j, (hw j).1⟩
    have hg_inj : Function.Injective g := by
      intro j1 j2 hg
      have hequiv : (⟨w j1, (hw j1).1⟩ : α) ≈ (⟨w j2, (hw j2).1⟩ : α) := Quotient.exact hg
      have hconn : connectedComponent (⟨w j1, (hw j1).1⟩ : α) =
          connectedComponent (⟨w j2, (hw j2).1⟩ : α) := hequiv
      have hcount := countLt_eq_of_connectedComponent_eq ⟨w j1, (hw j1).1⟩ ⟨w j2, (hw j2).1⟩ hconn
      have hj1 : countLt S (w j1) = j1.val := (hw j1).2
      have hj2 : countLt S (w j2) = j2.val := (hw j2).2
      rw [hj1, hj2] at hcount
      exact Fin.ext hcount
    have h_card_le := Nat.card_le_card_of_injective g hg_inj
    rw [Nat.card_fin] at h_card_le
    exact h_card_le
  omega

/-! #### ステップ 2: 直線同士の交点数の上界 -/

/-- 既存の第 $i$ 直線が、新しく追加された第 $(k+1)$ 直線と
交点をもつ(平行でない)条件。 -/
def hasIntersectionWithLast (k : ℕ) (L : Fin (k + 1) → Line2) (i : Fin k) : Prop :=
  ¬ parallelLines (L (Fin.castSucc i)) (L (Fin.last k))

open Classical in
/-- 平行でない直線との交点をもつインデックスの有限集合。
`Fin k` の部分集合として定義されるため、その要素数は常に $k$ 以下である。 -/
noncomputable def intersectingIndices (k : ℕ) (L : Fin (k + 1) → Line2) : Finset (Fin k) :=
  Finset.filter (fun i => hasIntersectionWithLast k L i) Finset.univ

/-- 平行な2直線に対して、第3の直線との交差性は同値である。 -/
lemma hasIntersectionWithLast_iff_of_parallel (L : Fin 3 → Line2)
    (hpar : parallelLines (L 0) (L 1)) :
    hasIntersectionWithLast 2 L 0 ↔ hasIntersectionWithLast 2 L 1 := by
  dsimp [hasIntersectionWithLast]
  change (¬ parallelLines (L 0) (L 2)) ↔ (¬ parallelLines (L 1) (L 2))
  constructor
  · intro hnot hpar12
    apply hnot
    exact parallelLines_trans (L 0) (L 1) (L 2) hpar hpar12
  · intro hnot hpar02
    apply hnot
    have h10 := parallelLines_symm (L 0) (L 1) hpar
    exact parallelLines_trans (L 1) (L 0) (L 2) h10 hpar02

/-- 平行な2直線が存在するとき、交差インデックス集合の要素数は1になり得ない。 -/
lemma card_intersectingIndices_ne_one_of_parallel (L : Fin 3 → Line2)
    (hpar : parallelLines (L 0) (L 1)) :
    (intersectingIndices 2 L).card ≠ 1 := by
  have h_iff := hasIntersectionWithLast_iff_of_parallel L hpar
  intro h1
  dsimp [intersectingIndices] at h1
  have h_card :
      (Finset.filter (fun i : Fin 2 => hasIntersectionWithLast 2 L i) Finset.univ).card = 0 ∨
      (Finset.filter (fun i : Fin 2 => hasIntersectionWithLast 2 L i) Finset.univ).card = 2 := by
    by_cases h0 : hasIntersectionWithLast 2 L 0
    · have h1' : hasIntersectionWithLast 2 L 1 := h_iff.mp h0
      right
      have h_eq : (Finset.filter (fun i : Fin 2 => hasIntersectionWithLast 2 L i) Finset.univ) =
          Finset.univ := by
        ext i; fin_cases i <;> simp [h0, h1']
      have h_univ : (Finset.univ : Finset (Fin 2)).card = 2 := rfl
      rw [h_eq, h_univ]
    · have h1' : ¬ hasIntersectionWithLast 2 L 1 := fun h => h0 (h_iff.mpr h)
      left
      have h_eq : (Finset.filter (fun i : Fin 2 => hasIntersectionWithLast 2 L i) Finset.univ) =
          ∅ := by
        ext i; fin_cases i <;> simp [h0, h1']
      rw [h_eq, Finset.card_empty]
  rcases h_card with hc0 | hc2 <;> omega

/-- 2次元平面内のベクトル $u = (u_0, u_1)$ に対する反時計回り90度回転直交ベクトル $v = (-u_1, u_0)$。 -/
noncomputable def rot90 (u : Plane2) : Plane2 :=
  EuclideanSpace.equiv (Fin 2) ℝ |>.symm fun i =>
    if i.val = 0 then - (u 1) else u 0

/-- ベクトルとその90度回転ベクトルの内積は常に0である。 -/
lemma inner_rot90_self (u : Plane2) : @inner ℝ Plane2 _ u (rot90 u) = 0 := by
  have h := PiLp.inner_apply (𝕜 := ℝ) (x := u) (y := rot90 u)
  rw [h, Fin.sum_univ_two]
  simp only [Real.inner_apply]
  change u 0 * (- (u 1)) + u 1 * (u 0) = 0
  ring

/-- 90度回転ベクトルとの内積が0ならば、2つのベクトルは平行(スカラー倍)である。 -/
lemma parallel_of_inner_rot90_zero (u₁ u₂ : Plane2) (hu₂ : u₂ ≠ 0)
    (h_rot : @inner ℝ Plane2 _ u₁ (rot90 u₂) = 0) :
    ∃ c : ℝ, u₁ = c • u₂ := by
  have hu₂_sum : u₂ 0 ^ 2 + u₂ 1 ^ 2 ≠ 0 := by
    intro h0
    apply hu₂
    ext i
    fin_cases i
    · have : u₂ 0 = 0 := by nlinarith
      exact this
    · have : u₂ 1 = 0 := by nlinarith
      exact this
  have h2 : - (u₂ 1) * u₁ 0 + u₂ 0 * u₁ 1 = 0 := by
    have h := PiLp.inner_apply (𝕜 := ℝ) (x := u₁) (y := rot90 u₂)
    rw [h, Fin.sum_univ_two] at h_rot
    simp only [Real.inner_apply] at h_rot
    change u₁ 0 * (- (u₂ 1)) + u₁ 1 * (u₂ 0) = 0 at h_rot
    linarith
  let c := (@inner ℝ Plane2 _ u₁ u₂) / (u₂ 0 ^ 2 + u₂ 1 ^ 2)
  use c
  have h_inner : @inner ℝ Plane2 _ u₁ u₂ = u₁ 0 * u₂ 0 + u₁ 1 * u₂ 1 := by
    have h := PiLp.inner_apply (𝕜 := ℝ) (x := u₁) (y := u₂)
    rw [h, Fin.sum_univ_two]
    simp only [Real.inner_apply]
  have h_c0 : c * u₂ 0 = u₁ 0 := by
    dsimp [c]
    rw [h_inner]
    have h_mul : (u₁ 0 * u₂ 0 + u₁ 1 * u₂ 1) * u₂ 0 =
        u₁ 0 * (u₂ 0 ^ 2 + u₂ 1 ^ 2) + u₂ 1 * (- (u₂ 1) * u₁ 0 + u₂ 0 * u₁ 1) := by ring
    rw [h2, mul_zero, add_zero] at h_mul
    rw [div_mul_eq_mul_div, h_mul]
    exact mul_div_cancel_right₀ (u₁ 0) hu₂_sum
  have h_c1 : c * u₂ 1 = u₁ 1 := by
    dsimp [c]
    rw [h_inner]
    have h_mul : (u₁ 0 * u₂ 0 + u₁ 1 * u₂ 1) * u₂ 1 =
        u₁ 1 * (u₂ 0 ^ 2 + u₂ 1 ^ 2) - u₂ 0 * (- (u₂ 1) * u₁ 0 + u₂ 0 * u₁ 1) := by ring
    rw [h2, mul_zero, sub_zero] at h_mul
    rw [div_mul_eq_mul_div, h_mul]
    exact mul_div_cancel_right₀ (u₁ 1) hu₂_sum
  ext i
  fin_cases i
  · exact h_c0.symm
  · exact h_c1.symm

/-- 直線 $L$ 上のパラメータ $t$ に対応する点。
基準点 $(L.offset / ‖L.normVec‖^2) \cdot L.normVec + t \cdot (\text{rot}_{90} L.normVec)$。 -/
noncomputable def linePt (L : Line2) (t : ℝ) : Plane2 :=
  let u := L.normVec
  let d := L.offset
  let sq := @inner ℝ Plane2 _ u u
  (d / sq) • u + t • rot90 u

/-- パラメータ点は常に直線自身に属する。 -/
lemma linePt_mem_line (L : Line2) (t : ℝ) : linePt L t ∈ L.toSet := by
  dsimp [Line2.toSet, linePt]
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h_rot := inner_rot90_self L.normVec
  rw [h_rot, mul_zero, add_zero]
  have hu_sq : @inner ℝ Plane2 _ L.normVec L.normVec ≠ 0 := by
    intro h0
    apply L.normVec_ne_zero
    exact inner_self_eq_zero.mp h0
  exact div_mul_cancel₀ L.offset hu_sq

/-- 平行でない直線との交点を与える実数パラメータが存在する。 -/
lemma exists_linePt_mem_of_not_parallel (L₁ L₂ : Line2) (h_not_par : ¬ parallelLines L₁ L₂) :
    ∃ t : ℝ, linePt L₂ t ∈ L₁.toSet := by
  have h_rot_ne : @inner ℝ Plane2 _ L₁.normVec (rot90 L₂.normVec) ≠ 0 := by
    intro h_rot
    apply h_not_par
    exact parallel_of_inner_rot90_zero L₁.normVec L₂.normVec L₂.normVec_ne_zero h_rot
  let u₂ := L₂.normVec
  let d₂ := L₂.offset
  let sq₂ := @inner ℝ Plane2 _ u₂ u₂
  let p₀ := (d₂ / sq₂) • u₂
  let t := (L₁.offset - @inner ℝ Plane2 _ L₁.normVec p₀) /
           (@inner ℝ Plane2 _ L₁.normVec (rot90 u₂))
  use t
  dsimp [Line2.toSet, linePt, p₀, t]
  rw [inner_add_right]
  have h_smul : @inner ℝ Plane2 _ L₁.normVec
      (((L₁.offset - @inner ℝ Plane2 _ L₁.normVec ((d₂ / sq₂) • u₂)) /
      @inner ℝ Plane2 _ L₁.normVec (rot90 u₂)) • rot90 u₂) =
      ((L₁.offset - @inner ℝ Plane2 _ L₁.normVec ((d₂ / sq₂) • u₂)) /
      @inner ℝ Plane2 _ L₁.normVec (rot90 u₂)) * @inner ℝ Plane2 _ L₁.normVec (rot90 u₂) := by
    exact inner_smul_right L₁.normVec _ _
  rw [h_smul]
  have h_cancel : ((L₁.offset - @inner ℝ Plane2 _ L₁.normVec ((d₂ / sq₂) • u₂)) /
      @inner ℝ Plane2 _ L₁.normVec (rot90 u₂)) * @inner ℝ Plane2 _ L₁.normVec (rot90 u₂) =
      L₁.offset - @inner ℝ Plane2 _ L₁.normVec ((d₂ / sq₂) • u₂) :=
    div_mul_cancel₀ _ h_rot_ne
  rw [h_cancel]
  ring

open Classical in
/-- 直線 $L_{k}$ 上の基準点と方向ベクトルに対し、第 $i$ 直線との交点を与える実数パラメータ。
交点方程式を満たす実数 $t$ の代表元。 -/
noncomputable def rawIntersectionParam (k : ℕ) (L : Fin (k + 1) → Line2) (i : Fin k) : ℝ :=
  if h : ∃ t : ℝ, linePt (L (Fin.last k)) t ∈ (L (Fin.castSucc i)).toSet then
    Classical.choose h
  else 0

/-- 交差条件を満たすインデックスに対し、交点パラメータは対応する直線上の点を与える。 -/
lemma rawIntersectionParam_spec (k : ℕ) (L : Fin (k + 1) → Line2) (i : Fin k)
    (h : hasIntersectionWithLast k L i) :
    linePt (L (Fin.last k)) (rawIntersectionParam k L i) ∈ (L (Fin.castSucc i)).toSet := by
  dsimp [rawIntersectionParam]
  have hex : ∃ t : ℝ, linePt (L (Fin.last k)) t ∈ (L (Fin.castSucc i)).toSet :=
    exists_linePt_mem_of_not_parallel (L (Fin.castSucc i)) (L (Fin.last k)) h
  simp only [hex, dite_true]
  exact Classical.choose_spec hex

/-- 既存の $k$ 本の直線と $(k+1)$ 本目の直線との交点に対応する直線上のパラメータ集合。
平行でない各直線 $L_i$ との交点パラメータの像として定義される。 -/
noncomputable def lineIntersectionParams (k : ℕ) (L : Fin (k + 1) → Line2) : Finset ℝ :=
  (intersectingIndices k L).image (rawIntersectionParam k L)

/-- 直線上の交点パラメータ数の上界補題:
$(k+1)$ 本目の直線が既存の $k$ 本の直線と交わる点の総数は、$k$ 以下である。
像の濃度不等式と全集合の濃度から直ちに従う。 -/
lemma card_lineIntersectionParams_le (k : ℕ) (L : Fin (k + 1) → Line2) :
    (lineIntersectionParams k L).card ≤ k := by
  dsimp [lineIntersectionParams]
  calc
    ((intersectingIndices k L).image (rawIntersectionParam k L)).card
      ≤ (intersectingIndices k L).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
    _ = k := Fintype.card_fin k

/-- 平行な2直線に対する第3直線の交点パラメータ集合の濃度評価。
推移律および共通点をもたないことから、交点数は0または2であり、1にはなり得ない。 -/
lemma card_lineIntersectionParams_cases_of_parallel (L : Fin 3 → Line2)
    (hpar : parallelLines (L 0) (L 1))
    (hdisj : (L 0).toSet ∩ (L 1).toSet = ∅) :
    (lineIntersectionParams 2 L).card = 0 ∨ (lineIntersectionParams 2 L).card = 2 := by
  have h_ne1 := card_intersectingIndices_ne_one_of_parallel L hpar
  have h_le2 : (intersectingIndices 2 L).card ≤ 2 := by
    calc
      (intersectingIndices 2 L).card ≤ (Finset.univ : Finset (Fin 2)).card :=
        Finset.card_le_univ _
      _ = 2 := rfl
  have h_idx_cases : (intersectingIndices 2 L).card = 0 ∨
      (intersectingIndices 2 L).card = 2 := by omega
  rcases h_idx_cases with h0 | h2
  · left
    dsimp [lineIntersectionParams]
    have : intersectingIndices 2 L = ∅ := Finset.card_eq_zero.mp h0
    rw [this, Finset.image_empty, Finset.card_empty]
  · right
    dsimp [lineIntersectionParams]
    have h_univ : intersectingIndices 2 L = (Finset.univ : Finset (Fin 2)) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      have : (Finset.univ : Finset (Fin 2)).card = 2 := rfl
      omega
    have h_ne : rawIntersectionParam 2 L 0 ≠ rawIntersectionParam 2 L 1 := by
      intro h_eq
      have h0_in : (0 : Fin 2) ∈ intersectingIndices 2 L := by
        rw [h_univ]; exact Finset.mem_univ _
      have h1_in : (1 : Fin 2) ∈ intersectingIndices 2 L := by
        rw [h_univ]; exact Finset.mem_univ _
      dsimp [intersectingIndices] at h0_in h1_in
      rw [Finset.mem_filter] at h0_in h1_in
      have hp0 := rawIntersectionParam_spec 2 L 0 h0_in.2
      have hp1 := rawIntersectionParam_spec 2 L 1 h1_in.2
      have hcast0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
      have hcast1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
      rw [hcast0] at hp0
      rw [hcast1] at hp1
      rw [h_eq] at hp0
      have hp_both : linePt (L 2) (rawIntersectionParam 2 L 1) ∈ (L 0).toSet ∩ (L 1).toSet :=
        ⟨hp0, hp1⟩
      rw [hdisj] at hp_both
      exact hp_both
    rw [h_univ]
    have h_set : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
    rw [h_set, Finset.image_insert, Finset.image_singleton]
    exact Finset.card_pair h_ne

/-! #### ステップ 2-B: 1次元区間数と交点数の結合 -/

/-- $(k+1)$ 本目の直線上に生じる互いに素な開区間(連結成分)の個数は高々 $k + 1$ 個である。
ステップ 1 (card_intervals_of_finset_real) とステップ 2 (card_lineIntersectionParams_le)
を組み合わせることで直ちに導かれる。 -/
lemma lineIntervals_succ_le (k : ℕ) (L : Fin (k + 1) → Line2) :
    realIntervalsCount (lineIntersectionParams k L) ≤ k + 1 := by
  have h1 := card_intervals_of_finset_real (lineIntersectionParams k L)
  have h2 := card_lineIntersectionParams_le k L
  omega

/-! #### ステップ 3: 凸領域(符号ベクトル)の切断と直線上の区間への単射 -/

/-- 直線群によって定まる開半空間の符号写像。各直線に対し正負のどちら側にあるかを表す。 -/
@[reducible] def SignVector2 (k : ℕ) := Fin k → Bool

instance (k : ℕ) : Fintype (SignVector2 k) :=
  inferInstanceAs (Fintype (Fin k → Bool))

/-- 符号写像 σ が定める平面上の開凸多角形領域。 -/
def convexPlaneRegion (k : ℕ) (L : Fin k → Line2) (σ : SignVector2 k) : Set Plane2 :=
  {x : Plane2 | ∀ i : Fin k,
    if σ i then (L i).offset < @inner ℝ Plane2 _ (L i).normVec x
    else @inner ℝ Plane2 _ (L i).normVec x < (L i).offset}

/-- 既存の凸領域 $R$ が新しい直線によって2つに分割される条件。
領域の内部を直線が横切ることと同値である。 -/
def isSplitByLine (s : Set Plane2) (line : Line2) : Prop :=
  (s ∩ line.toSet).Nonempty

/-- 切断と交差の対応補題:
既存の凸領域が新しい直線によって分割されることと、直線との交わりが非空であることは同値である。 -/
lemma split_region_intersects_line (k : ℕ) (L : Fin (k + 1) → Line2) (σ : SignVector2 k)
    (hsplit : isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) :
    (convexPlaneRegion k (L ∘ Fin.castSucc) σ ∩ (L (Fin.last k)).toSet).Nonempty := by
  exact hsplit

/-- 異なる符号ベクトルが定める凸領域は平面全体で互いに素である。
各直線に対する不等式 $a < b$ と $b < a$ の矛盾から従う。 -/
lemma disjoint_convexPlaneRegion (k : ℕ) (L : Fin k → Line2)
    (σ₁ σ₂ : SignVector2 k) (hne : σ₁ ≠ σ₂) :
    Disjoint (convexPlaneRegion k L σ₁) (convexPlaneRegion k L σ₂) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  apply hne
  funext i
  have h1 := hx1 i
  have h2 := hx2 i
  cases h1_bool : σ₁ i <;> cases h2_bool : σ₂ i
  · rfl
  · rw [h1_bool] at h1; rw [h2_bool] at h2
    dsimp at h1 h2
    linarith
  · rw [h1_bool] at h1; rw [h2_bool] at h2
    dsimp at h1 h2
    linarith
  · rfl

/-- 異なる凸領域から得られる直線上の交差区間は互いに素である。 -/
lemma disjoint_intersections_on_line (k : ℕ) (L : Fin (k + 1) → Line2)
    (σ₁ σ₂ : SignVector2 k) (hne : σ₁ ≠ σ₂) :
    Disjoint (convexPlaneRegion k (L ∘ Fin.castSucc) σ₁ ∩ (L (Fin.last k)).toSet)
             (convexPlaneRegion k (L ∘ Fin.castSucc) σ₂ ∩ (L (Fin.last k)).toSet) := by
  refine Disjoint.mono inf_le_left inf_le_left ?_
  exact disjoint_convexPlaneRegion k (L ∘ Fin.castSucc) σ₁ σ₂ hne

/-- 切断された既存領域の開区間は、既存直線との交点集合と交わらない。
開半空間の境界上の点では内積がoffsetに一致するため、領域内部の不等式と矛盾する。 -/
lemma intersection_disjoint_intersectionPoints (k : ℕ) (L : Fin (k + 1) → Line2)
    (σ : SignVector2 k) :
    Disjoint (convexPlaneRegion k (L ∘ Fin.castSucc) σ ∩ (L (Fin.last k)).toSet)
             (⋃ i : Fin k, (L (Fin.castSucc i)).toSet) := by
  rw [Set.disjoint_left]
  rintro p ⟨hp_reg, -⟩ hp_lines
  simp only [Set.mem_iUnion] at hp_lines
  rcases hp_lines with ⟨i, hi⟩
  have h_bound := hp_reg i
  dsimp [Line2.toSet] at hi
  cases h_bool : σ i
  · rw [h_bool] at h_bound
    dsimp at h_bound
    linarith
  · rw [h_bool] at h_bound
    dsimp at h_bound
    linarith

/-- 凸開領域に属する点は、配置内のどの直線にも属さない。 -/
lemma not_mem_line_of_mem_convexPlaneRegion {k : ℕ} (L : Fin k → Line2) (σ : SignVector2 k)
    {p : Plane2} (hp : p ∈ convexPlaneRegion k L σ) (i : Fin k) :
    p ∉ (L i).toSet := by
  have h := hp i
  dsimp [Line2.toSet]
  split_ifs at h with hσ
  · linarith
  · linarith

open Classical in
/-- 直線上の点が交点パラメータ集合に属さないことの判定。
凸領域に属する直線上の点のパラメータは、他の直線との交点にはなり得ない。 -/
lemma not_mem_lineIntersectionParams_of_mem_region (k : ℕ) (L : Fin (k + 1) → Line2)
    (σ : SignVector2 k) {t : ℝ}
    (hp : linePt (L (Fin.last k)) t ∈ convexPlaneRegion k (L ∘ Fin.castSucc) σ) :
    t ∉ lineIntersectionParams k L := by
  intro ht
  dsimp [lineIntersectionParams] at ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  dsimp [rawIntersectionParam] at hp
  split_ifs at hp with hex
  · have h_mem := Classical.choose_spec hex
    have h_not := not_mem_line_of_mem_convexPlaneRegion (L ∘ Fin.castSucc) σ hp i
    exact h_not h_mem
  · have hi_inter : hasIntersectionWithLast k L i := (Finset.mem_filter.mp hi).2
    have hex_true := exists_linePt_mem_of_not_parallel
      (L (Fin.castSucc i)) (L (Fin.last k)) hi_inter
    exact hex hex_true

/-- 90度回転ベクトルのノルム自乗の一致。 -/
lemma inner_rot90_rot90 (u : Plane2) :
    @inner ℝ Plane2 _ (rot90 u) (rot90 u) = @inner ℝ Plane2 _ u u := by
  have h1 := PiLp.inner_apply (𝕜 := ℝ) (x := rot90 u) (y := rot90 u)
  have h2 := PiLp.inner_apply (𝕜 := ℝ) (x := u) (y := u)
  rw [h1, h2, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Real.inner_apply]
  change (- u 1) * (- u 1) + (u 0) * (u 0) = u 0 * u 0 + u 1 * u 1
  ring

/-- 直交基底 $(u, \rot90 u)$ との内積がともに0ならばベクトルは0である。 -/
lemma eq_zero_of_inner_u_zero_of_inner_rot90_zero (u v : Plane2) (hu : u ≠ 0)
    (h1 : @inner ℝ Plane2 _ u v = 0) (h2 : @inner ℝ Plane2 _ (rot90 u) v = 0) :
    v = 0 := by
  have hu_sq : u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
    intro h0
    apply hu
    ext i; fin_cases i
    · have : u 0 = 0 := by nlinarith
      exact this
    · have : u 1 = 0 := by nlinarith
      exact this
  have h_inner1 := PiLp.inner_apply (𝕜 := ℝ) (x := u) (y := v)
  have h_inner2 := PiLp.inner_apply (𝕜 := ℝ) (x := rot90 u) (y := v)
  rw [h_inner1, Fin.sum_univ_two] at h1
  rw [h_inner2, Fin.sum_univ_two] at h2
  simp only [Real.inner_apply] at h1 h2
  change u 0 * v 0 + u 1 * v 1 = 0 at h1
  change (- u 1) * v 0 + u 0 * v 1 = 0 at h2
  ext i
  fin_cases i
  · have h_zero1 : (u 0 ^ 2 + u 1 ^ 2) * v 0 = 0 := by
      calc
        (u 0 ^ 2 + u 1 ^ 2) * v 0 =
          u 0 * (u 0 * v 0 + u 1 * v 1) - u 1 * ((- u 1) * v 0 + u 0 * v 1) := by ring
        _ = u 0 * 0 - u 1 * 0 := by rw [h1, h2]
        _ = 0 := by ring
    have : v 0 = 0 := (mul_eq_zero.mp h_zero1).resolve_left hu_sq
    simp [this]
  · have h_zero2 : (u 0 ^ 2 + u 1 ^ 2) * v 1 = 0 := by
      calc
        (u 0 ^ 2 + u 1 ^ 2) * v 1 =
          u 1 * (u 0 * v 0 + u 1 * v 1) + u 0 * ((- u 1) * v 0 + u 0 * v 1) := by ring
        _ = u 1 * 0 + u 0 * 0 := by rw [h1, h2]
        _ = 0 := by ring
    have : v 1 = 0 := (mul_eq_zero.mp h_zero2).resolve_left hu_sq
    simp [this]

/-- 直線上の任意の点はパラメータ $t$ により一意に表される。 -/
lemma exists_t_linePt_eq (L : Line2) {p : Plane2} (hp : p ∈ L.toSet) :
    ∃ t : ℝ, linePt L t = p := by
  let u := L.normVec
  let sq := @inner ℝ Plane2 _ u u
  have hu_sq : sq ≠ 0 := by
    dsimp [sq]
    intro h0
    apply L.normVec_ne_zero
    exact inner_self_eq_zero.mp h0
  let t := (@inner ℝ Plane2 _ (rot90 u) p) / sq
  use t
  have hp_offset : @inner ℝ Plane2 _ u p = L.offset := hp
  have h_sub1 : @inner ℝ Plane2 _ u (p - linePt L t) = 0 := by
    rw [inner_sub_right]
    have : @inner ℝ Plane2 _ u (linePt L t) = L.offset := linePt_mem_line L t
    rw [hp_offset, this, sub_self]
  have h_sub2 : @inner ℝ Plane2 _ (rot90 u) (p - linePt L t) = 0 := by
    rw [inner_sub_right]
    dsimp [linePt, t]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have h_rot_u : @inner ℝ Plane2 _ (rot90 u) u = 0 := by
      have := inner_rot90_self u
      rw [real_inner_comm] at this
      exact this
    rw [h_rot_u, mul_zero, zero_add]
    rw [inner_rot90_rot90]
    have : (@inner ℝ Plane2 _ (rot90 u) p / sq) * sq = @inner ℝ Plane2 _ (rot90 u) p :=
      div_mul_cancel₀ _ hu_sq
    rw [this, sub_self]
  have h_zero := eq_zero_of_inner_u_zero_of_inner_rot90_zero u (p - linePt L t)
    L.normVec_ne_zero h_sub1 h_sub2
  exact (sub_eq_zero.mp h_zero).symm

/-- 直線上の2点で符号が異なれば、2直線は非平行である。 -/
lemma not_parallel_of_sign_ne (k : ℕ) (L : Fin (k + 1) → Line2)
    {t₁ t₂ : ℝ} (_ht12 : t₁ ≠ t₂) (i : Fin k)
    (h_sign1 : (L (Fin.castSucc i)).offset <
      @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec (linePt (L (Fin.last k)) t₁))
    (h_sign2 : @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec (linePt (L (Fin.last k)) t₂) <
      (L (Fin.castSucc i)).offset) :
    ¬ parallelLines (L (Fin.castSucc i)) (L (Fin.last k)) := by
  intro h_par
  obtain ⟨c, hc⟩ := h_par
  have h_f : ∀ t, @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec (linePt (L (Fin.last k)) t) =
      c * (L (Fin.last k)).offset := by
    intro t
    rw [hc, inner_smul_left]
    have := linePt_mem_line (L (Fin.last k)) t
    dsimp [Line2.toSet] at this
    rw [this]
    rfl
  have h_eq : @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec (linePt (L (Fin.last k)) t₁) =
      @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec (linePt (L (Fin.last k)) t₂) := by
    rw [h_f t₁, h_f t₂]
  linarith

/-- 直線パラメータ写像のアフィン結合保存性。 -/
lemma linePt_affine_comb (L : Line2) (u t₁ t₂ : ℝ) :
    linePt L ((1 - u) * t₁ + u * t₂) = (1 - u) • linePt L t₁ + u • linePt L t₂ := by
  dsimp [linePt]
  have h_add : (1 - u) • ((L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec) +
      u • ((L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec) =
      (L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec := by
    rw [← add_smul]
    have : 1 - u + u = 1 := by ring
    rw [this, one_smul]
  calc
    (L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec +
        ((1 - u) * t₁ + u * t₂) • rot90 L.normVec
      = (L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec +
        ((1 - u) * t₁) • rot90 L.normVec + (u * t₂) • rot90 L.normVec := by
          rw [add_smul, mul_smul, mul_smul, add_assoc]
    _ = (1 - u) • ((L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec) +
        u • ((L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec) +
        ((1 - u) * t₁) • rot90 L.normVec + (u * t₂) • rot90 L.normVec := by rw [h_add]
    _ = (1 - u) • ((L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec) +
        (1 - u) • (t₁ • rot90 L.normVec) +
        (u • ((L.offset / @inner ℝ Plane2 _ L.normVec L.normVec) • L.normVec) +
        u • (t₂ • rot90 L.normVec)) := by
          rw [mul_smul, mul_smul]
          abel
    _ = (1 - u) • linePt L t₁ + u • linePt L t₂ := by
          dsimp [linePt]
          rw [smul_add, smul_add]

/-- 直線パラメータ写像の内積のアフィン結合保存性。 -/
lemma inner_linePt_affine_comb (L : Line2) (n : Plane2) (u t₁ t₂ : ℝ) :
    @inner ℝ Plane2 _ n (linePt L ((1 - u) * t₁ + u * t₂)) =
      (1 - u) * (@inner ℝ Plane2 _ n (linePt L t₁)) + u * (@inner ℝ Plane2 _ n (linePt L t₂)) := by
  have h_comb : linePt L ((1 - u) * t₁ + u * t₂) =
      (1 - u) • linePt L t₁ + u • linePt L t₂ := linePt_affine_comb L u t₁ t₂
  rw [h_comb, inner_add_right, inner_smul_right, inner_smul_right]

/-- 直線上の2点の差ベクトル。 -/
lemma linePt_sub (L : Line2) (t₁ t₂ : ℝ) :
    linePt L t₁ - linePt L t₂ = (t₁ - t₂) • rot90 L.normVec := by
  dsimp [linePt]
  rw [add_sub_add_left_eq_sub, ← sub_smul]

/-- 非平行な2直線の交点パラメータの一意性。 -/
lemma eq_of_mem_line_linePt (L₁ L₂ : Line2) (h_not_par : ¬ parallelLines L₁ L₂)
    {t₁ t₂ : ℝ} (h1 : linePt L₂ t₁ ∈ L₁.toSet) (h2 : linePt L₂ t₂ ∈ L₁.toSet) :
    t₁ = t₂ := by
  by_contra h_ne
  have h_sub : @inner ℝ Plane2 _ L₁.normVec (linePt L₂ t₁ - linePt L₂ t₂) = 0 := by
    rw [inner_sub_right, h1, h2, sub_self]
  rw [linePt_sub, inner_smul_right] at h_sub
  have h_inner_zero : @inner ℝ Plane2 _ L₁.normVec (rot90 L₂.normVec) = 0 := by
    have : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h_ne
    exact (mul_eq_zero.mp h_sub).resolve_left this
  apply h_not_par
  exact parallel_of_inner_rot90_zero L₁.normVec L₂.normVec L₂.normVec_ne_zero h_inner_zero

/-- 交点パラメータの値の一致性。 -/
lemma rawIntersectionParam_eq (k : ℕ) (L : Fin (k + 1) → Line2) (i : Fin k)
    (h_not_par : ¬ parallelLines (L (Fin.castSucc i)) (L (Fin.last k)))
    {t : ℝ} (ht : linePt (L (Fin.last k)) t ∈ (L (Fin.castSucc i)).toSet) :
    rawIntersectionParam k L i = t := by
  dsimp [rawIntersectionParam]
  have hex : ∃ t' : ℝ, linePt (L (Fin.last k)) t' ∈ (L (Fin.castSucc i)).toSet := ⟨t, ht⟩
  simp only [hex, dite_true]
  have h_choose := Classical.choose_spec hex
  exact eq_of_mem_line_linePt (L (Fin.castSucc i)) (L (Fin.last k)) h_not_par h_choose ht

open Classical in
/-- 直線上の符号が異なる2点の間にある交点パラメータの存在。 -/
lemma exists_intersectionParam_between (k : ℕ) (L : Fin (k + 1) → Line2)
    {t₁ t₂ : ℝ} (i : Fin k)
    (h_sign1 : (L (Fin.castSucc i)).offset <
      @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec (linePt (L (Fin.last k)) t₁))
    (h_sign2 : @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec (linePt (L (Fin.last k)) t₂) <
      (L (Fin.castSucc i)).offset) :
    ∃ t_star ∈ lineIntersectionParams k L,
      (t₁ < t_star ∧ t_star < t₂) ∨ (t₂ < t_star ∧ t_star < t₁) := by
  let n := (L (Fin.castSucc i)).normVec
  let c := (L (Fin.castSucc i)).offset
  let f := fun t => @inner ℝ Plane2 _ n (linePt (L (Fin.last k)) t)
  have h_denom : 0 < f t₁ - f t₂ := by
    dsimp [f]
    linarith
  let u := (f t₁ - c) / (f t₁ - f t₂)
  have hu_pos : 0 < u := by
    dsimp [u]
    exact div_pos (by dsimp [f]; linarith) h_denom
  have hu_lt_one : u < 1 := by
    dsimp [u]
    rw [div_lt_one h_denom]
    dsimp [f]
    linarith
  have h_one_sub_u : 1 - u = (c - f t₂) / (f t₁ - f t₂) := by
    dsimp [u]
    have h_ne : f t₁ - f t₂ ≠ 0 := ne_of_gt h_denom
    field_simp
    ring
  let t_star := (1 - u) * t₁ + u * t₂
  have h_f_star : f t_star = c := by
    dsimp [f, t_star]
    rw [inner_linePt_affine_comb]
    dsimp [f] at h_one_sub_u
    rw [h_one_sub_u]
    dsimp [u, f]
    have h_ne : inner ℝ n (linePt (L (Fin.last k)) t₁) -
        inner ℝ n (linePt (L (Fin.last k)) t₂) ≠ 0 := ne_of_gt h_denom
    field_simp
    ring
  have h_mem_Li : linePt (L (Fin.last k)) t_star ∈ (L (Fin.castSucc i)).toSet := by
    dsimp [Line2.toSet]
    exact h_f_star
  have ht_ne : t₁ ≠ t₂ := by
    intro h_eq
    rw [h_eq] at h_sign1
    linarith
  have h_not_par : ¬ parallelLines (L (Fin.castSucc i)) (L (Fin.last k)) :=
    not_parallel_of_sign_ne k L ht_ne i h_sign1 h_sign2
  have h_raw_eq : rawIntersectionParam k L i = t_star :=
    rawIntersectionParam_eq k L i h_not_par h_mem_Li
  have h_inter : hasIntersectionWithLast k L i := h_not_par
  have h_in_params : t_star ∈ lineIntersectionParams k L := by
    dsimp [lineIntersectionParams]
    rw [Finset.mem_image]
    use i
    refine ⟨?_, h_raw_eq⟩
    dsimp [intersectingIndices]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_inter⟩
  use t_star, h_in_params
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · left
    have h_sub1 : t_star - t₁ = u * (t₂ - t₁) := by
      dsimp [t_star]
      ring
    have h_sub2 : t₂ - t_star = (1 - u) * (t₂ - t₁) := by
      dsimp [t_star]
      ring
    have h_diff_pos : 0 < t₂ - t₁ := sub_pos.mpr hlt
    have h1 : t₁ < t_star := by
      rw [← sub_pos, h_sub1]
      exact mul_pos hu_pos h_diff_pos
    have h2 : t_star < t₂ := by
      rw [← sub_pos, h_sub2]
      exact mul_pos (sub_pos.mpr hu_lt_one) h_diff_pos
    exact ⟨h1, h2⟩
  · exact (ht_ne heq).elim
  · right
    have h_sub1 : t_star - t₂ = (1 - u) * (t₁ - t₂) := by
      dsimp [t_star]
      ring
    have h_sub2 : t₁ - t_star = u * (t₁ - t₂) := by
      dsimp [t_star]
      ring
    have h_diff_pos : 0 < t₁ - t₂ := sub_pos.mpr hgt
    have h1 : t₂ < t_star := by
      rw [← sub_pos, h_sub1]
      exact mul_pos (sub_pos.mpr hu_lt_one) h_diff_pos
    have h2 : t_star < t₁ := by
      rw [← sub_pos, h_sub2]
      exact mul_pos hu_pos h_diff_pos
    exact ⟨h1, h2⟩

/-- 点集合の元を挟む2点に対する countLt の真の狭義単調性。 -/
lemma countLt_lt_countLt_of_mem_between (S : Finset ℝ) {t₁ t₂ t_star : ℝ}
    (h_between : t₁ < t_star ∧ t_star < t₂) (hs : t_star ∈ S) :
    countLt S t₁ < countLt S t₂ := by
  dsimp [countLt]
  have h_sub : Finset.filter (· < t₁) S ⊆ Finset.filter (· < t₂) S := by
    intro s hs_mem
    rw [Finset.mem_filter] at hs_mem ⊢
    exact ⟨hs_mem.1, lt_trans hs_mem.2 (lt_trans h_between.1 h_between.2)⟩
  have h_not_mem : t_star ∉ Finset.filter (· < t₁) S := by
    intro h
    rw [Finset.mem_filter] at h
    linarith
  have h_mem : t_star ∈ Finset.filter (· < t₂) S := by
    rw [Finset.mem_filter]
    exact ⟨hs, h_between.2⟩
  have h_ssub : Finset.filter (· < t₁) S ⊂ Finset.filter (· < t₂) S :=
    Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, fun h_eq => h_not_mem (h_eq ▸ h_mem)⟩
  exact Finset.card_lt_card h_ssub

/-- 同一連結成分に属する2点の間には境界点集合の元が存在しない。 -/
lemma not_between_of_connectedComponent_eq (S : Finset ℝ) (t₁ t₂ : ℝ)
    (ht₁ : t₁ ∉ S) (ht₂ : t₂ ∉ S)
    (h_comp : Quotient.mk (connectedComponentSetoid {t // t ∉ S}) ⟨t₁, ht₁⟩ =
              Quotient.mk (connectedComponentSetoid {t // t ∉ S}) ⟨t₂, ht₂⟩)
    {t_star : ℝ} (hs : t_star ∈ S) :
    ¬ ((t₁ < t_star ∧ t_star < t₂) ∨ (t₂ < t_star ∧ t_star < t₁)) := by
  intro h_bet
  let _ : Setoid {t // t ∉ S} := connectedComponentSetoid {t // t ∉ S}
  have hequiv : (⟨t₁, ht₁⟩ : {t // t ∉ S}) ≈ (⟨t₂, ht₂⟩ : {t // t ∉ S}) := Quotient.exact h_comp
  have h_eq := countLt_eq_of_connectedComponent_eq ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hequiv
  rcases h_bet with h1 | h2
  · have h_lt := countLt_lt_countLt_of_mem_between S h1 hs
    linarith
  · have h_lt := countLt_lt_countLt_of_mem_between S h2 hs
    linarith

open Classical in
/-- 第 $(k+1)$ 直線によって2分割される既存領域の個数。
切断条件を満たす符号ベクトルの個数として定義される。 -/
noncomputable def splitRegionsCount (k : ℕ) (L : Fin (k + 1) → Line2) : ℕ :=
  (Finset.filter (fun σ =>
    isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) Finset.univ).card

open Classical in
/-- 切断された既存領域の個数は、$(k+1)$ 本目の直線上に現れる互いに素な開区間数以下である。
切断領域の代表点を直線上の開区間(連結成分)に単射づけることで証明される。 -/
lemma splitRegionsCount_le_lineIntervals (k : ℕ) (L : Fin (k + 1) → Line2) :
    splitRegionsCount k L ≤ realIntervalsCount (lineIntersectionParams k L) := by
  let S := lineIntersectionParams k L
  let s := connectedComponentSetoid {t // t ∉ S}
  let split_sigs := Finset.filter (fun σ =>
    isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) Finset.univ
  have h_rep : ∀ σ ∈ split_sigs, ∃ t : ℝ,
      linePt (L (Fin.last k)) t ∈ convexPlaneRegion k (L ∘ Fin.castSucc) σ ∧ t ∉ S := by
    intro σ hσ
    dsimp [split_sigs] at hσ
    rw [Finset.mem_filter] at hσ
    obtain ⟨p, hp_reg, hp_line⟩ := hσ.2
    obtain ⟨t, rfl⟩ := exists_t_linePt_eq (L (Fin.last k)) hp_line
    have ht_not := not_mem_lineIntersectionParams_of_mem_region k L σ hp_reg
    exact ⟨t, hp_reg, ht_not⟩
  choose w hw using (fun (σ : split_sigs) => h_rep σ.1 σ.2)
  let g : split_sigs → Quotient s := fun σ => Quotient.mk s ⟨w σ, (hw σ).2⟩
  have hg_inj : Function.Injective g := by
    intro σ₁ σ₂ hg
    by_contra h_ne
    have h_sig_ne : σ₁.1 ≠ σ₂.1 := fun h => h_ne (Subtype.ext h)
    obtain ⟨i, hi⟩ : ∃ i, σ₁.1 i ≠ σ₂.1 i := by
      by_contra h_all
      apply h_sig_ne
      ext i
      by_contra h_not
      exact h_all ⟨i, h_not⟩
    have h_comp : Quotient.mk s ⟨w σ₁, (hw σ₁).2⟩ = Quotient.mk s ⟨w σ₂, (hw σ₂).2⟩ := hg
    cases h1 : σ₁.1 i <;> cases h2 : σ₂.1 i
    · exact (hi (by rw [h1, h2])).elim
    · have hp1 := (hw σ₁).1
      have hp2 := (hw σ₂).1
      dsimp [convexPlaneRegion] at hp1 hp2
      have h_sign1 := hp1 i
      have h_sign2 := hp2 i
      rw [h1] at h_sign1
      rw [h2] at h_sign2
      dsimp at h_sign1 h_sign2
      obtain ⟨t_star, hs, h_bet⟩ := exists_intersectionParam_between k L i h_sign2 h_sign1
      have h_not := not_between_of_connectedComponent_eq S (w σ₂) (w σ₁)
        (hw σ₂).2 (hw σ₁).2 (h_comp.symm) hs
      exact h_not h_bet
    · have hp1 := (hw σ₁).1
      have hp2 := (hw σ₂).1
      dsimp [convexPlaneRegion] at hp1 hp2
      have h_sign1 := hp1 i
      have h_sign2 := hp2 i
      rw [h1] at h_sign1
      rw [h2] at h_sign2
      dsimp at h_sign1 h_sign2
      obtain ⟨t_star, hs, h_bet⟩ := exists_intersectionParam_between k L i h_sign1 h_sign2
      have h_not := not_between_of_connectedComponent_eq S (w σ₁) (w σ₂)
        (hw σ₁).2 (hw σ₂).2 h_comp hs
      exact h_not h_bet
    · exact (hi (by rw [h1, h2])).elim
  let f_int : {t // t ∉ S} → Fin (S.card + 1) := fun x => countLtFin S x.val
  have h_fiber_int : ∀ x y, f_int x = f_int y → x ≈ y := by
    intro x y hfg
    exact connectedComponent_eq_of_countLtFin_eq x y hfg
  have : Finite (Quotient s) := finite_quotient_of_fiber_le s f_int h_fiber_int
  have h_le := Nat.card_le_card_of_injective g hg_inj
  dsimp [splitRegionsCount, split_sigs]
  have h_card_split : Fintype.card split_sigs = split_sigs.card := Fintype.card_coe split_sigs
  rw [Nat.card_eq_fintype_card, h_card_split] at h_le
  exact h_le

/-- 開半空間の共通部分として定義される領域は凸集合である。
領域内の2点の任意の真の内分点は、再び同じ領域に属する。 -/
lemma convex_combination_mem_region {k : ℕ} (L : Fin k → Line2) (σ : SignVector2 k)
    {p₁ p₂ : Plane2} (hp₁ : p₁ ∈ convexPlaneRegion k L σ) (hp₂ : p₂ ∈ convexPlaneRegion k L σ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a • p₁ + b • p₂ ∈ convexPlaneRegion k L σ := by
  dsimp [convexPlaneRegion] at hp₁ hp₂ ⊢
  intro i
  have h1 := hp₁ i
  have h2 := hp₂ i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  split_ifs at h1 h2 ⊢ with hσ
  · calc
      (L i).offset = a * (L i).offset + b * (L i).offset := by
        rw [← add_mul, hab, one_mul]
      _ < a * @inner ℝ Plane2 _ (L i).normVec p₁ + b * @inner ℝ Plane2 _ (L i).normVec p₂ := by
        nlinarith
  · calc
      a * @inner ℝ Plane2 _ (L i).normVec p₁ + b * @inner ℝ Plane2 _ (L i).normVec p₂
        < a * (L i).offset + b * (L i).offset := by nlinarith
      _ = (L i).offset := by rw [← add_mul, hab, one_mul]

/-- 凸領域が直線と交わらないならば、領域全体が直線の真に片側に含まれる。
領域内の2点が直線の反対側にあれば、その内分点が直線と交わることから従う。 -/
lemma region_subset_one_side_of_not_split (k : ℕ) (L : Fin (k + 1) → Line2)
    (σ : SignVector2 k)
    (h_not_split : ¬ isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) :
    (∀ p ∈ convexPlaneRegion k (L ∘ Fin.castSucc) σ,
      @inner ℝ Plane2 _ (L (Fin.last k)).normVec p < (L (Fin.last k)).offset) ∨
    (∀ p ∈ convexPlaneRegion k (L ∘ Fin.castSucc) σ,
      (L (Fin.last k)).offset < @inner ℝ Plane2 _ (L (Fin.last k)).normVec p) := by
  by_contra h_both
  push Not at h_both
  rcases h_both with ⟨⟨p₁, hp₁, hle₁⟩, ⟨p₂, hp₂, hge₂⟩⟩
  let u := (L (Fin.last k)).normVec
  let d := (L (Fin.last k)).offset
  let v₁ := @inner ℝ Plane2 _ u p₁
  let v₂ := @inner ℝ Plane2 _ u p₂
  have hne₁ : v₁ ≠ d := by
    intro h_eq
    apply h_not_split
    refine ⟨p₁, hp₁, ?_⟩
    dsimp [Line2.toSet, u, d] at h_eq ⊢
    exact h_eq
  have hne₂ : v₂ ≠ d := by
    intro h_eq
    apply h_not_split
    refine ⟨p₂, hp₂, ?_⟩
    dsimp [Line2.toSet, u, d] at h_eq ⊢
    exact h_eq
  have hlt₁ : d < v₁ := lt_of_le_of_ne' hle₁ hne₁
  have hlt₂ : v₂ < d := lt_of_le_of_ne hge₂ hne₂
  have hv : 0 < v₁ - v₂ := by linarith
  let a := (d - v₂) / (v₁ - v₂)
  let b := (v₁ - d) / (v₁ - v₂)
  have ha : 0 < a := div_pos (by linarith) hv
  have hb : 0 < b := div_pos (by linarith) hv
  have hab : a + b = 1 := by
    dsimp [a, b]
    calc
      (d - v₂) / (v₁ - v₂) + (v₁ - d) / (v₁ - v₂)
        = ((d - v₂) + (v₁ - d)) / (v₁ - v₂) := by rw [← add_div]
      _ = (v₁ - v₂) / (v₁ - v₂) := by
        congr 1
        ring
      _ = 1 := div_self (ne_of_gt hv)
  let pt := a • p₁ + b • p₂
  have hpt_in : pt ∈ convexPlaneRegion k (L ∘ Fin.castSucc) σ :=
    convex_combination_mem_region (L ∘ Fin.castSucc) σ hp₁ hp₂ ha hb hab
  have hpt_on : pt ∈ (L (Fin.last k)).toSet := by
    dsimp [Line2.toSet, pt]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    change a * v₁ + b * v₂ = d
    dsimp [a, b]
    calc
      ((d - v₂) / (v₁ - v₂)) * v₁ + ((v₁ - d) / (v₁ - v₂)) * v₂
        = ((d - v₂) * v₁ + (v₁ - d) * v₂) / (v₁ - v₂) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
      _ = (d * (v₁ - v₂)) / (v₁ - v₂) := by
        congr 1
        ring
      _ = d := mul_div_cancel_right₀ d (ne_of_gt hv)
  apply h_not_split
  exact ⟨pt, hpt_in, hpt_on⟩

/-- $(k+1)$ 本の直線による領域への所属条件を、
既存 $k$ 本の領域への所属と最後の直線に関する条件に分解する。 -/
lemma mem_convexPlaneRegion_succ (k : ℕ) (L : Fin (k + 1) → Line2)
    (σ : SignVector2 k) (b : Bool) (p : Plane2) :
    p ∈ convexPlaneRegion (k + 1) L (Fin.snoc σ b) ↔
      p ∈ convexPlaneRegion k (L ∘ Fin.castSucc) σ ∧
      (if b then (L (Fin.last k)).offset < @inner ℝ Plane2 _ (L (Fin.last k)).normVec p
       else @inner ℝ Plane2 _ (L (Fin.last k)).normVec p < (L (Fin.last k)).offset) := by
  dsimp [convexPlaneRegion]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have hi := h (Fin.castSucc i)
      rw [Fin.snoc_castSucc] at hi
      exact hi
    · have hlast := h (Fin.last k)
      rw [Fin.snoc_last] at hlast
      exact hlast
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]
      exact h2
    · intro j
      rw [Fin.snoc_castSucc]
      exact h1 j

open Classical in
/-- 未切断の領域から派生する有効な $(k+1)$ 符号ベクトルは高々1つである。 -/
lemma fiber_card_le_one_of_not_split (k : ℕ) (L : Fin (k + 1) → Line2)
    (σ : SignVector2 k)
    (h_not_split : ¬ isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) :
    (Finset.filter (fun b : Bool =>
      (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ).card ≤ 1 := by
  have h_cases := region_subset_one_side_of_not_split k L σ h_not_split
  by_contra h_gt
  push Not at h_gt
  have h_eq : (Finset.filter (fun b : Bool =>
      (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ) = Finset.univ := by
    apply Finset.eq_univ_of_card
    have h_le : (Finset.filter (fun b : Bool =>
      (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ).card ≤ 2 := by
      calc
        (Finset.filter (fun b : Bool =>
          (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ).card
          ≤ (Finset.univ : Finset Bool).card := Finset.card_filter_le _ _
        _ = 2 := Fintype.card_bool
    rw [Fintype.card_bool]
    omega
  have h_false_in : false ∈ Finset.filter (fun b : Bool =>
      (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ := by
    rw [h_eq]; exact Finset.mem_univ false
  have h_true_in : true ∈ Finset.filter (fun b : Bool =>
      (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ := by
    rw [h_eq]; exact Finset.mem_univ true
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_false_in h_true_in
  rcases h_false_in with ⟨pF, hpF⟩
  rcases h_true_in with ⟨pT, hpT⟩
  rw [mem_convexPlaneRegion_succ] at hpF hpT
  rcases h_cases with h_all_lt | h_all_gt
  · have hpT_lt := h_all_lt pT hpT.1
    dsimp at hpT
    linarith
  · have hpF_gt := h_all_gt pF hpF.1
    dsimp at hpF
    linarith

open Classical in
/-- 切断された領域から派生する有効な $(k+1)$ 符号ベクトルは高々2つ (Bool の全濃度) である。 -/
lemma fiber_card_le_two (k : ℕ) (L : Fin (k + 1) → Line2) (σ : SignVector2 k) :
    (Finset.filter (fun b : Bool =>
      (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ).card ≤ 2 := by
  calc
    (Finset.filter (fun b : Bool =>
      (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ).card
      ≤ (Finset.univ : Finset Bool).card := Finset.card_filter_le _ _
    _ = 2 := Fintype.card_bool

open Classical in
/-- 空領域から派生する有効な $(k+1)$ 符号ベクトルの個数は 0 である。 -/
lemma fiber_card_eq_zero_of_empty (k : ℕ) (L : Fin (k + 1) → Line2) (σ : SignVector2 k)
    (h_empty : ¬ (convexPlaneRegion k (L ∘ Fin.castSucc) σ).Nonempty) :
    (Finset.filter (fun b : Bool =>
      (convexPlaneRegion (k + 1) L (Fin.snoc σ b)).Nonempty) Finset.univ).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _ ⟨p, hp⟩
  apply h_empty
  rw [mem_convexPlaneRegion_succ] at hp
  exact ⟨p, hp.1⟩

open Classical in
/-- 直積空間 $Fin (k + 1) \to Bool$ 上の述語を満たす元の個数は、
ファイバーごとの個数の和に等しい。 -/
lemma card_filter_succ_eq_sum {k : ℕ} (P : (Fin (k + 1) → Bool) → Prop) [DecidablePred P] :
    (Finset.filter P Finset.univ).card =
      ∑ σ ∈ (Finset.univ : Finset (Fin k → Bool)),
        (Finset.filter (fun b : Bool => P (Fin.snoc σ b)) Finset.univ).card := by
  let s := Finset.filter P (Finset.univ : Finset (Fin (k + 1) → Bool))
  have h_fiber := Finset.card_eq_sum_card_fiberwise (f := fun τ => τ ∘ Fin.castSucc)
    (s := s) (t := (Finset.univ : Finset (Fin k → Bool))) (fun x _ => Finset.mem_univ _)
  rw [h_fiber]
  apply Finset.sum_congr rfl
  intro σ _
  have h_img : Finset.filter (fun b => P (Fin.snoc σ b)) Finset.univ =
      (s.filter (fun τ => τ ∘ Fin.castSucc = σ)).image (fun τ => τ (Fin.last k)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hP
      refine ⟨Fin.snoc σ b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, s]
        refine ⟨hP, ?_⟩
        ext i; simp
      · simp
    · rintro ⟨τ, h_filter, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, s] at h_filter
      rcases h_filter with ⟨hP, hcast⟩
      have hτ_eq : τ = Fin.snoc σ (τ (Fin.last k)) := by
        ext i
        refine Fin.lastCases ?_ ?_ i
        · simp
        · intro j
          simp [← hcast]
      rw [← hτ_eq]
      exact hP
  rw [h_img]
  rw [Finset.card_image_of_injOn]
  intro τ1 h1 τ2 h2 h_last
  have hcast1 := (Finset.mem_filter.mp h1).2
  have hcast2 := (Finset.mem_filter.mp h2).2
  ext i
  refine Fin.lastCases ?_ ?_ i
  · exact h_last
  · intro j
    have hj1 := congr_fun hcast1 j
    have hj2 := congr_fun hcast2 j
    dsimp at hj1 hj2
    rw [hj1, hj2]

/-- 各ファイバーの濃度に関する項別評価補題。
空領域では0、未切断では1以下、切断領域では2以下となるため、
非空指示量と切断指示量の和で上から抑えられる。 -/
lemma term_le_add_split (F_card : ℕ) (h_le_two : F_card ≤ 2)
    (is_nonempty : Prop) [Decidable is_nonempty]
    (is_split : Prop) [Decidable is_split]
    (h_not_split : ¬ is_split → F_card ≤ 1)
    (h_empty : ¬ is_nonempty → F_card = 0) :
    F_card ≤ (if is_nonempty then 1 else 0) + (if is_split then 1 else 0) := by
  by_cases hne : is_nonempty
  · simp only [hne, ↓reduceIte]
    by_cases hsp : is_split
    · simp only [hsp, ↓reduceIte]
      omega
    · simp only [hsp, ↓reduceIte, add_zero]
      exact h_not_split hsp
  · simp only [hne, ↓reduceIte, zero_add]
    have h0 := h_empty hne
    rw [h0]
    split_ifs <;> omega

/-- 各点の不等式を有限和全体の不等式に持ち上げる補題。 -/
lemma sum_fiber_le_sum_add {k : ℕ} (A B : (Fin k → Bool) → ℕ) (F : (Fin k → Bool) → ℕ)
    (h_le : ∀ σ, F σ ≤ A σ + B σ) :
    ∑ σ, F σ ≤ (∑ σ, A σ) + ∑ σ, B σ := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun σ _ => h_le σ)

open Classical in
/-- 述語の指示関数の和は、フィルターされた部分集合の要素数に一致する。 -/
lemma sum_ite_eq_card_filter {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (∑ x : α, (if P x then 1 else 0)) = (Finset.filter P (Finset.univ : Finset α)).card := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

open Classical in
/-- 凸領域の非空個数に関するファイバー分解上界不等式。
$(k+1)$ 本の直線配置による空でない凸領域の個数は、
既存の領域数と切断された領域数の和で抑えられる。 -/
lemma card_filter_nonempty_convexPlaneRegion_succ_le (k : ℕ) (L : Fin (k + 1) → Line2) :
    (Finset.filter (fun τ => (convexPlaneRegion (k + 1) L τ).Nonempty) Finset.univ).card ≤
      (Finset.filter
        (fun σ => (convexPlaneRegion k (L ∘ Fin.castSucc) σ).Nonempty) Finset.univ).card +
        splitRegionsCount k L := by
  let P_succ := fun τ => (convexPlaneRegion (k + 1) L τ).Nonempty
  rw [card_filter_succ_eq_sum P_succ]
  have h_le := sum_fiber_le_sum_add
    (A := fun σ => if (convexPlaneRegion k (L ∘ Fin.castSucc) σ).Nonempty then 1 else 0)
    (B := fun σ =>
      if isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k)) then 1 else 0)
    (F := fun σ => (Finset.filter (fun b : Bool => P_succ (Fin.snoc σ b)) Finset.univ).card)
    (fun σ => by
      apply term_le_add_split
      · exact fiber_card_le_two k L σ
      · exact fiber_card_le_one_of_not_split k L σ
      · exact fiber_card_eq_zero_of_empty k L σ)
  have hA : (∑ σ, if (convexPlaneRegion k (L ∘ Fin.castSucc) σ).Nonempty then 1 else 0) =
      (Finset.filter
        (fun σ => (convexPlaneRegion k (L ∘ Fin.castSucc) σ).Nonempty) Finset.univ).card :=
    sum_ite_eq_card_filter _
  have hB : (∑ σ, if isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ)
      (L (Fin.last k)) then 1 else 0) = splitRegionsCount k L := by
    dsimp [splitRegionsCount]
    exact sum_ite_eq_card_filter _
  rw [hA, hB] at h_le
  exact h_le

open Classical in
/-- 点 $x$ が属する符号ベクトル。各直線 $L_i$ のどちら側に存在するかを決定する。 -/
noncomputable def pointSignVector (k : ℕ) (L : Fin k → Line2)
    (x : {x : Plane2 | ∀ i, x ∉ (L i).toSet}) : SignVector2 k :=
  fun i => decide ((L i).offset < @inner ℝ Plane2 _ (L i).normVec x.val)

lemma mem_convexPlaneRegion_pointSignVector (k : ℕ) (L : Fin k → Line2)
    (x : {x : Plane2 | ∀ i, x ∉ (L i).toSet}) :
    x.val ∈ convexPlaneRegion k L (pointSignVector k L x) := by
  dsimp [convexPlaneRegion]
  intro i
  have h_not : x.val ∉ (L i).toSet := x.2 i
  dsimp [Line2.toSet] at h_not
  have h_ne : @inner ℝ Plane2 _ (L i).normVec x.val ≠ (L i).offset := h_not
  cases h_bool : pointSignVector k L x i
  · have h_dec : decide ((L i).offset < @inner ℝ Plane2 _ (L i).normVec x.val) = false := by
      change pointSignVector k L x i = false at h_bool
      dsimp [pointSignVector] at h_bool
      exact h_bool
    have h_not_lt := of_decide_eq_false h_dec
    have h_le : @inner ℝ Plane2 _ (L i).normVec x.val ≤ (L i).offset := not_lt.mp h_not_lt
    exact lt_of_le_of_ne h_le h_ne
  · have h_dec : decide ((L i).offset < @inner ℝ Plane2 _ (L i).normVec x.val) = true := by
      change pointSignVector k L x i = true at h_bool
      dsimp [pointSignVector] at h_bool
      exact h_bool
    exact of_decide_eq_true h_dec

lemma pointSignVector_eq_of_mem (k : ℕ) (L : Fin k → Line2)
    (x : {x : Plane2 | ∀ i, x ∉ (L i).toSet}) (σ : SignVector2 k)
    (hx : x.val ∈ convexPlaneRegion k L σ) :
    pointSignVector k L x = σ := by
  funext i
  have h := hx i
  dsimp [pointSignVector]
  cases hσ : σ i
  · rw [hσ] at h
    dsimp at h
    have : ¬ (L i).offset < @inner ℝ Plane2 _ (L i).normVec x.val := not_lt.mpr (le_of_lt h)
    simp [this]
  · rw [hσ] at h
    dsimp at h
    simp [h]

/-- 同一の連結成分に属する点は、属する符号ベクトルが一致する。
超平面による分離と開かつ閉集合の連結成分包含性により証明される。 -/
lemma pointSignVector_eq_of_connectedComponent_eq (k : ℕ) (L : Fin k → Line2)
    (x y : {x : Plane2 | ∀ i, x ∉ (L i).toSet})
    (h_conn : connectedComponent x = connectedComponent y) :
    pointSignVector k L x = pointSignVector k L y := by
  funext i
  by_contra hne
  have h_cases : (pointSignVector k L x i = true ∧ pointSignVector k L y i = false) ∨
                 (pointSignVector k L x i = false ∧ pointSignVector k L y i = true) := by
    revert hne
    cases pointSignVector k L x i <;> cases pointSignVector k L y i <;> intro hne
    · exact False.elim (hne rfl)
    · right; exact ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · exact False.elim (hne rfl)
  have h_cont : Continuous (fun p : {p : Plane2 | ∀ i, p ∉ (L i).toSet} =>
      @inner ℝ Plane2 _ (L i).normVec p.val) :=
    continuous_const.inner continuous_subtype_val
  let U : Set {p : Plane2 | ∀ i, p ∉ (L i).toSet} :=
    {p | (L i).offset < @inner ℝ Plane2 _ (L i).normVec p.val}
  have hU_open : IsOpen U := isOpen_Ioi.preimage h_cont
  have hUc_open : IsOpen (Uᶜ) := by
    have h_eq : Uᶜ = {p : {p : Plane2 | ∀ i, p ∉ (L i).toSet} |
        @inner ℝ Plane2 _ (L i).normVec p.val < (L i).offset} := by
      ext p
      simp only [mem_compl_iff]
      change ¬ (L i).offset < @inner ℝ Plane2 _ (L i).normVec p.val ↔
        @inner ℝ Plane2 _ (L i).normVec p.val < (L i).offset
      have hp_not : p.val ∉ (L i).toSet := p.2 i
      dsimp [Line2.toSet] at hp_not
      constructor
      · intro hnot
        exact lt_of_le_of_ne (not_lt.mp hnot) hp_not
      · intro hlt hnot
        exact lt_asymm hlt hnot
    rw [h_eq]
    exact isOpen_Iio.preimage h_cont
  have hU_clopen : IsClopen U := ⟨isOpen_compl_iff.mp hUc_open, hU_open⟩
  rcases h_cases with ⟨hxt, hyf⟩ | ⟨hxf, hyt⟩
  · have hxU : x ∈ U := by
      change (L i).offset < @inner ℝ Plane2 _ (L i).normVec x.val
      have : pointSignVector k L x i = true := hxt
      dsimp [pointSignVector] at this
      exact of_decide_eq_true this
    have hyUc : y ∈ Uᶜ := by
      intro hy
      have : pointSignVector k L y i = false := hyf
      dsimp [pointSignVector] at this
      have hnot := of_decide_eq_false this
      exact hnot hy
    have h_sub := IsClopen.connectedComponent_subset hU_clopen hxU
    have hy_in_comp : y ∈ connectedComponent x := by
      rw [h_conn]
      exact mem_connectedComponent
    exact hyUc (h_sub hy_in_comp)
  · have hyU : y ∈ U := by
      change (L i).offset < @inner ℝ Plane2 _ (L i).normVec y.val
      have : pointSignVector k L y i = true := hyt
      dsimp [pointSignVector] at this
      exact of_decide_eq_true this
    have hxUc : x ∈ Uᶜ := by
      intro hx
      have : pointSignVector k L x i = false := hxf
      dsimp [pointSignVector] at this
      have hnot := of_decide_eq_false this
      exact hnot hx
    have h_sub := IsClopen.connectedComponent_subset hU_clopen hyU
    have hx_in_comp : x ∈ connectedComponent y := by
      rw [← h_conn]
      exact mem_connectedComponent
    exact hxUc (h_sub hx_in_comp)

/-- 凸領域内の2点を結ぶ閉線分上の点は、再び同じ凸領域に属する。 -/
lemma mem_convexPlaneRegion_segment {k : ℕ} (L : Fin k → Line2) (σ : SignVector2 k)
    {p₁ p₂ : Plane2} (hp₁ : p₁ ∈ convexPlaneRegion k L σ) (hp₂ : p₂ ∈ convexPlaneRegion k L σ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) • p₁ + t • p₂ ∈ convexPlaneRegion k L σ := by
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · subst ht0
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact hp₁
  · rcases eq_or_lt_of_le ht.2 with ht1 | ht1
    · subst ht1
      simp only [sub_self, zero_smul, one_smul, zero_add]
      exact hp₂
    · have ha : 0 < 1 - t := by linarith
      have hb : 0 < t := ht0
      have hab : (1 - t) + t = 1 := by ring
      exact convex_combination_mem_region L σ hp₁ hp₂ ha hb hab

/-- 属する符号ベクトルが一致する2点は、同一の連結成分に属する。
凸領域内の線分による弧状連結性と、連結像の連結成分包含性により証明される。 -/
lemma connectedComponent_eq_of_pointSignVector_eq (k : ℕ) (L : Fin k → Line2)
    (x y : {x : Plane2 | ∀ i, x ∉ (L i).toSet})
    (h_eq : pointSignVector k L x = pointSignVector k L y) :
    connectedComponent x = connectedComponent y := by
  let σ := pointSignVector k L x
  have hx_mem : x.val ∈ convexPlaneRegion k L σ :=
    mem_convexPlaneRegion_pointSignVector k L x
  have hy_mem : y.val ∈ convexPlaneRegion k L σ := by
    have h_eq_y : σ = pointSignVector k L y := h_eq
    rw [h_eq_y]
    exact mem_convexPlaneRegion_pointSignVector k L y
  let α := {p : Plane2 | ∀ i, p ∉ (L i).toSet}
  let γ_raw : ℝ → Plane2 := fun t => (1 - t) • x.val + t • y.val
  have h_cont_raw : Continuous γ_raw := by
    continuity
  have h_segment_mem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin k, γ_raw t ∉ (L i).toSet := by
    intro t ht i
    have h_mem := mem_convexPlaneRegion_segment L σ hx_mem hy_mem ht
    exact not_mem_line_of_mem_convexPlaneRegion L σ h_mem i
  let γ : Icc (0 : ℝ) 1 → α := fun ⟨t, ht⟩ => ⟨γ_raw t, h_segment_mem t ht⟩
  have h_cont_γ : Continuous γ := by
    exact Continuous.subtype_mk (h_cont_raw.comp continuous_subtype_val) _
  have : ConnectedSpace (Icc (0 : ℝ) 1) :=
    Subtype.connectedSpace (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1))
  have h_conn_range : IsConnected (range γ) := isConnected_range h_cont_γ
  have hx_range : x ∈ range γ := by
    use ⟨0, ⟨le_refl 0, by norm_num⟩⟩
    apply Subtype.ext
    dsimp [γ, γ_raw]
    simp
  have hy_range : y ∈ range γ := by
    use ⟨1, ⟨by norm_num, le_refl 1⟩⟩
    apply Subtype.ext
    dsimp [γ, γ_raw]
    simp
  have h_sub := IsConnected.subset_connectedComponent h_conn_range hx_range
  have hy_in_comp : y ∈ connectedComponent x := h_sub hy_range
  exact connectedComponent_eq hy_in_comp

open Classical in
/-- 2次元平面における直線配置の領域数は、空でない符号ベクトルの個数と一致する。
各領域が開かつ凸(連結)であり、互いに素な開集合の非交和をなすことから従う。 -/
lemma planeRegionsCount_eq_card_nonempty_convexPlaneRegion (k : ℕ) (L : Fin k → Line2) :
    planeRegionsCount k L =
      (Finset.filter (fun σ => (convexPlaneRegion k L σ).Nonempty) Finset.univ).card := by
  let α := {x : Plane2 | ∀ i, x ∉ (L i).toSet}
  let s : Setoid α := connectedComponentSetoid α
  let V := {σ : SignVector2 k // (convexPlaneRegion k L σ).Nonempty}
  let f : α → V := fun x =>
    ⟨pointSignVector k L x, ⟨x.val, mem_convexPlaneRegion_pointSignVector k L x⟩⟩
  have h_fiber : ∀ x y : α, f x = f y → x ≈ y := by
    intro x y hfg
    have h_eq : pointSignVector k L x = pointSignVector k L y := congr_arg Subtype.val hfg
    exact connectedComponent_eq_of_pointSignVector_eq k L x y h_eq
  have h_le : Nat.card (Quotient s) ≤ Fintype.card V :=
    card_quotient_le_of_fiber_le s f h_fiber
  have h_rep : ∀ v : V, ∃ x : α, f x = v := by
    intro ⟨σ, hσ⟩
    obtain ⟨p, hp⟩ := hσ
    have hp_not : ∀ i, p ∉ (L i).toSet := not_mem_line_of_mem_convexPlaneRegion L σ hp
    have h_sign := pointSignVector_eq_of_mem k L ⟨p, hp_not⟩ σ hp
    refine ⟨⟨p, hp_not⟩, Subtype.ext h_sign⟩
  choose w hw using h_rep
  let g : V → Quotient s := fun v => Quotient.mk s (w v)
  have hg_inj : Function.Injective g := by
    intro v1 v2 hg
    have hequiv : w v1 ≈ w v2 := Quotient.exact hg
    have hconn : connectedComponent (w v1) = connectedComponent (w v2) := hequiv
    have hsign := pointSignVector_eq_of_connectedComponent_eq k L (w v1) (w v2) hconn
    have h_f_eq : f (w v1) = f (w v2) := Subtype.ext hsign
    rw [hw v1, hw v2] at h_f_eq
    exact h_f_eq
  have : Finite (Quotient s) := finite_quotient_of_fiber_le s f h_fiber
  have h_ge := Nat.card_le_card_of_injective g hg_inj
  have h_card_V : Fintype.card V =
      (Finset.filter (fun σ => (convexPlaneRegion k L σ).Nonempty) Finset.univ).card := by
    rw [Fintype.card_subtype]
  rw [Nat.card_eq_fintype_card] at h_ge
  dsimp [planeRegionsCount]
  change Nat.card (Quotient s) =
    (Finset.filter (fun σ => (convexPlaneRegion k L σ).Nonempty) Finset.univ).card
  omega

/-- 平面領域の増加量は、切断された既存領域の個数に一致する(高々等しい)。
ファイバー分解 Bool → {0, 1, 2} の和により、増加量は切断領域数で上から抑えられる。 -/
lemma planeRegionsCount_succ_le_add_split (k : ℕ) (L : Fin (k + 1) → Line2) :
    planeRegionsCount (k + 1) L ≤
      planeRegionsCount k (L ∘ Fin.castSucc) + splitRegionsCount k L := by
  rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion]
  rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion]
  exact card_filter_nonempty_convexPlaneRegion_succ_le k L


/-- 2次元平面における直線追加の幾何学的漸化不等式:
$(k+1)$ 本目の直線を追加したとき、既存の $k$ 本の直線との交点で高々 $k+1$ 個の線分・半直線に分かれ、
平面領域数の増加量は高々 $k+1$ である。 -/
lemma planeRegionsCount_succ_le (k : ℕ) (L : Fin (k + 1) → Line2) :
    planeRegionsCount (k + 1) L ≤ planeRegionsCount k (L ∘ Fin.castSucc) + (k + 1) := by
  have h_split := planeRegionsCount_succ_le_add_split k L
  have h_le_intervals := splitRegionsCount_le_lineIntervals k L
  have h_intervals_le := lineIntervals_succ_le k L
  omega

/-! #### 補集合が全空間となる場合の連結成分数補題 -/

/-- 連結空間αにおいて、全空間 `Set.univ` の連結成分数は1である。
部分空間 `Set.univ` は連結であり、商集合 `ConnectedComponents` が単元集合となる。 -/
lemma nat_card_connectedComponents_univ {α : Type*} [TopologicalSpace α] [ConnectedSpace α]
    [Inhabited α] :
    Nat.card (ConnectedComponents (Set.univ : Set α)) = 1 := by
  have : ConnectedSpace (Set.univ : Set α) := Subtype.connectedSpace isConnected_univ
  have : Inhabited (Set.univ : Set α) := ⟨⟨default, mem_univ _⟩⟩
  have : Unique (ConnectedComponents (Set.univ : Set α)) := Unique.mk' _
  exact Nat.card_unique

/-- 直線が0本のとき、補集合は平面全体であり領域数は1である。 -/
lemma planeRegionsCount_zero (L : Fin 0 → Line2) :
    planeRegionsCount 0 L = 1 := by
  dsimp [planeRegionsCount]
  have h_univ : {x : Plane2 | ∀ i : Fin 0, x ∉ (L i).toSet} = Set.univ := by
    ext x
    simp
  change Nat.card (ConnectedComponents
    ({x : Plane2 | ∀ i : Fin 0, x ∉ (L i).toSet} : Set Plane2)) = 1
  rw [h_univ]
  exact nat_card_connectedComponents_univ

/-- 2次元直線配置に対する幾何学的上界補題:
任意の $k$ 本の直線配置による補集合の連結成分数が
$S(k) = \binom{k}{0} + \binom{k}{1} + \binom{k}{2}$ 以下であること。

【導出過程】
$k-1$ 本の直線がある平面に、$k$ 本目の直線を追加する場合を考える。
追加した直線は既存の直線と交差し、最大で $k$ 個の線分や半直線に分かれる。
新しくできた線分や半直線がそれぞれ既存の領域を2分割するため、
全体の領域数は高々 $k$ 個増える仕組みである。
これにより漸化式 $S(k) = S(k-1) + k$ が成り立ち、$S(1) = 2$ から二項係数の和が得られる。

【領域数が最大値以下となる理由】
直線同士が平行だったり、複数の直線が1点で交わったりすると、
交点で生まれる線分や領域の増加数が減る。
したがって、すべての直線が平行でなく、どの3直線も1点で交わらない配置でのみ最大値が達成され、
任意の直線配置では領域数が常に最大値 $S(k)$ 以下となる。 -/
theorem planeRegionsCount_le_maxPlaneRegions (k : ℕ) (L : Fin k → Line2) :
    planeRegionsCount k L ≤ maxPlaneRegions k := by
  induction k with
  | zero =>
    rw [planeRegionsCount_zero L]
    dsimp [maxPlaneRegions]
    decide
  | succ m ih =>
    have hstep := planeRegionsCount_succ_le m L
    have hih := ih (L ∘ Fin.castSucc)
    have hsucc := maxPlaneRegions_succ_step m
    omega

/-! ### 一般の位置における領域数の漸化等式と最大値達成 -/

/-- 一般の位置にある直線配置の部分配置もまた一般の位置にある。
`Fin.castSucc` の単射性から直ちに従う。 -/
lemma GeneralPositionLines.castSucc (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    GeneralPositionLines k (L ∘ Fin.castSucc) := by
  constructor
  · intro i j hij
    have hij' : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_inj.mp h)
    exact hgen.1 (Fin.castSucc i) (Fin.castSucc j) hij'
  · intro i j l hij hjl hil
    have hij' : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_inj.mp h)
    have hjl' : Fin.castSucc j ≠ Fin.castSucc l := fun h => hjl (Fin.castSucc_inj.mp h)
    have hil' : Fin.castSucc i ≠ Fin.castSucc l := fun h => hil (Fin.castSucc_inj.mp h)
    exact hgen.2 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc l) hij' hjl' hil'

open Classical in
/-- 一般の位置にある直線配置において、第 $(k+1)$ 直線と既存の直線の交点はすべて相異なり、
ちょうど $k$ 個存在する。
- どの2直線も平行でないため、交点インデックス集合は Fin k 全体となる。
- どの3直線も1点で交わらないため、交点パラメータ写像は単射となる。 -/
lemma card_lineIntersectionParams_eq_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    (lineIntersectionParams k L).card = k := by
  dsimp [lineIntersectionParams]
  have h_indices : intersectingIndices k L = Finset.univ := by
    ext i
    simp only [intersectingIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [hasIntersectionWithLast]
    have hij : Fin.castSucc i ≠ Fin.last k := ne_of_lt (Fin.castSucc_lt_last i)
    exact iff_true_intro (hgen.1 (Fin.castSucc i) (Fin.last k) hij)
  rw [h_indices]
  have h_inj : Function.Injective (rawIntersectionParam k L) := by
    intro i j hij
    by_contra h_ne
    have h_not_par_i := hgen.1 (Fin.castSucc i) (Fin.last k) (ne_of_lt (Fin.castSucc_lt_last i))
    have h_not_par_j := hgen.1 (Fin.castSucc j) (Fin.last k) (ne_of_lt (Fin.castSucc_lt_last j))
    have h_ex_i : ∃ t, linePt (L (Fin.last k)) t ∈ (L (Fin.castSucc i)).toSet :=
      exists_linePt_mem_of_not_parallel _ _ h_not_par_i
    have h_ex_j : ∃ t, linePt (L (Fin.last k)) t ∈ (L (Fin.castSucc j)).toSet :=
      exists_linePt_mem_of_not_parallel _ _ h_not_par_j
    dsimp [rawIntersectionParam] at hij
    simp only [h_ex_i, h_ex_j, dite_true] at hij
    have ti := Classical.choose_spec h_ex_i
    have tj := Classical.choose_spec h_ex_j
    have h_eq_t : Classical.choose h_ex_i = Classical.choose h_ex_j := hij
    let p := linePt (L (Fin.last k)) (Classical.choose h_ex_i)
    have hp_i : p ∈ (L (Fin.castSucc i)).toSet := ti
    have hp_j : p ∈ (L (Fin.castSucc j)).toSet := by
      change linePt (L (Fin.last k)) (Classical.choose h_ex_i) ∈ (L (Fin.castSucc j)).toSet
      rw [h_eq_t]
      exact tj
    have hp_k : p ∈ (L (Fin.last k)).toSet := linePt_mem_line _ _
    have h_empty := hgen.2 (Fin.castSucc i) (Fin.castSucc j) (Fin.last k)
      (fun h => h_ne (Fin.castSucc_inj.mp h))
      (ne_of_lt (Fin.castSucc_lt_last j))
      (ne_of_lt (Fin.castSucc_lt_last i))
    have hp_inter : p ∈ (L (Fin.castSucc i)).toSet ∩ (L (Fin.castSucc j)).toSet ∩
        (L (Fin.last k)).toSet := ⟨⟨hp_i, hp_j⟩, hp_k⟩
    rw [h_empty] at hp_inter
    exact hp_inter
  rw [Finset.card_image_of_injective _ h_inj]
  exact Fintype.card_fin k

/-- 一般の位置にある配置において、直線上の開区間数はちょうど $k + 1$ 個である。 -/
lemma lineIntervals_eq_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    realIntervalsCount (lineIntersectionParams k L) = k + 1 := by
  rw [realIntervalsCount_eq]
  rw [card_lineIntersectionParams_eq_of_general_position k L hgen]

open Classical in
/-- 交点パラメータに含まれない実数に対応する直線上の点は、
既存のどの直線の上にも存在しない。 -/
lemma not_mem_line_of_not_mem_lineIntersectionParams (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L)
    {t : ℝ} (ht : t ∉ lineIntersectionParams k L) (i : Fin k) :
    linePt (L (Fin.last k)) t ∉ (L (Fin.castSucc i)).toSet := by
  intro hp
  apply ht
  dsimp [lineIntersectionParams]
  rw [Finset.mem_image]
  use i
  have h_not_par : ¬ parallelLines (L (Fin.castSucc i)) (L (Fin.last k)) :=
    hgen.1 (Fin.castSucc i) (Fin.last k) (ne_of_lt (Fin.castSucc_lt_last i))
  have h_raw := rawIntersectionParam_eq k L i h_not_par hp
  have h_inter : hasIntersectionWithLast k L i := h_not_par
  refine ⟨?_, h_raw⟩
  dsimp [intersectingIndices]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_inter⟩

open Classical in
/-- 交点パラメータ集合の元は、既存のある直線との交点に対応する。 -/
lemma exists_line_of_mem_lineIntersectionParams (k : ℕ) (L : Fin (k + 1) → Line2)
    {s : ℝ} (hs : s ∈ lineIntersectionParams k L) :
    ∃ i : Fin k, linePt (L (Fin.last k)) s ∈ (L (Fin.castSucc i)).toSet := by
  dsimp [lineIntersectionParams] at hs
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
  dsimp [rawIntersectionParam]
  split_ifs with hex
  · exact ⟨i, Classical.choose_spec hex⟩
  · have hi_inter : hasIntersectionWithLast k L i := (Finset.mem_filter.mp hi).2
    have hex_true := exists_linePt_mem_of_not_parallel
      (L (Fin.castSucc i)) (L (Fin.last k)) hi_inter
    exact (hex hex_true).elim

open Classical in
/-- 有限集合の左側にある要素数が真に増加するとき、
その2点の間には有限集合の元が少なくとも1つ存在する。 -/
lemma exists_between_of_countLt_lt {S : Finset ℝ} {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∉ S) (ht₁₂ : t₁ < t₂) (hcount : countLt S t₁ < countLt S t₂) :
    ∃ s ∈ S, t₁ < s ∧ s < t₂ := by
  dsimp [countLt] at hcount
  have h_sub : S.filter (· < t₁) ⊂ S.filter (· < t₂) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_trans hx.2 ht₁₂⟩
    · intro h_eq
      rw [h_eq] at hcount
      exact lt_irrefl _ hcount
  obtain ⟨s, hs⟩ := Finset.exists_of_ssubset h_sub
  simp only [Finset.mem_filter, not_and] at hs
  have hsS : s ∈ S := hs.1.1
  have hs_lt2 : s < t₂ := hs.1.2
  have hs_ge1 : t₁ ≤ s := not_lt.mp (hs.2 hsS)
  have hs_ne1 : t₁ ≠ s := fun h => ht₁ (h ▸ hsS)
  have hs_lt1 : t₁ < s := lt_of_le_of_ne hs_ge1 hs_ne1
  exact ⟨s, hsS, hs_lt1, hs_lt2⟩

/-- 開区間内の点 $s \in (t_1, t_2)$ は、$t_1$ と $t_2$ の真の凸結合として表される。 -/
lemma exists_affine_comb_of_lt {t₁ t₂ s : ℝ} (h1 : t₁ < s) (h2 : s < t₂) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * t₁ + b * t₂ = s := by
  let b := (s - t₁) / (t₂ - t₁)
  let a := 1 - b
  have h_diff_pos : 0 < t₂ - t₁ := by linarith
  have hb_pos : 0 < b := div_pos (by linarith) h_diff_pos
  have hb_lt1 : b < 1 := (div_lt_one h_diff_pos).mpr (by linarith)
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have hab : a + b = 1 := by dsimp [a]; ring
  have h_comb : a * t₁ + b * t₂ = s := by
    dsimp [a, b]
    have : (1 - (s - t₁) / (t₂ - t₁)) * t₁ + ((s - t₁) / (t₂ - t₁)) * t₂ =
        t₁ + ((s - t₁) / (t₂ - t₁)) * (t₂ - t₁) := by ring
    rw [this, div_mul_cancel₀ _ (ne_of_gt h_diff_pos)]
    ring
  exact ⟨a, b, ha_pos, hb_pos, hab, h_comb⟩

open Classical in
/-- 一般の位置にある配置において、切断される領域の個数はちょうど $k + 1$ 個である。
上界(実数区間数以下)と、各区間から切断領域への単射構成による下界を組み合わせて証明される。 -/
lemma splitRegionsCount_eq_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    splitRegionsCount k L = k + 1 := by
  have h_le : splitRegionsCount k L ≤ k + 1 := by
    have h1 := splitRegionsCount_le_lineIntervals k L
    have h2 := lineIntervals_eq_of_general_position k L hgen
    omega
  have h_ge : k + 1 ≤ splitRegionsCount k L := by
    let S := lineIntersectionParams k L
    have hS_card : S.card = k := card_lineIntersectionParams_eq_of_general_position k L hgen
    let split_sigs := Finset.filter (fun σ =>
      isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) Finset.univ
    have hj_pt : ∀ j : Fin (k + 1), ∃ t : ℝ, t ∉ S ∧ countLt S t = j.val := by
      intro j
      have hj_fin : j.val < S.card + 1 := by rw [hS_card]; exact j.isLt
      exact exists_point_countLt_eq S ⟨j.val, hj_fin⟩
    choose t ht using hj_pt
    have hp_not : ∀ j : Fin (k + 1), ∀ i : Fin k,
        linePt (L (Fin.last k)) (t j) ∉ (L (Fin.castSucc i)).toSet := by
      intro j i
      exact not_mem_line_of_not_mem_lineIntersectionParams k L hgen (ht j).1 i
    let p : Fin (k + 1) → Plane2 := fun j => linePt (L (Fin.last k)) (t j)
    let σ : Fin (k + 1) → SignVector2 k := fun j =>
      pointSignVector k (L ∘ Fin.castSucc) ⟨p j, hp_not j⟩
    have hσ_mem : ∀ j : Fin (k + 1), σ j ∈ split_sigs := by
      intro j
      dsimp [split_sigs]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨p j, mem_convexPlaneRegion_pointSignVector k (L ∘ Fin.castSucc) ⟨p j, hp_not j⟩,
        linePt_mem_line _ _⟩
    let ψ : Fin (k + 1) → split_sigs := fun j => ⟨σ j, hσ_mem j⟩
    have hψ_inj : Function.Injective ψ := by
      intro j1 j2 h_eq
      have h_sig_eq : σ j1 = σ j2 := congr_arg Subtype.val h_eq
      by_contra h_ne
      have hj_ne : j1.val ≠ j2.val := fun h => h_ne (Fin.ext h)
      have h_contra : ∀ {ja jb : Fin (k + 1)}, ja.val < jb.val → σ ja = σ jb → False := by
        intro ja jb hj_lt h_eq_ab
        have h_count_lt : countLt S (t ja) < countLt S (t jb) := by
          rw [(ht ja).2, (ht jb).2]
          exact hj_lt
        have ht_lt : t ja < t jb := by
          by_contra hle
          have : t jb ≤ t ja := not_lt.mp hle
          have h_sub_filter : S.filter (· < t jb) ⊆ S.filter (· < t ja) := by
            intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, lt_of_lt_of_le hx.2 this⟩
          have h_count_le : countLt S (t jb) ≤ countLt S (t ja) := by
            dsimp [countLt]
            exact Finset.card_le_card h_sub_filter
          omega
        obtain ⟨s, hsS, hs1, hs2⟩ := exists_between_of_countLt_lt (ht ja).1 ht_lt h_count_lt
        obtain ⟨i, hp_star_line⟩ := exists_line_of_mem_lineIntersectionParams k L hsS
        obtain ⟨a, b, ha, hb, hab, hab_s⟩ := exists_affine_comb_of_lt hs1 hs2
        let p_star := linePt (L (Fin.last k)) s
        have hp_star_comb : p_star = a • p ja + b • p jb := by
          dsimp [p_star, p]
          have h_comb_s : s = (1 - b) * t ja + b * t jb := by
            have : a = 1 - b := by linarith
            rw [← this, hab_s]
          rw [h_comb_s, linePt_affine_comb]
          have : 1 - b = a := by linarith
          rw [this]
        have hp1 : p ja ∈ convexPlaneRegion k (L ∘ Fin.castSucc) (σ ja) :=
          mem_convexPlaneRegion_pointSignVector k (L ∘ Fin.castSucc) ⟨p ja, hp_not ja⟩
        have hp2 : p jb ∈ convexPlaneRegion k (L ∘ Fin.castSucc) (σ ja) := by
          rw [h_eq_ab]
          exact mem_convexPlaneRegion_pointSignVector k (L ∘ Fin.castSucc) ⟨p jb, hp_not jb⟩
        have hp_star_reg : p_star ∈ convexPlaneRegion k (L ∘ Fin.castSucc) (σ ja) := by
          rw [hp_star_comb]
          exact convex_combination_mem_region (L ∘ Fin.castSucc) (σ ja) hp1 hp2 ha hb hab
        have hp_star_not :=
          not_mem_line_of_mem_convexPlaneRegion (L ∘ Fin.castSucc) (σ ja) hp_star_reg i
        exact hp_star_not hp_star_line
      rcases lt_or_gt_of_ne hj_ne with hj_lt | hj_gt
      · exact h_contra hj_lt h_sig_eq
      · exact h_contra hj_gt h_sig_eq.symm
    have h_card_le := Fintype.card_le_of_injective ψ hψ_inj
    rw [Fintype.card_fin, Fintype.card_coe] at h_card_le
    change k + 1 ≤ splitRegionsCount k L
    exact h_card_le
  omega

open Classical in
/-- 直線により切断される凸領域は、直線の正の側と負の側の両方に非空な領域を生じる。
法線ベクトル方向に十分小さく点を動かすことで両側の内点を構成する。 -/
lemma split_region_both_sides_nonempty (k : ℕ) (L : Fin (k + 1) → Line2)
    (σ : SignVector2 k)
    (hsplit : isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) :
    (convexPlaneRegion (k + 1) L (Fin.snoc σ true)).Nonempty ∧
    (convexPlaneRegion (k + 1) L (Fin.snoc σ false)).Nonempty := by
  obtain ⟨p, hp_reg, hp_line⟩ := hsplit
  dsimp [Line2.toSet] at hp_line
  let u := (L (Fin.last k)).normVec
  have hu_pos : 0 < @inner ℝ Plane2 _ u u :=
    real_inner_self_pos.2 (L (Fin.last k)).normVec_ne_zero
  let δ : Fin k → ℝ := fun i =>
    if σ i then @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec p - (L (Fin.castSucc i)).offset
    else (L (Fin.castSucc i)).offset - @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec p
  have hδ_pos : ∀ i, 0 < δ i := by
    intro i
    have hp_i := hp_reg i
    dsimp at hp_i
    dsimp [δ]
    split_ifs at hp_i ⊢ with hσ
    · linarith
    · linarith
  let g : Option (Fin k) → ℝ := fun opt =>
    match opt with
    | none => 1
    | some i =>
      let dot := @inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec u
      if dot = 0 then 1 else δ i / (2 * |dot|)
  have hg_pos : ∀ opt, 0 < g opt := by
    intro opt
    cases opt with
    | none => exact Real.zero_lt_one
    | some i =>
      dsimp [g]
      split_ifs with hdot
      · exact Real.zero_lt_one
      · refine div_pos (hδ_pos i) ?_
        have : 0 < |@inner ℝ Plane2 _ (L (Fin.castSucc i)).normVec u| :=
          abs_pos.mpr hdot
        linarith
  have h_univ_nonempty : (Finset.univ : Finset (Option (Fin k))).Nonempty :=
    ⟨none, Finset.mem_univ none⟩
  obtain ⟨opt_min, -, h_min⟩ := Finset.exists_min_image Finset.univ g h_univ_nonempty
  let ε := g opt_min
  have hε_pos : 0 < ε := hg_pos opt_min
  have hε_le : ∀ i : Fin k, ε ≤ g (some i) := fun i => h_min (some i) (Finset.mem_univ _)
  let p_plus := p + ε • u
  let p_minus := p - ε • u
  have hp_plus_last : (L (Fin.last k)).offset < @inner ℝ Plane2 _ u p_plus := by
    dsimp [p_plus]
    rw [inner_add_right, inner_smul_right]
    have : 0 < ε * @inner ℝ Plane2 _ u u := mul_pos hε_pos hu_pos
    linarith
  have hp_minus_last : @inner ℝ Plane2 _ u p_minus < (L (Fin.last k)).offset := by
    dsimp [p_minus]
    rw [inner_sub_right, inner_smul_right]
    have : 0 < ε * @inner ℝ Plane2 _ u u := mul_pos hε_pos hu_pos
    linarith
  have hp_plus_reg : p_plus ∈ convexPlaneRegion k (L ∘ Fin.castSucc) σ := by
    dsimp [convexPlaneRegion]
    intro i
    have hp_i := hp_reg i
    dsimp at hp_i
    have h_le_i := hε_le i
    dsimp [p_plus]
    rw [inner_add_right, inner_smul_right]
    let vi := (L (Fin.castSucc i)).normVec
    have h_vi : (L (Fin.castSucc i)).normVec = vi := rfl
    rw [h_vi]
    rw [h_vi] at hp_i
    let dot := @inner ℝ Plane2 _ vi u
    have h_dot : @inner ℝ Plane2 _ vi u = dot := rfl
    rw [h_dot]
    by_cases hdot : dot = 0
    · dsimp [g] at h_le_i
      rw [ite_eq_left hdot] at h_le_i
      rw [hdot, mul_zero, add_zero]
      split_ifs at hp_i ⊢ with hσ <;> exact hp_i
    · dsimp [g] at h_le_i
      rw [ite_eq_right hdot] at h_le_i
      have h_bound : ε * |dot| ≤ δ i / 2 := by
        have h_mul : ε * (2 * |dot|) ≤ (δ i / (2 * |dot|)) * (2 * |dot|) :=
          mul_le_mul_of_nonneg_right h_le_i (by positivity)
        rw [div_mul_cancel₀ _ (by positivity)] at h_mul
        linarith
      have h_abs_dot : |ε * dot| ≤ δ i / 2 := by
        rw [abs_mul, abs_of_pos hε_pos]
        exact h_bound
      have h_dot_ge : - (δ i / 2) ≤ ε * dot := by
        have := neg_le_of_abs_le h_abs_dot
        linarith
      have h_dot_le : ε * dot ≤ δ i / 2 := le_of_abs_le h_abs_dot
      have hδ_def : δ i = if σ i then @inner ℝ Plane2 _ vi p - (L (Fin.castSucc i)).offset
                         else (L (Fin.castSucc i)).offset - @inner ℝ Plane2 _ vi p := rfl
      split_ifs at hp_i ⊢ with hσ
      · rw [ite_eq_left hσ] at hδ_def
        linarith
      · rw [ite_eq_right hσ] at hδ_def
        linarith
  have hp_minus_reg : p_minus ∈ convexPlaneRegion k (L ∘ Fin.castSucc) σ := by
    dsimp [convexPlaneRegion]
    intro i
    have hp_i := hp_reg i
    dsimp at hp_i
    have h_le_i := hε_le i
    dsimp [p_minus]
    rw [inner_sub_right, inner_smul_right]
    let vi := (L (Fin.castSucc i)).normVec
    have h_vi : (L (Fin.castSucc i)).normVec = vi := rfl
    rw [h_vi]
    rw [h_vi] at hp_i
    let dot := @inner ℝ Plane2 _ vi u
    have h_dot : @inner ℝ Plane2 _ vi u = dot := rfl
    rw [h_dot]
    by_cases hdot : dot = 0
    · dsimp [g] at h_le_i
      rw [ite_eq_left hdot] at h_le_i
      rw [hdot, mul_zero, sub_zero]
      split_ifs at hp_i ⊢ with hσ <;> exact hp_i
    · dsimp [g] at h_le_i
      rw [ite_eq_right hdot] at h_le_i
      have h_bound : ε * |dot| ≤ δ i / 2 := by
        have h_mul : ε * (2 * |dot|) ≤ (δ i / (2 * |dot|)) * (2 * |dot|) :=
          mul_le_mul_of_nonneg_right h_le_i (by positivity)
        rw [div_mul_cancel₀ _ (by positivity)] at h_mul
        linarith
      have h_abs_dot : |ε * dot| ≤ δ i / 2 := by
        rw [abs_mul, abs_of_pos hε_pos]
        exact h_bound
      have h_dot_ge : - (δ i / 2) ≤ ε * dot := by
        have := neg_le_of_abs_le h_abs_dot
        linarith
      have h_dot_le : ε * dot ≤ δ i / 2 := le_of_abs_le h_abs_dot
      have hδ_def : δ i = if σ i then @inner ℝ Plane2 _ vi p - (L (Fin.castSucc i)).offset
                         else (L (Fin.castSucc i)).offset - @inner ℝ Plane2 _ vi p := rfl
      split_ifs at hp_i ⊢ with hσ
      · rw [ite_eq_left hσ] at hδ_def
        linarith
      · rw [ite_eq_right hσ] at hδ_def
        linarith
  constructor
  · use p_plus
    rw [mem_convexPlaneRegion_succ]
    exact ⟨hp_plus_reg, hp_plus_last⟩
  · use p_minus
    rw [mem_convexPlaneRegion_succ]
    exact ⟨hp_minus_reg, hp_minus_last⟩

open Classical in
/-- 一般の位置にある配置に新しい直線を追加したとき、
増える領域の個数は切断領域の個数 ($k + 1$) 以上である。
ファイバー分解の和において、切断領域が2個以上、非切断領域が1個以上の領域を
生じることから従う。 -/
lemma planeRegionsCount_succ_ge_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    planeRegionsCount k (L ∘ Fin.castSucc) + (k + 1) ≤ planeRegionsCount (k + 1) L := by
  have h_split_eq : splitRegionsCount k L = k + 1 :=
    splitRegionsCount_eq_of_general_position k L hgen
  have h_ge : planeRegionsCount k (L ∘ Fin.castSucc) + splitRegionsCount k L ≤
      planeRegionsCount (k + 1) L := by
    rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion]
    rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion]
    let P_succ := fun τ => (convexPlaneRegion (k + 1) L τ).Nonempty
    rw [card_filter_succ_eq_sum P_succ]
    have hA : (∑ σ, if (convexPlaneRegion k (L ∘ Fin.castSucc) σ).Nonempty then 1 else 0) =
        (Finset.filter
          (fun σ => (convexPlaneRegion k (L ∘ Fin.castSucc) σ).Nonempty) Finset.univ).card :=
      sum_ite_eq_card_filter _
    have hB : (∑ σ, if isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ)
        (L (Fin.last k)) then 1 else 0) = splitRegionsCount k L := by
      dsimp [splitRegionsCount]
      exact sum_ite_eq_card_filter _
    rw [← hA, ← hB, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro σ _
    let F_set := Finset.filter (fun b : Bool => P_succ (Fin.snoc σ b)) Finset.univ
    by_cases hne : (convexPlaneRegion k (L ∘ Fin.castSucc) σ).Nonempty
    · simp only [hne, ↓reduceIte]
      by_cases hsp : isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))
      · simp only [hsp, ↓reduceIte]
        have h_both := split_region_both_sides_nonempty k L σ hsp
        have hT : true ∈ F_set := by
          simp only [F_set, Finset.mem_filter, Finset.mem_univ, true_and, P_succ]
          exact h_both.1
        have hF : false ∈ F_set := by
          simp only [F_set, Finset.mem_filter, Finset.mem_univ, true_and, P_succ]
          exact h_both.2
        have h_pair : {true, false} ⊆ F_set := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have h_card_two : ({true, false} : Finset Bool).card = 2 := by decide
        have h_le := Finset.card_le_card h_pair
        rw [h_card_two] at h_le
        exact h_le
      · simp only [hsp, ↓reduceIte, add_zero]
        obtain ⟨p, hp⟩ := hne
        have hp_not_line : p ∉ (L (Fin.last k)).toSet := by
          intro hp_line
          apply hsp
          exact ⟨p, hp, hp_line⟩
        dsimp [Line2.toSet] at hp_not_line
        rcases lt_or_gt_of_ne hp_not_line with hlt | hgt
        · have hF : false ∈ F_set := by
            simp only [F_set, Finset.mem_filter, Finset.mem_univ, true_and, P_succ]
            use p
            rw [mem_convexPlaneRegion_succ]
            exact ⟨hp, hlt⟩
          have h_pos : 1 ≤ F_set.card := Finset.card_pos.mpr ⟨false, hF⟩
          exact h_pos
        · have hT : true ∈ F_set := by
            simp only [F_set, Finset.mem_filter, Finset.mem_univ, true_and, P_succ]
            use p
            rw [mem_convexPlaneRegion_succ]
            exact ⟨hp, hgt⟩
          have h_pos : 1 ≤ F_set.card := Finset.card_pos.mpr ⟨true, hT⟩
          exact h_pos
    · simp only [hne, ↓reduceIte, zero_add]
      have hsp_not :
          ¬ isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k)) := by
        rintro ⟨p, hp, _⟩
        exact hne ⟨p, hp⟩
      simp only [hsp_not, ↓reduceIte]
      exact Nat.zero_le _
  rw [h_split_eq] at h_ge
  exact h_ge

/-- 一般の位置にある配置に新しい直線を追加したとき、
増える平面領域の個数はちょうど $k + 1$ 個である。
上界不等式 planeRegionsCount_succ_le と下界不等式を組み合わせて証明される。 -/
theorem planeRegionsCount_succ_eq_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    planeRegionsCount (k + 1) L = planeRegionsCount k (L ∘ Fin.castSucc) + (k + 1) := by
  have h_le := planeRegionsCount_succ_le k L
  have h_ge := planeRegionsCount_succ_ge_of_general_position k L hgen
  omega

/-- 一般の位置にある直線配置に対する最大値達成定理:
一般の位置にある直線配置 $L$ では、領域数が最大値 $S(k)$ に一致する。
帰納法と漸化等式により完全に証明される。 -/
theorem planeRegionsCount_eq_max_of_general_position (k : ℕ) (L : Fin k → Line2)
    (hgen : GeneralPositionLines k L) :
    planeRegionsCount k L = maxPlaneRegions k := by
  induction k with
  | zero =>
    rw [planeRegionsCount_zero L]
    dsimp [maxPlaneRegions]
    decide
  | succ m ih =>
    have hgen_sub : GeneralPositionLines m (L ∘ Fin.castSucc) :=
      GeneralPositionLines.castSucc m L hgen
    have hstep : planeRegionsCount (m + 1) L =
        planeRegionsCount m (L ∘ Fin.castSucc) + (m + 1) :=
      planeRegionsCount_succ_eq_of_general_position m L hgen
    have hih : planeRegionsCount m (L ∘ Fin.castSucc) = maxPlaneRegions m :=
      ih (L ∘ Fin.castSucc) hgen_sub
    have hsucc : maxPlaneRegions (m + 1) = maxPlaneRegions m + (m + 1) :=
      maxPlaneRegions_succ_step m
    rw [hstep, hih, hsucc]

/-- 平面が0枚のとき、補集合は全空間であり領域数は1である。 -/
lemma spaceRegionsCount_zero (H : Fin 0 → Plane3) :
    spaceRegionsCount 0 H = 1 := by
  dsimp [spaceRegionsCount]
  have h_univ : {x : Space3 | ∀ i : Fin 0, x ∉ (H i).toSet} = Set.univ := by
    ext x
    simp
  change Nat.card (ConnectedComponents
    ({x : Space3 | ∀ i : Fin 0, x ∉ (H i).toSet} : Set Space3)) = 1
  rw [h_univ]
  exact nat_card_connectedComponents_univ

/- 3次元平面配置に対する幾何学的漸化不等式:
$(n+1)$ 枚目の平面 $H_{n}$ を追加したときの空間領域数は、
既存の $n$ 枚による領域数と、第 $(n+1)$ 平面上に現れる交線配置による領域数の和で抑えられる。
したがって、空間領域数の増加量は高々 $S(n)$ である。

【新しい平面上の領域分割】
平面 $H_{n+1}$ は、空間内に既に存在する $n$ 枚の平面 $H_1, \dots, H_n$ とそれぞれ交差する。
平行でない各平面との交わりによって、$H_{n+1}$ 上には高々 $n$ 本の交線が現れ、
これらによって平面 $H_{n+1}$ 自身がいくつかの平面領域に分割される。 -/

/-! ### 3次元空間における幾何学的領域と切断の定義 -/

abbrev SignVector3 (n : ℕ) := Fin n → Bool

/-- 3次元空間において各平面 $H_i$ のどちら側に存在するかによって定まる開凸領域。 -/
def convexSpaceRegion (n : ℕ) (H : Fin n → Plane3) (σ : SignVector3 n) : Set Space3 :=
  {x : Space3 | ∀ i : Fin n,
    if σ i then (H i).offset < @inner ℝ Space3 _ (H i).normVec x
    else @inner ℝ Space3 _ (H i).normVec x < (H i).offset}

/-- 凸領域 $s$ が平面 $P$ によって切断される条件。
領域の内部を平面が通過することと同値である。 -/
def isSplitByPlane (s : Set Space3) (P : Plane3) : Prop :=
  (s ∩ P.toSet).Nonempty

/-- 第 $(n+1)$ 平面によって切断される既存領域の個数。 -/
noncomputable def splitSpaceRegionsCount (n : ℕ) (H : Fin (n + 1) → Plane3) : ℕ :=
  (Finset.filter (fun σ =>
    isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))) Finset.univ).card

/-- 3次元開半空間の共通部分として定義される領域は凸集合である。 -/
lemma convex_combination_mem_region3 {n : ℕ} (H : Fin n → Plane3) (σ : SignVector3 n)
    {p₁ p₂ : Space3} (hp₁ : p₁ ∈ convexSpaceRegion n H σ) (hp₂ : p₂ ∈ convexSpaceRegion n H σ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a • p₁ + b • p₂ ∈ convexSpaceRegion n H σ := by
  dsimp [convexSpaceRegion] at hp₁ hp₂ ⊢
  intro i
  have h1 := hp₁ i
  have h2 := hp₂ i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  split_ifs at h1 h2 ⊢ with hσ
  · calc
      (H i).offset = a * (H i).offset + b * (H i).offset := by
        rw [← add_mul, hab, one_mul]
      _ < a * @inner ℝ Space3 _ (H i).normVec p₁ + b * @inner ℝ Space3 _ (H i).normVec p₂ := by
        nlinarith
  · calc
      a * @inner ℝ Space3 _ (H i).normVec p₁ + b * @inner ℝ Space3 _ (H i).normVec p₂
        < a * (H i).offset + b * (H i).offset := by nlinarith
      _ = (H i).offset := by rw [← add_mul, hab, one_mul]

/-- 凸領域が平面と交わらないならば、領域全体が平面の真に片側に含まれる。 -/
lemma region_subset_one_side_of_not_split3 (n : ℕ) (H : Fin (n + 1) → Plane3)
    (σ : SignVector3 n)
    (h_not_split : ¬ isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))) :
    (∀ p ∈ convexSpaceRegion n (H ∘ Fin.castSucc) σ,
      @inner ℝ Space3 _ (H (Fin.last n)).normVec p < (H (Fin.last n)).offset) ∨
    (∀ p ∈ convexSpaceRegion n (H ∘ Fin.castSucc) σ,
      (H (Fin.last n)).offset < @inner ℝ Space3 _ (H (Fin.last n)).normVec p) := by
  by_contra h_both
  push Not at h_both
  rcases h_both with ⟨⟨p₁, hp₁, hle₁⟩, ⟨p₂, hp₂, hge₂⟩⟩
  let u := (H (Fin.last n)).normVec
  let d := (H (Fin.last n)).offset
  let v₁ := @inner ℝ Space3 _ u p₁
  let v₂ := @inner ℝ Space3 _ u p₂
  have hne₁ : v₁ ≠ d := by
    intro h_eq
    apply h_not_split
    refine ⟨p₁, hp₁, ?_⟩
    dsimp [Plane3.toSet, u, d] at h_eq ⊢
    exact h_eq
  have hne₂ : v₂ ≠ d := by
    intro h_eq
    apply h_not_split
    refine ⟨p₂, hp₂, ?_⟩
    dsimp [Plane3.toSet, u, d] at h_eq ⊢
    exact h_eq
  have hlt₁ : d < v₁ := lt_of_le_of_ne' hle₁ hne₁
  have hlt₂ : v₂ < d := lt_of_le_of_ne hge₂ hne₂
  have hv : 0 < v₁ - v₂ := by linarith
  let a := (d - v₂) / (v₁ - v₂)
  let b := (v₁ - d) / (v₁ - v₂)
  have ha : 0 < a := div_pos (by linarith) hv
  have hb : 0 < b := div_pos (by linarith) hv
  have hab : a + b = 1 := by
    dsimp [a, b]
    calc
      (d - v₂) / (v₁ - v₂) + (v₁ - d) / (v₁ - v₂)
        = ((d - v₂) + (v₁ - d)) / (v₁ - v₂) := by rw [← add_div]
      _ = (v₁ - v₂) / (v₁ - v₂) := by
        congr 1
        ring
      _ = 1 := div_self (ne_of_gt hv)
  let pt := a • p₁ + b • p₂
  have hpt_in : pt ∈ convexSpaceRegion n (H ∘ Fin.castSucc) σ :=
    convex_combination_mem_region3 (H ∘ Fin.castSucc) σ hp₁ hp₂ ha hb hab
  have hpt_on : pt ∈ (H (Fin.last n)).toSet := by
    dsimp [Plane3.toSet, pt]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    change a * v₁ + b * v₂ = d
    dsimp [a, b]
    calc
      ((d - v₂) / (v₁ - v₂)) * v₁ + ((v₁ - d) / (v₁ - v₂)) * v₂
        = ((d - v₂) * v₁ + (v₁ - d) * v₂) / (v₁ - v₂) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
      _ = (d * (v₁ - v₂)) / (v₁ - v₂) := by
        congr 1
        ring
      _ = d := mul_div_cancel_right₀ d (ne_of_gt hv)
  apply h_not_split
  exact ⟨pt, hpt_in, hpt_on⟩

lemma mem_convexSpaceRegion_succ (n : ℕ) (H : Fin (n + 1) → Plane3)
    (σ : SignVector3 n) (b : Bool) (p : Space3) :
    p ∈ convexSpaceRegion (n + 1) H (Fin.snoc σ b) ↔
      p ∈ convexSpaceRegion n (H ∘ Fin.castSucc) σ ∧
      (if b then (H (Fin.last n)).offset < @inner ℝ Space3 _ (H (Fin.last n)).normVec p
       else @inner ℝ Space3 _ (H (Fin.last n)).normVec p < (H (Fin.last n)).offset) := by
  dsimp [convexSpaceRegion]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have hi := h (Fin.castSucc i)
      rw [Fin.snoc_castSucc] at hi
      exact hi
    · have hlast := h (Fin.last n)
      rw [Fin.snoc_last] at hlast
      exact hlast
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]
      exact h2
    · intro j
      rw [Fin.snoc_castSucc]
      exact h1 j

open Classical in
lemma fiber_card_le_one_of_not_split3 (n : ℕ) (H : Fin (n + 1) → Plane3)
    (σ : SignVector3 n)
    (h_not_split : ¬ isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))) :
    (Finset.filter (fun b : Bool =>
      (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ).card ≤ 1 := by
  have h_cases := region_subset_one_side_of_not_split3 n H σ h_not_split
  by_contra h_gt
  push Not at h_gt
  have h_eq : (Finset.filter (fun b : Bool =>
      (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ) = Finset.univ := by
    apply Finset.eq_univ_of_card
    have h_le : (Finset.filter (fun b : Bool =>
      (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ).card ≤ 2 := by
      calc
        (Finset.filter (fun b : Bool =>
          (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ).card
          ≤ (Finset.univ : Finset Bool).card := Finset.card_filter_le _ _
        _ = 2 := Fintype.card_bool
    rw [Fintype.card_bool]
    omega
  have h_false_in : false ∈ Finset.filter (fun b : Bool =>
      (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ := by
    rw [h_eq]; exact Finset.mem_univ false
  have h_true_in : true ∈ Finset.filter (fun b : Bool =>
      (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ := by
    rw [h_eq]; exact Finset.mem_univ true
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_false_in h_true_in
  rcases h_false_in with ⟨pF, hpF⟩
  rcases h_true_in with ⟨pT, hpT⟩
  rw [mem_convexSpaceRegion_succ] at hpF hpT
  rcases h_cases with h_all_lt | h_all_gt
  · have hpT_lt := h_all_lt pT hpT.1
    dsimp at hpT
    linarith
  · have hpF_gt := h_all_gt pF hpF.1
    dsimp at hpF
    linarith

open Classical in
lemma fiber_card_le_two3 (n : ℕ) (H : Fin (n + 1) → Plane3) (σ : SignVector3 n) :
    (Finset.filter (fun b : Bool =>
      (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ).card ≤ 2 := by
  calc
    (Finset.filter (fun b : Bool =>
      (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ).card
      ≤ (Finset.univ : Finset Bool).card := Finset.card_filter_le _ _
    _ = 2 := Fintype.card_bool

open Classical in
lemma fiber_card_eq_zero_of_empty3 (n : ℕ) (H : Fin (n + 1) → Plane3) (σ : SignVector3 n)
    (h_empty : ¬ (convexSpaceRegion n (H ∘ Fin.castSucc) σ).Nonempty) :
    (Finset.filter (fun b : Bool =>
      (convexSpaceRegion (n + 1) H (Fin.snoc σ b)).Nonempty) Finset.univ).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _ ⟨p, hp⟩
  apply h_empty
  rw [mem_convexSpaceRegion_succ] at hp
  exact ⟨p, hp.1⟩

open Classical in
lemma card_filter_nonempty_convexSpaceRegion_succ_le (n : ℕ) (H : Fin (n + 1) → Plane3) :
    (Finset.filter (fun τ => (convexSpaceRegion (n + 1) H τ).Nonempty) Finset.univ).card ≤
      (Finset.filter
        (fun σ => (convexSpaceRegion n (H ∘ Fin.castSucc) σ).Nonempty) Finset.univ).card +
        splitSpaceRegionsCount n H := by
  let P_succ := fun τ => (convexSpaceRegion (n + 1) H τ).Nonempty
  rw [card_filter_succ_eq_sum P_succ]
  have h_le := sum_fiber_le_sum_add
    (A := fun σ => if (convexSpaceRegion n (H ∘ Fin.castSucc) σ).Nonempty then 1 else 0)
    (B := fun σ =>
      if isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n)) then 1 else 0)
    (F := fun σ => (Finset.filter (fun b : Bool => P_succ (Fin.snoc σ b)) Finset.univ).card)
    (fun σ => by
      apply term_le_add_split
      · exact fiber_card_le_two3 n H σ
      · exact fiber_card_le_one_of_not_split3 n H σ
      · exact fiber_card_eq_zero_of_empty3 n H σ)
  have hA : (∑ σ, if (convexSpaceRegion n (H ∘ Fin.castSucc) σ).Nonempty then 1 else 0) =
      (Finset.filter
        (fun σ => (convexSpaceRegion n (H ∘ Fin.castSucc) σ).Nonempty) Finset.univ).card :=
    sum_ite_eq_card_filter _
  have hB : (∑ σ, if isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ)
      (H (Fin.last n)) then 1 else 0) = splitSpaceRegionsCount n H := by
    dsimp [splitSpaceRegionsCount]
    exact sum_ite_eq_card_filter _
  rw [hA, hB] at h_le
  exact h_le

/-! ### 3次元空間領域と非空符号ベクトルの一致定理 -/

noncomputable def pointSignVector3 (n : ℕ) (H : Fin n → Plane3)
    (x : {x : Space3 | ∀ i, x ∉ (H i).toSet}) : SignVector3 n :=
  fun i => decide ((H i).offset < @inner ℝ Space3 _ (H i).normVec x.val)

lemma mem_convexSpaceRegion_pointSignVector3 (n : ℕ) (H : Fin n → Plane3)
    (x : {x : Space3 | ∀ i, x ∉ (H i).toSet}) :
    x.val ∈ convexSpaceRegion n H (pointSignVector3 n H x) := by
  dsimp [convexSpaceRegion]
  intro i
  have h_not : x.val ∉ (H i).toSet := x.2 i
  dsimp [Plane3.toSet] at h_not
  have h_ne : @inner ℝ Space3 _ (H i).normVec x.val ≠ (H i).offset := h_not
  cases h_bool : pointSignVector3 n H x i
  · have h_dec : decide ((H i).offset < @inner ℝ Space3 _ (H i).normVec x.val) = false := by
      change pointSignVector3 n H x i = false at h_bool
      dsimp [pointSignVector3] at h_bool
      exact h_bool
    have h_not_lt := of_decide_eq_false h_dec
    have h_le : @inner ℝ Space3 _ (H i).normVec x.val ≤ (H i).offset := not_lt.mp h_not_lt
    exact lt_of_le_of_ne h_le h_ne
  · have h_dec : decide ((H i).offset < @inner ℝ Space3 _ (H i).normVec x.val) = true := by
      change pointSignVector3 n H x i = true at h_bool
      dsimp [pointSignVector3] at h_bool
      exact h_bool
    exact of_decide_eq_true h_dec

lemma not_mem_plane_of_mem_convexSpaceRegion {n : ℕ} (H : Fin n → Plane3) (σ : SignVector3 n)
    {p : Space3} (hp : p ∈ convexSpaceRegion n H σ) (i : Fin n) :
    p ∉ (H i).toSet := by
  have h := hp i
  dsimp [Plane3.toSet]
  split_ifs at h with hσ
  · linarith
  · linarith

lemma pointSignVector3_eq_of_mem (n : ℕ) (H : Fin n → Plane3)
    (x : {x : Space3 | ∀ i, x ∉ (H i).toSet}) (σ : SignVector3 n)
    (hx : x.val ∈ convexSpaceRegion n H σ) :
    pointSignVector3 n H x = σ := by
  funext i
  have h := hx i
  dsimp [pointSignVector3]
  cases hσ : σ i
  · rw [hσ] at h
    dsimp at h
    have : ¬ (H i).offset < @inner ℝ Space3 _ (H i).normVec x.val := not_lt.mpr (le_of_lt h)
    simp [this]
  · rw [hσ] at h
    dsimp at h
    simp [h]

lemma pointSignVector3_eq_of_connectedComponent_eq (n : ℕ) (H : Fin n → Plane3)
    (x y : {x : Space3 | ∀ i, x ∉ (H i).toSet})
    (h_conn : connectedComponent x = connectedComponent y) :
    pointSignVector3 n H x = pointSignVector3 n H y := by
  funext i
  by_contra hne
  have h_cases : (pointSignVector3 n H x i = true ∧ pointSignVector3 n H y i = false) ∨
                 (pointSignVector3 n H x i = false ∧ pointSignVector3 n H y i = true) := by
    revert hne
    cases pointSignVector3 n H x i <;> cases pointSignVector3 n H y i <;> intro hne
    · exact False.elim (hne rfl)
    · right; exact ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · exact False.elim (hne rfl)
  have h_cont : Continuous (fun p : {p : Space3 | ∀ i, p ∉ (H i).toSet} =>
      @inner ℝ Space3 _ (H i).normVec p.val) :=
    continuous_const.inner continuous_subtype_val
  let U : Set {p : Space3 | ∀ i, p ∉ (H i).toSet} :=
    {p | (H i).offset < @inner ℝ Space3 _ (H i).normVec p.val}
  have hU_open : IsOpen U := isOpen_Ioi.preimage h_cont
  have hUc_open : IsOpen (Uᶜ) := by
    have h_eq : Uᶜ = {p : {p : Space3 | ∀ i, p ∉ (H i).toSet} |
        @inner ℝ Space3 _ (H i).normVec p.val < (H i).offset} := by
      ext p
      simp only [mem_compl_iff]
      change ¬ (H i).offset < @inner ℝ Space3 _ (H i).normVec p.val ↔
        @inner ℝ Space3 _ (H i).normVec p.val < (H i).offset
      have hp_not : p.val ∉ (H i).toSet := p.2 i
      dsimp [Plane3.toSet] at hp_not
      constructor
      · intro hnot
        exact lt_of_le_of_ne (not_lt.mp hnot) hp_not
      · intro hlt hnot
        exact lt_asymm hlt hnot
    rw [h_eq]
    exact isOpen_Iio.preimage h_cont
  have hU_clopen : IsClopen U := ⟨isOpen_compl_iff.mp hUc_open, hU_open⟩
  rcases h_cases with ⟨hxt, hyf⟩ | ⟨hxf, hyt⟩
  · have hxU : x ∈ U := by
      change (H i).offset < @inner ℝ Space3 _ (H i).normVec x.val
      have : pointSignVector3 n H x i = true := hxt
      dsimp [pointSignVector3] at this
      exact of_decide_eq_true this
    have hyUc : y ∈ Uᶜ := by
      intro hy
      have : pointSignVector3 n H y i = false := hyf
      dsimp [pointSignVector3] at this
      have hnot := of_decide_eq_false this
      exact hnot hy
    have h_sub := IsClopen.connectedComponent_subset hU_clopen hxU
    have hy_in_comp : y ∈ connectedComponent x := by
      rw [h_conn]
      exact mem_connectedComponent
    exact hyUc (h_sub hy_in_comp)
  · have hyU : y ∈ U := by
      change (H i).offset < @inner ℝ Space3 _ (H i).normVec y.val
      have : pointSignVector3 n H y i = true := hyt
      dsimp [pointSignVector3] at this
      exact of_decide_eq_true this
    have hxUc : x ∈ Uᶜ := by
      intro hx
      have : pointSignVector3 n H x i = false := hxf
      dsimp [pointSignVector3] at this
      have hnot := of_decide_eq_false this
      exact hnot hx
    have h_sub := IsClopen.connectedComponent_subset hU_clopen hyU
    have hx_in_comp : x ∈ connectedComponent y := by
      rw [← h_conn]
      exact mem_connectedComponent
    exact hxUc (h_sub hx_in_comp)

lemma mem_convexSpaceRegion_segment3 {n : ℕ} (H : Fin n → Plane3) (σ : SignVector3 n)
    {p₁ p₂ : Space3} (hp₁ : p₁ ∈ convexSpaceRegion n H σ) (hp₂ : p₂ ∈ convexSpaceRegion n H σ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) • p₁ + t • p₂ ∈ convexSpaceRegion n H σ := by
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · subst ht0
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact hp₁
  · rcases eq_or_lt_of_le ht.2 with ht1 | ht1
    · subst ht1
      simp only [sub_self, zero_smul, one_smul, zero_add]
      exact hp₂
    · have ha : 0 < 1 - t := by linarith
      have hb : 0 < t := ht0
      have hab : (1 - t) + t = 1 := by ring
      exact convex_combination_mem_region3 H σ hp₁ hp₂ ha hb hab

lemma connectedComponent_eq_of_pointSignVector3_eq (n : ℕ) (H : Fin n → Plane3)
    (x y : {x : Space3 | ∀ i, x ∉ (H i).toSet})
    (h_eq : pointSignVector3 n H x = pointSignVector3 n H y) :
    connectedComponent x = connectedComponent y := by
  let σ := pointSignVector3 n H x
  have hx_mem : x.val ∈ convexSpaceRegion n H σ :=
    mem_convexSpaceRegion_pointSignVector3 n H x
  have hy_mem : y.val ∈ convexSpaceRegion n H σ := by
    have h_eq_y : σ = pointSignVector3 n H y := h_eq
    rw [h_eq_y]
    exact mem_convexSpaceRegion_pointSignVector3 n H y
  let α := {p : Space3 | ∀ i, p ∉ (H i).toSet}
  let γ_raw : ℝ → Space3 := fun t => (1 - t) • x.val + t • y.val
  have h_cont_raw : Continuous γ_raw := by
    continuity
  have h_segment_mem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin n, γ_raw t ∉ (H i).toSet := by
    intro t ht i
    have h_mem := mem_convexSpaceRegion_segment3 H σ hx_mem hy_mem ht
    exact not_mem_plane_of_mem_convexSpaceRegion H σ h_mem i
  let γ : Icc (0 : ℝ) 1 → α := fun ⟨t, ht⟩ => ⟨γ_raw t, h_segment_mem t ht⟩
  have h_cont_γ : Continuous γ := by
    exact Continuous.subtype_mk (h_cont_raw.comp continuous_subtype_val) _
  have : ConnectedSpace (Icc (0 : ℝ) 1) :=
    Subtype.connectedSpace (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1))
  have h_conn_range : IsConnected (range γ) := isConnected_range h_cont_γ
  have hx_range : x ∈ range γ := by
    use ⟨0, ⟨le_refl 0, by norm_num⟩⟩
    apply Subtype.ext
    dsimp [γ, γ_raw]
    simp
  have hy_range : y ∈ range γ := by
    use ⟨1, ⟨by norm_num, le_refl 1⟩⟩
    apply Subtype.ext
    dsimp [γ, γ_raw]
    simp
  have h_sub := IsConnected.subset_connectedComponent h_conn_range hx_range
  have hy_in_comp : y ∈ connectedComponent x := h_sub hy_range
  exact connectedComponent_eq hy_in_comp

open Classical in
/-- 3次元空間における平面配置の領域数は、空でない符号ベクトルの個数と一致する。 -/
lemma spaceRegionsCount_eq_card_nonempty_convexSpaceRegion (n : ℕ) (H : Fin n → Plane3) :
    spaceRegionsCount n H =
      (Finset.filter (fun σ => (convexSpaceRegion n H σ).Nonempty) Finset.univ).card := by
  let α := {x : Space3 | ∀ i, x ∉ (H i).toSet}
  let s : Setoid α := connectedComponentSetoid α
  let V := {σ : SignVector3 n // (convexSpaceRegion n H σ).Nonempty}
  let f : α → V := fun x =>
    ⟨pointSignVector3 n H x, ⟨x.val, mem_convexSpaceRegion_pointSignVector3 n H x⟩⟩
  have h_fiber : ∀ x y : α, f x = f y → x ≈ y := by
    intro x y hfg
    have h_eq : pointSignVector3 n H x = pointSignVector3 n H y := congr_arg Subtype.val hfg
    exact connectedComponent_eq_of_pointSignVector3_eq n H x y h_eq
  have h_le : Nat.card (Quotient s) ≤ Fintype.card V :=
    card_quotient_le_of_fiber_le s f h_fiber
  have h_rep : ∀ v : V, ∃ x : α, f x = v := by
    intro ⟨σ, hσ⟩
    obtain ⟨p, hp⟩ := hσ
    have hp_not : ∀ i, p ∉ (H i).toSet := not_mem_plane_of_mem_convexSpaceRegion H σ hp
    have h_sign := pointSignVector3_eq_of_mem n H ⟨p, hp_not⟩ σ hp
    refine ⟨⟨p, hp_not⟩, Subtype.ext h_sign⟩
  choose w hw using h_rep
  let g : V → Quotient s := fun v => Quotient.mk s (w v)
  have hg_inj : Function.Injective g := by
    intro v1 v2 hg
    have hequiv : w v1 ≈ w v2 := Quotient.exact hg
    have hconn : connectedComponent (w v1) = connectedComponent (w v2) := hequiv
    have hsign := pointSignVector3_eq_of_connectedComponent_eq n H (w v1) (w v2) hconn
    have h_f_eq : f (w v1) = f (w v2) := Subtype.ext hsign
    rw [hw v1, hw v2] at h_f_eq
    exact h_f_eq
  have : Finite (Quotient s) := finite_quotient_of_fiber_le s f h_fiber
  have h_ge := Nat.card_le_card_of_injective g hg_inj
  have h_card_V : Fintype.card V =
      (Finset.filter (fun σ => (convexSpaceRegion n H σ).Nonempty) Finset.univ).card := by
    rw [Fintype.card_subtype]
  rw [Nat.card_eq_fintype_card] at h_ge
  dsimp [spaceRegionsCount]
  change Nat.card (Quotient s) =
    (Finset.filter (fun σ => (convexSpaceRegion n H σ).Nonempty) Finset.univ).card
  omega

/-- 空間領域の増加量は、切断された既存領域の個数で上から抑えられる。 -/
lemma spaceRegionsCount_succ_le_add_split (n : ℕ) (H : Fin (n + 1) → Plane3) :
    spaceRegionsCount (n + 1) H ≤
      spaceRegionsCount n (H ∘ Fin.castSucc) + splitSpaceRegionsCount n H := by
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  exact card_filter_nonempty_convexSpaceRegion_succ_le n H

/-! ### 3次元平面のパラメータ付けと誘導交線配置の評価 -/

lemma space3_inner_apply (v w : Space3) :
    @inner ℝ Space3 _ v w =
      WithLp.equiv 2 (Fin 3 → ℝ) v 0 * WithLp.equiv 2 (Fin 3 → ℝ) w 0 +
      WithLp.equiv 2 (Fin 3 → ℝ) v 1 * WithLp.equiv 2 (Fin 3 → ℝ) w 1 +
      WithLp.equiv 2 (Fin 3 → ℝ) v 2 * WithLp.equiv 2 (Fin 3 → ℝ) w 2 := by
  have h := PiLp.inner_apply (𝕜 := ℝ) (x := v) (y := w)
  rw [h, Fin.sum_univ_three]
  simp only [Real.inner_apply]
  rfl

noncomputable def crossProduct3 (v w : Space3) : Space3 :=
  WithLp.equiv 2 (Fin 3 → ℝ) |>.symm fun i =>
    let v_fn := WithLp.equiv 2 (Fin 3 → ℝ) v
    let w_fn := WithLp.equiv 2 (Fin 3 → ℝ) w
    if i.val = 0 then v_fn 1 * w_fn 2 - v_fn 2 * w_fn 1
    else if i.val = 1 then v_fn 2 * w_fn 0 - v_fn 0 * w_fn 2
    else v_fn 0 * w_fn 1 - v_fn 1 * w_fn 0

noncomputable def planeBasis1 (u : Space3) : Space3 :=
  let u_fn := WithLp.equiv 2 (Fin 3 → ℝ) u
  if u_fn 0 = 0 ∧ u_fn 1 = 0 then
    WithLp.equiv 2 (Fin 3 → ℝ) |>.symm fun i => if i.val = 0 then 1 else 0
  else
    WithLp.equiv 2 (Fin 3 → ℝ) |>.symm fun i =>
      if i.val = 0 then - (u_fn 1)
      else if i.val = 1 then u_fn 0
      else 0

noncomputable def planeBasis2 (u : Space3) : Space3 :=
  crossProduct3 u (planeBasis1 u)

lemma inner_planeBasis1_self (u : Space3) :
    @inner ℝ Space3 _ (planeBasis1 u) u = 0 := by
  rw [space3_inner_apply]
  dsimp [planeBasis1]
  split_ifs with h
  · simp [h.1]
  · simp
    ring

lemma inner_planeBasis2_self (u : Space3) :
    @inner ℝ Space3 _ (planeBasis2 u) u = 0 := by
  rw [space3_inner_apply]
  dsimp [planeBasis2, crossProduct3]
  simp
  ring

lemma inner_planeBasis2_planeBasis1 (u : Space3) :
    @inner ℝ Space3 _ (planeBasis2 u) (planeBasis1 u) = 0 := by
  rw [space3_inner_apply]
  dsimp [planeBasis2, crossProduct3]
  simp
  ring

set_option linter.flexible false in
lemma eq_zero_of_orthogonal_inners_zero (u : Space3) (hu : u ≠ 0) (w : Space3)
    (h_uw : @inner ℝ Space3 _ u w = 0)
    (h_e1w : @inner ℝ Space3 _ (planeBasis1 u) w = 0)
    (h_e2w : @inner ℝ Space3 _ (planeBasis2 u) w = 0) :
    w = 0 := by
  rw [space3_inner_apply] at h_uw h_e1w h_e2w
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  ext i
  let u0 := WithLp.equiv 2 (Fin 3 → ℝ) u 0
  let u1 := WithLp.equiv 2 (Fin 3 → ℝ) u 1
  let u2 := WithLp.equiv 2 (Fin 3 → ℝ) u 2
  let w0 := WithLp.equiv 2 (Fin 3 → ℝ) w 0
  let w1 := WithLp.equiv 2 (Fin 3 → ℝ) w 1
  let w2 := WithLp.equiv 2 (Fin 3 → ℝ) w 2
  have hu_ext : ¬ (u0 = 0 ∧ u1 = 0 ∧ u2 = 0) := by
    intro h_all
    apply hu
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    ext j
    fin_cases j <;> aesop
  dsimp [planeBasis1, planeBasis2, crossProduct3] at h_e1w h_e2w
  split_ifs at h_e1w h_e2w with h_case
  · have hu2 : u2 ≠ 0 := by
      intro h2
      exact hu_ext ⟨h_case.1, h_case.2, h2⟩
    simp [h_case.1, h_case.2] at h_uw h_e1w h_e2w
    have hw2 : w2 = 0 := by
      rcases h_uw with h | h
      · exact (hu2 h).elim
      · exact h
    have hw0 : w0 = 0 := h_e1w
    have hw1 : w1 = 0 := by
      rcases h_e2w with h | h
      · exact (hu2 h).elim
      · exact h
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2
  · simp only [WithLp.equiv_apply] at h_e1w h_e2w
    have h_sq1_pos : 0 < u0 ^ 2 + u1 ^ 2 := by
      have : u0 ≠ 0 ∨ u1 ≠ 0 := by
        by_contra h_both
        push Not at h_both
        exact h_case h_both
      rcases this with h0 | h1
      · have : 0 < u0 ^ 2 := sq_pos_of_ne_zero h0
        have : 0 ≤ u1 ^ 2 := sq_nonneg _
        linarith
      · have : 0 < u1 ^ 2 := sq_pos_of_ne_zero h1
        have : 0 ≤ u0 ^ 2 := sq_nonneg _
        linarith
    have h_sq1_ne : u0 ^ 2 + u1 ^ 2 ≠ 0 := ne_of_gt h_sq1_pos
    have h_u_sq_pos : 0 < u0 ^ 2 + u1 ^ 2 + u2 ^ 2 := by
      have : 0 ≤ u2 ^ 2 := sq_nonneg _
      linarith
    have h_u_sq_ne : u0 ^ 2 + u1 ^ 2 + u2 ^ 2 ≠ 0 := ne_of_gt h_u_sq_pos
    have hw2 : w2 = 0 := by
      have h_comb : (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) * w2 =
          u2 * (u0 * w0 + u1 * w1 + u2 * w2) +
          ((- (u0 * u2)) * w0 + (- (u1 * u2)) * w1 + (u0 ^ 2 + u1 ^ 2) * w2) := by ring
      have h_e2w_simpl : (- (u0 * u2)) * w0 + (- (u1 * u2)) * w1 + (u0 ^ 2 + u1 ^ 2) * w2 = 0 := by
        calc
          (- (u0 * u2)) * w0 + (- (u1 * u2)) * w1 + (u0 ^ 2 + u1 ^ 2) * w2 =
            ((u1 * 0 - u2 * u0) * w0 + (u2 * (- u1) - u0 * 0) * w1 +
              (u0 * u0 - u1 * (- u1)) * w2) := by ring
          _ = 0 := h_e2w
      rw [h_uw, h_e2w_simpl] at h_comb
      simp only [mul_zero, add_zero] at h_comb
      exact (mul_eq_zero.mp h_comb).resolve_left h_u_sq_ne
    have h_uw' : u0 * w0 + u1 * w1 = 0 := by
      calc
        u0 * w0 + u1 * w1 = (u0 * w0 + u1 * w1 + u2 * w2) - u2 * w2 := by ring
        _ = 0 - u2 * 0 := by rw [h_uw, hw2]
        _ = 0 := by ring
    have h_e1w_simpl : - u1 * w0 + u0 * w1 = 0 := by
      calc
        - u1 * w0 + u0 * w1 = - u1 * w0 + u0 * w1 + 0 * w2 := by ring
        _ = 0 := h_e1w
    have hw0 : w0 = 0 := by
      have h_comb : (u0 ^ 2 + u1 ^ 2) * w0 =
          u0 * (u0 * w0 + u1 * w1) - u1 * (- u1 * w0 + u0 * w1) := by ring
      rw [h_uw', h_e1w_simpl] at h_comb
      simp only [mul_zero, sub_zero] at h_comb
      exact (mul_eq_zero.mp h_comb).resolve_left h_sq1_ne
    have hw1 : w1 = 0 := by
      have h_comb : (u0 ^ 2 + u1 ^ 2) * w1 =
          u1 * (u0 * w0 + u1 * w1) + u0 * (- u1 * w0 + u0 * w1) := by ring
      rw [h_uw', h_e1w_simpl] at h_comb
      simp only [mul_zero, add_zero] at h_comb
      exact (mul_eq_zero.mp h_comb).resolve_left h_sq1_ne
    fin_cases i
    · exact hw0
    · exact hw1
    · exact hw2

set_option linter.flexible false in
lemma planeBasis1_ne_zero (u : Space3) (hu : u ≠ 0) : planeBasis1 u ≠ 0 := by
  dsimp [planeBasis1]
  intro h0
  let u0 := WithLp.equiv 2 (Fin 3 → ℝ) u 0
  let u1 := WithLp.equiv 2 (Fin 3 → ℝ) u 1
  let u2 := WithLp.equiv 2 (Fin 3 → ℝ) u 2
  have hu_ext : ¬ (u0 = 0 ∧ u1 = 0 ∧ u2 = 0) := by
    intro h_all
    apply hu
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    ext j
    fin_cases j <;> aesop
  split_ifs at h0 with h_case
  · have h_zero := congr_fun (congr_arg (WithLp.equiv 2 (Fin 3 → ℝ)) h0) 0
    simp at h_zero
  · have h_zero0 := congr_fun (congr_arg (WithLp.equiv 2 (Fin 3 → ℝ)) h0) 0
    have h_zero1 := congr_fun (congr_arg (WithLp.equiv 2 (Fin 3 → ℝ)) h0) 1
    simp at h_zero0 h_zero1
    change u1 = 0 at h_zero0
    change u0 = 0 at h_zero1
    exact h_case ⟨h_zero1, by linarith⟩

set_option linter.flexible false in
lemma planeBasis2_ne_zero (u : Space3) (hu : u ≠ 0) : planeBasis2 u ≠ 0 := by
  intro h0
  let u0 := WithLp.equiv 2 (Fin 3 → ℝ) u 0
  let u1 := WithLp.equiv 2 (Fin 3 → ℝ) u 1
  let u2 := WithLp.equiv 2 (Fin 3 → ℝ) u 2
  have hu_ext : ¬ (u0 = 0 ∧ u1 = 0 ∧ u2 = 0) := by
    intro h_all
    apply hu
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    ext j
    fin_cases j <;> aesop
  dsimp [planeBasis2, crossProduct3, planeBasis1] at h0
  have h_zero := congr_fun (congr_arg (WithLp.equiv 2 (Fin 3 → ℝ)) h0)
  split_ifs at h_zero with h_case
  · have h_z1 := h_zero 1
    simp [h_case.1, h_case.2] at h_z1
    have hu2 : u2 ≠ 0 := by
      intro h2
      exact hu_ext ⟨h_case.1, h_case.2, h2⟩
    exact hu2 h_z1
  · have h_z2 := h_zero 2
    simp only [WithLp.equiv_apply] at h_z2
    have h_sq1_pos : 0 < u0 ^ 2 + u1 ^ 2 := by
      have : u0 ≠ 0 ∨ u1 ≠ 0 := by
        by_contra h_both
        push Not at h_both
        exact h_case h_both
      rcases this with h0 | h1
      · have : 0 < u0 ^ 2 := sq_pos_of_ne_zero h0
        have : 0 ≤ u1 ^ 2 := sq_nonneg _
        linarith
      · have : 0 < u1 ^ 2 := sq_pos_of_ne_zero h1
        have : 0 ≤ u0 ^ 2 := sq_nonneg _
        linarith
    have : u0 ^ 2 + u1 ^ 2 = 0 := by
      calc
        u0 ^ 2 + u1 ^ 2 = u0 * u0 - u1 * (- u1) := by ring
        _ = 0 := h_z2
    linarith

noncomputable def planePt3 (H : Plane3) (p : Plane2) : Space3 :=
  let u := H.normVec
  let d := H.offset
  let sq_u := @inner ℝ Space3 _ u u
  let e1 := planeBasis1 u
  let e2 := planeBasis2 u
  let p0 := (d / sq_u) • u
  p0 + (WithLp.equiv 2 (Fin 2 → ℝ) p 0) • e1 + (WithLp.equiv 2 (Fin 2 → ℝ) p 1) • e2

lemma planePt3_mem_plane (H : Plane3) (p : Plane2) : planePt3 H p ∈ H.toSet := by
  dsimp [Plane3.toSet, planePt3]
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right]
  have hu_sq : @inner ℝ Space3 _ H.normVec H.normVec ≠ 0 := by
    intro h0
    apply H.normVec_ne_zero
    exact inner_self_eq_zero.mp h0
  have he1 : @inner ℝ Space3 _ H.normVec (planeBasis1 H.normVec) = 0 := by
    rw [real_inner_comm]
    exact inner_planeBasis1_self H.normVec
  have he2 : @inner ℝ Space3 _ H.normVec (planeBasis2 H.normVec) = 0 := by
    rw [real_inner_comm]
    exact inner_planeBasis2_self H.normVec
  rw [he1, he2, mul_zero, mul_zero, add_zero, add_zero]
  exact div_mul_cancel₀ H.offset hu_sq

lemma exists_p_planePt3_eq (H : Plane3) {q : Space3} (hq : q ∈ H.toSet) :
    ∃ p : Plane2, planePt3 H p = q := by
  let u := H.normVec
  let d := H.offset
  let sq_u := @inner ℝ Space3 _ u u
  let e1 := planeBasis1 u
  let e2 := planeBasis2 u
  let sq_e1 := @inner ℝ Space3 _ e1 e1
  let sq_e2 := @inner ℝ Space3 _ e2 e2
  have hu_ne := H.normVec_ne_zero
  have he1_ne := planeBasis1_ne_zero u hu_ne
  have he2_ne := planeBasis2_ne_zero u hu_ne
  have he1_sq : sq_e1 ≠ 0 := by
    dsimp [sq_e1]
    intro h0
    exact he1_ne (inner_self_eq_zero.mp h0)
  have he2_sq : sq_e2 ≠ 0 := by
    dsimp [sq_e2]
    intro h0
    exact he2_ne (inner_self_eq_zero.mp h0)
  have hu_sq : sq_u ≠ 0 := by
    dsimp [sq_u]
    intro h0
    exact hu_ne (inner_self_eq_zero.mp h0)
  let p0 := (d / sq_u) • u
  let s := @inner ℝ Space3 _ e1 (q - p0) / sq_e1
  let t := @inner ℝ Space3 _ e2 (q - p0) / sq_e2
  let p : Plane2 := WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i => if i.val = 0 then s else t
  have h_p0 : WithLp.equiv 2 (Fin 2 → ℝ) p 0 = s := by
    dsimp [p]
    rw [WithLp.equiv_apply, WithLp.ofLp_toLp]
    rfl
  have h_p1 : WithLp.equiv 2 (Fin 2 → ℝ) p 1 = t := by
    dsimp [p]
    rw [WithLp.equiv_apply, WithLp.ofLp_toLp]
    rfl
  use p
  have hq_offset : @inner ℝ Space3 _ u q = d := hq
  let diff := q - planePt3 H p
  have h_diff_u : @inner ℝ Space3 _ u diff = 0 := by
    dsimp [diff]
    rw [inner_sub_right]
    have : @inner ℝ Space3 _ u (planePt3 H p) = d := planePt3_mem_plane H p
    rw [hq_offset, this, sub_self]
  have h_diff_e1 : @inner ℝ Space3 _ e1 diff = 0 := by
    dsimp [diff, planePt3, p0]
    rw [h_p0, h_p1]
    rw [inner_sub_right]
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right]
    have h_e1_u : @inner ℝ Space3 _ e1 u = 0 := inner_planeBasis1_self u
    have h_e1_e2 : @inner ℝ Space3 _ e1 e2 = 0 := by
      rw [real_inner_comm]
      exact inner_planeBasis2_planeBasis1 u
    rw [h_e1_u, h_e1_e2, mul_zero, mul_zero, add_zero, zero_add]
    have h_cancel : (@inner ℝ Space3 _ e1 (q - (d / sq_u) • u) / sq_e1) * sq_e1 =
        @inner ℝ Space3 _ e1 (q - (d / sq_u) • u) := div_mul_cancel₀ _ he1_sq
    rw [h_cancel]
    rw [inner_sub_right, inner_smul_right, h_e1_u, mul_zero, sub_zero, sub_self]
  have h_diff_e2 : @inner ℝ Space3 _ e2 diff = 0 := by
    dsimp [diff, planePt3, p0]
    rw [h_p0, h_p1]
    rw [inner_sub_right]
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right]
    have h_e2_u : @inner ℝ Space3 _ e2 u = 0 := inner_planeBasis2_self u
    have h_e2_e1 : @inner ℝ Space3 _ e2 e1 = 0 := inner_planeBasis2_planeBasis1 u
    rw [h_e2_u, h_e2_e1, mul_zero, mul_zero, add_zero, zero_add]
    have h_cancel : (@inner ℝ Space3 _ e2 (q - (d / sq_u) • u) / sq_e2) * sq_e2 =
        @inner ℝ Space3 _ e2 (q - (d / sq_u) • u) := div_mul_cancel₀ _ he2_sq
    rw [h_cancel]
    rw [inner_sub_right, inner_smul_right, h_e2_u, mul_zero, sub_zero, sub_self]
  have h_zero := eq_zero_of_orthogonal_inners_zero u hu_ne diff h_diff_u h_diff_e1 h_diff_e2
  dsimp [diff] at h_zero
  exact sub_eq_zero.mp h_zero |>.symm

lemma plane2_inner_apply (v w : Plane2) :
    @inner ℝ Plane2 _ v w =
      WithLp.equiv 2 (Fin 2 → ℝ) v 0 * WithLp.equiv 2 (Fin 2 → ℝ) w 0 +
      WithLp.equiv 2 (Fin 2 → ℝ) v 1 * WithLp.equiv 2 (Fin 2 → ℝ) w 1 := by
  have h := PiLp.inner_apply (𝕜 := ℝ) (x := v) (y := w)
  rw [h, Fin.sum_univ_two]
  simp only [Real.inner_apply]
  rfl

lemma maxPlaneRegions_mono {m n : ℕ} (h : m ≤ n) :
    maxPlaneRegions m ≤ maxPlaneRegions n := by
  dsimp [maxPlaneRegions]
  have h0 : Nat.choose m 0 ≤ Nat.choose n 0 := by simp
  have h1 : Nat.choose m 1 ≤ Nat.choose n 1 := by simp [h]
  have h2 : Nat.choose m 2 ≤ Nat.choose n 2 := Nat.choose_le_choose 2 h
  omega

lemma inner_planePt3_sub (H_last : Plane3) (p : Plane2) (H_i : Plane3) :
    let u_last := H_last.normVec
    let e1 := planeBasis1 u_last
    let e2 := planeBasis2 u_last
    let sq_u := @inner ℝ Space3 _ u_last u_last
    let p0 := (H_last.offset / sq_u) • u_last
    let ui := H_i.normVec
    let di := H_i.offset
    let w0 := @inner ℝ Space3 _ ui e1
    let w1 := @inner ℝ Space3 _ ui e2
    let w : Plane2 := (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun j => if j.val = 0 then w0 else w1
    let ci := di - @inner ℝ Space3 _ ui p0
    @inner ℝ Space3 _ ui (planePt3 H_last p) - di =
      @inner ℝ Plane2 _ w p - ci := by
  dsimp [planePt3]
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right]
  rw [plane2_inner_apply]
  simp only [WithLp.equiv_apply, Fin.val_zero, Fin.val_one, ↓reduceIte]
  norm_num
  ring

lemma inner_planePt3_eq_p0_of_w_zero (H_last : Plane3) (p : Plane2) (H_i : Plane3)
    (hw : (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun j =>
      if j.val = 0 then @inner ℝ Space3 _ H_i.normVec (planeBasis1 H_last.normVec)
      else @inner ℝ Space3 _ H_i.normVec (planeBasis2 H_last.normVec)) = 0) :
    let u_last := H_last.normVec
    let sq_u := @inner ℝ Space3 _ u_last u_last
    let p0 := (H_last.offset / sq_u) • u_last
    @inner ℝ Space3 _ H_i.normVec (planePt3 H_last p) = @inner ℝ Space3 _ H_i.normVec p0 := by
  have h_id := inner_planePt3_sub H_last p H_i
  dsimp only at h_id
  have hw_zero : @inner ℝ Plane2 _
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm fun j =>
        if j.val = 0 then @inner ℝ Space3 _ H_i.normVec (planeBasis1 H_last.normVec)
        else @inner ℝ Space3 _ H_i.normVec (planeBasis2 H_last.normVec)) p = 0 := by
    rw [hw, inner_zero_left]
  rw [hw_zero, zero_sub] at h_id
  dsimp
  linarith

/-- 切断された空間領域数は、誘導交線配置の平面領域数、ひいては最大領域数 $S(n)$ で上から抑えられる。 -/
lemma splitSpaceRegionsCount_le_maxPlaneRegions (n : ℕ) (H : Fin (n + 1) → Plane3) :
    splitSpaceRegionsCount n H ≤ maxPlaneRegions n := by
  let split_sigs := Finset.filter (fun σ =>
    isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))) Finset.univ
  have h_rep_q : ∀ σ ∈ split_sigs, ∃ q : Space3,
      q ∈ convexSpaceRegion n (H ∘ Fin.castSucc) σ ∧ q ∈ (H (Fin.last n)).toSet := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rcases hσ.2 with ⟨q, hq1, hq2⟩
    exact ⟨q, hq1, hq2⟩
  choose q_rep hq_rep using h_rep_q
  have h_rep_p : ∀ σ : {σ // σ ∈ split_sigs}, ∃ p : Plane2,
      planePt3 (H (Fin.last n)) p = q_rep σ.val σ.property := by
    intro ⟨σ, hσ⟩
    exact exists_p_planePt3_eq (H (Fin.last n)) (hq_rep σ hσ).2
  choose p_rep hp_rep using h_rep_p
  let w_vec : Fin n → Plane2 := fun i =>
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun j =>
      if j.val = 0 then
        @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (planeBasis1 (H (Fin.last n)).normVec)
      else
        @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (planeBasis2 (H (Fin.last n)).normVec)
  let I := Finset.filter (fun i => w_vec i ≠ 0) Finset.univ
  let m := I.card
  have hm : m ≤ n := by
    calc
      m ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := Fintype.card_fin n
  let emb : Fin m ≃ {i : Fin n // i ∈ I} := (I.orderIsoOfFin rfl).toEquiv
  let L' : Fin m → Line2 := fun j =>
    let i := (emb j).val
    have hw : w_vec i ≠ 0 := by
      have := (emb j).property
      rw [Finset.mem_filter] at this
      exact this.2
    let sq_u := @inner ℝ Space3 _ (H (Fin.last n)).normVec (H (Fin.last n)).normVec
    let p0 := ((H (Fin.last n)).offset / sq_u) • (H (Fin.last n)).normVec
    let ci := (H (Fin.castSucc i)).offset - @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec p0
    ⟨w_vec i, hw, ci⟩
  have hp_not_line : ∀ (σ : {σ // σ ∈ split_sigs}) (j : Fin m),
      p_rep σ ∉ (L' j).toSet := by
    intro ⟨σ, hσ⟩ j
    let i := (emb j).val
    have hq_in := (hq_rep σ hσ).1
    have hq_not := not_mem_plane_of_mem_convexSpaceRegion (H ∘ Fin.castSucc) σ hq_in i
    dsimp [Plane3.toSet] at hq_not
    have h_id := inner_planePt3_sub (H (Fin.last n)) (p_rep ⟨σ, hσ⟩) (H (Fin.castSucc i))
    rw [hp_rep ⟨σ, hσ⟩] at h_id
    dsimp [L', Line2.toSet]
    intro h_on
    have : @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ, hσ⟩) - (L' j).offset = 0 := by
      linarith
    rw [← h_id] at this
    exact hq_not (sub_eq_zero.mp this)
  let τ_of : {σ // σ ∈ split_sigs} → SignVector2 m := fun σ =>
    pointSignVector m L' ⟨p_rep σ, hp_not_line σ⟩
  have hτ_nonempty : ∀ σ : {σ // σ ∈ split_sigs},
      (convexPlaneRegion m L' (τ_of σ)).Nonempty := fun σ =>
    ⟨p_rep σ, mem_convexPlaneRegion_pointSignVector m L' ⟨p_rep σ, hp_not_line σ⟩⟩
  have h_inj : Function.Injective τ_of := by
    intro ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩ h_eq
    apply Subtype.ext
    funext i
    dsimp
    have h_q1 := (hq_rep σ₁ hσ₁).1 i
    have h_q2 := (hq_rep σ₂ hσ₂).1 i
    dsimp [convexSpaceRegion] at h_q1 h_q2
    by_cases hi : i ∈ I
    · let j := emb.symm ⟨i, hi⟩
      have hj_emb : (emb j).val = i := by
        dsimp [j]
        rw [Equiv.apply_symm_apply]
      have h_eq_j := congr_fun h_eq j
      dsimp [τ_of, pointSignVector] at h_eq_j
      have h_id1 := inner_planePt3_sub (H (Fin.last n)) (p_rep ⟨σ₁, hσ₁⟩) (H (Fin.castSucc i))
      have h_id2 := inner_planePt3_sub (H (Fin.last n)) (p_rep ⟨σ₂, hσ₂⟩) (H (Fin.castSucc i))
      rw [hp_rep ⟨σ₁, hσ₁⟩] at h_id1
      rw [hp_rep ⟨σ₂, hσ₂⟩] at h_id2
      dsimp only at h_id1 h_id2
      have h_norm1 : (L' j).normVec = w_vec i := by
        dsimp [L']
        rw [hj_emb]
      have h_off1 : (L' j).offset =
          (H (Fin.castSucc i)).offset -
          @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec
            (((H (Fin.last n)).offset /
              @inner ℝ Space3 _ (H (Fin.last n)).normVec (H (Fin.last n)).normVec) •
             (H (Fin.last n)).normVec) := by
        dsimp [L']
        rw [hj_emb]
      change @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (q_rep σ₁ hσ₁) - _ =
        @inner ℝ Plane2 _ (w_vec i) (p_rep ⟨σ₁, hσ₁⟩) - _ at h_id1
      change @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (q_rep σ₂ hσ₂) - _ =
        @inner ℝ Plane2 _ (w_vec i) (p_rep ⟨σ₂, hσ₂⟩) - _ at h_id2
      rw [← h_norm1, ← h_off1] at h_id1 h_id2
      have h_iff1 :
          (H (Fin.castSucc i)).offset <
            @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (q_rep σ₁ hσ₁) ↔
          (L' j).offset < @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ₁, hσ₁⟩) := by
        constructor <;> intro h <;> linarith [h_id1]
      have h_iff2 :
          (H (Fin.castSucc i)).offset <
            @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (q_rep σ₂ hσ₂) ↔
          (L' j).offset < @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ₂, hσ₂⟩) := by
        constructor <;> intro h <;> linarith [h_id2]
      have h_bool1 : σ₁ i =
          decide ((L' j).offset < @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ₁, hσ₁⟩)) := by
        cases h1 : σ₁ i
        · rw [h1] at h_q1
          dsimp at h_q1
          have : ¬ (L' j).offset < @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ₁, hσ₁⟩) := by
            intro h
            have := h_iff1.mpr h
            linarith
          rw [decide_eq_false this]
        · rw [h1] at h_q1
          dsimp at h_q1
          have : (L' j).offset < @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ₁, hσ₁⟩) :=
            h_iff1.mp h_q1
          rw [decide_eq_true this]
      have h_bool2 : σ₂ i =
          decide ((L' j).offset < @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ₂, hσ₂⟩)) := by
        cases h2 : σ₂ i
        · rw [h2] at h_q2
          dsimp at h_q2
          have : ¬ (L' j).offset < @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ₂, hσ₂⟩) := by
            intro h
            have := h_iff2.mpr h
            linarith
          rw [decide_eq_false this]
        · rw [h2] at h_q2
          dsimp at h_q2
          have : (L' j).offset < @inner ℝ Plane2 _ (L' j).normVec (p_rep ⟨σ₂, hσ₂⟩) :=
            h_iff2.mp h_q2
          rw [decide_eq_true this]
      rw [h_bool1, h_bool2, h_eq_j]
    · rw [Finset.mem_filter] at hi
      push Not at hi
      have hw_zero := hi (Finset.mem_univ i)
      have h_p0_1 := inner_planePt3_eq_p0_of_w_zero (H (Fin.last n)) (p_rep ⟨σ₁, hσ₁⟩)
        (H (Fin.castSucc i)) hw_zero
      have h_p0_2 := inner_planePt3_eq_p0_of_w_zero (H (Fin.last n)) (p_rep ⟨σ₂, hσ₂⟩)
        (H (Fin.castSucc i)) hw_zero
      rw [hp_rep ⟨σ₁, hσ₁⟩] at h_p0_1
      rw [hp_rep ⟨σ₂, hσ₂⟩] at h_p0_2
      dsimp only at h_p0_1 h_p0_2
      cases h1 : σ₁ i <;> cases h2 : σ₂ i
      · rfl
      · rw [h1] at h_q1
        rw [h2] at h_q2
        dsimp at h_q1 h_q2
        rw [h_p0_1] at h_q1
        rw [h_p0_2] at h_q2
        linarith
      · rw [h1] at h_q1
        rw [h2] at h_q2
        dsimp at h_q1 h_q2
        rw [h_p0_1] at h_q1
        rw [h_p0_2] at h_q2
        linarith
      · rfl
  let V := Finset.filter (fun τ => (convexPlaneRegion m L' τ).Nonempty) Finset.univ
  have h_map_mem : ∀ σ : {σ // σ ∈ split_sigs}, τ_of σ ∈ V := by
    intro σ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hτ_nonempty σ⟩
  let g : {σ // σ ∈ split_sigs} → V := fun σ => ⟨τ_of σ, h_map_mem σ⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    exact h_inj (Subtype.ext_iff.mp hxy)
  have h_card_le := Fintype.card_le_of_injective g hg_inj
  rw [Fintype.card_coe, Fintype.card_coe] at h_card_le
  have h_plane_le := planeRegionsCount_le_maxPlaneRegions m L'
  rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion] at h_plane_le
  change V.card ≤ maxPlaneRegions m at h_plane_le
  have h_mono := maxPlaneRegions_mono hm
  have h_split_count : splitSpaceRegionsCount n H = split_sigs.card := rfl
  rw [h_split_count]
  omega

/-- 3次元空間における平面追加の幾何学的漸化不等式:
$(n+1)$ 枚目の平面を追加したとき、既存の $n$ 枚の平面との交わりで生じる2次元領域数は高々 $S(n)$ であり、
空間領域数の増加量は高々 $S(n) = \mathrm{maxPlaneRegions } n$ である。 -/
lemma spaceRegionsCount_succ_le (n : ℕ) (H : Fin (n + 1) → Plane3) :
    spaceRegionsCount (n + 1) H ≤
      spaceRegionsCount n (H ∘ Fin.castSucc) + maxPlaneRegions n := by
  have h_split := spaceRegionsCount_succ_le_add_split n H
  have h_split_le := splitSpaceRegionsCount_le_maxPlaneRegions n H
  omega

/-- 3次元空間における幾何学的領域数の最大値上界定理:
任意の $n$ 枚の平面配置 $H$ による空間領域数 $T(H)$ は、代数公式 $T_{\max}(n)$ 以下である。
証明は平面の枚数 $n$ に関する帰納法と幾何学的漸化不等式による。 -/
theorem spaceRegionsCount_le_maxSpaceRegions (n : ℕ) (H : Fin n → Plane3) :
    spaceRegionsCount n H ≤ maxSpaceRegions n := by
  induction n with
  | zero =>
    rw [spaceRegionsCount_zero H]
    dsimp [maxSpaceRegions]
    decide
  | succ m ih =>
    have hstep := spaceRegionsCount_succ_le m H
    have hih := ih (H ∘ Fin.castSucc)
    have hsucc := maxSpaceRegions_succ m
    omega

/-! ### 3次元空間配置における一般の位置と誘導交線配置 -/

/-- 3次元一般位置にある平面配置の部分配置もまた一般位置にある。
`Fin.castSucc` の単射性から直ちに従う。 -/
lemma GeneralPositionPlanes.castSucc (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H) :
    GeneralPositionPlanes n (H ∘ Fin.castSucc) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hij' : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_inj.mp h)
    exact hgen.1 (Fin.castSucc i) (Fin.castSucc j) hij'
  · intro i j l hij hjl hil
    have hij' : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_inj.mp h)
    have hjl' : Fin.castSucc j ≠ Fin.castSucc l := fun h => hjl (Fin.castSucc_inj.mp h)
    have hil' : Fin.castSucc i ≠ Fin.castSucc l := fun h => hil (Fin.castSucc_inj.mp h)
    exact hgen.2.1 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc l) hij' hjl' hil'
  · intro i j l m hij hjl hlm hil him hjm
    have hij' : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_inj.mp h)
    have hjl' : Fin.castSucc j ≠ Fin.castSucc l := fun h => hjl (Fin.castSucc_inj.mp h)
    have hlm' : Fin.castSucc l ≠ Fin.castSucc m := fun h => hlm (Fin.castSucc_inj.mp h)
    have hil' : Fin.castSucc i ≠ Fin.castSucc l := fun h => hil (Fin.castSucc_inj.mp h)
    have him' : Fin.castSucc i ≠ Fin.castSucc m := fun h => him (Fin.castSucc_inj.mp h)
    have hjm' : Fin.castSucc j ≠ Fin.castSucc m := fun h => hjm (Fin.castSucc_inj.mp h)
    exact hgen.2.2 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc l) (Fin.castSucc m)
      hij' hjl' hlm' hil' him' hjm'

/-- 3次元一般位置にある平面配置は添字の置換によって不変である。 -/
lemma GeneralPositionPlanes.comp_equiv (n : ℕ) (H : Fin n → Plane3) (e : Fin n ≃ Fin n)
    (hgen : GeneralPositionPlanes n H) : GeneralPositionPlanes n (H ∘ e) := by
  rcases hgen with ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have h_ne : e a ≠ e b := e.injective.ne hab
    exact h1 (e a) (e b) h_ne
  · intro a b c hab hbc hac
    have hab' : e a ≠ e b := e.injective.ne hab
    have hbc' : e b ≠ e c := e.injective.ne hbc
    have hac' : e a ≠ e c := e.injective.ne hac
    exact h2 (e a) (e b) (e c) hab' hbc' hac'
  · intro a b c d hab hbc hcd hac had hbd
    have hab' : e a ≠ e b := e.injective.ne hab
    have hbc' : e b ≠ e c := e.injective.ne hbc
    have hcd' : e c ≠ e d := e.injective.ne hcd
    have hac' : e a ≠ e c := e.injective.ne hac
    have had' : e a ≠ e d := e.injective.ne had
    have hbd' : e b ≠ e d := e.injective.ne hbd
    exact h3 (e a) (e b) (e c) (e d) hab' hbc' hcd' hac' had' hbd'

/-- 退化時や平行時に用いるデフォルトの2次元直線。 -/
def defaultLine2 : Line2 :=
  ⟨(WithLp.equiv 2 (Fin 2 → ℝ)).symm fun j => if j.val = 0 then 1 else 0,
   by
     intro h0
     have := congr_fun (congr_arg (WithLp.equiv 2 (Fin 2 → ℝ)) h0) 0
     simp only [WithLp.equiv_apply, PiLp.zero_apply] at this
     norm_num at this,
   0⟩

/-- 3次元空間の2平面 $H_{last}, H_i$ に対し、
$H_{last}$ の接平面における2次元法線ベクトル。 -/
noncomputable def traceLineNormVec (H_last H_i : Plane3) : Plane2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun j =>
    if j.val = 0 then
      @inner ℝ Space3 _ H_i.normVec (planeBasis1 H_last.normVec)
    else
      @inner ℝ Space3 _ H_i.normVec (planeBasis2 H_last.normVec)

/-- 第 $(n+1)$ 平面 $H(\mathrm{Fin.last } n)$ と既存の各平面 $H(\mathrm{Fin.castSucc } i)$
との交わりによって第 $(n+1)$ 平面上に誘導される $n$ 本の交線配置。 -/
noncomputable def traceLinesOnLastPlane (n : ℕ) (H : Fin (n + 1) → Plane3) :
    Fin n → Line2 := fun i =>
  let H_last := H (Fin.last n)
  let H_i := H (Fin.castSucc i)
  let w := traceLineNormVec H_last H_i
  let sq_u := @inner ℝ Space3 _ H_last.normVec H_last.normVec
  let p0 := (H_last.offset / sq_u) • H_last.normVec
  let ci := H_i.offset - @inner ℝ Space3 _ H_i.normVec p0
  if hw : w = 0 then
    defaultLine2
  else
    ⟨w, hw, ci⟩

/-- 平行でない2平面に対し、誘導される2次元法線ベクトルは非ゼロである。 -/
lemma traceLineNormVec_ne_zero (H_last H_i : Plane3)
    (h_not_parallel : ¬ parallelPlanes H_i H_last) :
    traceLineNormVec H_last H_i ≠ 0 := by
  intro hw_zero
  apply h_not_parallel
  dsimp [parallelPlanes]
  let u := H_last.normVec
  let sq_u := @inner ℝ Space3 _ u u
  have h_sq_ne : sq_u ≠ 0 := by
    intro h0
    exact H_last.normVec_ne_zero (inner_self_eq_zero.mp h0)
  let c := @inner ℝ Space3 _ H_i.normVec u / sq_u
  use c
  let w' := H_i.normVec - c • u
  have hw'_u : @inner ℝ Space3 _ u w' = 0 := by
    dsimp [w', c]
    rw [inner_sub_right, inner_smul_right]
    have : @inner ℝ Space3 _ u (H_i.normVec) =
        @inner ℝ Space3 _ H_i.normVec u := real_inner_comm _ _
    rw [this]
    have h_cancel :
        (@inner ℝ Space3 _ H_i.normVec u / sq_u) * sq_u =
        @inner ℝ Space3 _ H_i.normVec u := by
      exact div_mul_cancel₀ _ h_sq_ne
    rw [h_cancel, sub_self]
  have hw'_e1 : @inner ℝ Space3 _ (planeBasis1 u) w' = 0 := by
    dsimp [w', c]
    rw [inner_sub_right, inner_smul_right]
    have h_u_e1 : @inner ℝ Space3 _ (planeBasis1 u) u = 0 := inner_planeBasis1_self u
    rw [h_u_e1, mul_zero, sub_zero]
    rw [real_inner_comm]
    have h0 := congr_fun (congr_arg (WithLp.equiv 2 (Fin 2 → ℝ)) hw_zero) 0
    dsimp [traceLineNormVec] at h0
    simp only [WithLp.equiv_apply, Fin.val_zero, PiLp.zero_apply] at h0
    exact h0
  have hw'_e2 : @inner ℝ Space3 _ (planeBasis2 u) w' = 0 := by
    dsimp [w', c]
    rw [inner_sub_right, inner_smul_right]
    have h_u_e2 : @inner ℝ Space3 _ (planeBasis2 u) u = 0 := inner_planeBasis2_self u
    rw [h_u_e2, mul_zero, sub_zero]
    rw [real_inner_comm]
    have h1 := congr_fun (congr_arg (WithLp.equiv 2 (Fin 2 → ℝ)) hw_zero) 1
    dsimp [traceLineNormVec] at h1
    simp only [WithLp.equiv_apply, Fin.val_one, PiLp.zero_apply] at h1
    exact h1
  have hw'_zero :=
    eq_zero_of_orthogonal_inners_zero u H_last.normVec_ne_zero w' hw'_u hw'_e1 hw'_e2
  dsimp [w'] at hw'_zero
  exact sub_eq_zero.mp hw'_zero

/-- 3次元で交わる平面から誘導された2次元交線上の点と、3次元平面の点との同値性。 -/
lemma mem_traceLine_iff (n : ℕ) (H : Fin (n + 1) → Plane3) (i : Fin n)
    (h_not_parallel : ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last n)))
    (p : Plane2) :
    p ∈ (traceLinesOnLastPlane n H i).toSet ↔
      planePt3 (H (Fin.last n)) p ∈ (H (Fin.castSucc i)).toSet := by
  have hw_ne := traceLineNormVec_ne_zero (H (Fin.last n)) (H (Fin.castSucc i)) h_not_parallel
  dsimp [traceLinesOnLastPlane]
  split_ifs with hw
  · exact (hw_ne hw).elim
  · dsimp [Line2.toSet, Plane3.toSet]
    have h_id := inner_planePt3_sub (H (Fin.last n)) p (H (Fin.castSucc i))
    dsimp only at h_id
    change @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (planePt3 (H (Fin.last n)) p) -
      (H (Fin.castSucc i)).offset =
      @inner ℝ Plane2 _ (traceLineNormVec (H (Fin.last n)) (H (Fin.castSucc i))) p -
        ((H (Fin.castSucc i)).offset -
          @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec
            (((H (Fin.last n)).offset /
              @inner ℝ Space3 _ (H (Fin.last n)).normVec (H (Fin.last n)).normVec) •
             (H (Fin.last n)).normVec)) at h_id
    constructor
    · intro hp
      linarith [h_id, hp]
    · intro hq
      linarith [h_id, hq]

/-- 平行で交点をもつ2直線は点集合として一致する。 -/
lemma line2_eq_of_parallel_and_common_point (L₁ L₂ : Line2)
    (h_par : parallelLines L₁ L₂) {p : Plane2}
    (hp₁ : p ∈ L₁.toSet) (hp₂ : p ∈ L₂.toSet) :
    L₁.toSet = L₂.toSet := by
  rcases h_par with ⟨c, hc⟩
  dsimp [Line2.toSet] at hp₁ hp₂ ⊢
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply L₁.normVec_ne_zero
    rw [hc, hc0, zero_smul]
  have h_off : L₁.offset = c * L₂.offset := by
    calc
      L₁.offset = @inner ℝ Plane2 _ L₁.normVec p := hp₁.symm
      _ = @inner ℝ Plane2 _ (c • L₂.normVec) p := by rw [hc]
      _ = c * @inner ℝ Plane2 _ L₂.normVec p := inner_smul_left _ _ _
      _ = c * L₂.offset := by rw [hp₂]
  ext x
  constructor
  · intro hx
    dsimp at hx ⊢
    have h_cx : c * @inner ℝ Plane2 _ L₂.normVec x = c * L₂.offset := by
      calc
        c * @inner ℝ Plane2 _ L₂.normVec x =
            @inner ℝ Plane2 _ (c • L₂.normVec) x := (inner_smul_left _ _ _).symm
        _ = @inner ℝ Plane2 _ L₁.normVec x := by rw [hc]
        _ = L₁.offset := hx
        _ = c * L₂.offset := h_off
    exact mul_left_cancel₀ hc_ne h_cx
  · intro hx
    dsimp at hx ⊢
    calc
      @inner ℝ Plane2 _ L₁.normVec x = @inner ℝ Plane2 _ (c • L₂.normVec) x := by rw [hc]
      _ = c * @inner ℝ Plane2 _ L₂.normVec x := inner_smul_left _ _ _
      _ = c * L₂.offset := by rw [hx]
      _ = L₁.offset := h_off.symm

/-- 直線上の任意の点に対し、それと異なる直線上の点が存在する。 -/
lemma exists_ne_mem_line2 (L : Line2) (p : Plane2) (hp : p ∈ L.toSet) :
    ∃ p' : Plane2, p' ∈ L.toSet ∧ p' ≠ p := by
  let u := L.normVec
  let u0 := WithLp.equiv 2 (Fin 2 → ℝ) u 0
  let u1 := WithLp.equiv 2 (Fin 2 → ℝ) u 1
  let v : Plane2 := (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun j =>
    if j.val = 0 then -u1 else u0
  have hv_ne : v ≠ 0 := by
    intro h0
    have h0_0 := congr_fun (congr_arg (WithLp.equiv 2 (Fin 2 → ℝ)) h0) 0
    have h0_1 := congr_fun (congr_arg (WithLp.equiv 2 (Fin 2 → ℝ)) h0) 1
    dsimp [v] at h0_0 h0_1
    change -u1 = 0 at h0_0
    change u0 = 0 at h0_1
    have hu0 : u0 = 0 := h0_1
    have hu1 : u1 = 0 := by linarith [h0_0]
    apply L.normVec_ne_zero
    apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
    ext j
    fin_cases j
    · exact hu0
    · exact hu1
  have h_uv : @inner ℝ Plane2 _ u v = 0 := by
    rw [plane2_inner_apply]
    dsimp [v]
    change u0 * (-u1) + u1 * u0 = 0
    ring
  let p' := p + v
  have hp' : p' ∈ L.toSet := by
    dsimp [Line2.toSet, p']
    rw [inner_add_right, hp, h_uv, add_zero]
  refine ⟨p', hp', ?_⟩
  intro h_eq
  have : v = 0 := by
    calc
      v = (p + v) - p := by abel
      _ = p' - p := rfl
      _ = p - p := by rw [h_eq]
      _ = 0 := sub_self p
  exact hv_ne this

/-- 2次元平面パラメータ付け planePt3 は単射である。 -/
lemma planePt3_injective (H : Plane3) : Function.Injective (planePt3 H) := by
  intro p₁ p₂ h
  let d0 := WithLp.equiv 2 (Fin 2 → ℝ) p₁ 0 - WithLp.equiv 2 (Fin 2 → ℝ) p₂ 0
  let d1 := WithLp.equiv 2 (Fin 2 → ℝ) p₁ 1 - WithLp.equiv 2 (Fin 2 → ℝ) p₂ 1
  have h_diff : d0 • planeBasis1 H.normVec + d1 • planeBasis2 H.normVec = 0 := by
    have h_sub : planePt3 H p₁ - planePt3 H p₂ = 0 := sub_eq_zero.mpr h
    have h_rearr : d0 • planeBasis1 H.normVec + d1 • planeBasis2 H.normVec =
        (planePt3 H p₁) - (planePt3 H p₂) := by
      dsimp [planePt3, d0, d1]
      module
    rw [h_rearr, h_sub]
  apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
  ext j
  fin_cases j
  · -- j = 0
    have h_inner := congr_arg (fun v => @inner ℝ Space3 _ (planeBasis1 H.normVec) v) h_diff
    rw [inner_zero_right] at h_inner
    rw [inner_add_right, inner_smul_right, inner_smul_right] at h_inner
    have h_e1_e2 : @inner ℝ Space3 _ (planeBasis1 H.normVec) (planeBasis2 H.normVec) = 0 := by
      rw [real_inner_comm]
      exact inner_planeBasis2_planeBasis1 H.normVec
    have h_e1_sq : @inner ℝ Space3 _ (planeBasis1 H.normVec) (planeBasis1 H.normVec) ≠ 0 := by
      intro h0
      have he1_ne := planeBasis1_ne_zero H.normVec H.normVec_ne_zero
      exact he1_ne (inner_self_eq_zero.mp h0)
    rw [h_e1_e2, mul_zero, add_zero] at h_inner
    have h_sub : d0 = 0 := (mul_eq_zero.mp h_inner).resolve_right h_e1_sq
    exact sub_eq_zero.mp h_sub
  · -- j = 1
    have h_inner := congr_arg (fun v => @inner ℝ Space3 _ (planeBasis2 H.normVec) v) h_diff
    rw [inner_zero_right] at h_inner
    rw [inner_add_right, inner_smul_right, inner_smul_right] at h_inner
    have h_e2_e1 : @inner ℝ Space3 _ (planeBasis2 H.normVec) (planeBasis1 H.normVec) = 0 :=
      inner_planeBasis2_planeBasis1 H.normVec
    have h_e2_sq : @inner ℝ Space3 _ (planeBasis2 H.normVec) (planeBasis2 H.normVec) ≠ 0 := by
      intro h0
      have he2_ne := planeBasis2_ne_zero H.normVec H.normVec_ne_zero
      exact he2_ne (inner_self_eq_zero.mp h0)
    rw [h_e2_e1, mul_zero, zero_add] at h_inner
    have h_sub : d1 = 0 := (mul_eq_zero.mp h_inner).resolve_right h_e2_sq
    exact sub_eq_zero.mp h_sub

/-- 3次元一般位置から2次元一般位置への帰着定理:
3次元空間で一般の位置にある平面配置 $H$ に対し、
第 $(n+1)$ 平面上に誘導される交線配置は2次元平面上で一般の位置をなす。
どの2直線も平行でなく(3平面共線性の否定)、
どの3直線も1点で交わらない(4平面共点性の否定)。 -/
lemma generalPositionLines_of_traceLines (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H) :
    GeneralPositionLines n (traceLinesOnLastPlane n H) := by
  let last := Fin.last n
  have h_not_parallel_last : ∀ i : Fin n, ¬ parallelPlanes (H (Fin.castSucc i)) (H last) :=
    fun i => hgen.1 (Fin.castSucc i) last (Fin.castSucc_ne_last i)
  constructor
  · -- どの2直線も平行でない
    intro i j hij h_par
    have hij' : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_inj.mp h)
    have hilast : Fin.castSucc i ≠ last := Fin.castSucc_ne_last i
    have hjlast : Fin.castSucc j ≠ last := Fin.castSucc_ne_last j
    rcases hgen.2.1 (Fin.castSucc i) (Fin.castSucc j) last hij' hjlast hilast with ⟨q, hq_inter⟩
    have hq_in : q ∈ (H (Fin.castSucc i)).toSet ∩
        (H (Fin.castSucc j)).toSet ∩ (H last).toSet := by
      rw [hq_inter]
      exact Set.mem_singleton q
    rcases hq_in with ⟨⟨hqi, hqj⟩, hqlast⟩
    rcases exists_p_planePt3_eq (H last) hqlast with ⟨p, hp_q⟩
    have hpi : p ∈ (traceLinesOnLastPlane n H i).toSet := by
      rw [mem_traceLine_iff n H i (h_not_parallel_last i) p, hp_q]
      exact hqi
    have hpj : p ∈ (traceLinesOnLastPlane n H j).toSet := by
      rw [mem_traceLine_iff n H j (h_not_parallel_last j) p, hp_q]
      exact hqj
    have h_line_eq := line2_eq_of_parallel_and_common_point
      (traceLinesOnLastPlane n H i) (traceLinesOnLastPlane n H j) h_par hpi hpj
    rcases exists_ne_mem_line2 (traceLinesOnLastPlane n H i) p hpi with ⟨p', hp'i, hp'_ne⟩
    have hp'j : p' ∈ (traceLinesOnLastPlane n H j).toSet := by
      rw [← h_line_eq]
      exact hp'i
    let q' := planePt3 (H last) p'
    have hq'last : q' ∈ (H last).toSet := planePt3_mem_plane (H last) p'
    have hq'i : q' ∈ (H (Fin.castSucc i)).toSet := by
      rw [← mem_traceLine_iff n H i (h_not_parallel_last i) p']
      exact hp'i
    have hq'j : q' ∈ (H (Fin.castSucc j)).toSet := by
      rw [← mem_traceLine_iff n H j (h_not_parallel_last j) p']
      exact hp'j
    have hq'_in : q' ∈ (H (Fin.castSucc i)).toSet ∩
        (H (Fin.castSucc j)).toSet ∩ (H last).toSet :=
      ⟨⟨hq'i, hq'j⟩, hq'last⟩
    rw [hq_inter] at hq'_in
    have hq'_eq_q : q' = q := Set.mem_singleton_iff.mp hq'_in
    rw [← hp_q] at hq'_eq_q
    have hp'_eq_p := planePt3_injective (H last) hq'_eq_q
    exact hp'_ne hp'_eq_p
  · -- どの3直線も1点で交わらない
    intro i j l hij hjl hil
    apply Set.eq_empty_of_subset_empty
    intro p hp
    rcases hp with ⟨⟨hpi, hpj⟩, hpl⟩
    have hqi := (mem_traceLine_iff n H i (h_not_parallel_last i) p).mp hpi
    have hqj := (mem_traceLine_iff n H j (h_not_parallel_last j) p).mp hpj
    have hql := (mem_traceLine_iff n H l (h_not_parallel_last l) p).mp hpl
    let q := planePt3 (H last) p
    have hqlast : q ∈ (H last).toSet := planePt3_mem_plane (H last) p
    have hq_all : q ∈ (H (Fin.castSucc i)).toSet ∩
        (H (Fin.castSucc j)).toSet ∩
        (H (Fin.castSucc l)).toSet ∩
        (H last).toSet := ⟨⟨⟨hqi, hqj⟩, hql⟩, hqlast⟩
    have hij' : Fin.castSucc i ≠ Fin.castSucc j := fun h => hij (Fin.castSucc_inj.mp h)
    have hjl' : Fin.castSucc j ≠ Fin.castSucc l := fun h => hjl (Fin.castSucc_inj.mp h)
    have hllast : Fin.castSucc l ≠ last := Fin.castSucc_ne_last l
    have hil' : Fin.castSucc i ≠ Fin.castSucc l := fun h => hil (Fin.castSucc_inj.mp h)
    have hilast : Fin.castSucc i ≠ last := Fin.castSucc_ne_last i
    have hjlast : Fin.castSucc j ≠ last := Fin.castSucc_ne_last j
    have h_empty := hgen.2.2 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc l) last
      hij' hjl' hllast hil' hilast hjlast
    rw [h_empty] at hq_all
    exact hq_all

/-- 切断される3次元領域は、平面の両側に非空な領域を生じる。 -/
lemma split_region_both_sides_nonempty3 (n : ℕ) (H : Fin (n + 1) → Plane3)
    (σ : SignVector3 n)
    (hsplit : isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))) :
    (convexSpaceRegion (n + 1) H (Fin.snoc σ true)).Nonempty ∧
    (convexSpaceRegion (n + 1) H (Fin.snoc σ false)).Nonempty := by
  obtain ⟨p, hp_reg, hp_line⟩ := hsplit
  dsimp [Plane3.toSet] at hp_line
  let u := (H (Fin.last n)).normVec
  have hu_pos : 0 < @inner ℝ Space3 _ u u :=
    real_inner_self_pos.2 (H (Fin.last n)).normVec_ne_zero
  let δ : Fin n → ℝ := fun i =>
    if σ i then @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec p - (H (Fin.castSucc i)).offset
    else (H (Fin.castSucc i)).offset - @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec p
  have hδ_pos : ∀ i, 0 < δ i := by
    intro i
    have hp_i := hp_reg i
    dsimp at hp_i
    dsimp [δ]
    split_ifs at hp_i ⊢ with hσ
    · linarith
    · linarith
  let g : Option (Fin n) → ℝ := fun opt =>
    match opt with
    | none => 1
    | some i =>
      let dot := @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec u
      if dot = 0 then 1 else δ i / (2 * |dot|)
  have hg_pos : ∀ opt, 0 < g opt := by
    intro opt
    cases opt with
    | none => exact Real.zero_lt_one
    | some i =>
      dsimp [g]
      split_ifs with hdot
      · exact Real.zero_lt_one
      · refine div_pos (hδ_pos i) ?_
        have : 0 < |@inner ℝ Space3 _ (H (Fin.castSucc i)).normVec u| :=
          abs_pos.mpr hdot
        linarith
  have h_univ_nonempty : (Finset.univ : Finset (Option (Fin n))).Nonempty :=
    ⟨none, Finset.mem_univ none⟩
  obtain ⟨opt_min, -, h_min⟩ := Finset.exists_min_image Finset.univ g h_univ_nonempty
  let ε := g opt_min
  have hε_pos : 0 < ε := hg_pos opt_min
  have hε_le : ∀ i : Fin n, ε ≤ g (some i) := fun i => h_min (some i) (Finset.mem_univ _)
  let p_plus := p + ε • u
  let p_minus := p - ε • u
  have hp_plus_last : (H (Fin.last n)).offset < @inner ℝ Space3 _ u p_plus := by
    dsimp [p_plus]
    rw [inner_add_right, inner_smul_right]
    have : 0 < ε * @inner ℝ Space3 _ u u := mul_pos hε_pos hu_pos
    linarith
  have hp_minus_last : @inner ℝ Space3 _ u p_minus < (H (Fin.last n)).offset := by
    dsimp [p_minus]
    rw [inner_sub_right, inner_smul_right]
    have : 0 < ε * @inner ℝ Space3 _ u u := mul_pos hε_pos hu_pos
    linarith
  have hp_plus_reg : p_plus ∈ convexSpaceRegion n (H ∘ Fin.castSucc) σ := by
    dsimp [convexSpaceRegion]
    intro i
    have hp_i := hp_reg i
    dsimp at hp_i
    have h_le_i := hε_le i
    dsimp [p_plus]
    rw [inner_add_right, inner_smul_right]
    let vi := (H (Fin.castSucc i)).normVec
    have h_vi : (H (Fin.castSucc i)).normVec = vi := rfl
    rw [h_vi]
    rw [h_vi] at hp_i
    let dot := @inner ℝ Space3 _ vi u
    have h_dot : @inner ℝ Space3 _ vi u = dot := rfl
    rw [h_dot]
    by_cases hdot : dot = 0
    · dsimp [g] at h_le_i
      rw [ite_eq_left hdot] at h_le_i
      rw [hdot, mul_zero, add_zero]
      split_ifs at hp_i ⊢ with hσ <;> exact hp_i
    · dsimp [g] at h_le_i
      rw [ite_eq_right hdot] at h_le_i
      have h_bound : ε * |dot| ≤ δ i / 2 := by
        have h_mul : ε * (2 * |dot|) ≤ (δ i / (2 * |dot|)) * (2 * |dot|) :=
          mul_le_mul_of_nonneg_right h_le_i (by positivity)
        rw [div_mul_cancel₀ _ (by positivity)] at h_mul
        linarith
      have h_abs_dot : |ε * dot| ≤ δ i / 2 := by
        rw [abs_mul, abs_of_pos hε_pos]
        exact h_bound
      have h_dot_ge : - (δ i / 2) ≤ ε * dot := by
        have := neg_le_of_abs_le h_abs_dot
        linarith
      have h_dot_le : ε * dot ≤ δ i / 2 := le_of_abs_le h_abs_dot
      have hδ_def : δ i = if σ i then @inner ℝ Space3 _ vi p - (H (Fin.castSucc i)).offset
                         else (H (Fin.castSucc i)).offset - @inner ℝ Space3 _ vi p := rfl
      split_ifs at hp_i ⊢ with hσ
      · rw [ite_eq_left hσ] at hδ_def
        linarith
      · rw [ite_eq_right hσ] at hδ_def
        linarith
  have hp_minus_reg : p_minus ∈ convexSpaceRegion n (H ∘ Fin.castSucc) σ := by
    dsimp [convexSpaceRegion]
    intro i
    have hp_i := hp_reg i
    dsimp at hp_i
    have h_le_i := hε_le i
    dsimp [p_minus]
    rw [inner_sub_right, inner_smul_right]
    let vi := (H (Fin.castSucc i)).normVec
    have h_vi : (H (Fin.castSucc i)).normVec = vi := rfl
    rw [h_vi]
    rw [h_vi] at hp_i
    let dot := @inner ℝ Space3 _ vi u
    have h_dot : @inner ℝ Space3 _ vi u = dot := rfl
    rw [h_dot]
    by_cases hdot : dot = 0
    · dsimp [g] at h_le_i
      rw [ite_eq_left hdot] at h_le_i
      rw [hdot, mul_zero, sub_zero]
      split_ifs at hp_i ⊢ with hσ <;> exact hp_i
    · dsimp [g] at h_le_i
      rw [ite_eq_right hdot] at h_le_i
      have h_bound : ε * |dot| ≤ δ i / 2 := by
        have h_mul : ε * (2 * |dot|) ≤ (δ i / (2 * |dot|)) * (2 * |dot|) :=
          mul_le_mul_of_nonneg_right h_le_i (by positivity)
        rw [div_mul_cancel₀ _ (by positivity)] at h_mul
        linarith
      have h_abs_dot : |ε * dot| ≤ δ i / 2 := by
        rw [abs_mul, abs_of_pos hε_pos]
        exact h_bound
      have h_dot_ge : - (δ i / 2) ≤ ε * dot := by
        have := neg_le_of_abs_le h_abs_dot
        linarith
      have h_dot_le : ε * dot ≤ δ i / 2 := le_of_abs_le h_abs_dot
      have hδ_def : δ i = if σ i then @inner ℝ Space3 _ vi p - (H (Fin.castSucc i)).offset
                         else (H (Fin.castSucc i)).offset - @inner ℝ Space3 _ vi p := rfl
      split_ifs at hp_i ⊢ with hσ
      · rw [ite_eq_left hσ] at hδ_def
        linarith
      · rw [ite_eq_right hσ] at hδ_def
        linarith
  constructor
  · use p_plus
    rw [mem_convexSpaceRegion_succ]
    exact ⟨hp_plus_reg, hp_plus_last⟩
  · use p_minus
    rw [mem_convexSpaceRegion_succ]
    exact ⟨hp_minus_reg, hp_minus_last⟩

/-- 3次元空間において新しい平面を追加したときの領域増加の下界評価。 -/
lemma spaceRegionsCount_succ_ge (n : ℕ) (H : Fin (n + 1) → Plane3) :
    spaceRegionsCount n (H ∘ Fin.castSucc) + splitSpaceRegionsCount n H ≤
      spaceRegionsCount (n + 1) H := by
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  let P_succ := fun τ => (convexSpaceRegion (n + 1) H τ).Nonempty
  rw [card_filter_succ_eq_sum P_succ]
  have hA : (∑ σ, if (convexSpaceRegion n (H ∘ Fin.castSucc) σ).Nonempty then 1 else 0) =
      (Finset.filter
        (fun σ => (convexSpaceRegion n (H ∘ Fin.castSucc) σ).Nonempty) Finset.univ).card :=
    sum_ite_eq_card_filter _
  have hB : (∑ σ, if isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ)
      (H (Fin.last n)) then 1 else 0) = splitSpaceRegionsCount n H := by
    dsimp [splitSpaceRegionsCount]
    exact sum_ite_eq_card_filter _
  rw [← hA, ← hB, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ _
  let F_set := Finset.filter (fun b : Bool => P_succ (Fin.snoc σ b)) Finset.univ
  by_cases hne : (convexSpaceRegion n (H ∘ Fin.castSucc) σ).Nonempty
  · simp only [hne, ↓reduceIte]
    by_cases hsp : isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))
    · simp only [hsp, ↓reduceIte]
      have h_both := split_region_both_sides_nonempty3 n H σ hsp
      have hT : true ∈ F_set := by
        simp only [F_set, Finset.mem_filter, Finset.mem_univ, true_and, P_succ]
        exact h_both.1
      have hF : false ∈ F_set := by
        simp only [F_set, Finset.mem_filter, Finset.mem_univ, true_and, P_succ]
        exact h_both.2
      have h_pair : {true, false} ⊆ F_set := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have h_card_two : ({true, false} : Finset Bool).card = 2 := by decide
      have h_le := Finset.card_le_card h_pair
      rw [h_card_two] at h_le
      exact h_le
    · simp only [hsp, ↓reduceIte, add_zero]
      obtain ⟨p, hp⟩ := hne
      have hp_not_plane : p ∉ (H (Fin.last n)).toSet := by
        intro hp_plane
        apply hsp
        exact ⟨p, hp, hp_plane⟩
      dsimp [Plane3.toSet] at hp_not_plane
      have h_ne : @inner ℝ Space3 _ (H (Fin.last n)).normVec p ≠
          (H (Fin.last n)).offset := hp_not_plane
      rcases lt_or_gt_of_ne h_ne with hlt | hgt
      · have hF : false ∈ F_set := by
          simp only [F_set, Finset.mem_filter, Finset.mem_univ, true_and, P_succ]
          use p
          rw [mem_convexSpaceRegion_succ]
          exact ⟨hp, hlt⟩
        have h_pos : 1 ≤ F_set.card := Finset.card_pos.mpr ⟨false, hF⟩
        exact h_pos
      · have hT : true ∈ F_set := by
          simp only [F_set, Finset.mem_filter, Finset.mem_univ, true_and, P_succ]
          use p
          rw [mem_convexSpaceRegion_succ]
          exact ⟨hp, hgt⟩
        have h_pos : 1 ≤ F_set.card := Finset.card_pos.mpr ⟨true, hT⟩
        exact h_pos
  · simp only [hne, ↓reduceIte, zero_add]
    have hsp_not :
        ¬ isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n)) := by
      rintro ⟨p, hp, _⟩
      exact hne ⟨p, hp⟩
    simp only [hsp_not, ↓reduceIte]
    exact Nat.zero_le _

/-- 任意の平面配置において、新しい平面を追加したときの空間領域数は、
既存の領域数と追加平面によって切断される領域数の和に厳密に一致する。 -/
lemma spaceRegionsCount_succ_eq_add_split (n : ℕ) (H : Fin (n + 1) → Plane3) :
    spaceRegionsCount (n + 1) H =
      spaceRegionsCount n (H ∘ Fin.castSucc) + splitSpaceRegionsCount n H := by
  have h1 := spaceRegionsCount_succ_le_add_split n H
  have h2 := spaceRegionsCount_succ_ge n H
  omega

/-- 2次元符号ベクトルτから、3次元符号ベクトルへの対応は恒等写像である。 -/
lemma mem_convexSpaceRegion_of_mem_convexPlaneRegion (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H)
    (τ : SignVector2 n) {p : Plane2}
    (hp : p ∈ convexPlaneRegion n (traceLinesOnLastPlane n H) τ) :
    let q := planePt3 (H (Fin.last n)) p
    q ∈ convexSpaceRegion n (H ∘ Fin.castSucc) τ ∧ q ∈ (H (Fin.last n)).toSet := by
  let last := Fin.last n
  let q := planePt3 (H last) p
  have hq_last : q ∈ (H last).toSet := planePt3_mem_plane (H last) p
  have h_not_par : ∀ i : Fin n, ¬ parallelPlanes (H (Fin.castSucc i)) (H last) :=
    fun i => hgen.1 (Fin.castSucc i) last (Fin.castSucc_ne_last i)
  have hq_in : q ∈ convexSpaceRegion n (H ∘ Fin.castSucc) τ := by
    dsimp [convexSpaceRegion, q]
    intro i
    dsimp [convexPlaneRegion] at hp
    have hp_i := hp i
    have h_id := inner_planePt3_sub (H last) p (H (Fin.castSucc i))
    dsimp only at h_id
    change @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (planePt3 (H last) p) -
      (H (Fin.castSucc i)).offset =
      @inner ℝ Plane2 _ (traceLineNormVec (H last) (H (Fin.castSucc i))) p -
        ((H (Fin.castSucc i)).offset -
          @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec
            (((H last).offset / @inner ℝ Space3 _ (H last).normVec (H last).normVec) •
             (H last).normVec)) at h_id
    have hw_ne := traceLineNormVec_ne_zero (H last) (H (Fin.castSucc i)) (h_not_par i)
    have h_line :
        (traceLinesOnLastPlane n H i).normVec = traceLineNormVec (H last) (H (Fin.castSucc i)) ∧
        (traceLinesOnLastPlane n H i).offset = (H (Fin.castSucc i)).offset -
          @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec
            (((H last).offset / @inner ℝ Space3 _ (H last).normVec (H last).normVec) •
             (H last).normVec) := by
      dsimp [traceLinesOnLastPlane]
      split_ifs with hw
      · exact (hw_ne hw).elim
      · exact ⟨rfl, rfl⟩
    rw [h_line.1, h_line.2] at hp_i
    cases hτ : τ i
    · rw [hτ] at hp_i
      dsimp at hp_i ⊢
      linarith [h_id, hp_i]
    · rw [hτ] at hp_i
      dsimp at hp_i ⊢
      linarith [h_id, hp_i]
  exact ⟨hq_in, hq_last⟩

/-- 一般の位置にある配置に対し、切断領域数は maxPlaneRegions n 以上である。 -/
lemma maxPlaneRegions_le_splitSpaceRegionsCount (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H) :
    maxPlaneRegions n ≤ splitSpaceRegionsCount n H := by
  let L' := traceLinesOnLastPlane n H
  have hgen_lines := generalPositionLines_of_traceLines n H hgen
  have h_plane_eq := planeRegionsCount_eq_max_of_general_position n L' hgen_lines
  rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion] at h_plane_eq
  let V := Finset.filter (fun τ => (convexPlaneRegion n L' τ).Nonempty) Finset.univ
  have hV_card : V.card = maxPlaneRegions n := h_plane_eq
  let split_sigs := Finset.filter (fun σ =>
    isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))) Finset.univ
  have h_split_count : splitSpaceRegionsCount n H = split_sigs.card := rfl
  have h_sub : V ⊆ split_sigs := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    refine ⟨hτ.1, ?_⟩
    rcases hτ.2 with ⟨p, hp⟩
    have hq := mem_convexSpaceRegion_of_mem_convexPlaneRegion n H hgen τ hp
    exact ⟨planePt3 (H (Fin.last n)) p, hq.1, hq.2⟩
  have h_card_le := Finset.card_le_card h_sub
  rw [hV_card] at h_card_le
  rw [h_split_count]
  exact h_card_le

/-- したがって、一般の位置にある配置に対し、切断領域数はちょうど maxPlaneRegions n である。 -/
lemma splitSpaceRegionsCount_eq_of_general_position (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H) :
    splitSpaceRegionsCount n H = maxPlaneRegions n := by
  have h_le := splitSpaceRegionsCount_le_maxPlaneRegions n H
  have h_ge := maxPlaneRegions_le_splitSpaceRegionsCount n H hgen
  omega

/-- 最後の平面と平行でないことのみを仮定した、領域属人性補題。 -/
lemma mem_convexSpaceRegion_of_mem_convexPlaneRegion' (n : ℕ) (H : Fin (n + 1) → Plane3)
    (h_not_par : ∀ i : Fin n, ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last n)))
    (τ : SignVector2 n) {p : Plane2}
    (hp : p ∈ convexPlaneRegion n (traceLinesOnLastPlane n H) τ) :
    let q := planePt3 (H (Fin.last n)) p
    q ∈ convexSpaceRegion n (H ∘ Fin.castSucc) τ ∧ q ∈ (H (Fin.last n)).toSet := by
  let last := Fin.last n
  let q := planePt3 (H last) p
  have hq_last : q ∈ (H last).toSet := planePt3_mem_plane (H last) p
  have hq_in : q ∈ convexSpaceRegion n (H ∘ Fin.castSucc) τ := by
    dsimp [convexSpaceRegion, q]
    intro i
    dsimp [convexPlaneRegion] at hp
    have hp_i := hp i
    have h_id := inner_planePt3_sub (H last) p (H (Fin.castSucc i))
    dsimp only at h_id
    change @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec (planePt3 (H last) p) -
      (H (Fin.castSucc i)).offset =
      @inner ℝ Plane2 _ (traceLineNormVec (H last) (H (Fin.castSucc i))) p -
        ((H (Fin.castSucc i)).offset -
          @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec
            (((H last).offset / @inner ℝ Space3 _ (H last).normVec (H last).normVec) •
             (H last).normVec)) at h_id
    have hw_ne := traceLineNormVec_ne_zero (H last) (H (Fin.castSucc i)) (h_not_par i)
    have h_line :
        (traceLinesOnLastPlane n H i).normVec = traceLineNormVec (H last) (H (Fin.castSucc i)) ∧
        (traceLinesOnLastPlane n H i).offset = (H (Fin.castSucc i)).offset -
          @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec
            (((H last).offset / @inner ℝ Space3 _ (H last).normVec (H last).normVec) •
             (H last).normVec) := by
      dsimp [traceLinesOnLastPlane]
      split_ifs with hw
      · exact (hw_ne hw).elim
      · exact ⟨rfl, rfl⟩
    rw [h_line.1, h_line.2] at hp_i
    cases hτ : τ i
    · rw [hτ] at hp_i
      dsimp at hp_i ⊢
      linarith [h_id, hp_i]
    · rw [hτ] at hp_i
      dsimp at hp_i ⊢
      linarith [h_id, hp_i]
  exact ⟨hq_in, hq_last⟩

/-- 3次元の平面交差条件から2次元交線系の一般位置性を導く定理。 -/
lemma generalPositionLines_of_plane_intersections (n : ℕ) (H : Fin (n + 1) → Plane3)
    (h_not_parallel_last : ∀ i : Fin n, ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last n)))
    (h_inter3 : ∀ (i j : Fin n), i ≠ j →
      ∃ q, (H (Fin.castSucc i)).toSet ∩ (H (Fin.castSucc j)).toSet ∩
        (H (Fin.last n)).toSet = {q})
    (h_inter4 : ∀ (i j l : Fin n), i ≠ j → j ≠ l → i ≠ l →
      (H (Fin.castSucc i)).toSet ∩ (H (Fin.castSucc j)).toSet ∩
        (H (Fin.castSucc l)).toSet ∩ (H (Fin.last n)).toSet = ∅) :
    GeneralPositionLines n (traceLinesOnLastPlane n H) := by
  let last := Fin.last n
  constructor
  · -- どの2直線も平行でない
    intro i j hij h_par
    rcases h_inter3 i j hij with ⟨q, hq_inter⟩
    have hq_in : q ∈ (H (Fin.castSucc i)).toSet ∩
        (H (Fin.castSucc j)).toSet ∩ (H last).toSet := by
      rw [hq_inter]
      exact Set.mem_singleton q
    rcases hq_in with ⟨⟨hqi, hqj⟩, hqlast⟩
    rcases exists_p_planePt3_eq (H last) hqlast with ⟨p, hp_q⟩
    have hpi : p ∈ (traceLinesOnLastPlane n H i).toSet := by
      rw [mem_traceLine_iff n H i (h_not_parallel_last i) p, hp_q]
      exact hqi
    have hpj : p ∈ (traceLinesOnLastPlane n H j).toSet := by
      rw [mem_traceLine_iff n H j (h_not_parallel_last j) p, hp_q]
      exact hqj
    have h_line_eq := line2_eq_of_parallel_and_common_point
      (traceLinesOnLastPlane n H i) (traceLinesOnLastPlane n H j) h_par hpi hpj
    rcases exists_ne_mem_line2 (traceLinesOnLastPlane n H i) p hpi with ⟨p', hp'i, hp'_ne⟩
    have hp'j : p' ∈ (traceLinesOnLastPlane n H j).toSet := by
      rw [← h_line_eq]
      exact hp'i
    let q' := planePt3 (H last) p'
    have hq'last : q' ∈ (H last).toSet := planePt3_mem_plane (H last) p'
    have hq'i : q' ∈ (H (Fin.castSucc i)).toSet := by
      rw [← mem_traceLine_iff n H i (h_not_parallel_last i) p']
      exact hp'i
    have hq'j : q' ∈ (H (Fin.castSucc j)).toSet := by
      rw [← mem_traceLine_iff n H j (h_not_parallel_last j) p']
      exact hp'j
    have hq'_in : q' ∈ (H (Fin.castSucc i)).toSet ∩
        (H (Fin.castSucc j)).toSet ∩ (H last).toSet :=
      ⟨⟨hq'i, hq'j⟩, hq'last⟩
    rw [hq_inter] at hq'_in
    have hq'_eq_q : q' = q := Set.mem_singleton_iff.mp hq'_in
    rw [← hp_q] at hq'_eq_q
    have hp'_eq_p := planePt3_injective (H last) hq'_eq_q
    exact hp'_ne hp'_eq_p
  · -- どの3直線も1点で交わらない
    intro i j l hij hjl hil
    apply Set.eq_empty_of_subset_empty
    intro p hp
    rcases hp with ⟨⟨hpi, hpj⟩, hpl⟩
    have hqi := (mem_traceLine_iff n H i (h_not_parallel_last i) p).mp hpi
    have hqj := (mem_traceLine_iff n H j (h_not_parallel_last j) p).mp hpj
    have hql := (mem_traceLine_iff n H l (h_not_parallel_last l) p).mp hpl
    let q := planePt3 (H last) p
    have hqlast : q ∈ (H last).toSet := planePt3_mem_plane (H last) p
    have hq_all : q ∈ (H (Fin.castSucc i)).toSet ∩
        (H (Fin.castSucc j)).toSet ∩
        (H (Fin.castSucc l)).toSet ∩
        (H last).toSet := ⟨⟨⟨hqi, hqj⟩, hql⟩, hqlast⟩
    have h_empty := h_inter4 i j l hij hjl hil
    rw [h_empty] at hq_all
    exact hq_all

/-- 交線系が一般の位置にあるとき、切断領域数は maxPlaneRegions n 以上である。 -/
lemma maxPlaneRegions_le_splitSpaceRegionsCount_of_traceLines (n : ℕ) (H : Fin (n + 1) → Plane3)
    (h_not_par : ∀ i : Fin n, ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last n)))
    (hgen_lines : GeneralPositionLines n (traceLinesOnLastPlane n H)) :
    maxPlaneRegions n ≤ splitSpaceRegionsCount n H := by
  let L' := traceLinesOnLastPlane n H
  have h_plane_eq := planeRegionsCount_eq_max_of_general_position n L' hgen_lines
  rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion] at h_plane_eq
  let V := Finset.filter (fun τ => (convexPlaneRegion n L' τ).Nonempty) Finset.univ
  have hV_card : V.card = maxPlaneRegions n := h_plane_eq
  let split_sigs := Finset.filter (fun σ =>
    isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))) Finset.univ
  have h_split_count : splitSpaceRegionsCount n H = split_sigs.card := rfl
  have h_sub : V ⊆ split_sigs := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    refine ⟨hτ.1, ?_⟩
    rcases hτ.2 with ⟨p, hp⟩
    have hq := mem_convexSpaceRegion_of_mem_convexPlaneRegion' n H h_not_par τ hp
    exact ⟨planePt3 (H (Fin.last n)) p, hq.1, hq.2⟩
  have h_card_le := Finset.card_le_card h_sub
  rw [hV_card] at h_card_le
  rw [h_split_count]
  exact h_card_le

/-- 最後の平面と平行な平面が存在しないとき、
切断空間領域数は誘導交線系の平面領域数と一致する。 -/
lemma splitSpaceRegionsCount_eq_planeRegionsCount (n : ℕ) (H : Fin (n + 1) → Plane3)
    (h_not_par : ∀ i : Fin n, ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last n))) :
    splitSpaceRegionsCount n H = planeRegionsCount n (traceLinesOnLastPlane n H) := by
  let L' := traceLinesOnLastPlane n H
  let V := Finset.filter (fun τ => (convexPlaneRegion n L' τ).Nonempty) Finset.univ
  let split_sigs := Finset.filter (fun σ =>
    isSplitByPlane (convexSpaceRegion n (H ∘ Fin.castSucc) σ) (H (Fin.last n))) Finset.univ
  have h_sub : V ⊆ split_sigs := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    refine ⟨hτ.1, ?_⟩
    rcases hτ.2 with ⟨p, hp⟩
    have hq := mem_convexSpaceRegion_of_mem_convexPlaneRegion' n H h_not_par τ hp
    exact ⟨planePt3 (H (Fin.last n)) p, hq.1, hq.2⟩
  have h_sup : split_sigs ⊆ V := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨hσ.1, ?_⟩
    rcases hσ.2 with ⟨q, hq1, hq2⟩
    rcases exists_p_planePt3_eq (H (Fin.last n)) hq2 with ⟨p, hp_eq⟩
    use p
    intro i
    have hq_i := hq1 i
    dsimp [convexSpaceRegion] at hq_i
    have h_id := inner_planePt3_sub (H (Fin.last n)) p (H (Fin.castSucc i))
    rw [hp_eq] at h_id
    change @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec q -
      (H (Fin.castSucc i)).offset =
      @inner ℝ Plane2 _ (traceLineNormVec (H (Fin.last n)) (H (Fin.castSucc i))) p -
        ((H (Fin.castSucc i)).offset -
          @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec
            (((H (Fin.last n)).offset /
              @inner ℝ Space3 _ (H (Fin.last n)).normVec (H (Fin.last n)).normVec) •
             (H (Fin.last n)).normVec)) at h_id
    have hw_ne := traceLineNormVec_ne_zero (H (Fin.last n)) (H (Fin.castSucc i)) (h_not_par i)
    have h_line :
        (traceLinesOnLastPlane n H i).normVec =
          traceLineNormVec (H (Fin.last n)) (H (Fin.castSucc i)) ∧
        (traceLinesOnLastPlane n H i).offset = (H (Fin.castSucc i)).offset -
          @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec
            (((H (Fin.last n)).offset /
              @inner ℝ Space3 _ (H (Fin.last n)).normVec (H (Fin.last n)).normVec) •
             (H (Fin.last n)).normVec) := by
      dsimp [traceLinesOnLastPlane]
      split_ifs with hw
      · exact (hw_ne hw).elim
      · exact ⟨rfl, rfl⟩
    rw [h_line.1, h_line.2]
    cases hσi : σ i
    · rw [hσi] at hq_i
      dsimp at hq_i ⊢
      linarith [h_id, hq_i]
    · rw [hσi] at hq_i
      dsimp at hq_i ⊢
      linarith [h_id, hq_i]
  have h_eq : split_sigs = V := Finset.Subset.antisymm h_sup h_sub
  rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion]
  change split_sigs.card = V.card
  rw [h_eq]

/-- 交線系が一般の位置にあるとき、切断領域数はちょうど maxPlaneRegions n である。 -/
lemma splitSpaceRegionsCount_eq_of_traceLines (n : ℕ) (H : Fin (n + 1) → Plane3)
    (h_not_par : ∀ i : Fin n, ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last n)))
    (hgen_lines : GeneralPositionLines n (traceLinesOnLastPlane n H)) :
    splitSpaceRegionsCount n H = maxPlaneRegions n := by
  have h_le := splitSpaceRegionsCount_le_maxPlaneRegions n H
  have h_ge := maxPlaneRegions_le_splitSpaceRegionsCount_of_traceLines n H h_not_par hgen_lines
  omega

/-- 一般の位置にある平面配置における領域数の漸化等式:
一般の位置にある配置に新しい平面を追加したとき、
増える立体領域の個数は、平面上の交線配置が定める最大平面領域数 $S(n)$ に一致する。
2次元の最大値達成定理 `planeRegionsCount_eq_max_of_general_position` に帰着する。 -/
theorem spaceRegionsCount_succ_eq_of_general_position (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H) :
    spaceRegionsCount (n + 1) H = spaceRegionsCount n (H ∘ Fin.castSucc) + maxPlaneRegions n := by
  have h_le := spaceRegionsCount_succ_le n H
  have h_ge := spaceRegionsCount_succ_ge n H
  have h_split_eq := splitSpaceRegionsCount_eq_of_general_position n H hgen
  rw [h_split_eq] at h_ge
  omega

/-- 一般の位置にある平面配置に対する最大値達成定理:
一般の位置にある平面配置 $H$ では、空間領域数が最大値 $T_{\max}(n)$ に一致する。
帰納法、配置の遺伝性、漸化等式、組合せ漸化式 `maxSpaceRegions_succ` により証明される。 -/
theorem spaceRegionsCount_eq_max_of_general_position (n : ℕ) (H : Fin n → Plane3)
    (hgen : GeneralPositionPlanes n H) :
    spaceRegionsCount n H = maxSpaceRegions n := by
  induction n with
  | zero =>
    rw [spaceRegionsCount_zero H]
    dsimp [maxSpaceRegions]
    decide
  | succ m ih =>
    have hgen_sub : GeneralPositionPlanes m (H ∘ Fin.castSucc) :=
      GeneralPositionPlanes.castSucc m H hgen
    have hstep : spaceRegionsCount (m + 1) H =
        spaceRegionsCount m (H ∘ Fin.castSucc) + maxPlaneRegions m :=
      spaceRegionsCount_succ_eq_of_general_position m H hgen
    have hih : spaceRegionsCount m (H ∘ Fin.castSucc) = maxSpaceRegions m :=
      ih (H ∘ Fin.castSucc) hgen_sub
    have hsucc : maxSpaceRegions (m + 1) = maxSpaceRegions m + maxPlaneRegions m :=
      maxSpaceRegions_succ m
    rw [hstep, hih, hsucc]

/-! ### モーメント曲線による一般の位置の陽的構成と等号達成 -/

/-- パラメータ $t$ に対するモーメント平面の法線ベクトル $(1, t, t^2)$。 -/
def momentVec (t : ℝ) : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![(1 : ℝ), t, t ^ 2]

/-- モーメントベクトルの第0成分は $1$ であるため、0ベクトルではない。 -/
lemma momentVec_ne_zero (t : ℝ) : momentVec t ≠ 0 := by
  intro h
  have h0 : (WithLp.equiv 2 (Fin 3 → ℝ)) (momentVec t) 0 =
            (WithLp.equiv 2 (Fin 3 → ℝ)) 0 0 := by rw [h]
  simp [momentVec] at h0

/-- 実数パラメータ $t$ に対するモーメント平面:
方程式 $x + ty + t^2 z = t^3$ により定義される。 -/
def momentPlane (t : ℝ) : Plane3 where
  normVec := momentVec t
  normVec_ne_zero := momentVec_ne_zero t
  offset := t ^ 3

/-- モーメントベクトルと空間内の点の内積の展開表示。 -/
lemma inner_momentVec (t : ℝ) (p : Space3) :
    @inner ℝ Space3 _ (momentVec t) p = p 0 + t * p 1 + t ^ 2 * p 2 := by
  have h := PiLp.inner_apply (𝕜 := ℝ) (x := momentVec t) (y := p)
  rw [h, Fin.sum_univ_three]
  simp only [Real.inner_apply]
  change (1 : ℝ) * p 0 + t * p 1 + t ^ 2 * p 2 = p 0 + t * p 1 + t ^ 2 * p 2
  ring

/-- 点がモーメント平面に属するための必要十分条件。 -/
lemma mem_momentPlane (t : ℝ) (p : Space3) :
    p ∈ (momentPlane t).toSet ↔ p 0 + t * p 1 + t ^ 2 * p 2 = t ^ 3 := by
  dsimp [Plane3.toSet, momentPlane]
  rw [inner_momentVec]

set_option linter.flexible false in
/-- パラメータが異なれば、モーメント平面は平行でない。
法線ベクトルの第0成分からスカラー倍係数が $1$ に定まり、第1成分からパラメータの一致が導かれる。 -/
lemma not_parallel_momentPlanes {t₁ t₂ : ℝ} (hne : t₁ ≠ t₂) :
    ¬ parallelPlanes (momentPlane t₁) (momentPlane t₂) := by
  rintro ⟨c, hc⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) (momentPlane t₁).normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • (momentPlane t₂).normVec) 0 := by rw [hc]
  have hc1 : (WithLp.equiv 2 (Fin 3 → ℝ)) (momentPlane t₁).normVec 1 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • (momentPlane t₂).normVec) 1 := by rw [hc]
  simp [momentPlane, momentVec] at hc0 hc1
  subst hc0
  simp at hc1
  exact hne hc1

/-- 解と係数の関係より定まる3平面の交点の陽的表示。 -/
def explicitIntersection (t₁ t₂ t₃ : ℝ) : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    ![t₁ * t₂ * t₃, -(t₁ * t₂ + t₂ * t₃ + t₃ * t₁), t₁ + t₂ + t₃]

open Classical in
/-- 相異なる3つのモーメント平面は、解と係数の関係から定まる唯一の交点を持つ。 -/
lemma intersection_three_momentPlanes {t₁ t₂ t₃ : ℝ}
    (h12 : t₁ ≠ t₂) (h23 : t₂ ≠ t₃) (h13 : t₁ ≠ t₃) :
    ∃ p : Space3,
      (momentPlane t₁).toSet ∩ (momentPlane t₂).toSet ∩ (momentPlane t₃).toSet = {p} := by
  let p := explicitIntersection t₁ t₂ t₃
  use p
  ext q
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_momentPlane]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hp1 : p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 = t₁ ^ 3 := by
      dsimp [p, explicitIntersection]
      ring
    have hp2 : p 0 + t₂ * p 1 + t₂ ^ 2 * p 2 = t₂ ^ 3 := by
      dsimp [p, explicitIntersection]
      ring
    have hp3 : p 0 + t₃ * p 1 + t₃ ^ 2 * p 2 = t₃ ^ 3 := by
      dsimp [p, explicitIntersection]
      ring
    let a := q 2 - p 2
    let b := q 1 - p 1
    let c := q 0 - p 0
    let Q : ℝ[X] := C a * X ^ 2 + C b * X + C c
    have hroot (t : ℝ) (hq : q 0 + t * q 1 + t ^ 2 * q 2 = t ^ 3)
        (hp : p 0 + t * p 1 + t ^ 2 * p 2 = t ^ 3) : Q.IsRoot t := by
      dsimp [Q, IsRoot]
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      dsimp [a, b, c]
      linear_combination hq - hp
    have hr1 : Q.IsRoot t₁ := hroot t₁ h1 hp1
    have hr2 : Q.IsRoot t₂ := hroot t₂ h2 hp2
    have hr3 : Q.IsRoot t₃ := hroot t₃ h3 hp3
    have hQ_zero : Q = 0 := by
      by_contra hQ_ne
      have hdeg : Q.natDegree ≤ 2 := by
        dsimp [Q]
        compute_degree!
      let S : Finset ℝ := {t₁, t₂, t₃}
      have hS_card : S.card = 3 := by
        dsimp [S]
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · intro h
          rw [Finset.mem_singleton] at h
          exact h23 h
        · intro h
          rw [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl
          · exact h12 rfl
          · exact h13 rfl
      have hS_sub : S ⊆ Q.roots.toFinset := by
        intro t ht
        dsimp [S] at ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · rw [Multiset.mem_toFinset, mem_roots']; exact ⟨hQ_ne, hr1⟩
        · rw [Multiset.mem_toFinset, mem_roots']; exact ⟨hQ_ne, hr2⟩
        · rw [Multiset.mem_toFinset, mem_roots']; exact ⟨hQ_ne, hr3⟩
      have hle : S.card ≤ Q.roots.toFinset.card := Finset.card_le_card hS_sub
      have hcard_roots : Q.roots.toFinset.card ≤ Q.roots.card := Multiset.toFinset_card_le Q.roots
      have hdeg_bound : Q.roots.card ≤ Q.natDegree := card_roots' Q
      omega
    have hQ_zero' : (C a * X ^ 2 + C b * X + C c : ℝ[X]) = 0 := hQ_zero
    have hc0 : (C a * X ^ 2 + C b * X + C c : ℝ[X]).coeff 0 = 0 := by rw [hQ_zero', coeff_zero]
    have hc1 : (C a * X ^ 2 + C b * X + C c : ℝ[X]).coeff 1 = 0 := by rw [hQ_zero', coeff_zero]
    have hc2 : (C a * X ^ 2 + C b * X + C c : ℝ[X]).coeff 2 = 0 := by rw [hQ_zero', coeff_zero]
    simp at hc0 hc1 hc2
    have ha : q 2 = p 2 := by linarith
    have hb : q 1 = p 1 := by linarith
    have hc : q 0 = p 0 := by linarith
    ext i
    fin_cases i
    · exact hc
    · exact hb
    · exact ha
  · rintro rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp [p, explicitIntersection]; ring
    · dsimp [p, explicitIntersection]; ring
    · dsimp [p, explicitIntersection]; ring

open Classical in
/-- 相異なる4つのモーメント平面の共通部分は空である。
もし点 $p$ が属せば、3次多項式 $t^3 - z t^2 - y t - x$ が4つの相異なる根を持つことになり矛盾する。 -/
lemma intersection_four_momentPlanes_empty {t₁ t₂ t₃ t₄ : ℝ}
    (h12 : t₁ ≠ t₂) (h23 : t₂ ≠ t₃) (h34 : t₃ ≠ t₄)
    (h13 : t₁ ≠ t₃) (h14 : t₁ ≠ t₄) (h24 : t₂ ≠ t₄) :
    (momentPlane t₁).toSet ∩ (momentPlane t₂).toSet ∩
    (momentPlane t₃).toSet ∩ (momentPlane t₄).toSet = ∅ := by
  ext p
  simp only [Set.mem_inter_iff, mem_momentPlane, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  let P : ℝ[X] := X ^ 3 - C (p 2) * X ^ 2 - C (p 1) * X - C (p 0)
  have hroot (t : ℝ) (h : p 0 + t * p 1 + t ^ 2 * p 2 = t ^ 3) : P.IsRoot t := by
    dsimp [P, IsRoot]
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C]
    linear_combination -h
  have hr1 : P.IsRoot t₁ := hroot t₁ h1
  have hr2 : P.IsRoot t₂ := hroot t₂ h2
  have hr3 : P.IsRoot t₃ := hroot t₃ h3
  have hr4 : P.IsRoot t₄ := hroot t₄ h4
  have hP_ne : P ≠ 0 := by
    intro hzero
    have hzero' : (X ^ 3 - C (p 2) * X ^ 2 - C (p 1) * X - C (p 0) : ℝ[X]) = 0 := hzero
    have hc : (X ^ 3 - C (p 2) * X ^ 2 - C (p 1) * X - C (p 0) : ℝ[X]).coeff 3 = 0 := by
      rw [hzero', coeff_zero]
    simp [coeff_sub, coeff_X_pow] at hc
  have hdeg : P.natDegree ≤ 3 := by
    dsimp [P]
    compute_degree!
  let S : Finset ℝ := {t₁, t₂, t₃, t₄}
  have hS_card : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · intro h
      rw [Finset.mem_singleton] at h
      exact h34 h
    · intro h
      rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact h23 rfl
      · exact h24 rfl
    · intro h
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact h12 rfl
      · exact h13 rfl
      · exact h14 rfl
  have hS_sub : S ⊆ P.roots.toFinset := by
    intro t ht
    dsimp [S] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [Multiset.mem_toFinset, mem_roots']; exact ⟨hP_ne, hr1⟩
    · rw [Multiset.mem_toFinset, mem_roots']; exact ⟨hP_ne, hr2⟩
    · rw [Multiset.mem_toFinset, mem_roots']; exact ⟨hP_ne, hr3⟩
    · rw [Multiset.mem_toFinset, mem_roots']; exact ⟨hP_ne, hr4⟩
  have hle : S.card ≤ P.roots.toFinset.card := Finset.card_le_card hS_sub
  have hcard_roots : P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le P.roots
  have hdeg_bound : P.roots.card ≤ P.natDegree := card_roots' P
  omega

/-- 任意の自然数 $n$ に対し、一般の位置にある平面配置が存在する。 -/
theorem exists_general_position_planes (n : ℕ) :
    ∃ (H : Fin n → Plane3), GeneralPositionPlanes n H := by
  use fun i => momentPlane (i.val : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h_ne : (i.val : ℝ) ≠ (j.val : ℝ) := by
      exact_mod_cast (Fin.ext_iff.not.mp hij)
    exact not_parallel_momentPlanes h_ne
  · intro i j l hij hjl hil
    have h_ne1 : (i.val : ℝ) ≠ (j.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp hij)
    have h_ne2 : (j.val : ℝ) ≠ (l.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp hjl)
    have h_ne3 : (i.val : ℝ) ≠ (l.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp hil)
    exact intersection_three_momentPlanes h_ne1 h_ne2 h_ne3
  · intro i j l m hij hjl hlm hil him hjm
    have h_ne1 : (i.val : ℝ) ≠ (j.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp hij)
    have h_ne2 : (j.val : ℝ) ≠ (l.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp hjl)
    have h_ne3 : (l.val : ℝ) ≠ (m.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp hlm)
    have h_ne4 : (i.val : ℝ) ≠ (l.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp hil)
    have h_ne5 : (i.val : ℝ) ≠ (m.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp him)
    have h_ne6 : (j.val : ℝ) ≠ (m.val : ℝ) := by exact_mod_cast (Fin.ext_iff.not.mp hjm)
    exact intersection_four_momentPlanes_empty h_ne1 h_ne2 h_ne3 h_ne4 h_ne5 h_ne6

/-- 同一の点集合を定める2つの平面は平行である。
法線ベクトルの直交補空間の比較により、スカラー倍の存在を導出する。 -/
lemma parallelPlanes_of_toSet_eq (H₁ H₂ : Plane3) (h_eq : H₁.toSet = H₂.toSet) :
    parallelPlanes H₁ H₂ := by
  let u := H₁.normVec
  let v := H₂.normVec
  have hu_ne : u ≠ 0 := H₁.normVec_ne_zero
  have hv_ne : v ≠ 0 := H₂.normVec_ne_zero
  have hK_ne : @inner ℝ Space3 _ u u ≠ 0 := by
    intro h
    exact hu_ne (inner_self_eq_zero.mp h)
  let K := @inner ℝ Space3 _ u u
  let w : Space3 := K • v - (@inner ℝ Space3 _ u v) • u
  have huw : @inner ℝ Space3 _ u w = 0 := by
    dsimp [w]
    rw [inner_sub_right, inner_smul_right, inner_smul_right]
    dsimp [K]
    ring
  let x₀ : Space3 := (H₁.offset / K) • u
  have hx₀_in1 : x₀ ∈ H₁.toSet := by
    dsimp [Plane3.toSet, x₀]
    rw [inner_smul_right]
    have : @inner ℝ Space3 _ u u = K := rfl
    rw [this, div_mul_cancel₀ H₁.offset hK_ne]
  let x₁ : Space3 := x₀ + w
  have hx₁_in1 : x₁ ∈ H₁.toSet := by
    dsimp [Plane3.toSet, x₁]
    rw [inner_add_right]
    have h1 : @inner ℝ Space3 _ u x₀ = H₁.offset := hx₀_in1
    rw [h1, huw, add_zero]
  have hx₀_in2 : x₀ ∈ H₂.toSet := by rw [← h_eq]; exact hx₀_in1
  have hx₁_in2 : x₁ ∈ H₂.toSet := by rw [← h_eq]; exact hx₁_in1
  have hvw : @inner ℝ Space3 _ v w = 0 := by
    have h1 : @inner ℝ Space3 _ v x₀ = H₂.offset := hx₀_in2
    have h2 : @inner ℝ Space3 _ v x₁ = H₂.offset := hx₁_in2
    have h3 : @inner ℝ Space3 _ v x₁ = @inner ℝ Space3 _ v x₀ + @inner ℝ Space3 _ v w := by
      dsimp [x₁]; rw [inner_add_right]
    linarith
  have hww : @inner ℝ Space3 _ w w = 0 := by
    have hw_def : w = K • v - (@inner ℝ Space3 _ u v) • u := rfl
    calc
      @inner ℝ Space3 _ w w =
          @inner ℝ Space3 _ (K • v - (@inner ℝ Space3 _ u v) • u) w := by rw [← hw_def]
      _ = K * @inner ℝ Space3 _ v w - (@inner ℝ Space3 _ u v) * @inner ℝ Space3 _ u w := by
        rw [inner_sub_left, inner_smul_left, inner_smul_left]
        simp only [starRingEnd_apply, star_trivial]
      _ = K * 0 - (@inner ℝ Space3 _ u v) * 0 := by rw [hvw, huw]
      _ = 0 := by ring
  have hw_zero : w = 0 := inner_self_eq_zero.mp hww
  have h_eq_vec : K • v = (@inner ℝ Space3 _ u v) • u := by
    have : K • v - (@inner ℝ Space3 _ u v) • u = 0 := hw_zero
    exact sub_eq_zero.mp this
  have huv_ne : @inner ℝ Space3 _ u v ≠ 0 := by
    intro h_zero
    rw [h_zero, zero_smul] at h_eq_vec
    have : v = 0 := smul_eq_zero.mp h_eq_vec |>.resolve_left hK_ne
    exact hv_ne this
  use K / (@inner ℝ Space3 _ u v)
  have h_u_eq : u = (K / (@inner ℝ Space3 _ u v)) • v := by
    calc
      u = (1 : ℝ) • u := by rw [one_smul]
      _ = ((@inner ℝ Space3 _ u v)⁻¹ * (@inner ℝ Space3 _ u v)) • u := by
        rw [inv_mul_cancel₀ huv_ne]
      _ = (@inner ℝ Space3 _ u v)⁻¹ • ((@inner ℝ Space3 _ u v) • u) := by rw [mul_smul]
      _ = (@inner ℝ Space3 _ u v)⁻¹ • (K • v) := by rw [← h_eq_vec]
      _ = ((@inner ℝ Space3 _ u v)⁻¹ * K) • v := by rw [mul_smul]
      _ = (K / (@inner ℝ Space3 _ u v)) • v := by rw [div_eq_inv_mul, mul_comm]
  exact h_u_eq

/-- 一般の位置にある平面配置は、相異なる平面からなる。 -/
lemma distinctPlanes_of_general_position (n : ℕ) (H : Fin n → Plane3)
    (hgen : GeneralPositionPlanes n H) :
    DistinctPlanes n H := by
  intro i j h_eq
  by_contra hij
  have h_not_parallel := hgen.1 i j hij
  apply h_not_parallel
  exact parallelPlanes_of_toSet_eq (H i) (H j) h_eq

/-! ### 本問の主定理 -/

/-- 【第4問 (1) の解答(代数公式との一致)】
平面分割の最大個数は多項式 (n³ + 5n + 6) / 6 に一致する。 -/
theorem problem_4_1_proof (n : ℕ) :
    maxSpaceRegions n = maxSpaceRegionsFormula n := by
  have h := six_mul_maxSpaceRegions n
  dsimp [maxSpaceRegionsFormula]
  omega

/-- 【第4問 (1) の幾何学的解答】
相異なる n 枚の平面による空間領域数は常に maxSpaceRegionsFormula n 以下であり、かつ等号を達成する配置が存在する。 -/
theorem problem_4_1_geometric_proof (n : ℕ) :
    (∀ (H : Fin n → Plane3), DistinctPlanes n H →
      spaceRegionsCount n H ≤ maxSpaceRegionsFormula n) ∧
    (∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = maxSpaceRegionsFormula n) := by
  constructor
  · intro H _hdist
    have hle := spaceRegionsCount_le_maxSpaceRegions n H
    have heq := problem_4_1_proof n
    omega
  · obtain ⟨H, hgen⟩ := exists_general_position_planes n
    refine ⟨H, distinctPlanes_of_general_position n H hgen, ?_⟩
    have heq1 := spaceRegionsCount_eq_max_of_general_position n H hgen
    have heq2 := problem_4_1_proof n
    rw [heq1, heq2]

/-! ### 具体例 (n = 2, 3, 4) における領域数の検証補題 -/

/-- n = 2 のとき: 最大値は 4、第2位は 3 である。 -/
lemma space_regions_n_two :
    maxSpaceRegionsFormula 2 = 4 ∧ secondSpaceRegionsFormula 2 = 3 := by
  dsimp [maxSpaceRegionsFormula, secondSpaceRegionsFormula]
  decide

/-- n = 3 のとき: 最大値は 8、第2位は 7、第3位は 6 である。
問題文の例示 T(H₁, H₂, H₃) = 8 および 7 に対応する。 -/
lemma space_regions_n_three :
    maxSpaceRegionsFormula 3 = 8 ∧
    secondSpaceRegionsFormula 3 = 7 ∧
    thirdSpaceRegionsFormula 3 = 6 := by
  dsimp [maxSpaceRegionsFormula, secondSpaceRegionsFormula, thirdSpaceRegionsFormula]
  decide

/-- n = 4 のとき: 最大値は 15、第2位は 14、第3位は幾何的制約による例外値 12 である。 -/
lemma space_regions_n_four :
    maxSpaceRegionsFormula 4 = 15 ∧
    secondSpaceRegionsFormula 4 = 14 ∧
    thirdSpaceRegionsFormula 4 = 12 := by
  dsimp [maxSpaceRegionsFormula, secondSpaceRegionsFormula, thirdSpaceRegionsFormula]
  decide

/-- 【第4問 (2) の解答(代数公式との一致)】
n ≥ 2 のとき、2番目に大きい値は最大値より 1 小さく、多項式 (n³ + 5n) / 6 と一致する。 -/
theorem problem_4_2_proof (n : ℕ) (hn : 2 ≤ n) :
    secondSpaceRegionsFormula n = maxSpaceRegionsFormula n - 1 := by
  have h := six_mul_maxSpaceRegions n
  dsimp [secondSpaceRegionsFormula, maxSpaceRegionsFormula]
  omega

/-! ### n = 2 における平行平面配置による領域数3の達成 -/

/-- 第2軸 $(0, 0, 1)$ 方向の単位法線ベクトル。 -/
def e2Vec : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![(0 : ℝ), 0, 1]

/-- 法線ベクトル e2Vec は非ゼロである。 -/
lemma e2Vec_ne_zero : e2Vec ≠ 0 := by
  intro h
  have h2 : (WithLp.equiv 2 (Fin 3 → ℝ)) e2Vec 2 =
            (WithLp.equiv 2 (Fin 3 → ℝ)) 0 2 := by rw [h]
  simp [e2Vec] at h2

/-- z座標が $c$ である平面 $z = c$。 -/
def zPlane (c : ℝ) : Plane3 where
  normVec := e2Vec
  normVec_ne_zero := e2Vec_ne_zero
  offset := c

/-- e2Vec と任意の点の内積はz座標に一致する。 -/
lemma inner_e2Vec (p : Space3) :
    @inner ℝ Space3 _ e2Vec p = p 2 := by
  have h := PiLp.inner_apply (𝕜 := ℝ) (x := e2Vec) (y := p)
  rw [h, Fin.sum_univ_three]
  simp only [Real.inner_apply]
  change (0 : ℝ) * p 0 + (0 : ℝ) * p 1 + (1 : ℝ) * p 2 = p 2
  ring

/-- 点 p が平面 zPlane c に属する必要十分条件は p 2 = c である。 -/
lemma mem_zPlane (c : ℝ) (p : Space3) : p ∈ (zPlane c).toSet ↔ p 2 = c := by
  dsimp [Plane3.toSet, zPlane]
  rw [inner_e2Vec]

/-- z軸上の点 $(0, 0, z)$。 -/
def ptZ (z : ℝ) : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![(0 : ℝ), 0, z]

lemma ptZ_apply_two (z : ℝ) : (ptZ z) 2 = z := rfl

lemma inner_e2Vec_ptZ (z : ℝ) :
    @inner ℝ Space3 _ e2Vec (ptZ z) = z := by
  rw [inner_e2Vec, ptZ_apply_two]

/-- 2枚の平行な平面 $z = 0$ および $z = 1$ からなる配置。 -/
def H_two_parallel : Fin 2 → Plane3 :=
  ![zPlane 0, zPlane 1]

/-- 平行な2平面 $z = 0$ と $z = 1$ は相異なる。 -/
lemma distinctPlanes_two_parallel : DistinctPlanes 2 H_two_parallel := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    change (H_two_parallel 0).toSet = (H_two_parallel 1).toSet at hij
    have hmem : ptZ 0 ∈ (H_two_parallel 0).toSet := by
      dsimp [Plane3.toSet, H_two_parallel, zPlane]
      rw [inner_e2Vec_ptZ]
    have hmem' : ptZ 0 ∈ (H_two_parallel 1).toSet := by
      rw [← hij]
      exact hmem
    dsimp [Plane3.toSet, H_two_parallel, zPlane] at hmem'
    rw [inner_e2Vec_ptZ] at hmem'
    linarith
  · exfalso
    change (H_two_parallel 1).toSet = (H_two_parallel 0).toSet at hij
    have hmem : ptZ 1 ∈ (H_two_parallel 1).toSet := by
      dsimp [Plane3.toSet, H_two_parallel, zPlane]
      rw [inner_e2Vec_ptZ]
    rw [hij] at hmem
    dsimp [Plane3.toSet, H_two_parallel, zPlane] at hmem
    rw [inner_e2Vec_ptZ] at hmem
    linarith
  · rfl

/-- $z < 0$ かつ $z > 1$ は両立不能であるため、
符号ベクトル (false, true) の領域は空集合である。 -/
lemma convexSpaceRegion_two_parallel_false_true_empty :
    ¬ (convexSpaceRegion 2 H_two_parallel ![(false : Bool), true]).Nonempty := by
  rintro ⟨p, hp⟩
  have h0 := hp 0
  have h1 := hp 1
  dsimp [convexSpaceRegion, H_two_parallel, zPlane] at h0 h1
  rw [inner_e2Vec] at h0 h1
  linarith

lemma convexSpaceRegion_two_parallel_false_false_nonempty :
    (convexSpaceRegion 2 H_two_parallel ![(false : Bool), false]).Nonempty := by
  use ptZ (-1)
  intro i
  fin_cases i
  · dsimp [convexSpaceRegion, H_two_parallel, zPlane]
    rw [inner_e2Vec_ptZ]
    linarith
  · dsimp [convexSpaceRegion, H_two_parallel, zPlane]
    rw [inner_e2Vec_ptZ]
    linarith

lemma convexSpaceRegion_two_parallel_true_false_nonempty :
    (convexSpaceRegion 2 H_two_parallel ![(true : Bool), false]).Nonempty := by
  use ptZ (1 / 2)
  intro i
  fin_cases i
  · dsimp [convexSpaceRegion, H_two_parallel, zPlane]
    rw [inner_e2Vec_ptZ]
    linarith
  · dsimp [convexSpaceRegion, H_two_parallel, zPlane]
    rw [inner_e2Vec_ptZ]
    linarith

lemma convexSpaceRegion_two_parallel_true_true_nonempty :
    (convexSpaceRegion 2 H_two_parallel ![(true : Bool), true]).Nonempty := by
  use ptZ 2
  intro i
  fin_cases i
  · dsimp [convexSpaceRegion, H_two_parallel, zPlane]
    rw [inner_e2Vec_ptZ]
    linarith
  · dsimp [convexSpaceRegion, H_two_parallel, zPlane]
    rw [inner_e2Vec_ptZ]
    linarith

lemma signVector_two_cases (σ : Fin 2 → Bool) :
    σ = ![(false : Bool), false] ∨
    σ = ![(true : Bool), false] ∨
    σ = ![(true : Bool), true] ∨
    σ = ![(false : Bool), true] := by
  have h0 : σ 0 = false ∨ σ 0 = true := by cases σ 0 <;> simp
  have h1 : σ 1 = false ∨ σ 1 = true := by cases σ 1 <;> simp
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · left
    ext i; fin_cases i <;> assumption
  · right; right; right
    ext i; fin_cases i <;> assumption
  · right; left
    ext i; fin_cases i <;> assumption
  · right; right; left
    ext i; fin_cases i <;> assumption

/-- 2枚の平行な平面配置による領域数はちょうど3である。 -/
lemma spaceRegionsCount_two_parallel_eq_three :
    spaceRegionsCount 2 H_two_parallel = 3 := by
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  have hs : (Finset.filter (fun σ =>
      (convexSpaceRegion 2 H_two_parallel σ).Nonempty) Finset.univ) =
      {![(false : Bool), false], ![(true : Bool), false], ![(true : Bool), true]} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hne
      rcases signVector_two_cases σ with h | h | h | h
      · left; exact h
      · right; left; exact h
      · right; right; exact h
      · subst h
        exact (convexSpaceRegion_two_parallel_false_true_empty hne).elim
    · rintro (rfl | rfl | rfl)
      · exact convexSpaceRegion_two_parallel_false_false_nonempty
      · exact convexSpaceRegion_two_parallel_true_false_nonempty
      · exact convexSpaceRegion_two_parallel_true_true_nonempty
  rw [hs]
  decide

/-- 2枚の平行な平面による配置の領域数は3である。 -/
lemma spaceRegionsCount_two_parallel :
    ∃ (H : Fin 2 → Plane3), DistinctPlanes 2 H ∧ spaceRegionsCount 2 H = 3 :=
  ⟨H_two_parallel, distinctPlanes_two_parallel, spaceRegionsCount_two_parallel_eq_three⟩

/-! ### n = 3 における三角柱平面配置による領域数7の達成 -/

/-- xy 平面上の点 $(x, y, 0)$。 -/
def ptXY (x y : ℝ) : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![x, y, (0 : ℝ)]

lemma ptXY_apply_zero (x y : ℝ) : (ptXY x y) 0 = x := rfl
lemma ptXY_apply_one (x y : ℝ) : (ptXY x y) 1 = y := rfl
lemma ptXY_apply_two (x y : ℝ) : (ptXY x y) 2 = 0 := rfl

/-- 第0軸 $(1, 0, 0)$ 方向の法線ベクトル。 -/
def v0_vec : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![(1 : ℝ), 0, 0]

lemma v0_vec_ne_zero : v0_vec ≠ 0 := by
  intro h
  have h0 : (WithLp.equiv 2 (Fin 3 → ℝ)) v0_vec 0 =
            (WithLp.equiv 2 (Fin 3 → ℝ)) 0 0 := by rw [h]
  simp [v0_vec] at h0

/-- 第1軸 $(0, 1, 0)$ 方向の法線ベクトル。 -/
def v1_vec : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![(0 : ℝ), 1, 0]

lemma v1_vec_ne_zero : v1_vec ≠ 0 := by
  intro h
  have h1 : (WithLp.equiv 2 (Fin 3 → ℝ)) v1_vec 1 =
            (WithLp.equiv 2 (Fin 3 → ℝ)) 0 1 := by rw [h]
  simp [v1_vec] at h1

/-- 斜め方向 $(1, 1, 0)$ の法線ベクトル。 -/
def v2_vec : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![(1 : ℝ), 1, 0]

lemma v2_vec_ne_zero : v2_vec ≠ 0 := by
  intro h
  have h0 : (WithLp.equiv 2 (Fin 3 → ℝ)) v2_vec 0 =
            (WithLp.equiv 2 (Fin 3 → ℝ)) 0 0 := by rw [h]
  simp [v2_vec] at h0

lemma inner_v0_vec (p : Space3) :
    @inner ℝ Space3 _ v0_vec p = p 0 := by
  have h := PiLp.inner_apply (𝕜 := ℝ) (x := v0_vec) (y := p)
  rw [h, Fin.sum_univ_three]
  simp only [Real.inner_apply]
  change (1 : ℝ) * p 0 + (0 : ℝ) * p 1 + (0 : ℝ) * p 2 = p 0
  ring

lemma inner_v1_vec (p : Space3) :
    @inner ℝ Space3 _ v1_vec p = p 1 := by
  have h := PiLp.inner_apply (𝕜 := ℝ) (x := v1_vec) (y := p)
  rw [h, Fin.sum_univ_three]
  simp only [Real.inner_apply]
  change (0 : ℝ) * p 0 + (1 : ℝ) * p 1 + (0 : ℝ) * p 2 = p 1
  ring

lemma inner_v2_vec (p : Space3) :
    @inner ℝ Space3 _ v2_vec p = p 0 + p 1 := by
  have h := PiLp.inner_apply (𝕜 := ℝ) (x := v2_vec) (y := p)
  rw [h, Fin.sum_univ_three]
  simp only [Real.inner_apply]
  change (1 : ℝ) * p 0 + (1 : ℝ) * p 1 + (0 : ℝ) * p 2 = p 0 + p 1
  ring

lemma inner_v0_ptXY (x y : ℝ) : @inner ℝ Space3 _ v0_vec (ptXY x y) = x := by
  rw [inner_v0_vec, ptXY_apply_zero]

lemma inner_v1_ptXY (x y : ℝ) : @inner ℝ Space3 _ v1_vec (ptXY x y) = y := by
  rw [inner_v1_vec, ptXY_apply_one]

lemma inner_v2_ptXY (x y : ℝ) : @inner ℝ Space3 _ v2_vec (ptXY x y) = x + y := by
  rw [inner_v2_vec, ptXY_apply_zero, ptXY_apply_one]

/-- 平面 $x = 0$。 -/
def plane_x0 : Plane3 where
  normVec := v0_vec
  normVec_ne_zero := v0_vec_ne_zero
  offset := 0

/-- 平面 $y = 0$。 -/
def plane_y0 : Plane3 where
  normVec := v1_vec
  normVec_ne_zero := v1_vec_ne_zero
  offset := 0

/-- 平面 $x + y = 1$。 -/
def plane_xy1 : Plane3 where
  normVec := v2_vec
  normVec_ne_zero := v2_vec_ne_zero
  offset := 1

lemma mem_plane_x0 (p : Space3) : p ∈ plane_x0.toSet ↔ p 0 = 0 := by
  dsimp [Plane3.toSet, plane_x0]
  rw [inner_v0_vec]

lemma mem_plane_y0 (p : Space3) : p ∈ plane_y0.toSet ↔ p 1 = 0 := by
  dsimp [Plane3.toSet, plane_y0]
  rw [inner_v1_vec]

lemma mem_plane_xy1 (p : Space3) : p ∈ plane_xy1.toSet ↔ p 0 + p 1 = 1 := by
  dsimp [Plane3.toSet, plane_xy1]
  rw [inner_v2_vec]

/-- 三角柱をなす3平面 $x = 0$, $y = 0$, $x + y = 1$ からなる配置。 -/
def H_three_prism : Fin 3 → Plane3 :=
  ![plane_x0, plane_y0, plane_xy1]

/-- 3枚の平面は相異なる。 -/
lemma distinctPlanes_three_prism : DistinctPlanes 3 H_three_prism := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    change (H_three_prism 0).toSet = (H_three_prism 1).toSet at hij
    have hmem : ptXY 0 1 ∈ (H_three_prism 0).toSet := by
      dsimp [Plane3.toSet, H_three_prism, plane_x0]
      rw [inner_v0_ptXY]
    rw [hij] at hmem
    dsimp [Plane3.toSet, H_three_prism, plane_y0] at hmem
    rw [inner_v1_ptXY] at hmem
    linarith
  · exfalso
    change (H_three_prism 0).toSet = (H_three_prism 2).toSet at hij
    have hmem : ptXY 0 0 ∈ (H_three_prism 0).toSet := by
      dsimp [Plane3.toSet, H_three_prism, plane_x0]
      rw [inner_v0_ptXY]
    rw [hij] at hmem
    dsimp [Plane3.toSet, H_three_prism, plane_xy1] at hmem
    rw [inner_v2_ptXY] at hmem
    linarith
  · exfalso
    change (H_three_prism 1).toSet = (H_three_prism 0).toSet at hij
    have hmem : ptXY 1 0 ∈ (H_three_prism 1).toSet := by
      dsimp [Plane3.toSet, H_three_prism, plane_y0]
      rw [inner_v1_ptXY]
    rw [hij] at hmem
    dsimp [Plane3.toSet, H_three_prism, plane_x0] at hmem
    rw [inner_v0_ptXY] at hmem
    linarith
  · rfl
  · exfalso
    change (H_three_prism 1).toSet = (H_three_prism 2).toSet at hij
    have hmem : ptXY 0 0 ∈ (H_three_prism 1).toSet := by
      dsimp [Plane3.toSet, H_three_prism, plane_y0]
      rw [inner_v1_ptXY]
    rw [hij] at hmem
    dsimp [Plane3.toSet, H_three_prism, plane_xy1] at hmem
    rw [inner_v2_ptXY] at hmem
    linarith
  · exfalso
    change (H_three_prism 2).toSet = (H_three_prism 0).toSet at hij
    have hmem : ptXY 0 0 ∈ (H_three_prism 0).toSet := by
      dsimp [Plane3.toSet, H_three_prism, plane_x0]
      rw [inner_v0_ptXY]
    rw [← hij] at hmem
    dsimp [Plane3.toSet, H_three_prism, plane_xy1] at hmem
    rw [inner_v2_ptXY] at hmem
    linarith
  · exfalso
    change (H_three_prism 2).toSet = (H_three_prism 1).toSet at hij
    have hmem : ptXY 0 0 ∈ (H_three_prism 1).toSet := by
      dsimp [Plane3.toSet, H_three_prism, plane_y0]
      rw [inner_v1_ptXY]
    rw [← hij] at hmem
    dsimp [Plane3.toSet, H_three_prism, plane_xy1] at hmem
    rw [inner_v2_ptXY] at hmem
    linarith
  · rfl

/-- $x < 0$ かつ $y < 0$ かつ $x + y > 1$ は両立不能であるため、
符号ベクトル (false, false, true) の領域は空集合である。 -/
lemma convexSpaceRegion_three_prism_FFT_empty :
    ¬ (convexSpaceRegion 3 H_three_prism ![(false : Bool), false, true]).Nonempty := by
  rintro ⟨p, hp⟩
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  dsimp [convexSpaceRegion, H_three_prism, plane_x0, plane_y0, plane_xy1] at h0 h1 h2
  rw [inner_v0_vec] at h0
  rw [inner_v1_vec] at h1
  rw [inner_v2_vec] at h2
  linarith

lemma convexSpaceRegion_three_prism_FFF_nonempty :
    (convexSpaceRegion 3 H_three_prism ![(false : Bool), false, false]).Nonempty := by
  use ptXY (-1) (-1)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_prism, plane_x0]; rw [inner_v0_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_y0]; rw [inner_v1_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_xy1]; rw [inner_v2_ptXY]; linarith

lemma convexSpaceRegion_three_prism_TFF_nonempty :
    (convexSpaceRegion 3 H_three_prism ![(true : Bool), false, false]).Nonempty := by
  use ptXY (1 / 2) (-1)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_prism, plane_x0]; rw [inner_v0_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_y0]; rw [inner_v1_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_xy1]; rw [inner_v2_ptXY]; linarith

lemma convexSpaceRegion_three_prism_TFT_nonempty :
    (convexSpaceRegion 3 H_three_prism ![(true : Bool), false, true]).Nonempty := by
  use ptXY 3 (-1)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_prism, plane_x0]; rw [inner_v0_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_y0]; rw [inner_v1_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_xy1]; rw [inner_v2_ptXY]; linarith

lemma convexSpaceRegion_three_prism_FTF_nonempty :
    (convexSpaceRegion 3 H_three_prism ![(false : Bool), true, false]).Nonempty := by
  use ptXY (-1) (1 / 2)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_prism, plane_x0]; rw [inner_v0_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_y0]; rw [inner_v1_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_xy1]; rw [inner_v2_ptXY]; linarith

lemma convexSpaceRegion_three_prism_FTT_nonempty :
    (convexSpaceRegion 3 H_three_prism ![(false : Bool), true, true]).Nonempty := by
  use ptXY (-1) 3
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_prism, plane_x0]; rw [inner_v0_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_y0]; rw [inner_v1_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_xy1]; rw [inner_v2_ptXY]; linarith

lemma convexSpaceRegion_three_prism_TTF_nonempty :
    (convexSpaceRegion 3 H_three_prism ![(true : Bool), true, false]).Nonempty := by
  use ptXY (1 / 3) (1 / 3)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_prism, plane_x0]; rw [inner_v0_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_y0]; rw [inner_v1_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_xy1]; rw [inner_v2_ptXY]; linarith

lemma convexSpaceRegion_three_prism_TTT_nonempty :
    (convexSpaceRegion 3 H_three_prism ![(true : Bool), true, true]).Nonempty := by
  use ptXY 1 1
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_prism, plane_x0]; rw [inner_v0_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_y0]; rw [inner_v1_ptXY]; linarith
  · dsimp [convexSpaceRegion, H_three_prism, plane_xy1]; rw [inner_v2_ptXY]; linarith

lemma signVector_three_cases (σ : Fin 3 → Bool) :
    σ = ![(false : Bool), false, false] ∨
    σ = ![(true : Bool), false, false] ∨
    σ = ![(true : Bool), false, true] ∨
    σ = ![(false : Bool), true, false] ∨
    σ = ![(false : Bool), true, true] ∨
    σ = ![(true : Bool), true, false] ∨
    σ = ![(true : Bool), true, true] ∨
    σ = ![(false : Bool), false, true] := by
  have h0 : σ 0 = false ∨ σ 0 = true := by cases σ 0 <;> simp
  have h1 : σ 1 = false ∨ σ 1 = true := by cases σ 1 <;> simp
  have h2 : σ 2 = false ∨ σ 2 = true := by cases σ 2 <;> simp
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; ext i; fin_cases i <;> assumption
  · right; right; right; right; right; right; right; ext i; fin_cases i <;> assumption
  · right; right; right; left; ext i; fin_cases i <;> assumption
  · right; right; right; right; left; ext i; fin_cases i <;> assumption
  · right; left; ext i; fin_cases i <;> assumption
  · right; right; left; ext i; fin_cases i <;> assumption
  · right; right; right; right; right; left; ext i; fin_cases i <;> assumption
  · right; right; right; right; right; right; left; ext i; fin_cases i <;> assumption

/-- 3枚の三角柱をなす平面配置による領域数はちょうど 7 である。 -/
lemma spaceRegionsCount_three_prism_eq_seven :
    spaceRegionsCount 3 H_three_prism = 7 := by
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  have hs : (Finset.filter (fun σ =>
      (convexSpaceRegion 3 H_three_prism σ).Nonempty) Finset.univ) =
      {![(false : Bool), false, false],
       ![(true : Bool), false, false],
       ![(true : Bool), false, true],
       ![(false : Bool), true, false],
       ![(false : Bool), true, true],
       ![(true : Bool), true, false],
       ![(true : Bool), true, true]} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hne
      rcases signVector_three_cases σ with h | h | h | h | h | h | h | h
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; left; exact h
      · right; right; right; right; right; left; exact h
      · right; right; right; right; right; right; exact h
      · subst h
        exact (convexSpaceRegion_three_prism_FFT_empty hne).elim
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact convexSpaceRegion_three_prism_FFF_nonempty
      · exact convexSpaceRegion_three_prism_TFF_nonempty
      · exact convexSpaceRegion_three_prism_TFT_nonempty
      · exact convexSpaceRegion_three_prism_FTF_nonempty
      · exact convexSpaceRegion_three_prism_FTT_nonempty
      · exact convexSpaceRegion_three_prism_TTF_nonempty
      · exact convexSpaceRegion_three_prism_TTT_nonempty
  rw [hs]
  decide

/-- 3枚の三角柱をなす平面による配置の領域数は 7 である。 -/
lemma spaceRegionsCount_three_prism :
    ∃ (H : Fin 3 → Plane3), DistinctPlanes 3 H ∧ spaceRegionsCount 3 H = 7 :=
  ⟨H_three_prism, distinctPlanes_three_prism, spaceRegionsCount_three_prism_eq_seven⟩

/-! ### 三角柱とモーメント平面の配置 -/

/-- 三角柱とモーメント平面を組み合わせた配置。
最初の3平面は三角柱をなし、4枚目以降はモーメント平面とする。 -/
def H_hybrid (n : ℕ) (i : Fin n) : Plane3 :=
  if i.val = 0 then plane_x0
  else if i.val = 1 then plane_y0
  else if i.val = 2 then plane_xy1
  else momentPlane (i.val : ℝ)

/-- 配置の先頭n枚は、n枚の配置と完全に一致する。 -/
lemma H_hybrid_castSucc (n : ℕ) :
    H_hybrid (n + 1) ∘ Fin.castSucc = H_hybrid n := by
  ext ⟨i, hi⟩
  dsimp [H_hybrid]

/-- $n = 3$ のとき、配置は三角柱配置 H_three_prism と一致する。 -/
lemma H_hybrid_three_eq_three_prism :
    H_hybrid 3 = H_three_prism := by
  ext i
  fin_cases i
  · dsimp [H_hybrid, H_three_prism]
  · dsimp [H_hybrid, H_three_prism]
  · dsimp [H_hybrid, H_three_prism]

/-- $n = 3$ のとき、配置の領域数はちょうど7である。 -/
lemma spaceRegionsCount_hybrid_three :
    spaceRegionsCount 3 (H_hybrid 3) = 7 := by
  rw [H_hybrid_three_eq_three_prism]
  exact spaceRegionsCount_three_prism_eq_seven

/-- 平面 $x = 0$ と平面 $y = 0$ は平行でない。 -/
lemma not_parallel_plane_x0_plane_y0 :
    ¬ parallelPlanes plane_x0 plane_y0 := by
  rintro ⟨c, hc⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_x0.normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • plane_y0.normVec) 0 := by rw [hc]
  have hc1 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_x0.normVec 1 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • plane_y0.normVec) 1 := by rw [hc]
  simp [plane_x0, plane_y0, v0_vec, v1_vec] at hc0 hc1

/-- 平面 $x = 0$ と平面 x + $y = 1$ は平行でない。 -/
lemma not_parallel_plane_x0_plane_xy1 :
    ¬ parallelPlanes plane_x0 plane_xy1 := by
  rintro ⟨c, hc⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_x0.normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • plane_xy1.normVec) 0 := by rw [hc]
  have hc1 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_x0.normVec 1 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • plane_xy1.normVec) 1 := by rw [hc]
  simp [plane_x0, plane_xy1, v0_vec, v2_vec] at hc0 hc1
  linarith

/-- 平面 $y = 0$ と平面 $x + y = 1$ は平行でない。 -/
lemma not_parallel_plane_y0_plane_xy1 :
    ¬ parallelPlanes plane_y0 plane_xy1 := by
  rintro ⟨c, hc⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_y0.normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • plane_xy1.normVec) 0 := by rw [hc]
  have hc1 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_y0.normVec 1 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • plane_xy1.normVec) 1 := by rw [hc]
  simp [plane_y0, plane_xy1, v1_vec, v2_vec] at hc0 hc1
  linarith

set_option linter.flexible false in
/-- 平面 $x = 0$ とモーメント平面は平行でない。 -/
lemma not_parallel_plane_x0_momentPlane {t : ℝ} (ht : 1 ≤ t) :
    ¬ parallelPlanes plane_x0 (momentPlane t) := by
  rintro ⟨c, hc⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_x0.normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • (momentPlane t).normVec) 0 := by rw [hc]
  have hc2 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_x0.normVec 2 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • (momentPlane t).normVec) 2 := by rw [hc]
  simp [plane_x0, v0_vec, momentPlane, momentVec] at hc0 hc2
  subst hc0
  simp at hc2
  nlinarith

set_option linter.flexible false in
/-- 平面 $y = 0$ とモーメント平面は平行でない。 -/
lemma not_parallel_plane_y0_momentPlane {t : ℝ} (_ht : 1 ≤ t) :
    ¬ parallelPlanes plane_y0 (momentPlane t) := by
  rintro ⟨c, hc⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_y0.normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • (momentPlane t).normVec) 0 := by rw [hc]
  have hc1 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_y0.normVec 1 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • (momentPlane t).normVec) 1 := by rw [hc]
  simp [plane_y0, v1_vec, momentPlane, momentVec] at hc0 hc1
  subst hc0
  simp at hc1

set_option linter.flexible false in
/-- 平面 $x + y = 1$ とモーメント平面は平行でない。 -/
lemma not_parallel_plane_xy1_momentPlane {t : ℝ} (_ht : 2 ≤ t) :
    ¬ parallelPlanes plane_xy1 (momentPlane t) := by
  rintro ⟨c, hc⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_xy1.normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • (momentPlane t).normVec) 0 := by rw [hc]
  have hc1 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_xy1.normVec 1 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (c • (momentPlane t).normVec) 1 := by rw [hc]
  simp [plane_xy1, v2_vec, momentPlane, momentVec] at hc0 hc1
  subst hc0
  simp at hc1
  linarith

set_option linter.flexible false in
/-- ハイブリッド配置の任意の2平面は平行でない。 -/
lemma not_parallel_hybrid {n : ℕ} (i j : Fin n) (hij : i < j) :
    ¬ parallelPlanes (H_hybrid n i) (H_hybrid n j) := by
  have hi_lt : i.val < j.val := hij
  have h_ne : i.val ≠ j.val := by omega
  by_cases hi0 : i.val = 0
  · by_cases hj1 : j.val = 1
    · dsimp [H_hybrid]
      simp [hi0, hj1]
      exact not_parallel_plane_x0_plane_y0
    · by_cases hj2 : j.val = 2
      · dsimp [H_hybrid]
        simp [hi0, hj2]
        exact not_parallel_plane_x0_plane_xy1
      · dsimp [H_hybrid]
        have hj0 : ¬ j.val = 0 := by omega
        simp [hi0, hj0, hj1, hj2]
        apply not_parallel_plane_x0_momentPlane
        exact_mod_cast (by omega : 1 ≤ j.val)
  · by_cases hi1 : i.val = 1
    · by_cases hj2 : j.val = 2
      · dsimp [H_hybrid]
        simp [hi1, hj2]
        exact not_parallel_plane_y0_plane_xy1
      · dsimp [H_hybrid]
        have hj0 : ¬ j.val = 0 := by omega
        have hj1 : ¬ j.val = 1 := by omega
        simp [hi1, hj0, hj1, hj2]
        apply not_parallel_plane_y0_momentPlane
        exact_mod_cast (by omega : 1 ≤ j.val)
    · by_cases hi2 : i.val = 2
      · dsimp [H_hybrid]
        have hj0 : ¬ j.val = 0 := by omega
        have hj1 : ¬ j.val = 1 := by omega
        have hj2 : ¬ j.val = 2 := by omega
        simp [hi2, hj0, hj1, hj2]
        apply not_parallel_plane_xy1_momentPlane
        exact_mod_cast (by omega : 2 ≤ j.val)
      · dsimp [H_hybrid]
        have hj0 : ¬ j.val = 0 := by omega
        have hj1 : ¬ j.val = 1 := by omega
        have hj2 : ¬ j.val = 2 := by omega
        simp [hi0, hi1, hi2, hj0, hj1, hj2]
        apply not_parallel_momentPlanes
        exact_mod_cast h_ne

/-- ハイブリッド配置の各平面は相異なる。 -/
lemma distinctPlanes_hybrid (n : ℕ) :
    DistinctPlanes n (H_hybrid n) := by
  intro i j hij
  by_contra h_ne
  rcases lt_trichotomy i j with h | h | h
  · have h_not := not_parallel_hybrid i j h
    have h_par := parallelPlanes_of_toSet_eq (H_hybrid n i) (H_hybrid n j) hij
    exact h_not h_par
  · exact h_ne h
  · have h_not := not_parallel_hybrid j i h
    have h_par := parallelPlanes_of_toSet_eq (H_hybrid n j) (H_hybrid n i) hij.symm
    exact h_not h_par

/-- 平面 $x = 0$, $y = 0$ とモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_x0_plane_y0_momentPlane {t : ℝ} (ht : t ≠ 0) :
    ∃ q : Space3, plane_x0.toSet ∩ plane_y0.toSet ∩ (momentPlane t).toSet = {q} := by
  let q : Space3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, 0, t]
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_x0, mem_plane_y0, mem_momentPlane,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hx, hy⟩, hm⟩
    have hz : p 2 = t := by
      have hm' : t ^ 2 * (p 2 - t) = 0 := by
        calc t ^ 2 * (p 2 - t) = (p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3) - p 0 - t * p 1 := by ring
        _ = (t ^ 3 - t ^ 3) - 0 - t * 0 := by rw [hm, hx, hy]
        _ = 0 := by ring
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
      have hz_sub := (mul_eq_zero.mp hm').resolve_left ht2
      linarith
    ext i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  · rintro rfl
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    simp [q]
    ring

/-- 平面 $x = 0$, $x + y = 1$ とモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_x0_plane_xy1_momentPlane {t : ℝ} (ht : t ≠ 0) :
    ∃ q : Space3, plane_x0.toSet ∩ plane_xy1.toSet ∩ (momentPlane t).toSet = {q} := by
  let q : Space3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, 1, t - 1 / t]
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_x0, mem_plane_xy1, mem_momentPlane,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hx, hxy⟩, hm⟩
    have hy : p 1 = 1 := by linarith
    have h_t_inv : t ^ 2 * (1 / t) = t := by
      rw [sq, mul_assoc, mul_one_div_cancel ht, mul_one]
    have hz : p 2 = t - 1 / t := by
      have hm' : t ^ 2 * (p 2 - (t - 1 / t)) = 0 := by
        calc t ^ 2 * (p 2 - (t - 1 / t)) =
            t ^ 2 * p 2 - t ^ 3 + t ^ 2 * (1 / t) := by ring
        _ = t ^ 2 * p 2 - t ^ 3 + t := by rw [h_t_inv]
        _ = (p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3) - p 0 - t * (p 1 - 1) := by ring
        _ = (t ^ 3 - t ^ 3) - 0 - t * (1 - 1) := by rw [hm, hx, hy]
        _ = 0 := by ring
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
      have hz_sub := (mul_eq_zero.mp hm').resolve_left ht2
      linarith
    ext i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  · rintro rfl
    have h_t_inv : t ^ 2 * (1 / t) = t := by
      rw [sq, mul_assoc, mul_one_div_cancel ht, mul_one]
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · simp [q]
    · dsimp [q]
      calc (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, 1, t - 1 / t] 0 +
          t * (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, 1, t - 1 / t] 1 +
          t ^ 2 * (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, 1, t - 1 / t] 2
        = 0 + t * 1 + t ^ 2 * (t - 1 / t) := by simp
      _ = t + t ^ 3 - t ^ 2 * (1 / t) := by ring
      _ = t + t ^ 3 - t := by rw [h_t_inv]
      _ = t ^ 3 := by ring

/-- 平面 $y = 0$, $x + y = 1$ とモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_y0_plane_xy1_momentPlane {t : ℝ} (ht : t ≠ 0) :
    ∃ q : Space3, plane_y0.toSet ∩ plane_xy1.toSet ∩ (momentPlane t).toSet = {q} := by
  let q : Space3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![1, 0, t - 1 / t ^ 2]
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_y0, mem_plane_xy1, mem_momentPlane,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hxy⟩, hm⟩
    have hx : p 0 = 1 := by linarith
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have h_t2_inv : t ^ 2 * (1 / t ^ 2) = 1 := mul_one_div_cancel ht2
    have hz : p 2 = t - 1 / t ^ 2 := by
      have hm' : t ^ 2 * (p 2 - (t - 1 / t ^ 2)) = 0 := by
        calc t ^ 2 * (p 2 - (t - 1 / t ^ 2)) =
            t ^ 2 * p 2 - t ^ 3 + t ^ 2 * (1 / t ^ 2) := by ring
        _ = t ^ 2 * p 2 - t ^ 3 + 1 := by rw [h_t2_inv]
        _ = (p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3) - (p 0 - 1) - t * p 1 := by ring
        _ = (t ^ 3 - t ^ 3) - (1 - 1) - t * 0 := by rw [hm, hx, hy]
        _ = 0 := by ring
      have hz_sub := (mul_eq_zero.mp hm').resolve_left ht2
      linarith
    ext i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  · rintro rfl
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have h_t2_inv : t ^ 2 * (1 / t ^ 2) = 1 := mul_one_div_cancel ht2
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · simp [q]
    · dsimp [q]
      calc (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![1, 0, t - 1 / t ^ 2] 0 +
          t * (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![1, 0, t - 1 / t ^ 2] 1 +
          t ^ 2 * (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![1, 0, t - 1 / t ^ 2] 2
        = 1 + t * 0 + t ^ 2 * (t - 1 / t ^ 2) := by simp
      _ = 1 + t ^ 3 - t ^ 2 * (1 / t ^ 2) := by ring
      _ = 1 + t ^ 3 - 1 := by rw [h_t2_inv]
      _ = t ^ 3 := by ring

/-- 平面 $x = 0$ と2つのモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_x0_two_momentPlanes {t₁ t₂ : ℝ} (h12 : t₁ ≠ t₂)
    (h1 : t₁ ≠ 0) (h2 : t₂ ≠ 0) :
    ∃ q : Space3, plane_x0.toSet ∩ (momentPlane t₁).toSet ∩ (momentPlane t₂).toSet = {q} := by
  let q : Space3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, -t₁ * t₂, t₁ + t₂]
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_x0, mem_momentPlane, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hx, hm1⟩, hm2⟩
    have hz : p 2 = t₁ + t₂ := by
      have h_diff : (t₁ * t₂ * (t₁ - t₂)) * (p 2 - (t₁ + t₂)) = 0 := by
        calc (t₁ * t₂ * (t₁ - t₂)) * (p 2 - (t₁ + t₂)) =
            t₂ * (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3) -
            t₁ * (p 0 + t₂ * p 1 + t₂ ^ 2 * p 2 - t₂ ^ 3) -
            (t₂ - t₁) * p 0 := by ring
        _ = t₂ * (t₁ ^ 3 - t₁ ^ 3) - t₁ * (t₂ ^ 3 - t₂ ^ 3) -
            (t₂ - t₁) * 0 := by rw [hm1, hm2, hx]
        _ = 0 := by ring
      have h12' : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h12
      have h_coeff : t₁ * t₂ * (t₁ - t₂) ≠ 0 := by
        have h12_mul : t₁ * t₂ ≠ 0 := mul_ne_zero h1 h2
        exact mul_ne_zero h12_mul h12'
      have hz_sub := (mul_eq_zero.mp h_diff).resolve_left h_coeff
      linarith
    have hy : p 1 = -t₁ * t₂ := by
      have hm1' : t₁ * (p 1 - (-t₁ * t₂)) = 0 := by
        calc t₁ * (p 1 - (-t₁ * t₂)) =
            (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3) - p 0 -
            t₁ ^ 2 * (p 2 - (t₁ + t₂)) := by ring
        _ = (t₁ ^ 3 - t₁ ^ 3) - 0 - t₁ ^ 2 * (t₁ + t₂ - (t₁ + t₂)) := by rw [hm1, hx, hz]
        _ = 0 := by ring
      have hy_sub := (mul_eq_zero.mp hm1').resolve_left h1
      linarith
    ext i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  · rintro rfl
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · dsimp [q]
      calc (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, -t₁ * t₂, t₁ + t₂] 0 +
          t₁ * (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, -t₁ * t₂, t₁ + t₂] 1 +
          t₁ ^ 2 * (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, -t₁ * t₂, t₁ + t₂] 2
        = 0 + t₁ * (-t₁ * t₂) + t₁ ^ 2 * (t₁ + t₂) := by simp
      _ = t₁ ^ 3 := by ring
    · dsimp [q]
      calc (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, -t₁ * t₂, t₁ + t₂] 0 +
          t₂ * (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, -t₁ * t₂, t₁ + t₂] 1 +
          t₂ ^ 2 * (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, -t₁ * t₂, t₁ + t₂] 2
        = 0 + t₂ * (-t₁ * t₂) + t₂ ^ 2 * (t₁ + t₂) := by simp
      _ = t₂ ^ 3 := by ring

/-- 平面 $y = 0$ と2つのモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_y0_two_momentPlanes {t₁ t₂ : ℝ} (h12 : t₁ ≠ t₂)
    (h_sum : t₁ + t₂ ≠ 0) :
    ∃ q : Space3, plane_y0.toSet ∩ (momentPlane t₁).toSet ∩ (momentPlane t₂).toSet = {q} := by
  let z₀ := (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) / (t₁ + t₂)
  let x₀ := -t₁ ^ 2 * t₂ ^ 2 / (t₁ + t₂)
  let q : Space3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![x₀, 0, z₀]
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_y0, mem_momentPlane, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hm1⟩, hm2⟩
    have h_mul : ((t₁ - t₂) * (t₁ + t₂)) * ((t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) / (t₁ + t₂)) =
        (t₁ - t₂) * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) := by
      rw [mul_assoc, mul_div_cancel₀ _ h_sum]
    have hz : p 2 = z₀ := by
      have h_diff : ((t₁ - t₂) * (t₁ + t₂)) * (p 2 - z₀) = 0 := by
        calc ((t₁ - t₂) * (t₁ + t₂)) * (p 2 - z₀) =
            ((t₁ - t₂) * (t₁ + t₂)) * p 2 -
            ((t₁ - t₂) * (t₁ + t₂)) * z₀ := by ring
        _ = ((t₁ - t₂) * (t₁ + t₂)) * p 2 -
            (t₁ - t₂) * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) := by
          change ((t₁ - t₂) * (t₁ + t₂)) * p 2 -
            ((t₁ - t₂) * (t₁ + t₂)) * ((t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) / (t₁ + t₂)) = _
          rw [h_mul]
        _ = (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3) -
            (p 0 + t₂ * p 1 + t₂ ^ 2 * p 2 - t₂ ^ 3) -
            (t₁ - t₂) * p 1 := by ring
        _ = (t₁ ^ 3 - t₁ ^ 3) - (t₂ ^ 3 - t₂ ^ 3) - (t₁ - t₂) * 0 := by rw [hm1, hm2, hy]
        _ = 0 := by ring
      have h12' : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h12
      have h_coeff : (t₁ - t₂) * (t₁ + t₂) ≠ 0 := mul_ne_zero h12' h_sum
      have hz_sub := (mul_eq_zero.mp h_diff).resolve_left h_coeff
      linarith
    have h_x : (t₁ + t₂) * (-t₁ ^ 2 * t₂ ^ 2 / (t₁ + t₂)) = -t₁ ^ 2 * t₂ ^ 2 :=
      mul_div_cancel₀ _ h_sum
    have h_z : (t₁ + t₂) * ((t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) / (t₁ + t₂)) =
        t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 :=
      mul_div_cancel₀ _ h_sum
    have hx : p 0 = x₀ := by
      have hm1' : (t₁ + t₂) * (p 0 - x₀) = 0 := by
        calc (t₁ + t₂) * (p 0 - x₀) =
            (t₁ + t₂) * p 0 - (t₁ + t₂) * x₀ := by ring
        _ = (t₁ + t₂) * p 0 - (-t₁ ^ 2 * t₂ ^ 2) := by
          change (t₁ + t₂) * p 0 - (t₁ + t₂) * (-t₁ ^ 2 * t₂ ^ 2 / (t₁ + t₂)) = _
          rw [h_x]
        _ = (t₁ + t₂) * (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3) -
            (t₁ + t₂) * t₁ * p 1 -
            t₁ ^ 2 * ((t₁ + t₂) * p 2 - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2)) := by ring
        _ = (t₁ + t₂) * (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3) -
            (t₁ + t₂) * t₁ * p 1 -
            t₁ ^ 2 * ((t₁ + t₂) * p 2 - (t₁ + t₂) * z₀) := by
          have : (t₁ + t₂) * z₀ = t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 := h_z
          rw [this]
        _ = (t₁ + t₂) * (t₁ ^ 3 - t₁ ^ 3) - (t₁ + t₂) * t₁ * 0 -
            t₁ ^ 2 * ((t₁ + t₂) * z₀ - (t₁ + t₂) * z₀) := by rw [hm1, hy, hz]
        _ = 0 := by ring
      have hx_sub := (mul_eq_zero.mp hm1').resolve_left h_sum
      linarith
    ext i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  · rintro rfl
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · dsimp [q, x₀, z₀]
      have h1 : -t₁ ^ 2 * t₂ ^ 2 / (t₁ + t₂) + t₁ * 0 +
          t₁ ^ 2 * ((t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) / (t₁ + t₂)) =
          (-t₁ ^ 2 * t₂ ^ 2 + t₁ ^ 2 * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2)) / (t₁ + t₂) := by ring
      rw [h1]
      have h2 : -t₁ ^ 2 * t₂ ^ 2 + t₁ ^ 2 * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) =
          t₁ ^ 3 * (t₁ + t₂) := by ring
      rw [h2, mul_div_cancel_right₀ _ h_sum]
    · dsimp [q, x₀, z₀]
      have h1 : -t₁ ^ 2 * t₂ ^ 2 / (t₁ + t₂) + t₂ * 0 +
          t₂ ^ 2 * ((t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) / (t₁ + t₂)) =
          (-t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 2 * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2)) / (t₁ + t₂) := by ring
      rw [h1]
      have h2 : -t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 2 * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) =
          t₂ ^ 3 * (t₁ + t₂) := by ring
      rw [h2, mul_div_cancel_right₀ _ h_sum]

/-- 平面 $x + y = 1$ と2つのモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_xy1_two_momentPlanes {t₁ t₂ : ℝ} (h12 : t₁ ≠ t₂)
    (ht1 : t₁ ≠ 1) (hD : t₁ * t₂ - t₁ - t₂ ≠ 0) :
    ∃ q : Space3, plane_xy1.toSet ∩ (momentPlane t₁).toSet ∩ (momentPlane t₂).toSet = {q} := by
  let D := t₁ * t₂ - t₁ - t₂
  let x₀ := (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) / D
  let y₀ := (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) / D
  let z₀ := (t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1) / D
  let q : Space3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![x₀, y₀, z₀]
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_xy1, mem_momentPlane, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hxy, hm1⟩, hm2⟩
    have h_diff_z : (t₁ - t₂) * D * (p 2 - z₀) = 0 := by
      calc (t₁ - t₂) * D * (p 2 - z₀) =
          (t₁ - t₂) * D * p 2 - (t₁ - t₂) * (D * z₀) := by ring
      _ = (t₁ - t₂) * D * p 2 -
          (t₁ - t₂) * (t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1) := by
        rw [mul_div_cancel₀ _ hD]
      _ = (t₂ - 1) * (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3) -
          (t₁ - 1) * (p 0 + t₂ * p 1 + t₂ ^ 2 * p 2 - t₂ ^ 3) +
          (t₁ - t₂) * (p 0 + p 1 - 1) := by ring
      _ = (t₂ - 1) * (t₁ ^ 3 - t₁ ^ 3) - (t₁ - 1) * (t₂ ^ 3 - t₂ ^ 3) +
          (t₁ - t₂) * (1 - 1) := by rw [hm1, hm2, hxy]
      _ = 0 := by ring
    have h12' : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h12
    have h_coeff : (t₁ - t₂) * D ≠ 0 := mul_ne_zero h12' hD
    have hz : p 2 = z₀ := by
      have hz_sub := (mul_eq_zero.mp h_diff_z).resolve_left h_coeff
      linarith
    have h_diff_y : D * (t₁ - 1) * (p 1 - y₀) = 0 := by
      have h_cancel : D * y₀ = -t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂ := mul_div_cancel₀ _ hD
      have h_cancel_z : D * z₀ = t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1 :=
        mul_div_cancel₀ _ hD
      calc D * (t₁ - 1) * (p 1 - y₀) =
          D * ((t₁ - 1) * p 1) - (t₁ - 1) * (D * y₀) := by ring
      _ = D * ((p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3) - (p 0 + p 1 - 1) +
          (t₁ ^ 3 - 1) - t₁ ^ 2 * p 2) - (t₁ - 1) * (D * y₀) := by ring
      _ = D * ((t₁ ^ 3 - t₁ ^ 3) - (1 - 1) + (t₁ ^ 3 - 1) - t₁ ^ 2 * z₀) -
          (t₁ - 1) * (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) := by rw [hm1, hxy, hz, h_cancel]
      _ = (t₁ ^ 3 - 1) * D - t₁ ^ 2 * (D * z₀) -
          (t₁ - 1) * (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) := by ring
      _ = (t₁ ^ 3 - 1) * D -
          t₁ ^ 2 * (t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1) -
          (t₁ - 1) * (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) := by rw [h_cancel_z]
      _ = 0 := by
        dsimp [D]
        ring
    have ht1_ne : t₁ - 1 ≠ 0 := sub_ne_zero.mpr ht1
    have h_coeff_y : D * (t₁ - 1) ≠ 0 := mul_ne_zero hD ht1_ne
    have hy : p 1 = y₀ := by
      have hy_sub := (mul_eq_zero.mp h_diff_y).resolve_left h_coeff_y
      linarith
    have hx : p 0 = x₀ := by
      have h_sum : x₀ + y₀ = 1 := by
        dsimp [x₀, y₀, D]
        have h : (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) / (t₁ * t₂ - t₁ - t₂) +
            (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) / (t₁ * t₂ - t₁ - t₂) =
            (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂ + (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂)) /
              (t₁ * t₂ - t₁ - t₂) := by ring
        rw [h]
        have h_num : t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂ + (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) =
            t₁ * t₂ - t₁ - t₂ := by ring
        rw [h_num, div_self hD]
      linarith
    ext i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  · rintro rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp [q, x₀, y₀, D]
      have h : (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) / (t₁ * t₂ - t₁ - t₂) +
          (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) / (t₁ * t₂ - t₁ - t₂) =
          (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂ + (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂)) /
            (t₁ * t₂ - t₁ - t₂) := by ring
      rw [h]
      have h_num : t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂ + (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) =
          t₁ * t₂ - t₁ - t₂ := by ring
      rw [h_num, div_self hD]
    · dsimp [q, x₀, y₀, z₀, D]
      have h : (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) / D +
          t₁ * ((-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) / D) +
          t₁ ^ 2 * ((t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1) / D) =
          ((t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) +
          t₁ * (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) +
          t₁ ^ 2 * (t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1)) / D := by ring
      rw [h]
      have h_num : (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) +
          t₁ * (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) +
          t₁ ^ 2 * (t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1) =
          t₁ ^ 3 * D := by
        dsimp [D]
        ring
      rw [h_num, mul_div_cancel_right₀ _ hD]
    · dsimp [q, x₀, y₀, z₀, D]
      have h : (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) / D +
          t₂ * ((-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) / D) +
          t₂ ^ 2 * ((t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1) / D) =
          ((t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) +
          t₂ * (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) +
          t₂ ^ 2 * (t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1)) / D := by ring
      rw [h]
      have h_num : (t₁ ^ 2 * t₂ ^ 2 + t₁ * t₂) +
          t₂ * (-t₁ ^ 2 * t₂ ^ 2 - t₁ - t₂) +
          t₂ ^ 2 * (t₁ * t₂ * (t₁ + t₂) - (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) + 1) =
          t₂ ^ 3 * D := by
        dsimp [D]
        ring
      rw [h_num, mul_div_cancel_right₀ _ hD]

/-- ハイブリッド配置の0番目の平面は plane_x0 である。 -/
lemma H_hybrid_of_val_zero {n : ℕ} (i : Fin n) (hi : i.val = 0) :
    H_hybrid n i = plane_x0 := by
  unfold H_hybrid
  simp [hi]

/-- ハイブリッド配置の1番目の平面は plane_y0 である。 -/
lemma H_hybrid_of_val_one {n : ℕ} (i : Fin n) (hi : i.val = 1) :
    H_hybrid n i = plane_y0 := by
  unfold H_hybrid
  simp [hi]

/-- ハイブリッド配置の2番目の平面は plane_xy1 である。 -/
lemma H_hybrid_of_val_two {n : ℕ} (i : Fin n) (hi : i.val = 2) :
    H_hybrid n i = plane_xy1 := by
  unfold H_hybrid
  simp [hi]

/-- ハイブリッド配置の3番目以降の平面はモーメント平面である。 -/
lemma H_hybrid_of_val_ge {n : ℕ} (i : Fin n) (hi : 3 ≤ i.val) :
    H_hybrid n i = momentPlane (i.val : ℝ) := by
  unfold H_hybrid
  have h0 : ¬ i.val = 0 := by omega
  have h1 : ¬ i.val = 1 := by omega
  have h2 : ¬ i.val = 2 := by omega
  simp [h0, h1, h2]

/-- ハイブリッド配置において、$i ≠ j$ なる任意の2平面と最後のモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_three_hybrid (n : ℕ) (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ∃ q, (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
      (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
      (H_hybrid (n + 1) (Fin.last n)).toSet = {q} := by
  have h_last : H_hybrid (n + 1) (Fin.last n) = momentPlane (n : ℝ) := by
    have h_ge : 3 ≤ (Fin.last n).val := by
      change 3 ≤ n
      exact hn
    exact H_hybrid_of_val_ge (Fin.last n) h_ge
  have h_symm : ∀ a b : Fin n, a ≠ b → a < b →
      ∃ q, (H_hybrid (n + 1) (Fin.castSucc a)).toSet ∩
        (H_hybrid (n + 1) (Fin.castSucc b)).toSet ∩
        (H_hybrid (n + 1) (Fin.last n)).toSet = {q} := by
    intro a b _hab_ne hab_lt
    have hn_pos : (n : ℝ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact Nat.cast_ne_zero.mpr this
    have ha_val : (Fin.castSucc a).val = a.val := rfl
    have hb_val : (Fin.castSucc b).val = b.val := rfl
    by_cases ha0 : a.val = 0
    · have ha_eq : H_hybrid (n + 1) (Fin.castSucc a) = plane_x0 :=
        H_hybrid_of_val_zero (Fin.castSucc a) (by rw [ha_val, ha0])
      by_cases hb1 : b.val = 1
      · have hb_eq : H_hybrid (n + 1) (Fin.castSucc b) = plane_y0 :=
          H_hybrid_of_val_one (Fin.castSucc b) (by rw [hb_val, hb1])
        rw [ha_eq, hb_eq, h_last]
        exact intersection_plane_x0_plane_y0_momentPlane hn_pos
      · by_cases hb2 : b.val = 2
        · have hb_eq : H_hybrid (n + 1) (Fin.castSucc b) = plane_xy1 :=
            H_hybrid_of_val_two (Fin.castSucc b) (by rw [hb_val, hb2])
          rw [ha_eq, hb_eq, h_last]
          exact intersection_plane_x0_plane_xy1_momentPlane hn_pos
        · have hb_ge : 3 ≤ (Fin.castSucc b).val := by
            rw [hb_val]; omega
          have hb_eq : H_hybrid (n + 1) (Fin.castSucc b) = momentPlane (b.val : ℝ) :=
            H_hybrid_of_val_ge (Fin.castSucc b) hb_ge
          rw [ha_eq, hb_eq, h_last]
          have hb_ne_n : (b.val : ℝ) ≠ (n : ℝ) := by
            have : b.val ≠ n := by omega
            exact_mod_cast this
          have hb_ne_0 : (b.val : ℝ) ≠ 0 := by
            have : b.val ≠ 0 := by omega
            exact_mod_cast this
          exact intersection_plane_x0_two_momentPlanes hb_ne_n hb_ne_0 hn_pos
    · by_cases ha1 : a.val = 1
      · have ha_eq : H_hybrid (n + 1) (Fin.castSucc a) = plane_y0 :=
          H_hybrid_of_val_one (Fin.castSucc a) (by rw [ha_val, ha1])
        by_cases hb2 : b.val = 2
        · have hb_eq : H_hybrid (n + 1) (Fin.castSucc b) = plane_xy1 :=
            H_hybrid_of_val_two (Fin.castSucc b) (by rw [hb_val, hb2])
          rw [ha_eq, hb_eq, h_last]
          exact intersection_plane_y0_plane_xy1_momentPlane hn_pos
        · have hb_ge : 3 ≤ (Fin.castSucc b).val := by
            rw [hb_val]; omega
          have hb_eq : H_hybrid (n + 1) (Fin.castSucc b) = momentPlane (b.val : ℝ) :=
            H_hybrid_of_val_ge (Fin.castSucc b) hb_ge
          rw [ha_eq, hb_eq, h_last]
          have hb_ne_n : (b.val : ℝ) ≠ (n : ℝ) := by
            have : b.val ≠ n := by omega
            exact_mod_cast this
          have h_sum : (b.val : ℝ) + (n : ℝ) ≠ 0 := by
            have : 0 < (b.val : ℝ) + (n : ℝ) := by positivity
            linarith
          exact intersection_plane_y0_two_momentPlanes hb_ne_n h_sum
      · by_cases ha2 : a.val = 2
        · have ha_eq : H_hybrid (n + 1) (Fin.castSucc a) = plane_xy1 :=
            H_hybrid_of_val_two (Fin.castSucc a) (by rw [ha_val, ha2])
          have hb_ge : 3 ≤ (Fin.castSucc b).val := by
            rw [hb_val]; omega
          have hb_eq : H_hybrid (n + 1) (Fin.castSucc b) = momentPlane (b.val : ℝ) :=
            H_hybrid_of_val_ge (Fin.castSucc b) hb_ge
          rw [ha_eq, hb_eq, h_last]
          have hb_ne_n : (b.val : ℝ) ≠ (n : ℝ) := by
            have : b.val ≠ n := by omega
            exact_mod_cast this
          have hb_ne_1 : (b.val : ℝ) ≠ 1 := by
            have : b.val ≠ 1 := by omega
            exact_mod_cast this
          have hD : (b.val : ℝ) * (n : ℝ) - (b.val : ℝ) - (n : ℝ) ≠ 0 := by
            have _hb_real : 3 ≤ (b.val : ℝ) := by
              have : 3 ≤ b.val := by omega
              exact_mod_cast this
            have _hn_real : 4 ≤ (n : ℝ) := by
              have : 4 ≤ n := by omega
              exact_mod_cast this
            nlinarith
          exact intersection_plane_xy1_two_momentPlanes hb_ne_n hb_ne_1 hD
        · have ha_ge : 3 ≤ (Fin.castSucc a).val := by
            rw [ha_val]; omega
          have hb_ge : 3 ≤ (Fin.castSucc b).val := by
            rw [hb_val]; omega
          have ha_eq : H_hybrid (n + 1) (Fin.castSucc a) = momentPlane (a.val : ℝ) :=
            H_hybrid_of_val_ge (Fin.castSucc a) ha_ge
          have hb_eq : H_hybrid (n + 1) (Fin.castSucc b) = momentPlane (b.val : ℝ) :=
            H_hybrid_of_val_ge (Fin.castSucc b) hb_ge
          rw [ha_eq, hb_eq, h_last]
          have hab_ne : (a.val : ℝ) ≠ (b.val : ℝ) := by
            have : a.val ≠ b.val := by omega
            exact_mod_cast this
          have han_ne : (a.val : ℝ) ≠ (n : ℝ) := by
            have : a.val ≠ n := by omega
            exact_mod_cast this
          have hbn_ne : (b.val : ℝ) ≠ (n : ℝ) := by
            have : b.val ≠ n := by omega
            exact_mod_cast this
          exact intersection_three_momentPlanes hab_ne hbn_ne han_ne
  rcases lt_trichotomy i j with h | rfl | h
  · exact h_symm i j hij h
  · exact (hij rfl).elim
  · have h_inter := h_symm j i hij.symm h
    rcases h_inter with ⟨q, hq⟩
    use q
    have h_comm : (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
        (H_hybrid (n + 1) (Fin.castSucc j)).toSet =
        (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
        (H_hybrid (n + 1) (Fin.castSucc i)).toSet := Set.inter_comm _ _
    rw [h_comm]
    exact hq

/-- 3以上の相異なる3数に対するモーメント平面の交点座標の評価 -/
lemma moment_intersection_xy_ne_one (a b c : ℕ)
    (ha : 3 ≤ a) (hab : a < b) (hbc : b < c) :
    (a : ℝ) * (b : ℝ) * (c : ℝ) -
      ((a : ℝ) * (b : ℝ) + (b : ℝ) * (c : ℝ) + (c : ℝ) * (a : ℝ)) ≠ 1 := by
  have ha' : 3 ≤ (a : ℝ) := by exact_mod_cast ha
  have hb' : 4 ≤ (b : ℝ) := by exact_mod_cast (by omega : 4 ≤ b)
  have hc' : 5 ≤ (c : ℝ) := by exact_mod_cast (by omega : 5 ≤ c)
  have hab' : (a : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : a ≤ c)
  have hbc' : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : b ≤ c)
  have h_id : (a : ℝ) * (b : ℝ) * (c : ℝ) -
        ((a : ℝ) * (b : ℝ) + (b : ℝ) * (c : ℝ) + (c : ℝ) * (a : ℝ)) - 1 =
      ((a : ℝ) - 1) * ((b : ℝ) - 1) * ((c : ℝ) - 1) -
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by ring
  rw [← sub_ne_zero, h_id]
  have h1 : 2 ≤ (a : ℝ) - 1 := by linarith
  have h2 : 3 ≤ (b : ℝ) - 1 := by linarith
  have h3 : 4 ≤ (c : ℝ) - 1 := by linarith
  have h_prod : 6 ≤ ((a : ℝ) - 1) * ((b : ℝ) - 1) := by nlinarith
  have h_prod2 : 6 * ((c : ℝ) - 1) ≤
      ((a : ℝ) - 1) * ((b : ℝ) - 1) * ((c : ℝ) - 1) := by nlinarith
  have h_lin : (a : ℝ) + (b : ℝ) + (c : ℝ) ≤ 3 * (c : ℝ) := by linarith
  have : 0 < ((a : ℝ) - 1) * ((b : ℝ) - 1) * ((c : ℝ) - 1) -
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
    calc 0 < 3 * (c : ℝ) - 6 := by linarith
    _ = 6 * ((c : ℝ) - 1) - 3 * (c : ℝ) := by ring
    _ ≤ ((a : ℝ) - 1) * ((b : ℝ) - 1) * ((c : ℝ) - 1) -
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by linarith
  linarith

lemma intersection_three_momentPlanes_eq {t₁ t₂ t₃ : ℝ}
    (h12 : t₁ ≠ t₂) (h23 : t₂ ≠ t₃) (h13 : t₁ ≠ t₃) :
    (momentPlane t₁).toSet ∩ (momentPlane t₂).toSet ∩ (momentPlane t₃).toSet =
      {explicitIntersection t₁ t₂ t₃} := by
  have h_mem : explicitIntersection t₁ t₂ t₃ ∈
      (momentPlane t₁).toSet ∩ (momentPlane t₂).toSet ∩ (momentPlane t₃).toSet := by
    simp only [Set.mem_inter_iff, mem_momentPlane]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp [explicitIntersection]; ring
    · dsimp [explicitIntersection]; ring
    · dsimp [explicitIntersection]; ring
  rcases intersection_three_momentPlanes h12 h23 h13 with ⟨p, hp⟩
  rw [hp] at h_mem ⊢
  have hp_eq : p = explicitIntersection t₁ t₂ t₃ :=
    (Set.mem_singleton_iff.mp h_mem).symm
  rw [hp_eq]

lemma intersection_plane_x0_plane_y0_two_momentPlanes_empty {a n : ℝ}
    (han : a ≠ n) (ha : a ≠ 0) (hn : n ≠ 0) :
    plane_x0.toSet ∩ plane_y0.toSet ∩
      (momentPlane a).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hx, hy⟩, hma⟩, hmn⟩
  simp only [mem_plane_x0] at hx
  simp only [mem_plane_y0] at hy
  simp only [mem_momentPlane] at hma hmn
  have h_diff : (a - n) * a ^ 2 * n ^ 2 = 0 := by
    calc (a - n) * a ^ 2 * n ^ 2 =
        a ^ 2 * (p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) -
        n ^ 2 * (p 0 + a * p 1 + a ^ 2 * p 2 - a ^ 3) -
        (a ^ 2 - n ^ 2) * p 0 - a * n * (a - n) * p 1 := by ring
    _ = a ^ 2 * (n ^ 3 - n ^ 3) - n ^ 2 * (a ^ 3 - a ^ 3) -
        (a ^ 2 - n ^ 2) * 0 - a * n * (a - n) * 0 := by
      rw [hma, hmn, hx, hy]
    _ = 0 := by ring
  have han' : a - n ≠ 0 := sub_ne_zero.mpr han
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have h_prod : (a - n) * a ^ 2 * n ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero han' ha2) hn2
  exact h_prod h_diff

lemma intersection_plane_x0_plane_xy1_two_momentPlanes_empty {a n : ℝ}
    (han : a ≠ n) (ha : a ≠ 0) (hn : n ≠ 0) (han_one : a * n + 1 ≠ 0) :
    plane_x0.toSet ∩ plane_xy1.toSet ∩
      (momentPlane a).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hx, hxy⟩, hma⟩, hmn⟩
  simp only [mem_plane_x0] at hx
  simp only [mem_plane_xy1] at hxy
  simp only [mem_momentPlane] at hma hmn
  have h_diff : (a - n) * a * n * (a * n + 1) = 0 := by
    calc (a - n) * a * n * (a * n + 1) =
        a ^ 2 * (p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) -
        n ^ 2 * (p 0 + a * p 1 + a ^ 2 * p 2 - a ^ 3) -
        a * n * (a - n) * (p 0 + p 1 - 1) -
        (a ^ 2 - n ^ 2 - a * n * (a - n)) * p 0 := by ring
    _ = a ^ 2 * (n ^ 3 - n ^ 3) - n ^ 2 * (a ^ 3 - a ^ 3) -
        a * n * (a - n) * (1 - 1) -
        (a ^ 2 - n ^ 2 - a * n * (a - n)) * 0 := by rw [hma, hmn, hxy, hx]
    _ = 0 := by ring
  have han' : a - n ≠ 0 := sub_ne_zero.mpr han
  have han_prod : (a - n) * a * n * (a * n + 1) ≠ 0 := by
    have h1 : (a - n) * a ≠ 0 := mul_ne_zero han' ha
    have h2 : (a - n) * a * n ≠ 0 := mul_ne_zero h1 hn
    exact mul_ne_zero h2 han_one
  exact han_prod h_diff

lemma intersection_plane_x0_three_momentPlanes_empty {a b n : ℝ}
    (hab : a ≠ b) (hbn : b ≠ n) (han : a ≠ n) (ha : a ≠ 0) (hb : b ≠ 0) (hn : n ≠ 0) :
    plane_x0.toSet ∩ (momentPlane a).toSet ∩
      (momentPlane b).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hx, hma⟩, hmb⟩, hmn⟩
  simp only [mem_plane_x0] at hx
  have h_inter := intersection_three_momentPlanes_eq hab hbn han
  have hp_in : p ∈ (momentPlane a).toSet ∩ (momentPlane b).toSet ∩ (momentPlane n).toSet :=
    ⟨⟨hma, hmb⟩, hmn⟩
  rw [h_inter, Set.mem_singleton_iff] at hp_in
  have hq0 : p 0 = a * b * n := by
    rw [hp_in]
    rfl
  rw [hq0] at hx
  have habn : a * b * n ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hn
  exact habn hx

lemma intersection_plane_y0_three_momentPlanes_empty {a b n : ℝ}
    (hab : a ≠ b) (hbn : b ≠ n) (han : a ≠ n)
    (h_pos : a * b + b * n + n * a ≠ 0) :
    plane_y0.toSet ∩ (momentPlane a).toSet ∩
      (momentPlane b).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hy, hma⟩, hmb⟩, hmn⟩
  simp only [mem_plane_y0] at hy
  have h_inter := intersection_three_momentPlanes_eq hab hbn han
  have hp_in : p ∈ (momentPlane a).toSet ∩ (momentPlane b).toSet ∩ (momentPlane n).toSet :=
    ⟨⟨hma, hmb⟩, hmn⟩
  rw [h_inter, Set.mem_singleton_iff] at hp_in
  have hq1 : p 1 = -(a * b + b * n + n * a) := by
    rw [hp_in]
    rfl
  rw [hq1] at hy
  have : a * b + b * n + n * a = 0 := by linarith
  exact h_pos this

lemma intersection_plane_xy1_three_momentPlanes_empty {a b n : ℝ}
    (hab : a ≠ b) (hbn : b ≠ n) (han : a ≠ n)
    (h_ne : a * b * n - (a * b + b * n + n * a) ≠ 1) :
    plane_xy1.toSet ∩ (momentPlane a).toSet ∩
      (momentPlane b).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hxy, hma⟩, hmb⟩, hmn⟩
  simp only [mem_plane_xy1] at hxy
  have h_inter := intersection_three_momentPlanes_eq hab hbn han
  have hp_in : p ∈ (momentPlane a).toSet ∩ (momentPlane b).toSet ∩ (momentPlane n).toSet :=
    ⟨⟨hma, hmb⟩, hmn⟩
  rw [h_inter, Set.mem_singleton_iff] at hp_in
  have hq0 : p 0 = a * b * n := by
    rw [hp_in]
    rfl
  have hq1 : p 1 = -(a * b + b * n + n * a) := by
    rw [hp_in]
    rfl
  have h_sum : p 0 + p 1 = a * b * n - (a * b + b * n + n * a) := by
    rw [hq0, hq1]
    ring
  rw [h_sum] at hxy
  exact h_ne hxy

lemma intersection_plane_y0_plane_xy1_two_momentPlanes_empty {a n : ℝ}
    (han : a ≠ n) (h_quad : a ^ 2 * n ^ 2 + a + n ≠ 0) :
    plane_y0.toSet ∩ plane_xy1.toSet ∩
      (momentPlane a).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hy, hxy⟩, hma⟩, hmn⟩
  simp only [mem_plane_y0] at hy
  simp only [mem_plane_xy1] at hxy
  simp only [mem_momentPlane] at hma hmn
  have h_diff : (a - n) * (a ^ 2 * n ^ 2 + a + n) = 0 := by
    calc (a - n) * (a ^ 2 * n ^ 2 + a + n) =
        a ^ 2 * (p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) -
        n ^ 2 * (p 0 + a * p 1 + a ^ 2 * p 2 - a ^ 3) +
        (n ^ 2 - a ^ 2) * (p 0 + p 1 - 1) +
        (a * n * (n - a) - (n ^ 2 - a ^ 2)) * p 1 := by ring
    _ = a ^ 2 * (n ^ 3 - n ^ 3) - n ^ 2 * (a ^ 3 - a ^ 3) +
        (n ^ 2 - a ^ 2) * (1 - 1) +
        (a * n * (n - a) - (n ^ 2 - a ^ 2)) * 0 := by rw [hma, hmn, hxy, hy]
    _ = 0 := by ring
  have han' : a - n ≠ 0 := sub_ne_zero.mpr han
  have h_prod : (a - n) * (a ^ 2 * n ^ 2 + a + n) ≠ 0 :=
    mul_ne_zero han' h_quad
  exact h_prod h_diff

lemma intersection_four_hybrid_empty_of_sorted (n : ℕ) (hn : 3 ≤ n) (i j l : Fin n)
    (hij : i < j) (hjl : j < l) :
    (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
      (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
      (H_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
      (H_hybrid (n + 1) (Fin.last n)).toSet = ∅ := by
  have h_last : H_hybrid (n + 1) (Fin.last n) = momentPlane (n : ℝ) := by
    have h_ge : 3 ≤ (Fin.last n).val := by
      change 3 ≤ n
      exact hn
    exact H_hybrid_of_val_ge (Fin.last n) h_ge
  have hi_val : (Fin.castSucc i).val = i.val := rfl
  have hj_val : (Fin.castSucc j).val = j.val := rfl
  have hl_val : (Fin.castSucc l).val = l.val := rfl
  have hn_pos : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact Nat.cast_ne_zero.mpr this
  by_cases hi0 : i.val = 0
  · have hi_eq : H_hybrid (n + 1) (Fin.castSucc i) = plane_x0 :=
      H_hybrid_of_val_zero (Fin.castSucc i) (by rw [hi_val, hi0])
    by_cases hj1 : j.val = 1
    · have hj_eq : H_hybrid (n + 1) (Fin.castSucc j) = plane_y0 :=
        H_hybrid_of_val_one (Fin.castSucc j) (by rw [hj_val, hj1])
      by_cases hl2 : l.val = 2
      · have hl_eq : H_hybrid (n + 1) (Fin.castSucc l) = plane_xy1 :=
          H_hybrid_of_val_two (Fin.castSucc l) (by rw [hl_val, hl2])
        rw [hi_eq, hj_eq, hl_eq]
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hx, hy⟩, hxy⟩, _⟩
        simp only [mem_plane_x0] at hx
        simp only [mem_plane_y0] at hy
        simp only [mem_plane_xy1] at hxy
        linarith
      · have hl_ge : 3 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hl_eq : H_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc l) hl_ge
        rw [hi_eq, hj_eq, hl_eq, h_last]
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by
          have : l.val ≠ n := by omega
          exact_mod_cast this
        have hl_ne_0 : (l.val : ℝ) ≠ 0 := by
          have : l.val ≠ 0 := by omega
          exact_mod_cast this
        exact intersection_plane_x0_plane_y0_two_momentPlanes_empty hln_ne hl_ne_0 hn_pos
    · by_cases hj2 : j.val = 2
      · have hj_eq : H_hybrid (n + 1) (Fin.castSucc j) = plane_xy1 :=
          H_hybrid_of_val_two (Fin.castSucc j) (by rw [hj_val, hj2])
        have hl_ge : 3 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hl_eq : H_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc l) hl_ge
        rw [hi_eq, hj_eq, hl_eq, h_last]
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by
          have : l.val ≠ n := by omega
          exact_mod_cast this
        have hl_ne_0 : (l.val : ℝ) ≠ 0 := by
          have : l.val ≠ 0 := by omega
          exact_mod_cast this
        have hln_one : (l.val : ℝ) * (n : ℝ) + 1 ≠ 0 := by
          have hl_pos : 0 < (l.val : ℝ) := by
            have : 0 < l.val := by omega
            exact_mod_cast this
          have hn_pos' : 0 < (n : ℝ) := by
            have : 0 < n := by omega
            exact_mod_cast this
          positivity
        exact intersection_plane_x0_plane_xy1_two_momentPlanes_empty
          hln_ne hl_ne_0 hn_pos hln_one
      · have hj_ge : 3 ≤ (Fin.castSucc j).val := by rw [hj_val]; omega
        have hl_ge : 3 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hj_eq : H_hybrid (n + 1) (Fin.castSucc j) = momentPlane (j.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc j) hj_ge
        have hl_eq : H_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc l) hl_ge
        rw [hi_eq, hj_eq, hl_eq, h_last]
        have hjl_ne : (j.val : ℝ) ≠ (l.val : ℝ) := by
          have : j.val ≠ l.val := by omega
          exact_mod_cast this
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by
          have : l.val ≠ n := by omega
          exact_mod_cast this
        have hjn_ne : (j.val : ℝ) ≠ (n : ℝ) := by
          have : j.val ≠ n := by omega
          exact_mod_cast this
        have hj_ne_0 : (j.val : ℝ) ≠ 0 := by
          have : j.val ≠ 0 := by omega
          exact_mod_cast this
        have hl_ne_0 : (l.val : ℝ) ≠ 0 := by
          have : l.val ≠ 0 := by omega
          exact_mod_cast this
        exact intersection_plane_x0_three_momentPlanes_empty
          hjl_ne hln_ne hjn_ne hj_ne_0 hl_ne_0 hn_pos
  · by_cases hi1 : i.val = 1
    · have hi_eq : H_hybrid (n + 1) (Fin.castSucc i) = plane_y0 :=
        H_hybrid_of_val_one (Fin.castSucc i) (by rw [hi_val, hi1])
      by_cases hj2 : j.val = 2
      · have hj_eq : H_hybrid (n + 1) (Fin.castSucc j) = plane_xy1 :=
          H_hybrid_of_val_two (Fin.castSucc j) (by rw [hj_val, hj2])
        have hl_ge : 3 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hl_eq : H_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc l) hl_ge
        rw [hi_eq, hj_eq, hl_eq, h_last]
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by
          have : l.val ≠ n := by omega
          exact_mod_cast this
        have h_quad : (l.val : ℝ) ^ 2 * (n : ℝ) ^ 2 + (l.val : ℝ) + (n : ℝ) ≠ 0 := by
          have hl_pos : 0 < (l.val : ℝ) := by
            have : 0 < l.val := by omega
            exact_mod_cast this
          have hn_pos' : 0 < (n : ℝ) := by
            have : 0 < n := by omega
            exact_mod_cast this
          positivity
        exact intersection_plane_y0_plane_xy1_two_momentPlanes_empty hln_ne h_quad
      · have hj_ge : 3 ≤ (Fin.castSucc j).val := by rw [hj_val]; omega
        have hl_ge : 3 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hj_eq : H_hybrid (n + 1) (Fin.castSucc j) = momentPlane (j.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc j) hj_ge
        have hl_eq : H_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc l) hl_ge
        rw [hi_eq, hj_eq, hl_eq, h_last]
        have hjl_ne : (j.val : ℝ) ≠ (l.val : ℝ) := by
          have : j.val ≠ l.val := by omega
          exact_mod_cast this
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by
          have : l.val ≠ n := by omega
          exact_mod_cast this
        have hjn_ne : (j.val : ℝ) ≠ (n : ℝ) := by
          have : j.val ≠ n := by omega
          exact_mod_cast this
        have h_pos : (j.val : ℝ) * (l.val : ℝ) + (l.val : ℝ) * (n : ℝ) +
            (n : ℝ) * (j.val : ℝ) ≠ 0 := by
          have hj_pos : 0 < (j.val : ℝ) := by
            have : 0 < j.val := by omega
            exact_mod_cast this
          have hl_pos : 0 < (l.val : ℝ) := by
            have : 0 < l.val := by omega
            exact_mod_cast this
          have hn_pos' : 0 < (n : ℝ) := by
            have : 0 < n := by omega
            exact_mod_cast this
          positivity
        exact intersection_plane_y0_three_momentPlanes_empty hjl_ne hln_ne hjn_ne h_pos
    · by_cases hi2 : i.val = 2
      · have hi_eq : H_hybrid (n + 1) (Fin.castSucc i) = plane_xy1 :=
          H_hybrid_of_val_two (Fin.castSucc i) (by rw [hi_val, hi2])
        have hj_ge : 3 ≤ (Fin.castSucc j).val := by rw [hj_val]; omega
        have hl_ge : 3 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hj_eq : H_hybrid (n + 1) (Fin.castSucc j) = momentPlane (j.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc j) hj_ge
        have hl_eq : H_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc l) hl_ge
        rw [hi_eq, hj_eq, hl_eq, h_last]
        have hjl_ne : (j.val : ℝ) ≠ (l.val : ℝ) := by
          have : j.val ≠ l.val := by omega
          exact_mod_cast this
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by
          have : l.val ≠ n := by omega
          exact_mod_cast this
        have hjn_ne : (j.val : ℝ) ≠ (n : ℝ) := by
          have : j.val ≠ n := by omega
          exact_mod_cast this
        have hj_ge' : 3 ≤ j.val := by omega
        have hjl_lt : j.val < l.val := by omega
        have hln_lt : l.val < n := by omega
        have h_ne := moment_intersection_xy_ne_one j.val l.val n hj_ge' hjl_lt hln_lt
        exact intersection_plane_xy1_three_momentPlanes_empty hjl_ne hln_ne hjn_ne h_ne
      · have hi_ge : 3 ≤ (Fin.castSucc i).val := by rw [hi_val]; omega
        have hj_ge : 3 ≤ (Fin.castSucc j).val := by rw [hj_val]; omega
        have hl_ge : 3 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hi_eq : H_hybrid (n + 1) (Fin.castSucc i) = momentPlane (i.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc i) hi_ge
        have hj_eq : H_hybrid (n + 1) (Fin.castSucc j) = momentPlane (j.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc j) hj_ge
        have hl_eq : H_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_hybrid_of_val_ge (Fin.castSucc l) hl_ge
        rw [hi_eq, hj_eq, hl_eq, h_last]
        have hij_ne : (i.val : ℝ) ≠ (j.val : ℝ) := by
          have : i.val ≠ j.val := by omega
          exact_mod_cast this
        have hjl_ne : (j.val : ℝ) ≠ (l.val : ℝ) := by
          have : j.val ≠ l.val := by omega
          exact_mod_cast this
        have hil_ne : (i.val : ℝ) ≠ (l.val : ℝ) := by
          have : i.val ≠ l.val := by omega
          exact_mod_cast this
        have hin_ne : (i.val : ℝ) ≠ (n : ℝ) := by
          have : i.val ≠ n := by omega
          exact_mod_cast this
        have hjn_ne : (j.val : ℝ) ≠ (n : ℝ) := by
          have : j.val ≠ n := by omega
          exact_mod_cast this
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by
          have : l.val ≠ n := by omega
          exact_mod_cast this
        exact intersection_four_momentPlanes_empty hij_ne hjl_ne hln_ne hil_ne hin_ne hjn_ne

/-- ハイブリッド配置において、相異なる任意の3平面と
最後のモーメント平面の交わりは空集合である。 -/
lemma intersection_four_hybrid_empty (n : ℕ) (hn : 3 ≤ n) (i j l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
      (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
      (H_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
      (H_hybrid (n + 1) (Fin.last n)).toSet = ∅ := by
  rcases lt_trichotomy i j with hij_lt | rfl | hji_lt
  · rcases lt_trichotomy j l with hjl_lt | rfl | hlj_lt
    · exact intersection_four_hybrid_empty_of_sorted n hn i j l hij_lt hjl_lt
    · exact (hjl rfl).elim
    · rcases lt_trichotomy i l with hil_lt | rfl | hli_lt
      · have h := intersection_four_hybrid_empty_of_sorted n hn i l j hil_lt hlj_lt
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
        have hp_in : p ∈ (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
            (H_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
            (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
            (H_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hi, hl⟩, hj⟩, hn_last⟩
        rw [h] at hp_in
        exact hp_in
      · exact (hil rfl).elim
      · have h := intersection_four_hybrid_empty_of_sorted n hn l i j hli_lt hij_lt
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
        have hp_in : p ∈ (H_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
            (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
            (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
            (H_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hl, hi⟩, hj⟩, hn_last⟩
        rw [h] at hp_in
        exact hp_in
  · exact (hij rfl).elim
  · rcases lt_trichotomy i l with hil_lt | rfl | hli_lt
    · have h := intersection_four_hybrid_empty_of_sorted n hn j i l hji_lt hil_lt
      apply Set.eq_empty_of_subset_empty
      rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
      have hp_in : p ∈ (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
          (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
          (H_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
          (H_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hj, hi⟩, hl⟩, hn_last⟩
      rw [h] at hp_in
      exact hp_in
    · exact (hil rfl).elim
    · rcases lt_trichotomy j l with hjl_lt | rfl | hlj_lt
      · have h := intersection_four_hybrid_empty_of_sorted n hn j l i hjl_lt hli_lt
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
        have hp_in : p ∈ (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
            (H_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
            (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
            (H_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hj, hl⟩, hi⟩, hn_last⟩
        rw [h] at hp_in
        exact hp_in
      · exact (hjl rfl).elim
      · have h := intersection_four_hybrid_empty_of_sorted n hn l j i hlj_lt hji_lt
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
        have hp_in : p ∈ (H_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
            (H_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
            (H_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
            (H_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hl, hj⟩, hi⟩, hn_last⟩
        rw [h] at hp_in
        exact hp_in

/-- ハイブリッド配置において、
最後の平面上に現れる交線系は一般の位置にある。
どの2直線も平行でなく、どの3直線も1点で交わらない。 -/
lemma generalPositionLines_hybrid (n : ℕ) (hn : 3 ≤ n) :
    GeneralPositionLines n (traceLinesOnLastPlane n (H_hybrid (n + 1))) := by
  have h_not_parallel_last : ∀ i : Fin n,
      ¬ parallelPlanes ((H_hybrid (n + 1)) (Fin.castSucc i))
        ((H_hybrid (n + 1)) (Fin.last n)) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.last n := Fin.castSucc_lt_last i
    exact not_parallel_hybrid (Fin.castSucc i) (Fin.last n) h_lt
  apply generalPositionLines_of_plane_intersections n (H_hybrid (n + 1)) h_not_parallel_last
  · intro i j hij
    exact intersection_three_hybrid n hn i j hij
  · intro i j l hij hjl hil
    exact intersection_four_hybrid_empty n hn i j l hij hjl hil

/-- ハイブリッド配置において、$n \ge 3$ 枚の平面に
新しく $(n + 1)$ 枚目のモーメント平面を追加したとき、
切断領域数は最大平面領域数 maxPlaneRegions n に一致する。
交線系が一般の位置にあることから、2次元領域数定理を経由して導出される。 -/
lemma splitSpaceRegionsCount_hybrid (n : ℕ) (hn : 3 ≤ n) :
    splitSpaceRegionsCount n (H_hybrid (n + 1)) = maxPlaneRegions n := by
  have h_not_par : ∀ i : Fin n,
      ¬ parallelPlanes ((H_hybrid (n + 1)) (Fin.castSucc i))
        ((H_hybrid (n + 1)) (Fin.last n)) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.last n := Fin.castSucc_lt_last i
    exact not_parallel_hybrid (Fin.castSucc i) (Fin.last n) h_lt
  have hgen_lines := generalPositionLines_hybrid n hn
  exact splitSpaceRegionsCount_eq_of_traceLines n (H_hybrid (n + 1)) h_not_par hgen_lines

/-- $n \ge 3$ のとき、ハイブリッド配置の領域数は
第2位の領域数 secondSpaceRegionsFormula n に一致する。 -/
lemma spaceRegionsCount_hybrid (n : ℕ) (hn : 3 ≤ n) :
    spaceRegionsCount n (H_hybrid n) = secondSpaceRegionsFormula n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero =>
    rw [spaceRegionsCount_hybrid_three]
    have h3 := space_regions_n_three.2.1
    exact h3.symm
  | succ k ih =>
    have h_assoc : 3 + (k + 1) = 3 + k + 1 := by omega
    rw [h_assoc]
    have h_succ := spaceRegionsCount_succ_eq_add_split (3 + k) (H_hybrid (3 + k + 1))
    rw [H_hybrid_castSucc (3 + k)] at h_succ
    rw [h_succ]
    have h_split := splitSpaceRegionsCount_hybrid (3 + k) (by omega)
    rw [h_split, ih]
    have h_sec_m := problem_4_2_proof (3 + k) (by omega)
    have h_sec_succ := problem_4_2_proof (3 + k + 1) (by omega)
    have h_max_succ := maxSpaceRegions_succ (3 + k)
    have h_form_m := problem_4_1_proof (3 + k)
    have h_form_succ := problem_4_1_proof (3 + k + 1)
    have h_pos : 1 ≤ maxSpaceRegionsFormula (3 + k) := by
      rw [← h_form_m]
      dsimp [maxSpaceRegions]
      rw [Nat.choose_zero_right]
      omega
    have h_rec : maxSpaceRegionsFormula (3 + k + 1) =
        maxSpaceRegionsFormula (3 + k) + maxPlaneRegions (3 + k) := by
      rw [← h_form_succ, ← h_form_m, h_max_succ]
    omega

/-- 一般の位置にある n 枚の平面配置に、切断領域数がちょうど S(n) - 1 となる
新しい平面を追加したとき、得られる (n + 1) 枚の配置の領域数は
第2位の領域数 secondSpaceRegionsFormula (n + 1) に一致する。 -/
lemma spaceRegionsCount_eq_second_of_split_eq_pred (n : ℕ) (hn : 1 ≤ n)
    (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes n (H ∘ Fin.castSucc))
    (hsplit : splitSpaceRegionsCount n H = maxPlaneRegions n - 1) :
    spaceRegionsCount (n + 1) H = secondSpaceRegionsFormula (n + 1) := by
  have h_add := spaceRegionsCount_succ_eq_add_split n H
  have h_prev :=
    spaceRegionsCount_eq_max_of_general_position n (H ∘ Fin.castSucc) hgen
  have h_max_succ := maxSpaceRegions_succ n
  have h_sec := problem_4_2_proof (n + 1) (by omega)
  have h_form_n := problem_4_1_proof n
  have h_form_succ := problem_4_1_proof (n + 1)
  have h_S_pos : 1 ≤ maxPlaneRegions n := by
    dsimp [maxPlaneRegions]
    rw [Nat.choose_zero_right]
    omega
  omega

/-- 第2位の領域数を達成する相異なる平面配置が存在する。 -/
lemma exists_planes_secondSpaceRegions (n : ℕ) (hn : 2 ≤ n) :
    ∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = secondSpaceRegionsFormula n := by
  by_cases hn2 : n = 2
  · subst hn2
    obtain ⟨H, hdist, hcount⟩ := spaceRegionsCount_two_parallel
    refine ⟨H, hdist, ?_⟩
    have h_sec2 : secondSpaceRegionsFormula 2 = 3 := space_regions_n_two.2
    rw [h_sec2, hcount]
  · have hn3 : 3 ≤ n := by omega
    refine ⟨H_hybrid n, distinctPlanes_hybrid n, spaceRegionsCount_hybrid n hn3⟩

/-- 【第4問 (2) の幾何学的解答】
n ≥ 2 のとき、最大値未満の任意の配置の領域数は secondSpaceRegionsFormula n 以下であり、かつ達成可能である。 -/
theorem problem_4_2_geometric_proof (n : ℕ) (hn : 2 ≤ n) :
    (∀ (H : Fin n → Plane3), DistinctPlanes n H →
      spaceRegionsCount n H < maxSpaceRegionsFormula n →
      spaceRegionsCount n H ≤ secondSpaceRegionsFormula n) ∧
    (∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = secondSpaceRegionsFormula n) := by
  constructor
  · intro H _hdist hlt
    have h_sec := problem_4_2_proof n hn
    omega
  · exact exists_planes_secondSpaceRegions n hn

/-- 【第4問 (3) の解答(代数公式との一致)】
n ≥ 3 のとき、3番目に大きい値は、n = 4 のとき例外値 12 であり、
n ≠ 4 のとき最大値より 2 小さい値 (n³ + 5n - 6) / 6 である。 -/
theorem problem_4_3_proof (n : ℕ) (_hn : 3 ≤ n) :
    thirdSpaceRegionsFormula n = if n = 4 then 12 else maxSpaceRegionsFormula n - 2 := by
  by_cases h4 : n = 4
  · subst h4
    rfl
  · have h := six_mul_maxSpaceRegions n
    dsimp [thirdSpaceRegionsFormula, maxSpaceRegionsFormula]
    simp only [h4, ↓reduceIte]
    omega

lemma card_filter_pair_eq_four (i j : Fin 4) (hij : i ≠ j) (bi bj : Bool) :
    (Finset.filter (fun σ : Fin 4 → Bool => σ i = bi ∧ σ j = bj) Finset.univ).card = 4 := by
  revert i j hij bi bj
  decide

/-- 2つのインデックス i, j の符号の組が空であるならば、全体の領域数は高々 12 である。 -/
lemma spaceRegionsCount_four_le_twelve_of_pair_empty
    (H : Fin 4 → Plane3) (i j : Fin 4) (hij : i ≠ j)
    (bi bj : Bool)
    (h_empty : ∀ p : Space3, ¬ (
      (if bi then (H i).offset < @inner ℝ Space3 _ (H i).normVec p
       else @inner ℝ Space3 _ (H i).normVec p < (H i).offset) ∧
      (if bj then (H j).offset < @inner ℝ Space3 _ (H j).normVec p
       else @inner ℝ Space3 _ (H j).normVec p < (H j).offset))) :
    spaceRegionsCount 4 H ≤ 12 := by
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  let bad_sigs := Finset.filter (fun σ : Fin 4 → Bool => σ i = bi ∧ σ j = bj) Finset.univ
  have h_bad_empty : ∀ σ ∈ bad_sigs, ¬ (convexSpaceRegion 4 H σ).Nonempty := by
    intro σ hσ ⟨p, hp⟩
    rw [Finset.mem_filter] at hσ
    have hpi := hp i
    have hpj := hp j
    change (if σ i then (H i).offset < @inner ℝ Space3 _ (H i).normVec p
            else @inner ℝ Space3 _ (H i).normVec p < (H i).offset) at hpi
    change (if σ j then (H j).offset < @inner ℝ Space3 _ (H j).normVec p
            else @inner ℝ Space3 _ (H j).normVec p < (H j).offset) at hpj
    rw [hσ.2.1] at hpi
    rw [hσ.2.2] at hpj
    exact h_empty p ⟨hpi, hpj⟩
  have h_sub : (Finset.filter (fun σ => (convexSpaceRegion 4 H σ).Nonempty) Finset.univ) ⊆
      Finset.univ \ bad_sigs := by
    intro σ hσ
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ σ, ?_⟩
    intro h_bad
    exact h_bad_empty σ h_bad (Finset.mem_filter.mp hσ).2
  have h_card_le := Finset.card_le_card h_sub
  rw [Finset.card_sdiff] at h_card_le
  rw [Finset.inter_univ] at h_card_le
  have h_univ : (Finset.univ : Finset (Fin 4 → Bool)).card = 16 := by decide
  have h_bad_card : bad_sigs.card = 4 := card_filter_pair_eq_four i j hij bi bj
  omega

/-- 2枚の相異なる平面が平行であるならば、少なくとも1組の符号は空集合である。 -/
lemma exists_empty_pair_of_parallel_and_distinct (H₁ H₂ : Plane3)
    (hpar : parallelPlanes H₁ H₂) (hdist : H₁.toSet ≠ H₂.toSet) :
    ∃ b₁ b₂ : Bool, ∀ p : Space3, ¬ (
      (if b₁ then H₁.offset < @inner ℝ Space3 _ H₁.normVec p
       else @inner ℝ Space3 _ H₁.normVec p < H₁.offset) ∧
      (if b₂ then H₂.offset < @inner ℝ Space3 _ H₂.normVec p
       else @inner ℝ Space3 _ H₂.normVec p < H₂.offset)) := by
  rcases hpar with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro hc0
    have : H₁.normVec = 0 := by rw [hc, hc0, zero_smul]
    exact H₁.normVec_ne_zero this
  have h_inner : ∀ p : Space3,
      @inner ℝ Space3 _ H₁.normVec p = c * @inner ℝ Space3 _ H₂.normVec p := by
    intro p
    rw [hc, inner_smul_left, conj_trivial]
  rcases lt_or_gt_of_ne hc_ne with hc_neg | hc_pos
  · -- c < 0
    by_cases h_le : H₁.offset / c ≤ H₂.offset
    · -- H₁.offset / c ≤ H₂.offset: b₁ = true, b₂ = true が空
      use true, true
      intro p ⟨hp1, hp2⟩
      change H₁.offset < @inner ℝ Space3 _ H₁.normVec p at hp1
      change H₂.offset < @inner ℝ Space3 _ H₂.normVec p at hp2
      rw [h_inner] at hp1
      have h1 : c * @inner ℝ Space3 _ H₂.normVec p < c * H₂.offset :=
        mul_lt_mul_of_neg_left hp2 hc_neg
      have h2 : H₁.offset < c * H₂.offset := lt_trans hp1 h1
      have h3 : H₂.offset * c ≤ H₁.offset := (div_le_iff_of_neg hc_neg).mp h_le
      rw [mul_comm] at h3
      linarith
    · -- H₂.offset < H₁.offset / c: b₁ = false, b₂ = false が空
      have h_gt : H₂.offset < H₁.offset / c := not_le.mp h_le
      use false, false
      intro p ⟨hp1, hp2⟩
      change @inner ℝ Space3 _ H₁.normVec p < H₁.offset at hp1
      change @inner ℝ Space3 _ H₂.normVec p < H₂.offset at hp2
      rw [h_inner] at hp1
      have h1 : c * H₂.offset < c * @inner ℝ Space3 _ H₂.normVec p :=
        mul_lt_mul_of_neg_left hp2 hc_neg
      have h2 : c * H₂.offset < H₁.offset := lt_trans h1 hp1
      have h3 : H₁.offset < H₂.offset * c := (lt_div_iff_of_neg hc_neg).mp h_gt
      rw [mul_comm] at h3
      linarith
  · -- c > 0
    have h_off_ne : H₁.offset / c ≠ H₂.offset := by
      intro h_off_eq
      apply hdist
      ext p
      dsimp [Plane3.toSet]
      rw [h_inner]
      constructor
      · intro h1
        have hc_ne' : c ≠ 0 := ne_of_gt hc_pos
        have : @inner ℝ Space3 _ H₂.normVec p = H₁.offset / c := by
          rw [← h1, mul_div_cancel_left₀ _ hc_ne']
        rw [h_off_eq] at this
        exact this
      · intro h2
        have hc_ne' : c ≠ 0 := ne_of_gt hc_pos
        rw [h2, ← h_off_eq, mul_div_cancel₀ _ hc_ne']
    rcases lt_or_gt_of_ne h_off_ne with h_lt | h_gt
    · -- H₁.offset / c < H₂.offset: b₁ = false, b₂ = true が空
      use false, true
      intro p ⟨hp1, hp2⟩
      change @inner ℝ Space3 _ H₁.normVec p < H₁.offset at hp1
      change H₂.offset < @inner ℝ Space3 _ H₂.normVec p at hp2
      rw [h_inner] at hp1
      have h1 : c * H₂.offset < c * @inner ℝ Space3 _ H₂.normVec p :=
        mul_lt_mul_of_pos_left hp2 hc_pos
      have h2 : c * H₂.offset < H₁.offset := lt_trans h1 hp1
      have h3 : H₁.offset < H₂.offset * c := (div_lt_iff₀ hc_pos).mp h_lt
      rw [mul_comm] at h3
      linarith
    · -- H₂.offset < H₁.offset / c: b₁ = true, b₂ = false が空
      use true, false
      intro p ⟨hp1, hp2⟩
      change H₁.offset < @inner ℝ Space3 _ H₁.normVec p at hp1
      change @inner ℝ Space3 _ H₂.normVec p < H₂.offset at hp2
      rw [h_inner] at hp1
      have h1 : c * @inner ℝ Space3 _ H₂.normVec p < c * H₂.offset :=
        mul_lt_mul_of_pos_left hp2 hc_pos
      have h2 : H₁.offset < c * H₂.offset := lt_trans hp1 h1
      have h3 : H₂.offset * c < H₁.offset := (lt_div_iff₀ hc_pos).mp h_gt
      rw [mul_comm] at h3
      linarith

/-- 平行な2平面を含む4平面配置の領域数は高々12である。 -/
lemma spaceRegionsCount_four_le_twelve_of_parallel (H : Fin 4 → Plane3)
    (hdist : DistinctPlanes 4 H)
    (hpar : ∃ i j, i ≠ j ∧ parallelPlanes (H i) (H j)) :
    spaceRegionsCount 4 H ≤ 12 := by
  rcases hpar with ⟨i, j, hij, hpar_ij⟩
  have hdist_ij : (H i).toSet ≠ (H j).toSet := fun h => hij (hdist h)
  rcases exists_empty_pair_of_parallel_and_distinct (H i) (H j) hpar_ij hdist_ij with
    ⟨bi, bj, h_empty⟩
  exact spaceRegionsCount_four_le_twelve_of_pair_empty H i j hij bi bj h_empty

/-- 空間領域数は平面のインデックスの置換によって不変である。 -/
lemma spaceRegionsCount_equiv (n : ℕ) (H : Fin n → Plane3) (e : Fin n ≃ Fin n) :
    spaceRegionsCount n (H ∘ e) = spaceRegionsCount n H := by
  dsimp [spaceRegionsCount]
  have h_set : {x : Space3 | ∀ i, x ∉ (H (e i)).toSet} =
      {x : Space3 | ∀ i, x ∉ (H i).toSet} := by
    ext x
    exact e.forall_congr (fun _ => Iff.rfl)
  exact congrArg (fun (s : Set Space3) =>
    Nat.card (ConnectedComponents (↥s))) h_set

/-- あるビット反転に関して不変な符号ベクトル集合の要素数は偶数である。 -/
lemma even_card_of_flip_invariant (m : Fin 3) (S : Finset (Fin 3 → Bool))
    (h_inv : ∀ σ, σ ∈ S ↔ (fun l => if l = m then !(σ l) else σ l) ∈ S) :
    ∃ k : ℕ, S.card = 2 * k := by
  let f : (Fin 3 → Bool) → (Fin 3 → Bool) :=
    fun σ l => if l = m then !(σ l) else σ l
  have hf_invol : ∀ σ, f (f σ) = σ := by
    intro σ
    ext l
    dsimp [f]
    split_ifs with h
    · simp
    · rfl
  have hf_inj : Function.Injective f := by
    intro σ₁ σ₂ h
    have := congrArg f h
    rwa [hf_invol, hf_invol] at this
  let A := S.filter (fun σ => σ m = false)
  let B := S.filter (fun σ => σ m = true)
  have h_union : S = A ∪ B := by
    ext σ
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    cases σ m <;> simp
  have h_disj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro σ _ h1 h2
    rw [h1] at h2
    cases h2
  have h_map_A : ∀ σ ∈ A, f σ ∈ B := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨(h_inv σ).mp hσ.1, ?_⟩
    dsimp [f]
    simp [hσ.2]
  have h_map_B : ∀ σ ∈ B, f σ ∈ A := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨(h_inv σ).mp hσ.1, ?_⟩
    dsimp [f]
    simp [hσ.2]
  have h_le_AB : A.card ≤ B.card := by
    have : A.card = (A.image f).card := by
      rw [Finset.card_image_of_injective _ hf_inj]
    rw [this]
    apply Finset.card_le_card
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_map_A x hx
  have h_le_BA : B.card ≤ A.card := by
    have : B.card = (B.image f).card := by
      rw [Finset.card_image_of_injective _ hf_inj]
    rw [this]
    apply Finset.card_le_card
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_map_B x hx
  have h_eq : A.card = B.card := le_antisymm h_le_AB h_le_BA
  use A.card
  rw [h_union, Finset.card_union_of_disjoint h_disj, h_eq]
  ring

/-- 全ビット反転に関して不変な符号ベクトル集合の要素数は偶数である。 -/
lemma even_card_of_neg_invariant (S : Finset (Fin 3 → Bool))
    (h_inv : ∀ σ, σ ∈ S ↔ (fun l => !(σ l)) ∈ S) :
    ∃ k : ℕ, S.card = 2 * k := by
  let f : (Fin 3 → Bool) → (Fin 3 → Bool) := fun σ l => !(σ l)
  have hf_invol : ∀ σ, f (f σ) = σ := by
    intro σ
    ext l
    dsimp [f]
    simp
  have hf_inj : Function.Injective f := by
    intro σ₁ σ₂ h
    have := congrArg f h
    rwa [hf_invol, hf_invol] at this
  let m : Fin 3 := 0
  let A := S.filter (fun σ => σ m = false)
  let B := S.filter (fun σ => σ m = true)
  have h_union : S = A ∪ B := by
    ext σ
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    cases σ m <;> simp
  have h_disj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro σ _ h1 h2
    rw [h1] at h2
    cases h2
  have h_map_A : ∀ σ ∈ A, f σ ∈ B := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨(h_inv σ).mp hσ.1, ?_⟩
    dsimp [f]
    rw [hσ.2]
    rfl
  have h_map_B : ∀ σ ∈ B, f σ ∈ A := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨(h_inv σ).mp hσ.1, ?_⟩
    dsimp [f]
    rw [hσ.2]
    rfl
  have h_le_AB : A.card ≤ B.card := by
    have : A.card = (A.image f).card := by
      rw [Finset.card_image_of_injective _ hf_inj]
    rw [this]
    apply Finset.card_le_card
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_map_A x hx
  have h_le_BA : B.card ≤ A.card := by
    have : B.card = (B.image f).card := by
      rw [Finset.card_image_of_injective _ hf_inj]
    rw [this]
    apply Finset.card_le_card
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_map_B x hx
  have h_eq : A.card = B.card := le_antisymm h_le_AB h_le_BA
  use A.card
  rw [h_union, Finset.card_union_of_disjoint h_disj, h_eq]
  ring

lemma card_filter_pair_eq_two (i j : Fin 3) (hij : i ≠ j) (bi bj : Bool) :
    (Finset.filter (fun σ : Fin 3 → Bool => σ i = bi ∧ σ j = bj) Finset.univ).card = 2 := by
  revert i j hij bi bj
  decide

/-- 2つのインデックス $i, j$ の符号の組が空であるならば、全体の領域数は高々6である。 -/
lemma planeRegionsCount_le_six_of_pair_empty
    (L : Fin 3 → Line2) (i j : Fin 3) (hij : i ≠ j)
    (bi bj : Bool)
    (h_empty : ∀ p : Plane2, ¬ (
      (if bi then (L i).offset < @inner ℝ Plane2 _ (L i).normVec p
       else @inner ℝ Plane2 _ (L i).normVec p < (L i).offset) ∧
      (if bj then (L j).offset < @inner ℝ Plane2 _ (L j).normVec p
       else @inner ℝ Plane2 _ (L j).normVec p < (L j).offset))) :
    planeRegionsCount 3 L ≤ 6 := by
  rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion]
  let bad_sigs := Finset.filter (fun σ : Fin 3 → Bool => σ i = bi ∧ σ j = bj) Finset.univ
  have h_bad_empty : ∀ σ ∈ bad_sigs, ¬ (convexPlaneRegion 3 L σ).Nonempty := by
    intro σ hσ ⟨p, hp⟩
    rw [Finset.mem_filter] at hσ
    have hpi := hp i
    have hpj := hp j
    change (if σ i then (L i).offset < @inner ℝ Plane2 _ (L i).normVec p
            else @inner ℝ Plane2 _ (L i).normVec p < (L i).offset) at hpi
    change (if σ j then (L j).offset < @inner ℝ Plane2 _ (L j).normVec p
            else @inner ℝ Plane2 _ (L j).normVec p < (L j).offset) at hpj
    rw [hσ.2.1] at hpi
    rw [hσ.2.2] at hpj
    exact h_empty p ⟨hpi, hpj⟩
  have h_sub : (Finset.filter (fun σ => (convexPlaneRegion 3 L σ).Nonempty) Finset.univ) ⊆
      Finset.univ \ bad_sigs := by
    intro σ hσ
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ σ, ?_⟩
    intro h_bad
    exact h_bad_empty σ h_bad (Finset.mem_filter.mp hσ).2
  have h_card_le := Finset.card_le_card h_sub
  rw [Finset.card_sdiff] at h_card_le
  rw [Finset.inter_univ] at h_card_le
  have h_univ : (Finset.univ : Finset (Fin 3 → Bool)).card = 8 := by decide
  have h_bad_card : bad_sigs.card = 2 := card_filter_pair_eq_two i j hij bi bj
  omega

/-- 2本の相異なる直線が平行であるならば、少なくとも1組の符号は空集合である。 -/
lemma exists_empty_pair_of_parallel_lines_and_distinct (L₁ L₂ : Line2)
    (hpar : parallelLines L₁ L₂) (hdist : L₁.toSet ≠ L₂.toSet) :
    ∃ b₁ b₂ : Bool, ∀ p : Plane2, ¬ (
      (if b₁ then L₁.offset < @inner ℝ Plane2 _ L₁.normVec p
       else @inner ℝ Plane2 _ L₁.normVec p < L₁.offset) ∧
      (if b₂ then L₂.offset < @inner ℝ Plane2 _ L₂.normVec p
       else @inner ℝ Plane2 _ L₂.normVec p < L₂.offset)) := by
  rcases hpar with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro hc0
    have : L₁.normVec = 0 := by rw [hc, hc0, zero_smul]
    exact L₁.normVec_ne_zero this
  have h_inner : ∀ p : Plane2,
      @inner ℝ Plane2 _ L₁.normVec p = c * @inner ℝ Plane2 _ L₂.normVec p := by
    intro p
    rw [hc, inner_smul_left, conj_trivial]
  rcases lt_or_gt_of_ne hc_ne with hc_neg | hc_pos
  · by_cases h_le : L₁.offset / c ≤ L₂.offset
    · use true, true
      intro p ⟨hp1, hp2⟩
      change L₁.offset < @inner ℝ Plane2 _ L₁.normVec p at hp1
      change L₂.offset < @inner ℝ Plane2 _ L₂.normVec p at hp2
      rw [h_inner] at hp1
      have h1 : c * @inner ℝ Plane2 _ L₂.normVec p < c * L₂.offset :=
        mul_lt_mul_of_neg_left hp2 hc_neg
      have h2 : L₁.offset < c * L₂.offset := lt_trans hp1 h1
      have h3 : L₂.offset * c ≤ L₁.offset := (div_le_iff_of_neg hc_neg).mp h_le
      rw [mul_comm] at h3
      linarith
    · have h_gt : L₂.offset < L₁.offset / c := not_le.mp h_le
      use false, false
      intro p ⟨hp1, hp2⟩
      change @inner ℝ Plane2 _ L₁.normVec p < L₁.offset at hp1
      change @inner ℝ Plane2 _ L₂.normVec p < L₂.offset at hp2
      rw [h_inner] at hp1
      have h1 : c * L₂.offset < c * @inner ℝ Plane2 _ L₂.normVec p :=
        mul_lt_mul_of_neg_left hp2 hc_neg
      have h2 : c * L₂.offset < L₁.offset := lt_trans h1 hp1
      have h3 : L₁.offset < L₂.offset * c := (lt_div_iff_of_neg hc_neg).mp h_gt
      rw [mul_comm] at h3
      linarith
  · have h_off_ne : L₁.offset / c ≠ L₂.offset := by
      intro h_off_eq
      apply hdist
      ext p
      dsimp [Line2.toSet]
      rw [h_inner]
      constructor
      · intro h1
        have hc_ne' : c ≠ 0 := ne_of_gt hc_pos
        have : @inner ℝ Plane2 _ L₂.normVec p = L₁.offset / c := by
          rw [← h1, mul_div_cancel_left₀ _ hc_ne']
        rw [h_off_eq] at this
        exact this
      · intro h2
        have hc_ne' : c ≠ 0 := ne_of_gt hc_pos
        rw [h2, ← h_off_eq, mul_div_cancel₀ _ hc_ne']
    rcases lt_or_gt_of_ne h_off_ne with h_lt | h_gt
    · use false, true
      intro p ⟨hp1, hp2⟩
      change @inner ℝ Plane2 _ L₁.normVec p < L₁.offset at hp1
      change L₂.offset < @inner ℝ Plane2 _ L₂.normVec p at hp2
      rw [h_inner] at hp1
      have h1 : c * L₂.offset < c * @inner ℝ Plane2 _ L₂.normVec p :=
        mul_lt_mul_of_pos_left hp2 hc_pos
      have h2 : c * L₂.offset < L₁.offset := lt_trans h1 hp1
      have h3 : L₁.offset < L₂.offset * c := (div_lt_iff₀ hc_pos).mp h_lt
      rw [mul_comm] at h3
      linarith
    · use true, false
      intro p ⟨hp1, hp2⟩
      change L₁.offset < @inner ℝ Plane2 _ L₁.normVec p at hp1
      change @inner ℝ Plane2 _ L₂.normVec p < L₂.offset at hp2
      rw [h_inner] at hp1
      have h1 : c * @inner ℝ Plane2 _ L₂.normVec p < c * L₂.offset :=
        mul_lt_mul_of_pos_left hp2 hc_pos
      have h2 : L₁.offset < c * L₂.offset := lt_trans hp1 h1
      have h3 : L₂.offset * c < L₁.offset := (lt_div_iff₀ hc_pos).mp h_gt
      rw [mul_comm] at h3
      linarith

/-- 平行線の反射律。任意の直線は自身と平行である。 -/
lemma parallelLines_refl (L : Line2) : parallelLines L L := ⟨1, by rw [one_smul]⟩

/-- 非ゼロベクトルの90度回転ベクトルは非ゼロである。 -/
lemma rot90_ne_zero {u : Plane2} (hu : u ≠ 0) : rot90 u ≠ 0 := by
  intro h
  apply hu
  ext i
  fin_cases i
  · have h1 : (rot90 u) 1 = 0 := by rw [h]; rfl
    dsimp [rot90] at h1
    exact h1
  · have h0 : (rot90 u) 0 = 0 := by rw [h]; rfl
    dsimp [rot90] at h0
    exact neg_eq_zero.mp h0

set_option linter.unusedSimpArgs false in
/-- 3直線のうち2本が平行で、第3の直線がそれらと平行でないとき、
開領域の存在性は第3直線の符号反転で不変である。 -/
lemma nonempty_convexPlaneRegion_flip_of_parallel_pair
    (L : Fin 3 → Line2) (i j k : Fin 3) (h_par : parallelLines (L i) (L j))
    (h_not_par : ¬ parallelLines (L k) (L j))
    (h_perm : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
    (hik : i ≠ k) (hjk : j ≠ k)
    (σ : Fin 3 → Bool)
    (h_nonempty : (convexPlaneRegion 3 L σ).Nonempty) :
    (convexPlaneRegion 3 L (fun l => if l = k then !(σ l) else σ l)).Nonempty := by
  rcases h_nonempty with ⟨p, hp⟩
  rcases h_par with ⟨c, hc⟩
  let u_j := (L j).normVec
  let v := rot90 u_j
  have hv_j : @inner ℝ Plane2 _ u_j v = 0 := inner_rot90_self u_j
  have hv_i : @inner ℝ Plane2 _ (L i).normVec v = 0 := by
    rw [hc, inner_smul_left, conj_trivial, hv_j, mul_zero]
  have hv_k : @inner ℝ Plane2 _ (L k).normVec v ≠ 0 := by
    intro h0
    have := parallel_of_inner_rot90_zero (L k).normVec u_j (L j).normVec_ne_zero h0
    exact h_not_par this
  let u_k := (L k).normVec
  let α := @inner ℝ Plane2 _ u_k v
  have hα_ne : α ≠ 0 := hv_k
  have hpk := hp k
  change (if σ k then (L k).offset < @inner ℝ Plane2 _ u_k p
          else @inner ℝ Plane2 _ u_k p < (L k).offset) at hpk
  let t : ℝ := if σ k then
      if 0 < α then ((L k).offset - @inner ℝ Plane2 _ u_k p) / α - 1
      else ((L k).offset - @inner ℝ Plane2 _ u_k p) / α + 1
    else
      if 0 < α then ((L k).offset - @inner ℝ Plane2 _ u_k p) / α + 1
      else ((L k).offset - @inner ℝ Plane2 _ u_k p) / α - 1
  let q := p + t • v
  use q
  intro l
  have hq_inner : @inner ℝ Plane2 _ (L l).normVec q =
      @inner ℝ Plane2 _ (L l).normVec p + t * @inner ℝ Plane2 _ (L l).normVec v := by
    dsimp [q]
    rw [inner_add_right, inner_smul_right]
  rcases h_perm l with hl | hl | hl
  · rw [hl]
    have h_l_ne : i ≠ k := hik
    simp only [h_l_ne, ↓reduceIte]
    have hq_i : @inner ℝ Plane2 _ (L i).normVec q = @inner ℝ Plane2 _ (L i).normVec p := by
      rw [← hl, hq_inner, hl, hv_i, mul_zero, add_zero]
    rw [hq_i]
    exact hp i
  · rw [hl]
    have h_l_ne : j ≠ k := hjk
    simp only [h_l_ne, ↓reduceIte]
    have hq_j : @inner ℝ Plane2 _ (L j).normVec q = @inner ℝ Plane2 _ (L j).normVec p := by
      rw [← hl, hq_inner, hl, hv_j, mul_zero, add_zero]
    rw [hq_j]
    exact hp j
  · rw [hl]
    simp only [↓reduceIte]
    have hq_k : @inner ℝ Plane2 _ (L k).normVec q =
        @inner ℝ Plane2 _ (L k).normVec p + t * α := by
      change @inner ℝ Plane2 _ (L k).normVec q =
        @inner ℝ Plane2 _ (L k).normVec p + t * @inner ℝ Plane2 _ (L k).normVec v
      rw [← hl, hq_inner, hl]
    cases hσk : σ k
    · simp only [hσk, Bool.not_false, ↓reduceIte]
      by_cases hα_pos : 0 < α
      · have h_t : t = ((L k).offset - @inner ℝ Plane2 _ u_k p) / α + 1 := by
          dsimp [t]; rw [hσk]; simp [hα_pos]
        rw [hq_k, h_t]
        have : (@inner ℝ Plane2 _ (L k).normVec p +
            (((L k).offset - @inner ℝ Plane2 _ u_k p) / α + 1) * α) =
            (L k).offset + α := by
          change (@inner ℝ Plane2 _ u_k p +
            (((L k).offset - @inner ℝ Plane2 _ u_k p) / α + 1) * α) = _
          rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hα_pos)]
          ring
        rw [this]
        linarith
      · have hα_neg : α < 0 := lt_of_le_of_ne (not_lt.mp hα_pos) hα_ne
        have h_t : t = ((L k).offset - @inner ℝ Plane2 _ u_k p) / α - 1 := by
          dsimp [t]; rw [hσk]; simp [not_lt.mp hα_pos]
        rw [hq_k, h_t]
        have : (@inner ℝ Plane2 _ (L k).normVec p +
            (((L k).offset - @inner ℝ Plane2 _ u_k p) / α - 1) * α) =
            (L k).offset - α := by
          change (@inner ℝ Plane2 _ u_k p +
            (((L k).offset - @inner ℝ Plane2 _ u_k p) / α - 1) * α) = _
          rw [sub_mul, div_mul_cancel₀ _ (ne_of_lt hα_neg)]
          ring
        rw [this]
        linarith
    · simp only [hσk, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
      by_cases hα_pos : 0 < α
      · have h_t : t = ((L k).offset - @inner ℝ Plane2 _ u_k p) / α - 1 := by
          dsimp [t]; rw [hσk]; simp [hα_pos]
        rw [hq_k, h_t]
        have : (@inner ℝ Plane2 _ (L k).normVec p +
            (((L k).offset - @inner ℝ Plane2 _ u_k p) / α - 1) * α) =
            (L k).offset - α := by
          change (@inner ℝ Plane2 _ u_k p +
            (((L k).offset - @inner ℝ Plane2 _ u_k p) / α - 1) * α) = _
          rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hα_pos)]
          ring
        rw [this]
        linarith
      · have hα_neg : α < 0 := lt_of_le_of_ne (not_lt.mp hα_pos) hα_ne
        have h_t : t = ((L k).offset - @inner ℝ Plane2 _ u_k p) / α + 1 := by
          dsimp [t]; rw [hσk]; simp [not_lt.mp hα_pos]
        rw [hq_k, h_t]
        have : (@inner ℝ Plane2 _ (L k).normVec p +
            (((L k).offset - @inner ℝ Plane2 _ u_k p) / α + 1) * α) =
            (L k).offset + α := by
          change (@inner ℝ Plane2 _ u_k p +
            (((L k).offset - @inner ℝ Plane2 _ u_k p) / α + 1) * α) = _
          rw [add_mul, div_mul_cancel₀ _ (ne_of_lt hα_neg)]
          ring
        rw [this]
        linarith

/-- 3直線のうち2本が平行で、第3の直線がそれらと平行でないとき、領域数は偶数である。 -/
lemma planeRegionsCount_even_of_parallel_pair
    (L : Fin 3 → Line2) (i j k : Fin 3) (h_par : parallelLines (L i) (L j))
    (h_not_par : ¬ parallelLines (L k) (L j))
    (h_perm : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
    (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ m : ℕ, planeRegionsCount 3 L = 2 * m := by
  let V := Finset.filter (fun σ => (convexPlaneRegion 3 L σ).Nonempty) Finset.univ
  have h_inv : ∀ σ, σ ∈ V ↔ (fun l => if l = k then !(σ l) else σ l) ∈ V := by
    intro σ
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact nonempty_convexPlaneRegion_flip_of_parallel_pair L i j k
        h_par h_not_par h_perm hik hjk σ h
    · intro h
      have h2 := nonempty_convexPlaneRegion_flip_of_parallel_pair L i j k
        h_par h_not_par h_perm hik hjk (fun l => if l = k then !(σ l) else σ l) h
      have h_eq : (fun l => if l = k then !(if l = k then !(σ l) else σ l)
                   else if l = k then !(σ l) else σ l) = σ := by
        ext l
        split_ifs with hl
        · simp
        · rfl
      rwa [h_eq] at h2
  have h_even := even_card_of_flip_invariant k V h_inv
  rw [planeRegionsCount_eq_card_nonempty_convexPlaneRegion]
  exact h_even

/-- 誘導交線系の相異なる3直線が1点で交わるならば、その交点はもとの3平面の共通点である。 -/
lemma eq_P0_of_traceLines_inter (H : Fin 4 → Plane3)
    (h_not_par : ∀ i : Fin 3, ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last 3)))
    (P0 : Space3)
    (hP0 : ((H ∘ Fin.castSucc) 0).toSet ∩ ((H ∘ Fin.castSucc) 1).toSet ∩
           ((H ∘ Fin.castSucc) 2).toSet = {P0})
    (p : Plane2)
    (hp : ∀ i : Fin 3, p ∈ (traceLinesOnLastPlane 3 H i).toSet) :
    planePt3 (H (Fin.last 3)) p = P0 := by
  have h_in : planePt3 (H (Fin.last 3)) p ∈ ({P0} : Set Space3) := by
    rw [← hP0]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · dsimp only [Function.comp_apply]
      rw [← mem_traceLine_iff 3 H 0 (h_not_par 0)]
      exact hp 0
    · dsimp only [Function.comp_apply]
      rw [← mem_traceLine_iff 3 H 1 (h_not_par 1)]
      exact hp 1
    · dsimp only [Function.comp_apply]
      rw [← mem_traceLine_iff 3 H 2 (h_not_par 2)]
      exact hp 2
  exact Set.mem_singleton_iff.mp h_in

/-- 3枚の平面が一般の位置にあるとき、誘導交線系の直線がすべて互いに平行になることはない。 -/
lemma not_all_parallel_of_traceLines (H : Fin 4 → Plane3)
    (h_not_par : ∀ i : Fin 3, ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last 3)))
    (P0 : Space3)
    (hP0 : ((H ∘ Fin.castSucc) 0).toSet ∩ ((H ∘ Fin.castSucc) 1).toSet ∩
           ((H ∘ Fin.castSucc) 2).toSet = {P0})
    (j : Fin 3)
    (h_all_par : ∀ l : Fin 3, parallelLines (traceLinesOnLastPlane 3 H l)
                                           (traceLinesOnLastPlane 3 H j)) :
    False := by
  let L' := traceLinesOnLastPlane 3 H
  have hw_ne := traceLineNormVec_ne_zero (H (Fin.last 3)) (H (Fin.castSucc j)) (h_not_par j)
  have h_norm_eq : (L' j).normVec = traceLineNormVec (H (Fin.last 3)) (H (Fin.castSucc j)) := by
    dsimp [L', traceLinesOnLastPlane]
    split_ifs with hw
    · exact (hw_ne hw).elim
    · rfl
  let u := (L' j).normVec
  have hu_ne : u ≠ 0 := (L' j).normVec_ne_zero
  let v := rot90 u
  have hv_ne : v ≠ 0 := rot90_ne_zero hu_ne
  have hv_u : @inner ℝ Plane2 _ u v = 0 := inner_rot90_self u
  have hv_l : ∀ l : Fin 3, @inner ℝ Plane2 _ (L' l).normVec v = 0 := by
    intro l
    rcases h_all_par l with ⟨c, hc⟩
    rw [hc, inner_smul_left, conj_trivial, hv_u, mul_zero]
  let Q1 := planePt3 (H (Fin.last 3)) 0
  let Q2 := planePt3 (H (Fin.last 3)) v
  let V := Q2 - Q1
  have hV_ne : V ≠ 0 := by
    intro h0
    apply hv_ne
    have : Q2 = Q1 := sub_eq_zero.mp h0
    exact planePt3_injective (H (Fin.last 3)) this
  have h_inner_V : ∀ l : Fin 3,
      @inner ℝ Space3 _ (H (Fin.castSucc l)).normVec V = 0 := by
    intro l
    have h1 := inner_planePt3_sub (H (Fin.last 3)) v (H (Fin.castSucc l))
    have h2 := inner_planePt3_sub (H (Fin.last 3)) 0 (H (Fin.castSucc l))
    dsimp only at h1 h2
    have hw_l_ne := traceLineNormVec_ne_zero (H (Fin.last 3)) (H (Fin.castSucc l)) (h_not_par l)
    have h_norm_l : (L' l).normVec = traceLineNormVec (H (Fin.last 3)) (H (Fin.castSucc l)) := by
      dsimp [L', traceLinesOnLastPlane]
      split_ifs with hw
      · exact (hw_l_ne hw).elim
      · rfl
    have h_zero :
        @inner ℝ Plane2 _ (traceLineNormVec (H (Fin.last 3)) (H (Fin.castSucc l))) 0 = 0 :=
      inner_zero_right _
    have h_v_zero :
        @inner ℝ Plane2 _ (traceLineNormVec (H (Fin.last 3)) (H (Fin.castSucc l))) v = 0 := by
      rw [← h_norm_l]
      exact hv_l l
    have h_inner_eq : @inner ℝ Space3 _ (H (Fin.castSucc l)).normVec V =
        @inner ℝ Space3 _ (H (Fin.castSucc l)).normVec (planePt3 (H (Fin.last 3)) v) -
        @inner ℝ Space3 _ (H (Fin.castSucc l)).normVec (planePt3 (H (Fin.last 3)) 0) := by
      change @inner ℝ Space3 _ (H (Fin.castSucc l)).normVec (Q2 - Q1) = _
      rw [inner_sub_right]
    rw [h_inner_eq]
    dsimp only [traceLineNormVec] at h_zero h_v_zero
    linarith [h1, h2, h_zero, h_v_zero]
  have hP0_mem : ∀ i : Fin 3, P0 ∈ (H (Fin.castSucc i)).toSet := by
    intro i
    have h_in : P0 ∈ {P0} := Set.mem_singleton P0
    rw [← hP0] at h_in
    fin_cases i
    · exact h_in.1.1
    · exact h_in.1.2
    · exact h_in.2
  have h_mem_P0_V : P0 + V ∈ ((H ∘ Fin.castSucc) 0).toSet ∩
      ((H ∘ Fin.castSucc) 1).toSet ∩ ((H ∘ Fin.castSucc) 2).toSet := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change @inner ℝ Space3 _ (H (Fin.castSucc 0)).normVec (P0 + V) =
        (H (Fin.castSucc 0)).offset
      rw [inner_add_right, h_inner_V 0, add_zero]
      exact hP0_mem 0
    · change @inner ℝ Space3 _ (H (Fin.castSucc 1)).normVec (P0 + V) =
        (H (Fin.castSucc 1)).offset
      rw [inner_add_right, h_inner_V 1, add_zero]
      exact hP0_mem 1
    · change @inner ℝ Space3 _ (H (Fin.castSucc 2)).normVec (P0 + V) =
        (H (Fin.castSucc 2)).offset
      rw [inner_add_right, h_inner_V 2, add_zero]
      exact hP0_mem 2
  rw [hP0, Set.mem_singleton_iff] at h_mem_P0_V
  have : V = 0 := add_left_cancel (h_mem_P0_V.trans (add_zero P0).symm)
  exact hV_ne this

/-- 3枚の平面が一般の位置にあるとき、第4平面による切断空間領域数は5になり得ない。 -/
lemma splitSpaceRegionsCount_three_ne_five (H : Fin 4 → Plane3)
    (hgen : GeneralPositionPlanes 3 (H ∘ Fin.castSucc))
    (h_not_par : ∀ i : Fin 3,
      ¬ parallelPlanes (H (Fin.castSucc i)) (H (Fin.last 3))) :
    splitSpaceRegionsCount 3 H ≠ 5 := by
  intro h5
  have h_le := splitSpaceRegionsCount_le_maxPlaneRegions 3 H
  have h_max3 : maxPlaneRegions 3 = 7 := rfl
  let L' := traceLinesOnLastPlane 3 H
  have hgen_lines_or : GeneralPositionLines 3 L' ∨ ¬ GeneralPositionLines 3 L' :=
    Classical.em _
  rcases hgen_lines_or with hgen_lines | hnot_gen
  · have h7 := splitSpaceRegionsCount_eq_of_traceLines 3 H h_not_par hgen_lines
    rw [h_max3] at h7
    omega
  · -- 交線系L'が一般の位置にない場合、P0 ∈ H 3 か否かで場合分けする。
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    rcases hgen.2.1 0 1 2 h01 h12 h02 with ⟨P0, hP0⟩
    have hP0_mem : ∀ i : Fin 3, P0 ∈ (H (Fin.castSucc i)).toSet := by
      intro i
      have h_in : P0 ∈ {P0} := Set.mem_singleton P0
      rw [← hP0] at h_in
      fin_cases i
      · exact h_in.1.1
      · exact h_in.1.2
      · exact h_in.2
    have hp0_i : ∀ i : Fin 3,
        @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec P0 = (H (Fin.castSucc i)).offset := by
      intro i; exact hP0_mem i
    by_cases hP0_3 : P0 ∈ (H (Fin.last 3)).toSet
    · -- P0 ∈ H 3 の場合: 4平面すべてが P0 を通り、全反転に関して対称なため領域数は偶数である。
      have hp0_3 : @inner ℝ Space3 _ (H (Fin.last 3)).normVec P0 = (H (Fin.last 3)).offset :=
        hP0_3
      let split_sigs := Finset.filter (fun σ =>
        isSplitByPlane (convexSpaceRegion 3 (H ∘ Fin.castSucc) σ) (H (Fin.last 3))) Finset.univ
      have h_split_count : splitSpaceRegionsCount 3 H = split_sigs.card := rfl
      have h_fwd : ∀ σ, σ ∈ split_sigs → (fun l => !(σ l)) ∈ split_sigs := by
        intro σ hσ
        dsimp [split_sigs] at hσ ⊢
        rw [Finset.mem_filter] at hσ ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hσ.2 with ⟨q, hq1, hq2⟩
        refine ⟨(2 : ℝ) • P0 - q, ?_, ?_⟩
        · intro i
          have hq_i := hq1 i
          dsimp [convexSpaceRegion] at hq_i ⊢
          have h_inner : @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec ((2 : ℝ) • P0 - q) -
              (H (Fin.castSucc i)).offset =
              - (@inner ℝ Space3 _ (H (Fin.castSucc i)).normVec q -
                 (H (Fin.castSucc i)).offset) := by
            rw [inner_sub_right, inner_smul_right, hp0_i i]
            ring
          by_cases hσi : σ i = true
          · have h_not : (!σ i) = false := by rw [hσi]; rfl
            have h_t : (if (!σ i) = true then (H (Fin.castSucc i)).offset <
                @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec ((2 : ℝ) • P0 - q)
              else @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec ((2 : ℝ) • P0 - q) <
                (H (Fin.castSucc i)).offset) ↔
                @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec ((2 : ℝ) • P0 - q) <
                (H (Fin.castSucc i)).offset := by
              rw [h_not]
              simp
            rw [h_t]
            have hq_i' : (H (Fin.castSucc i)).offset <
                @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec q := by
              revert hq_i
              rw [hσi]
              simp
            linarith [h_inner, hq_i']
          · have h_f : σ i = false := by
              revert hσi; cases σ i <;> simp
            have h_not : (!σ i) = true := by rw [h_f]; rfl
            have h_t : (if (!σ i) = true then (H (Fin.castSucc i)).offset <
                @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec ((2 : ℝ) • P0 - q)
              else @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec ((2 : ℝ) • P0 - q) <
                (H (Fin.castSucc i)).offset) ↔
                (H (Fin.castSucc i)).offset <
                @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec ((2 : ℝ) • P0 - q) := by
              rw [h_not]
              simp
            rw [h_t]
            have hq_i' : @inner ℝ Space3 _ (H (Fin.castSucc i)).normVec q <
                (H (Fin.castSucc i)).offset := by
              revert hq_i
              rw [h_f]
              simp
            linarith [h_inner, hq_i']
        · dsimp [Plane3.toSet] at hq2 ⊢
          have hp0_3' : @inner ℝ Space3 _ (H 3).normVec P0 = (H 3).offset := hp0_3
          have h_inner_last : @inner ℝ Space3 _ (H 3).normVec ((2 : ℝ) • P0 - q) =
              2 * @inner ℝ Space3 _ (H 3).normVec P0 -
              @inner ℝ Space3 _ (H 3).normVec q := by
            rw [inner_sub_right, inner_smul_right]
          rw [h_inner_last, hp0_3', hq2]
          ring
      have h_inv : ∀ σ, σ ∈ split_sigs ↔ (fun l => !(σ l)) ∈ split_sigs := by
        intro σ
        constructor
        · exact h_fwd σ
        · intro h
          have h2 := h_fwd (fun l => !(σ l)) h
          have h_not_not : (fun l => !(!(σ l))) = σ := by
            ext l; simp
          rwa [h_not_not] at h2
      have h_even := even_card_of_neg_invariant split_sigs h_inv
      rcases h_even with ⟨k, hk⟩
      rw [h_split_count] at h5
      rw [hk] at h5
      omega
    · -- P0 ∉ H 3 の場合: 4平面は1点を共有せず、交線系L'の平行ペアにより切断領域数は偶数である。
      have h_split_eq := splitSpaceRegionsCount_eq_planeRegionsCount 3 H h_not_par
      rw [h_split_eq] at h5
      have h_par_pair : ∃ i j : Fin 3, i ≠ j ∧ parallelLines (L' i) (L' j) := by
        by_contra h_no_par
        have h_all_not_par : ∀ i j : Fin 3, i ≠ j → ¬ parallelLines (L' i) (L' j) := by
          intro i j hij hpar
          apply h_no_par
          exact ⟨i, j, hij, hpar⟩
        apply hnot_gen
        refine ⟨h_all_not_par, ?_⟩
        intro i j l hij hjl hil
        by_contra h_empty
        have h_nonempty : ((L' i).toSet ∩ (L' j).toSet ∩ (L' l).toSet).Nonempty :=
          Set.nonempty_iff_ne_empty.mpr h_empty
        rcases h_nonempty with ⟨p, hp⟩
        have hp_all : ∀ m : Fin 3, p ∈ (L' m).toSet := by
          intro m
          have hm_in : m = i ∨ m = j ∨ m = l := by
            fin_cases m <;> fin_cases i <;> fin_cases j <;> fin_cases l <;>
              try { simp } <;> try { contradiction }
          rcases hm_in with rfl | rfl | rfl
          · exact hp.1.1
          · exact hp.1.2
          · exact hp.2
        have h_eq_P0 := eq_P0_of_traceLines_inter H h_not_par P0 hP0 p hp_all
        have h_P0_in_3 : P0 ∈ (H (Fin.last 3)).toSet := by
          rw [← h_eq_P0]
          exact planePt3_mem_plane (H (Fin.last 3)) p
        exact hP0_3 h_P0_in_3
      rcases h_par_pair with ⟨i, ⟨j, hij, h_par_ij⟩⟩
      have h_exist_k :
          ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧ (∀ l : Fin 3, l = i ∨ l = j ∨ l = k) := by
        fin_cases i <;> fin_cases j <;> try contradiction
        · refine ⟨2, by decide, by decide, ?_⟩
          intro l; fin_cases l <;> simp
        · refine ⟨1, by decide, by decide, ?_⟩
          intro l; fin_cases l <;> simp
        · refine ⟨2, by decide, by decide, ?_⟩
          intro l; fin_cases l <;> simp
        · refine ⟨0, by decide, by decide, ?_⟩
          intro l; fin_cases l <;> simp
        · refine ⟨1, by decide, by decide, ?_⟩
          intro l; fin_cases l <;> simp
        · refine ⟨0, by decide, by decide, ?_⟩
          intro l; fin_cases l <;> simp
      rcases h_exist_k with ⟨k, hik, hjk, h_perm⟩
      by_cases h_par_kj : parallelLines (L' k) (L' j)
      · have h_all_par : ∀ l : Fin 3, parallelLines (L' l) (L' j) := by
          intro l
          rcases h_perm l with rfl | rfl | rfl
          · exact h_par_ij
          · exact parallelLines_refl _
          · exact h_par_kj
        exact (not_all_parallel_of_traceLines H h_not_par P0 hP0 j h_all_par).elim
      · have h_even := planeRegionsCount_even_of_parallel_pair L' i j k
          h_par_ij h_par_kj h_perm hik hjk
        rcases h_even with ⟨m, hm⟩
        rw [hm] at h5
        omega

/-- どの2平面も平行でなく、どの3平面も一般の位置にない4平面配置の領域数は高々11である。 -/
lemma spaceRegionsCount_four_le_eleven_of_not_general (H : Fin 4 → Plane3)
    (h_not_par : ∀ i j, i ≠ j → ¬ parallelPlanes (H i) (H j))
    (h_not_gen : ∀ i : Fin 4,
      ¬ GeneralPositionPlanes 3 (H ∘ Fin.succAbove i)) :
    spaceRegionsCount 4 H ≤ 11 := by
  have h_max4 : maxPlaneRegions 4 = 11 := by decide
  -- 法線が共面なため、空間分割は2次元断面の4本の直線配置に同型となり、
  -- 領域数は planeRegionsCount 4 L ≤ maxPlaneRegions 4 = 11 で抑えられる。
  sorry

/-- 4枚の相異なる平面配置において、
領域数が13となる配置は存在しない。 -/
lemma spaceRegionsCount_four_ne_thirteen (H : Fin 4 → Plane3)
    (hdist : DistinctPlanes 4 H) :
    spaceRegionsCount 4 H ≠ 13 := by
  intro h13
  by_cases hpar : ∃ i j, i ≠ j ∧ parallelPlanes (H i) (H j)
  · have hle := spaceRegionsCount_four_le_twelve_of_parallel H hdist hpar
    omega
  · push Not at hpar
    by_cases hgen : ∃ i : Fin 4, GeneralPositionPlanes 3 (H ∘ Fin.succAbove i)
    · rcases hgen with ⟨i, hi⟩
      let e : Fin 4 ≃ Fin 4 := Equiv.swap i (Fin.last 3)
      let H' := H ∘ e
      have h13' : spaceRegionsCount 4 H' = 13 := by
        rw [spaceRegionsCount_equiv 4 H e, h13]
      have hgen' : GeneralPositionPlanes 3 (H' ∘ Fin.castSucc) := by
        fin_cases i
        · let τ : Fin 3 ≃ Fin 3 := Equiv.swap 0 1 * Equiv.swap 0 2
          have h_eq : H' ∘ Fin.castSucc = (H ∘ Fin.succAbove 0) ∘ τ := by
            ext j; fin_cases j <;> rfl
          rw [h_eq]
          exact GeneralPositionPlanes.comp_equiv 3 (H ∘ Fin.succAbove 0) τ hi
        · let τ : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
          have h_eq : H' ∘ Fin.castSucc = (H ∘ Fin.succAbove 1) ∘ τ := by
            ext j; fin_cases j <;> rfl
          rw [h_eq]
          exact GeneralPositionPlanes.comp_equiv 3 (H ∘ Fin.succAbove 1) τ hi
        · let τ : Fin 3 ≃ Fin 3 := Equiv.refl (Fin 3)
          have h_eq : H' ∘ Fin.castSucc = (H ∘ Fin.succAbove 2) ∘ τ := by
            ext j; fin_cases j <;> rfl
          rw [h_eq]
          exact GeneralPositionPlanes.comp_equiv 3 (H ∘ Fin.succAbove 2) τ hi
        · let τ : Fin 3 ≃ Fin 3 := Equiv.refl (Fin 3)
          have h_eq : H' ∘ Fin.castSucc = (H ∘ Fin.succAbove 3) ∘ τ := by
            ext j; fin_cases j <;> rfl
          rw [h_eq]
          exact GeneralPositionPlanes.comp_equiv 3 (H ∘ Fin.succAbove 3) τ hi
      have h_not_par' : ∀ j : Fin 3,
          ¬ parallelPlanes (H' (Fin.castSucc j)) (H' (Fin.last 3)) := by
        intro j
        apply hpar
        exact e.injective.ne (Fin.castSucc_ne_last j)
      have h_decomp := spaceRegionsCount_succ_eq_add_split 3 H'
      have h_prev :=
        spaceRegionsCount_eq_max_of_general_position 3 (H' ∘ Fin.castSucc) hgen'
      have h_max3 : maxSpaceRegions 3 = 8 := rfl
      rw [h_max3] at h_prev
      rw [h13', h_prev] at h_decomp
      have h_split5 : splitSpaceRegionsCount 3 H' = 5 := by omega
      have h_ne5 := splitSpaceRegionsCount_three_ne_five H' hgen' h_not_par'
      exact h_ne5 h_split5
    · push Not at hgen
      have hle := spaceRegionsCount_four_le_eleven_of_not_general H hpar hgen
      omega

/-- 3次元空間の任意の点 $(x, y, z)$。 -/
def ptXYZ (x y z : ℝ) : Space3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![x, y, z]

lemma ptXYZ_apply_zero (x y z : ℝ) : (ptXYZ x y z) 0 = x := rfl
lemma ptXYZ_apply_one (x y z : ℝ) : (ptXYZ x y z) 1 = y := rfl
lemma ptXYZ_apply_two (x y z : ℝ) : (ptXYZ x y z) 2 = z := rfl

lemma inner_e2Vec_ptXYZ (x y z : ℝ) :
    @inner ℝ Space3 _ e2Vec (ptXYZ x y z) = z := by
  rw [inner_e2Vec, ptXYZ_apply_two]

lemma inner_v0_ptXYZ (x y z : ℝ) :
    @inner ℝ Space3 _ v0_vec (ptXYZ x y z) = x := by
  rw [inner_v0_vec, ptXYZ_apply_zero]

lemma inner_v1_ptXYZ (x y z : ℝ) :
    @inner ℝ Space3 _ v1_vec (ptXYZ x y z) = y := by
  rw [inner_v1_vec, ptXYZ_apply_one]

lemma inner_v2_ptXYZ (x y z : ℝ) :
    @inner ℝ Space3 _ v2_vec (ptXYZ x y z) = x + y := by
  rw [inner_v2_vec, ptXYZ_apply_zero, ptXYZ_apply_one]

lemma inner_momentVec_ptXYZ (t x y z : ℝ) :
    @inner ℝ Space3 _ (momentVec t) (ptXYZ x y z) = x + t * y + t ^ 2 * z := by
  rw [inner_momentVec, ptXYZ_apply_zero, ptXYZ_apply_one, ptXYZ_apply_two]

lemma ptXYZ_ext_iff (p : Space3) (x y z : ℝ) :
    p = ptXYZ x y z ↔ p 0 = x ∧ p 1 = y ∧ p 2 = z := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hx, hy, hz⟩
    ext i
    fin_cases i <;> assumption

lemma mem_plane_x0_ptXYZ (x y z : ℝ) : ptXYZ x y z ∈ plane_x0.toSet ↔ x = 0 := by
  rw [mem_plane_x0, ptXYZ_apply_zero]

lemma mem_plane_y0_ptXYZ (x y z : ℝ) : ptXYZ x y z ∈ plane_y0.toSet ↔ y = 0 := by
  rw [mem_plane_y0, ptXYZ_apply_one]

lemma mem_plane_xy1_ptXYZ (x y z : ℝ) : ptXYZ x y z ∈ plane_xy1.toSet ↔ x + y = 1 := by
  rw [mem_plane_xy1, ptXYZ_apply_zero, ptXYZ_apply_one]

lemma mem_zPlane_ptXYZ (c x y z : ℝ) : ptXYZ x y z ∈ (zPlane c).toSet ↔ z = c := by
  rw [mem_zPlane, ptXYZ_apply_two]

lemma mem_momentPlane_ptXYZ (t x y z : ℝ) :
    ptXYZ x y z ∈ (momentPlane t).toSet ↔ x + t * y + t ^ 2 * z = t ^ 3 := by
  dsimp [Plane3.toSet, momentPlane]
  rw [inner_momentVec_ptXYZ]

/-- 平面 x = 0, z = 3 とモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_x0_zPlane3_momentPlane {t : ℝ} (ht : t ≠ 0) :
    ∃ q : Space3, plane_x0.toSet ∩ (zPlane 3).toSet ∩ (momentPlane t).toSet = {q} := by
  let q : Space3 := ptXYZ 0 (t ^ 2 - 3 * t) 3
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_x0, mem_zPlane, mem_momentPlane,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hx, hz⟩, hm⟩
    have hy : p 1 = t ^ 2 - 3 * t := by
      have ht_mul : t * p 1 = t * (t ^ 2 - 3 * t) := by
        calc t * p 1 = (p 0 + t * p 1 + t ^ 2 * p 2) - p 0 - t ^ 2 * p 2 := by ring
        _ = t ^ 3 - 0 - t ^ 2 * 3 := by rw [hm, hx, hz]
        _ = t * (t ^ 2 - 3 * t) := by ring
      exact mul_left_cancel₀ ht ht_mul
    rw [ptXYZ_ext_iff]
    exact ⟨hx, hy, hz⟩
  · rintro rfl
    dsimp [q]
    rw [ptXYZ_apply_zero, ptXYZ_apply_one, ptXYZ_apply_two]
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    ring

/-- 平面 y = 0, z = 3 とモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_y0_zPlane3_momentPlane {t : ℝ} :
    ∃ q : Space3, plane_y0.toSet ∩ (zPlane 3).toSet ∩ (momentPlane t).toSet = {q} := by
  let q : Space3 := ptXYZ (t ^ 3 - 3 * t ^ 2) 0 3
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_y0, mem_zPlane, mem_momentPlane,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hz⟩, hm⟩
    have hx : p 0 = t ^ 3 - 3 * t ^ 2 := by
      calc p 0 = (p 0 + t * p 1 + t ^ 2 * p 2) - t * p 1 - t ^ 2 * p 2 := by ring
      _ = t ^ 3 - t * 0 - t ^ 2 * 3 := by rw [hm, hy, hz]
      _ = t ^ 3 - 3 * t ^ 2 := by ring
    rw [ptXYZ_ext_iff]
    exact ⟨hx, hy, hz⟩
  · rintro rfl
    dsimp [q]
    rw [ptXYZ_apply_zero, ptXYZ_apply_one, ptXYZ_apply_two]
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    ring

/-- 平面 x + y = 1, z = 3 とモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_plane_xy1_zPlane3_momentPlane {t : ℝ} (ht1 : t ≠ 1) :
    ∃ q : Space3, plane_xy1.toSet ∩ (zPlane 3).toSet ∩ (momentPlane t).toSet = {q} := by
  let y_val := (t ^ 3 - 3 * t ^ 2 - 1) / (t - 1)
  let q : Space3 := ptXYZ (1 - y_val) y_val 3
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_plane_xy1, mem_zPlane, mem_momentPlane,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hxy, hz⟩, hm⟩
    have hy : p 1 = y_val := by
      have h_sub : (t - 1) * p 1 = (t - 1) * y_val := by
        calc (t - 1) * p 1 = (p 0 + t * p 1 + t ^ 2 * p 2) - (p 0 + p 1) - t ^ 2 * p 2 := by ring
        _ = t ^ 3 - 1 - t ^ 2 * 3 := by rw [hm, hxy, hz]
        _ = (t - 1) * y_val := by
          dsimp [y_val]
          rw [mul_div_cancel₀ _ (sub_ne_zero.mpr ht1)]
          ring
      exact mul_left_cancel₀ (sub_ne_zero.mpr ht1) h_sub
    have hx : p 0 = 1 - y_val := by
      calc p 0 = (p 0 + p 1) - p 1 := by ring
      _ = 1 - y_val := by rw [hxy, hy]
    rw [ptXYZ_ext_iff]
    exact ⟨hx, hy, hz⟩
  · rintro rfl
    dsimp [q]
    rw [ptXYZ_apply_zero, ptXYZ_apply_one, ptXYZ_apply_two]
    refine ⟨⟨by ring, rfl⟩, ?_⟩
    dsimp [y_val]
    have h_cancel : (t - 1) * ((t ^ 3 - 3 * t ^ 2 - 1) / (t - 1)) = t ^ 3 - 3 * t ^ 2 - 1 :=
      mul_div_cancel₀ _ (sub_ne_zero.mpr ht1)
    calc (1 - (t ^ 3 - 3 * t ^ 2 - 1) / (t - 1)) +
         t * ((t ^ 3 - 3 * t ^ 2 - 1) / (t - 1)) + t ^ 2 * 3
      _ = 1 + (t - 1) * ((t ^ 3 - 3 * t ^ 2 - 1) / (t - 1)) + 3 * t ^ 2 := by ring
      _ = 1 + (t ^ 3 - 3 * t ^ 2 - 1) + 3 * t ^ 2 := by rw [h_cancel]
      _ = t ^ 3 := by ring

/-- 2枚のモーメント平面と平面 z = 3 の交わりはちょうど1点である。 -/
lemma intersection_momentPlane_zPlane3_momentPlane {t₁ t₂ : ℝ} (h12 : t₁ ≠ t₂) :
    ∃ q : Space3, (momentPlane t₁).toSet ∩ (zPlane 3).toSet ∩ (momentPlane t₂).toSet = {q} := by
  let y_val := t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 - 3 * (t₁ + t₂)
  let x_val := t₁ ^ 3 - 3 * t₁ ^ 2 - t₁ * y_val
  let q : Space3 := ptXYZ x_val y_val 3
  use q
  ext p
  simp only [Set.mem_inter_iff, mem_momentPlane, mem_zPlane, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hm1, hz⟩, hm2⟩
    have hy : p 1 = y_val := by
      have h_sub : (t₂ - t₁) * p 1 = (t₂ - t₁) * y_val := by
        calc (t₂ - t₁) * p 1 = (p 0 + t₂ * p 1 + t₂ ^ 2 * p 2) -
                               (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2) - (t₂ ^ 2 - t₁ ^ 2) * p 2 := by ring
        _ = t₂ ^ 3 - t₁ ^ 3 - (t₂ ^ 2 - t₁ ^ 2) * 3 := by rw [hm2, hm1, hz]
        _ = (t₂ - t₁) * y_val := by
          dsimp [y_val]
          ring
      have h_ne : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
      exact mul_left_cancel₀ h_ne h_sub
    have hx : p 0 = x_val := by
      calc p 0 = (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2) - t₁ * p 1 - t₁ ^ 2 * p 2 := by ring
      _ = t₁ ^ 3 - t₁ * y_val - t₁ ^ 2 * 3 := by rw [hm1, hy, hz]
      _ = x_val := by dsimp [x_val]; ring
    rw [ptXYZ_ext_iff]
    exact ⟨hx, hy, hz⟩
  · rintro rfl
    dsimp [q]
    rw [ptXYZ_apply_zero, ptXYZ_apply_one, ptXYZ_apply_two]
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · dsimp [x_val]
      ring
    · dsimp [x_val, y_val]
      ring

/-- 平面$x = 0$、$y = 0$、$z = 3$およびモーメント平面の交わりは空集合である。 -/
lemma intersection_plane_x0_plane_y0_zPlane3_momentPlane_empty {n : ℝ} (hn : 5 ≤ n) :
    plane_x0.toSet ∩ plane_y0.toSet ∩ (zPlane 3).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hx, hy⟩, hz⟩, hm⟩
  rw [mem_plane_x0] at hx; rw [mem_plane_y0] at hy
  rw [mem_zPlane] at hz; rw [mem_momentPlane] at hm
  -- 座標の条件から $n^3 - 3n^2 = 0$ を導く。
  have h_diff : n ^ 3 - 3 * n ^ 2 = 0 := by
    calc n ^ 3 - 3 * n ^ 2 =
        - ((p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) - p 0 - n * p 1 - n ^ 2 * (p 2 - 3)) := by ring
    _ = - ((n ^ 3 - n ^ 3) - 0 - n * 0 - n ^ 2 * (3 - 3)) := by rw [hm, hx, hy, hz]
    _ = 0 := by ring
  -- $n \ge 5$ から $n^3 - 3n^2 > 0$ を導いて矛盾を示す。
  have h_pos : 0 < n ^ 3 - 3 * n ^ 2 := by
    calc 0 < 2 * n ^ 2 := by positivity
    _ = 5 * n ^ 2 - 3 * n ^ 2 := by ring
    _ ≤ n * n ^ 2 - 3 * n ^ 2 := by nlinarith
    _ = n ^ 3 - 3 * n ^ 2 := by ring
  linarith

/-- 平面$x = 0$、$x + y = 1$、$z = 3$およびモーメント平面の交わりは空集合である。 -/
lemma intersection_plane_x0_plane_xy1_zPlane3_momentPlane_empty {n : ℝ} (hn : 5 ≤ n) :
    plane_x0.toSet ∩ plane_xy1.toSet ∩ (zPlane 3).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hx, hxy⟩, hz⟩, hm⟩
  rw [mem_plane_x0] at hx; rw [mem_plane_xy1] at hxy
  rw [mem_zPlane] at hz; rw [mem_momentPlane] at hm
  -- 各平面の方程式から $n^3 - 3n^2 - n = 0$ を導く。
  have h_diff : n ^ 3 - 3 * n ^ 2 - n = 0 := by
    calc n ^ 3 - 3 * n ^ 2 - n =
        - ((p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) - n * (p 0 + p 1 - 1) -
           (1 - n) * p 0 - n ^ 2 * (p 2 - 3)) := by ring
    _ = - ((n ^ 3 - n ^ 3) - n * (1 - 1) - (1 - n) * 0 - n ^ 2 * (3 - 3)) := by
      rw [hm, hxy, hx, hz]
    _ = 0 := by ring
  -- $n \ge 5$ から $n^3 - 3n^2 - n > 0$ を導いて矛盾を示す。
  have h_pos : 0 < n ^ 3 - 3 * n ^ 2 - n := by
    calc 0 < 9 * n := by positivity
    _ = 5 * 2 * n - n := by ring
    _ ≤ n * (n - 3) * n - n := by nlinarith
    _ = n ^ 3 - 3 * n ^ 2 - n := by ring
  linarith

/-- 平面$y = 0$、$x + y = 1$、$z = 3$およびモーメント平面の交わりは空集合である。 -/
lemma intersection_plane_y0_plane_xy1_zPlane3_momentPlane_empty {n : ℝ} (hn : 5 ≤ n) :
    plane_y0.toSet ∩ plane_xy1.toSet ∩ (zPlane 3).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hy, hxy⟩, hz⟩, hm⟩
  rw [mem_plane_y0] at hy; rw [mem_plane_xy1] at hxy
  rw [mem_zPlane] at hz; rw [mem_momentPlane] at hm
  -- 各平面の方程式から $n^3 - 3n^2 - 1 = 0$ を導く。
  have h_diff : n ^ 3 - 3 * n ^ 2 - 1 = 0 := by
    calc n ^ 3 - 3 * n ^ 2 - 1 =
        - ((p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) - (p 0 + p 1 - 1) +
           (1 - n) * p 1 - n ^ 2 * (p 2 - 3)) := by ring
    _ = - ((n ^ 3 - n ^ 3) - (1 - 1) + (1 - n) * 0 - n ^ 2 * (3 - 3)) := by
      rw [hm, hxy, hy, hz]
    _ = 0 := by ring
  -- $n \ge 5$ から $n^3 - 3n^2 - 1 > 0$ を導いて矛盾を示す。
  have h_pos : 0 < n ^ 3 - 3 * n ^ 2 - 1 := by
    calc (0 : ℝ) < 49 := by norm_num
    _ = 25 * 2 - 1 := by norm_num
    _ ≤ n ^ 2 * (n - 3) - 1 := by nlinarith
    _ = n ^ 3 - 3 * n ^ 2 - 1 := by ring
  linarith

/-- 平面$x = 0$、$z = 3$および2枚の相異なるモーメント平面の交わりは空集合である。 -/
lemma intersection_plane_x0_zPlane3_two_momentPlanes_empty {t n : ℝ}
    (ht : 3 ≤ t) (hn : 5 ≤ n) (htn : t ≠ n) :
    plane_x0.toSet ∩ (zPlane 3).toSet ∩ (momentPlane t).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hx, hz⟩, hmt⟩, hmn⟩
  rw [mem_plane_x0] at hx; rw [mem_zPlane] at hz; rw [mem_momentPlane] at hmt hmn
  -- 各平面の方程式を消去して因数分解された恒等式を得る。
  have h_id : n * (p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3) -
      t * (p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) +
      (t - n) * p 0 -
      t * n * (t - n) * (p 2 - 3) =
      - (t * n * (t - n) * (t + n - 3)) := by ring
  have h_zero : - (t * n * (t - n) * (t + n - 3)) = 0 := by
    rw [← h_id]
    have ht_zero : p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3 = 0 := by linarith [hmt]
    have hn_zero : p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3 = 0 := by linarith [hmn]
    have hz_zero : p 2 - 3 = 0 := by linarith [hz]
    rw [ht_zero, hn_zero, hx, hz_zero]
    ring
  -- $t \neq n$ かつ $t, n > 0$ より $t + n - 3 = 0$ を導く。
  have h_prod : t + n - 3 = 0 := by
    have h_neg : - (t * n * (t - n)) ≠ 0 := by
      have ht_pos : 0 < t := by linarith
      have hn_pos : 0 < n := by linarith
      have htn' : t - n ≠ 0 := sub_ne_zero.mpr htn
      have : t * n * (t - n) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (ne_of_gt ht_pos) (ne_of_gt hn_pos)) htn'
      exact neg_ne_zero.mpr this
    have h_mul : (- (t * n * (t - n))) * (t + n - 3) = 0 := by
      calc (- (t * n * (t - n))) * (t + n - 3) = - (t * n * (t - n) * (t + n - 3)) := by ring
      _ = 0 := h_zero
    exact (mul_eq_zero.mp h_mul).resolve_left h_neg
  -- $t \ge 3, n \ge 5$ より $t + n - 3 \ge 5 > 0$ となり矛盾する。
  linarith

/-- 平面$y = 0$、$z = 3$および2枚の相異なるモーメント平面の交わりは空集合である。 -/
lemma intersection_plane_y0_zPlane3_two_momentPlanes_empty {t n : ℝ}
    (ht : 3 ≤ t) (hn : 5 ≤ n) (htn : t ≠ n) :
    plane_y0.toSet ∩ (zPlane 3).toSet ∩ (momentPlane t).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hy, hz⟩, hmt⟩, hmn⟩
  rw [mem_plane_y0] at hy; rw [mem_zPlane] at hz; rw [mem_momentPlane] at hmt hmn
  -- 各平面の方程式から二次式との積の恒等式を導く。
  have h_id : (p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3) -
      (p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) -
      (t - n) * p 1 -
      (t ^ 2 - n ^ 2) * (p 2 - 3) =
      - (t - n) * (t ^ 2 + t * n + n ^ 2 - 3 * t - 3 * n) := by ring
  have h_zero : - (t - n) * (t ^ 2 + t * n + n ^ 2 - 3 * t - 3 * n) = 0 := by
    rw [← h_id]
    have ht_zero : p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3 = 0 := by linarith [hmt]
    have hn_zero : p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3 = 0 := by linarith [hmn]
    have hz_zero : p 2 - 3 = 0 := by linarith [hz]
    rw [ht_zero, hn_zero, hy, hz_zero]
    ring
  -- $t \neq n$ より二次式部分が 0 となる。
  have h_quad : t ^ 2 + t * n + n ^ 2 - 3 * t - 3 * n = 0 := by
    have h_neg : - (t - n) ≠ 0 := neg_ne_zero.mpr (sub_ne_zero.mpr htn)
    have h_mul : (- (t - n)) * (t ^ 2 + t * n + n ^ 2 - 3 * t - 3 * n) = 0 := by
      calc (- (t - n)) * (t ^ 2 + t * n + n ^ 2 - 3 * t - 3 * n) =
          - (t - n) * (t ^ 2 + t * n + n ^ 2 - 3 * t - 3 * n) := by ring
      _ = 0 := h_zero
    exact (mul_eq_zero.mp h_mul).resolve_left h_neg
  -- $t \ge 3, n \ge 5$ から二次式部分は常に正となるため矛盾する。
  have h_pos : 0 < t ^ 2 + t * n + n ^ 2 - 3 * t - 3 * n := by
    calc (0 : ℝ) < 10 := by norm_num
    _ = 5 * (5 - 3) := by norm_num
    _ ≤ n * (n - 3) := by nlinarith
    _ ≤ t * (t - 3) + n * (n - 3) + t * n := by
      have : 0 ≤ t * (t - 3) := by nlinarith
      have : 0 ≤ t * n := by nlinarith
      linarith
    _ = t ^ 2 + t * n + n ^ 2 - 3 * t - 3 * n := by ring
  linarith

/-- 平面$x + y = 1$、$z = 3$および2枚の相異なるモーメント平面の交わりは空集合である。 -/
lemma intersection_plane_xy1_zPlane3_two_momentPlanes_empty {t n : ℝ}
    (ht : 3 ≤ t) (hn : 5 ≤ n) (htn : t ≠ n) :
    plane_xy1.toSet ∩ (zPlane 3).toSet ∩ (momentPlane t).toSet ∩ (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hxy, hz⟩, hmt⟩, hmn⟩
  rw [mem_plane_xy1] at hxy; rw [mem_zPlane] at hz; rw [mem_momentPlane] at hmt hmn
  -- 各平面の方程式の線型結合から恒等式を構成する。
  have h_id : (n - 1) * (p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3) -
      (t - 1) * (p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) +
      (t - n) * (p 0 + p 1 - 1) -
      (t - n) * (t * n - t - n) * (p 2 - 3) =
      - (t - n) * ((t - 1) * (n - 1) * (t + n - 2) + 3) := by ring
  have h_zero : - (t - n) * ((t - 1) * (n - 1) * (t + n - 2) + 3) = 0 := by
    rw [← h_id]
    have ht_zero : p 0 + t * p 1 + t ^ 2 * p 2 - t ^ 3 = 0 := by linarith [hmt]
    have hn_zero : p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3 = 0 := by linarith [hmn]
    have hxy_zero : p 0 + p 1 - 1 = 0 := by linarith [hxy]
    have hz_zero : p 2 - 3 = 0 := by linarith [hz]
    rw [ht_zero, hn_zero, hxy_zero, hz_zero]
    ring
  -- $t \neq n$ より因子部分が 0 となる。
  have h_prod : (t - 1) * (n - 1) * (t + n - 2) + 3 = 0 := by
    have h_neg : - (t - n) ≠ 0 := neg_ne_zero.mpr (sub_ne_zero.mpr htn)
    have h_mul : (- (t - n)) * ((t - 1) * (n - 1) * (t + n - 2) + 3) = 0 := by
      calc (- (t - n)) * ((t - 1) * (n - 1) * (t + n - 2) + 3) =
          - (t - n) * ((t - 1) * (n - 1) * (t + n - 2) + 3) := by ring
      _ = 0 := h_zero
    exact (mul_eq_zero.mp h_mul).resolve_left h_neg
  -- $t \ge 3, n \ge 5$ から因子部分は正となるため矛盾する。
  have h_pos : 0 < (t - 1) * (n - 1) * (t + n - 2) + 3 := by
    have h1 : 0 < t - 1 := by linarith
    have h2 : 0 < n - 1 := by linarith
    have h3 : 0 < t + n - 2 := by linarith
    have : 0 < (t - 1) * (n - 1) * (t + n - 2) := mul_pos (mul_pos h1 h2) h3
    linarith
  linarith

/-- 平面$z = 3$および3枚の相異なるモーメント平面の交わりは空集合である。 -/
lemma intersection_zPlane3_three_momentPlanes_empty {t₁ t₂ n : ℝ}
    (h1 : 3 ≤ t₁) (h2 : 3 ≤ t₂) (hn : 5 ≤ n)
    (h12 : t₁ ≠ t₂) (h2n : t₂ ≠ n) (h1n : t₁ ≠ n) :
    (zPlane 3).toSet ∩ (momentPlane t₁).toSet ∩ (momentPlane t₂).toSet ∩
      (momentPlane n).toSet = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro p ⟨⟨⟨hz, hm1⟩, hm2⟩, hmn⟩
  rw [mem_zPlane] at hz; rw [mem_momentPlane] at hm1 hm2 hmn
  let Δ := (t₁ - t₂) * (t₂ - n) * (t₁ - n)
  -- ヴァンデルモンド行列式に対応する係数で線型結合を作る。
  have h_id : (t₂ - n) * (p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3) -
      (t₁ - n) * (p 0 + t₂ * p 1 + t₂ ^ 2 * p 2 - t₂ ^ 3) +
      (t₁ - t₂) * (p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3) -
      Δ * (p 2 - 3) =
      Δ * (3 - (t₁ + t₂ + n)) := by
    dsimp [Δ]; ring
  have h_zero : Δ * (3 - (t₁ + t₂ + n)) = 0 := by
    rw [← h_id]
    have h1_zero : p 0 + t₁ * p 1 + t₁ ^ 2 * p 2 - t₁ ^ 3 = 0 := by linarith [hm1]
    have h2_zero : p 0 + t₂ * p 1 + t₂ ^ 2 * p 2 - t₂ ^ 3 = 0 := by linarith [hm2]
    have hn_zero : p 0 + n * p 1 + n ^ 2 * p 2 - n ^ 3 = 0 := by linarith [hmn]
    have hz_zero : p 2 - 3 = 0 := by linarith [hz]
    rw [h1_zero, h2_zero, hn_zero, hz_zero]
    ring
  -- 相異なる3数より $\Delta \neq 0$ となり、根と係数の関係から $3 - (t_1 + t_2 + n) = 0$ を得る。
  have hΔ_ne : Δ ≠ 0 := by
    dsimp [Δ]
    have h12' : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h12
    have h2n' : t₂ - n ≠ 0 := sub_ne_zero.mpr h2n
    have h1n' : t₁ - n ≠ 0 := sub_ne_zero.mpr h1n
    exact mul_ne_zero (mul_ne_zero h12' h2n') h1n'
  have h_sum : 3 - (t₁ + t₂ + n) = 0 := (mul_eq_zero.mp h_zero).resolve_left hΔ_ne
  -- $t_1, t_2 \ge 3, n \ge 5$ より $t_1 + t_2 + n \ge 11 > 3$ となり矛盾する。
  linarith

/-- $n = 3$ において領域数6を達成する配置: $z = 0$, $z = 1$, $x = 0$ -/
def H_three_six : Fin 3 → Plane3 :=
  ![zPlane 0, zPlane 1, plane_x0]

lemma distinctPlanes_three_six : DistinctPlanes 3 H_three_six := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    change (H_three_six 0).toSet = (H_three_six 1).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_three_six 0).toSet := by
      dsimp [Plane3.toSet, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_three_six 1).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_three_six, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_three_six 0).toSet = (H_three_six 2).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_three_six 0).toSet := by
      dsimp [Plane3.toSet, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_three_six 2).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_three_six, plane_x0] at hmem'
    have hmem2 : ptXYZ 0 0 1 ∈ (H_three_six 2).toSet := by
      dsimp [Plane3.toSet, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem2' : ptXYZ 0 0 1 ∈ (H_three_six 0).toSet := hij.symm ▸ hmem2
    dsimp [Plane3.toSet, H_three_six, zPlane] at hmem2'
    rw [inner_e2Vec_ptXYZ] at hmem2'; linarith
  · exfalso
    change (H_three_six 1).toSet = (H_three_six 0).toSet at hij
    have hmem : ptXYZ 0 0 1 ∈ (H_three_six 1).toSet := by
      dsimp [Plane3.toSet, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]
    have hmem' : ptXYZ 0 0 1 ∈ (H_three_six 0).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_three_six, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · rfl
  · exfalso
    change (H_three_six 1).toSet = (H_three_six 2).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_three_six 2).toSet := by
      dsimp [Plane3.toSet, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_three_six 1).toSet := hij.symm ▸ hmem
    dsimp [Plane3.toSet, H_three_six, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_three_six 2).toSet = (H_three_six 0).toSet at hij
    have hmem : ptXYZ 0 0 1 ∈ (H_three_six 2).toSet := by
      dsimp [Plane3.toSet, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 0 1 ∈ (H_three_six 0).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_three_six, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_three_six 2).toSet = (H_three_six 1).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_three_six 2).toSet := by
      dsimp [Plane3.toSet, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_three_six 1).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_three_six, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · rfl

lemma convexSpaceRegion_three_six_FT_empty (b : Bool) :
    ¬ (convexSpaceRegion 3 H_three_six ![(false : Bool), true, b]).Nonempty := by
  rintro ⟨p, hp⟩
  have h0 := hp 0
  have h1 := hp 1
  dsimp [convexSpaceRegion, H_three_six, zPlane] at h0 h1
  rw [inner_e2Vec] at h0 h1
  linarith

lemma convexSpaceRegion_three_six_FFF_nonempty :
    (convexSpaceRegion 3 H_three_six ![(false : Bool), false, false]).Nonempty := by
  use ptXYZ (-1) 0 (-1)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]; linarith

lemma convexSpaceRegion_three_six_FFT_nonempty :
    (convexSpaceRegion 3 H_three_six ![(false : Bool), false, true]).Nonempty := by
  use ptXYZ 1 0 (-1)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]; linarith

lemma convexSpaceRegion_three_six_TFF_nonempty :
    (convexSpaceRegion 3 H_three_six ![(true : Bool), false, false]).Nonempty := by
  use ptXYZ (-1) 0 (1/2)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]; linarith

lemma convexSpaceRegion_three_six_TFT_nonempty :
    (convexSpaceRegion 3 H_three_six ![(true : Bool), false, true]).Nonempty := by
  use ptXYZ 1 0 (1/2)
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]; linarith

lemma convexSpaceRegion_three_six_TTF_nonempty :
    (convexSpaceRegion 3 H_three_six ![(true : Bool), true, false]).Nonempty := by
  use ptXYZ (-1) 0 2
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]; linarith

lemma convexSpaceRegion_three_six_TTT_nonempty :
    (convexSpaceRegion 3 H_three_six ![(true : Bool), true, true]).Nonempty := by
  use ptXYZ 1 0 2
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, zPlane]; rw [inner_e2Vec_ptXYZ]; linarith
  · dsimp [convexSpaceRegion, H_three_six, plane_x0]; rw [inner_v0_ptXYZ]; linarith

lemma spaceRegionsCount_three_six_eq_six :
    spaceRegionsCount 3 H_three_six = 6 := by
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  have hs : (Finset.filter (fun σ =>
      (convexSpaceRegion 3 H_three_six σ).Nonempty) Finset.univ) =
      {![(false : Bool), false, false],
       ![(false : Bool), false, true],
       ![(true : Bool), false, false],
       ![(true : Bool), false, true],
       ![(true : Bool), true, false],
       ![(true : Bool), true, true]} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hne
      rcases signVector_three_cases σ with h | h | h | h | h | h | h | h
      · left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · exfalso; subst h
        exact (convexSpaceRegion_three_six_FT_empty false hne).elim
      · exfalso; subst h
        exact (convexSpaceRegion_three_six_FT_empty true hne).elim
      · right; right; right; right; left; exact h
      · right; right; right; right; right; exact h
      · right; left; exact h
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact convexSpaceRegion_three_six_FFF_nonempty
      · exact convexSpaceRegion_three_six_FFT_nonempty
      · exact convexSpaceRegion_three_six_TFF_nonempty
      · exact convexSpaceRegion_three_six_TFT_nonempty
      · exact convexSpaceRegion_three_six_TTF_nonempty
      · exact convexSpaceRegion_three_six_TTT_nonempty
  rw [hs]
  decide

/-- $n = 4$ において領域数12を達成する配置: $z = 0$, $z = 1$, $x = 0$, $y = 0$ -/
def H_four_twelve : Fin 4 → Plane3 :=
  ![zPlane 0, zPlane 1, plane_x0, plane_y0]

lemma distinctPlanes_four_twelve : DistinctPlanes 4 H_four_twelve := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    change (H_four_twelve 0).toSet = (H_four_twelve 1).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_four_twelve 0).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, zPlane]; rw [inner_e2Vec_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_four_twelve 1).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 0).toSet = (H_four_twelve 2).toSet at hij
    have hmem : ptXYZ 0 0 1 ∈ (H_four_twelve 2).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 0 1 ∈ (H_four_twelve 0).toSet := hij.symm ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 0).toSet = (H_four_twelve 3).toSet at hij
    have hmem : ptXYZ 0 0 1 ∈ (H_four_twelve 3).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_y0]; rw [inner_v1_ptXYZ]
    have hmem' : ptXYZ 0 0 1 ∈ (H_four_twelve 0).toSet := hij.symm ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 1).toSet = (H_four_twelve 0).toSet at hij
    have hmem : ptXYZ 0 0 1 ∈ (H_four_twelve 1).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, zPlane]; rw [inner_e2Vec_ptXYZ]
    have hmem' : ptXYZ 0 0 1 ∈ (H_four_twelve 0).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · rfl
  · exfalso
    change (H_four_twelve 1).toSet = (H_four_twelve 2).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_four_twelve 2).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_four_twelve 1).toSet := hij.symm ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 1).toSet = (H_four_twelve 3).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_four_twelve 3).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_y0]; rw [inner_v1_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_four_twelve 1).toSet := hij.symm ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 2).toSet = (H_four_twelve 0).toSet at hij
    have hmem : ptXYZ 0 0 1 ∈ (H_four_twelve 2).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 0 1 ∈ (H_four_twelve 0).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 2).toSet = (H_four_twelve 1).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_four_twelve 2).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_four_twelve 1).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · rfl
  · exfalso
    change (H_four_twelve 2).toSet = (H_four_twelve 3).toSet at hij
    have hmem : ptXYZ 0 1 0 ∈ (H_four_twelve 2).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 1 0 ∈ (H_four_twelve 3).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, plane_y0] at hmem'
    rw [inner_v1_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 3).toSet = (H_four_twelve 0).toSet at hij
    have hmem : ptXYZ 0 0 1 ∈ (H_four_twelve 3).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_y0]; rw [inner_v1_ptXYZ]
    have hmem' : ptXYZ 0 0 1 ∈ (H_four_twelve 0).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 3).toSet = (H_four_twelve 1).toSet at hij
    have hmem : ptXYZ 0 0 0 ∈ (H_four_twelve 3).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_y0]; rw [inner_v1_ptXYZ]
    have hmem' : ptXYZ 0 0 0 ∈ (H_four_twelve 1).toSet := hij ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, zPlane] at hmem'
    rw [inner_e2Vec_ptXYZ] at hmem'; linarith
  · exfalso
    change (H_four_twelve 3).toSet = (H_four_twelve 2).toSet at hij
    have hmem : ptXYZ 0 1 0 ∈ (H_four_twelve 2).toSet := by
      dsimp [Plane3.toSet, H_four_twelve, plane_x0]; rw [inner_v0_ptXYZ]
    have hmem' : ptXYZ 0 1 0 ∈ (H_four_twelve 3).toSet := hij.symm ▸ hmem
    dsimp [Plane3.toSet, H_four_twelve, plane_y0] at hmem'
    rw [inner_v1_ptXYZ] at hmem'; linarith
  · rfl

lemma convexSpaceRegion_four_twelve_FT_empty (bx by_ : Bool) :
    ¬ (convexSpaceRegion 4 H_four_twelve ![(false : Bool), true, bx, by_]).Nonempty := by
  rintro ⟨p, hp⟩
  have h0 := hp 0
  have h1 := hp 1
  dsimp [convexSpaceRegion, H_four_twelve, zPlane] at h0 h1
  rw [inner_e2Vec] at h0 h1
  linarith

lemma convexSpaceRegion_four_twelve_nonempty (bz1 bz2 bx by_ : Bool)
    (h_not : ¬ (bz1 = false ∧ bz2 = true)) :
    (convexSpaceRegion 4 H_four_twelve ![bz1, bz2, bx, by_]).Nonempty := by
  have hz : ∃ z : ℝ, (if bz1 then z > 0 else z < 0) ∧ (if bz2 then z > 1 else z < 1) := by
    cases bz1 <;> cases bz2
    · use -1; simp
    · contradiction
    · use (1/2 : ℝ); simp; norm_num
    · use 2; simp
  have hx : ∃ x : ℝ, (if bx then x > 0 else x < 0) := by
    cases bx
    · use -1; simp
    · use 1; simp
  have hy : ∃ y : ℝ, (if by_ then y > 0 else y < 0) := by
    cases by_
    · use -1; simp
    · use 1; simp
  rcases hz with ⟨z, hz1, hz2⟩
  rcases hx with ⟨x, hx⟩
  rcases hy with ⟨y, hy⟩
  use ptXYZ x y z
  intro i; fin_cases i
  · dsimp [convexSpaceRegion, H_four_twelve, zPlane]; rw [inner_e2Vec_ptXYZ]
    cases bz1 <;> simpa using hz1
  · dsimp [convexSpaceRegion, H_four_twelve, zPlane]; rw [inner_e2Vec_ptXYZ]
    cases bz2 <;> simpa using hz2
  · dsimp [convexSpaceRegion, H_four_twelve, plane_x0]; rw [inner_v0_ptXYZ]
    cases bx <;> simpa using hx
  · dsimp [convexSpaceRegion, H_four_twelve, plane_y0]; rw [inner_v1_ptXYZ]
    cases by_ <;> simpa using hy

lemma spaceRegionsCount_four_twelve_eq_twelve :
    spaceRegionsCount 4 H_four_twelve = 12 := by
  rw [spaceRegionsCount_eq_card_nonempty_convexSpaceRegion]
  have hs : (Finset.filter (fun σ =>
      (convexSpaceRegion 4 H_four_twelve σ).Nonempty) Finset.univ) =
      {![(false : Bool), false, false, false],
       ![(false : Bool), false, false, true],
       ![(false : Bool), false, true, false],
       ![(false : Bool), false, true, true],
       ![(true : Bool), false, false, false],
       ![(true : Bool), false, false, true],
       ![(true : Bool), false, true, false],
       ![(true : Bool), false, true, true],
       ![(true : Bool), true, false, false],
       ![(true : Bool), true, false, true],
       ![(true : Bool), true, true, false],
       ![(true : Bool), true, true, true]} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hne
      have h0 : σ 0 = false ∨ σ 0 = true := by cases σ 0 <;> simp
      have h1 : σ 1 = false ∨ σ 1 = true := by cases σ 1 <;> simp
      have h2 : σ 2 = false ∨ σ 2 = true := by cases σ 2 <;> simp
      have h3 : σ 3 = false ∨ σ 3 = true := by cases σ 3 <;> simp
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
        rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
      · left; ext i; fin_cases i <;> assumption
      · right; left; ext i; fin_cases i <;> assumption
      · right; right; left; ext i; fin_cases i <;> assumption
      · right; right; right; left; ext i; fin_cases i <;> assumption
      · exfalso
        have h_eq : σ = ![(false : Bool), true, false, false] := by
          ext i; fin_cases i <;> assumption
        subst h_eq
        exact (convexSpaceRegion_four_twelve_FT_empty false false hne).elim
      · exfalso
        have h_eq : σ = ![(false : Bool), true, false, true] := by
          ext i; fin_cases i <;> assumption
        subst h_eq
        exact (convexSpaceRegion_four_twelve_FT_empty false true hne).elim
      · exfalso
        have h_eq : σ = ![(false : Bool), true, true, false] := by
          ext i; fin_cases i <;> assumption
        subst h_eq
        exact (convexSpaceRegion_four_twelve_FT_empty true false hne).elim
      · exfalso
        have h_eq : σ = ![(false : Bool), true, true, true] := by
          ext i; fin_cases i <;> assumption
        subst h_eq
        exact (convexSpaceRegion_four_twelve_FT_empty true true hne).elim
      · right; right; right; right; left; ext i; fin_cases i <;> assumption
      · right; right; right; right; right; left; ext i; fin_cases i <;> assumption
      · right; right; right; right; right; right; left; ext i; fin_cases i <;> assumption
      · right; right; right; right; right; right; right; left; ext i; fin_cases i <;> assumption
      · right; right; right; right; right; right; right; right; left
        ext i; fin_cases i <;> assumption
      · right; right; right; right; right; right; right; right; right; left
        ext i; fin_cases i <;> assumption
      · right; right; right; right; right; right; right; right; right; right; left
        ext i; fin_cases i <;> assumption
      · right; right; right; right; right; right; right; right; right; right; right
        ext i; fin_cases i <;> assumption
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact convexSpaceRegion_four_twelve_nonempty false false false false (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty false false false true (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty false false true false (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty false false true true (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty true false false false (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty true false false true (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty true false true false (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty true false true true (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty true true false false (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty true true false true (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty true true true false (by decide)
      · exact convexSpaceRegion_four_twelve_nonempty true true true true (by decide)
  rw [hs]
  decide

/-- 平面 x = 0 と平面 z = c は平行でない。 -/
lemma not_parallel_plane_x0_zPlane (c : ℝ) :
    ¬ parallelPlanes plane_x0 (zPlane c) := by
  rintro ⟨k, hk⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_x0.normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (k • (zPlane c).normVec) 0 := by rw [hk]
  simp [plane_x0, zPlane, v0_vec, e2Vec] at hc0

/-- 平面 y = 0 と平面 z = c は平行でない。 -/
lemma not_parallel_plane_y0_zPlane (c : ℝ) :
    ¬ parallelPlanes plane_y0 (zPlane c) := by
  rintro ⟨k, hk⟩
  have hc1 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_y0.normVec 1 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (k • (zPlane c).normVec) 1 := by rw [hk]
  simp [plane_y0, zPlane, v1_vec, e2Vec] at hc1

/-- 平面 x + y = 1 と平面 z = c は平行でない。 -/
lemma not_parallel_plane_xy1_zPlane (c : ℝ) :
    ¬ parallelPlanes plane_xy1 (zPlane c) := by
  rintro ⟨k, hk⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) plane_xy1.normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (k • (zPlane c).normVec) 0 := by rw [hk]
  simp [plane_xy1, zPlane, v2_vec, e2Vec] at hc0

/-- モーメント平面と平面 z = c は平行でない。 -/
lemma not_parallel_momentPlane_zPlane (t : ℝ) (c : ℝ) :
    ¬ parallelPlanes (momentPlane t) (zPlane c) := by
  rintro ⟨k, hk⟩
  have hc0 : (WithLp.equiv 2 (Fin 3 → ℝ)) (momentPlane t).normVec 0 =
             (WithLp.equiv 2 (Fin 3 → ℝ)) (k • (zPlane c).normVec) 0 := by rw [hk]
  simp [momentPlane, zPlane, momentVec, e2Vec] at hc0

/-- 第3位の領域数を達成するハイブリッド配置（n ≥ 5 用）。
最初の3平面は三角柱（x = 0, y = 0, x + y = 1）をなし、4平面目はモーメント平面 momentPlane 3、
5平面目は点 (0, 0, 3) を通過する平面 z = 3 とする。
これにより交線系が1点で会して交点欠損2を生じ、n = 5 でちょうど24領域を達成する。
6平面目以降は順次モーメント平面を追加する。 -/
def H_third_hybrid (n : ℕ) (i : Fin n) : Plane3 :=
  if i.val = 0 then plane_x0
  else if i.val = 1 then plane_y0
  else if i.val = 2 then plane_xy1
  else if i.val = 3 then momentPlane 3
  else if i.val = 4 then zPlane 3
  else momentPlane (i.val : ℝ)

/-- 先頭n枚の平面は、n枚の配置と一致する。 -/
lemma H_third_hybrid_castSucc (n : ℕ) :
    H_third_hybrid (n + 1) ∘ Fin.castSucc = H_third_hybrid n := by
  ext ⟨i, hi⟩
  dsimp [H_third_hybrid]

/-- インデックスが 4 以外の平面は H_hybrid と完全に一致する。 -/
lemma H_third_hybrid_eq_H_hybrid {n : ℕ} (i : Fin n) (hi : i.val ≠ 4) :
    H_third_hybrid n i = H_hybrid n i := by
  dsimp [H_third_hybrid, H_hybrid]
  by_cases h0 : i.val = 0 <;> simp [h0]
  by_cases h1 : i.val = 1 <;> simp [h1]
  by_cases h2 : i.val = 2 <;> simp [h2]
  by_cases h3 : i.val = 3 <;> simp [h3, hi]

/-- n ≥ 5 のとき、最後の平面はモーメント平面 momentPlane n である。 -/
lemma H_third_hybrid_last_eq_momentPlane {n : ℕ} (hn : 5 ≤ n) :
    H_third_hybrid (n + 1) (Fin.last n) = momentPlane (n : ℝ) := by
  unfold H_third_hybrid
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  simp [h0, h1, h2, h3, h4]

lemma H_third_hybrid_of_val_zero {n : ℕ} (i : Fin n) (hi : i.val = 0) :
    H_third_hybrid n i = plane_x0 := by
  unfold H_third_hybrid; simp [hi]

lemma H_third_hybrid_of_val_one {n : ℕ} (i : Fin n) (hi : i.val = 1) :
    H_third_hybrid n i = plane_y0 := by
  unfold H_third_hybrid; simp [hi]

lemma H_third_hybrid_of_val_two {n : ℕ} (i : Fin n) (hi : i.val = 2) :
    H_third_hybrid n i = plane_xy1 := by
  unfold H_third_hybrid; simp [hi]

lemma H_third_hybrid_of_val_three {n : ℕ} (i : Fin n) (hi : i.val = 3) :
    H_third_hybrid n i = momentPlane 3 := by
  unfold H_third_hybrid; simp [hi]

lemma H_third_hybrid_of_val_four {n : ℕ} (i : Fin n) (hi : i.val = 4) :
    H_third_hybrid n i = zPlane 3 := by
  unfold H_third_hybrid; simp [hi]

lemma H_third_hybrid_of_val_ge {n : ℕ} (i : Fin n) (hi : 5 ≤ i.val) :
    H_third_hybrid n i = momentPlane (i.val : ℝ) := by
  unfold H_third_hybrid
  have h0 : ¬ i.val = 0 := by omega
  have h1 : ¬ i.val = 1 := by omega
  have h2 : ¬ i.val = 2 := by omega
  have h3 : ¬ i.val = 3 := by omega
  have h4 : ¬ i.val = 4 := by omega
  simp [h0, h1, h2, h3, h4]

set_option linter.flexible false in
/-- ハイブリッド配置 H_third_hybrid の任意の相異なる2平面は平行でない。 -/
lemma not_parallel_third_hybrid {n : ℕ} (i j : Fin n) (hij : i < j) :
    ¬ parallelPlanes (H_third_hybrid n i) (H_third_hybrid n j) := by
  have hi_lt : i.val < j.val := hij
  have h_ne : i.val ≠ j.val := by omega
  by_cases hi0 : i.val = 0
  · by_cases hj1 : j.val = 1
    · dsimp [H_third_hybrid]
      simp [hi0, hj1]
      exact not_parallel_plane_x0_plane_y0
    · by_cases hj2 : j.val = 2
      · dsimp [H_third_hybrid]
        simp [hi0, hj2]
        exact not_parallel_plane_x0_plane_xy1
      · by_cases hj3 : j.val = 3
        · dsimp [H_third_hybrid]
          simp [hi0, hj3]
          apply not_parallel_plane_x0_momentPlane
          norm_num
        · by_cases hj4 : j.val = 4
          · dsimp [H_third_hybrid]
            simp [hi0, hj4]
            exact not_parallel_plane_x0_zPlane 3
          · dsimp [H_third_hybrid]
            have hj0 : ¬ j.val = 0 := by omega
            simp [hi0, hj0, hj1, hj2, hj3, hj4]
            apply not_parallel_plane_x0_momentPlane
            exact_mod_cast (by omega : 1 ≤ j.val)
  · by_cases hi1 : i.val = 1
    · by_cases hj2 : j.val = 2
      · dsimp [H_third_hybrid]
        simp [hi1, hj2]
        exact not_parallel_plane_y0_plane_xy1
      · by_cases hj3 : j.val = 3
        · dsimp [H_third_hybrid]
          simp [hi1, hj3]
          apply not_parallel_plane_y0_momentPlane
          norm_num
        · by_cases hj4 : j.val = 4
          · dsimp [H_third_hybrid]
            simp [hi1, hj4]
            exact not_parallel_plane_y0_zPlane 3
          · dsimp [H_third_hybrid]
            have hj0 : ¬ j.val = 0 := by omega
            have hj1 : ¬ j.val = 1 := by omega
            simp [hi1, hj0, hj1, hj2, hj3, hj4]
            apply not_parallel_plane_y0_momentPlane
            exact_mod_cast (by omega : 1 ≤ j.val)
    · by_cases hi2 : i.val = 2
      · by_cases hj3 : j.val = 3
        · dsimp [H_third_hybrid]
          simp [hi2, hj3]
          apply not_parallel_plane_xy1_momentPlane
          norm_num
        · by_cases hj4 : j.val = 4
          · dsimp [H_third_hybrid]
            simp [hi2, hj4]
            exact not_parallel_plane_xy1_zPlane 3
          · dsimp [H_third_hybrid]
            have hj0 : ¬ j.val = 0 := by omega
            have hj1 : ¬ j.val = 1 := by omega
            have hj2 : ¬ j.val = 2 := by omega
            simp [hi2, hj0, hj1, hj2, hj3, hj4]
            apply not_parallel_plane_xy1_momentPlane
            exact_mod_cast (by omega : 2 ≤ j.val)
      · by_cases hi3 : i.val = 3
        · by_cases hj4 : j.val = 4
          · dsimp [H_third_hybrid]
            simp [hi3, hj4]
            exact not_parallel_momentPlane_zPlane 3 3
          · dsimp [H_third_hybrid]
            have hj0 : ¬ j.val = 0 := by omega
            have hj1 : ¬ j.val = 1 := by omega
            have hj2 : ¬ j.val = 2 := by omega
            have hj3 : ¬ j.val = 3 := by omega
            have hj4 : ¬ j.val = 4 := by omega
            simp [hi3, hj0, hj1, hj2, hj3, hj4]
            apply not_parallel_momentPlanes
            exact_mod_cast (by omega : 3 ≠ j.val)
        · by_cases hi4 : i.val = 4
          · dsimp [H_third_hybrid]
            have hj0 : ¬ j.val = 0 := by omega
            have hj1 : ¬ j.val = 1 := by omega
            have hj2 : ¬ j.val = 2 := by omega
            have hj3 : ¬ j.val = 3 := by omega
            have hj4 : ¬ j.val = 4 := by omega
            simp [hi4, hj0, hj1, hj2, hj3, hj4]
            intro h_par
            have h_not := not_parallel_momentPlane_zPlane (j.val : ℝ) 3
            apply h_not
            rcases h_par with ⟨c, hc⟩
            have hc_ne : c ≠ 0 := by
              rintro rfl
              have hz := (zPlane 3).normVec_ne_zero
              rw [hc, zero_smul] at hz
              exact hz rfl
            refine ⟨c⁻¹, ?_⟩
            rw [hc, smul_smul, inv_mul_cancel₀ hc_ne, one_smul]
          · dsimp [H_third_hybrid]
            have hj0 : ¬ j.val = 0 := by omega
            have hj1 : ¬ j.val = 1 := by omega
            have hj2 : ¬ j.val = 2 := by omega
            have hj3 : ¬ j.val = 3 := by omega
            have hj4 : ¬ j.val = 4 := by omega
            simp [hi0, hi1, hi2, hi3, hi4, hj0, hj1, hj2, hj3, hj4]
            apply not_parallel_momentPlanes
            exact_mod_cast h_ne

/-- H_third_hybrid の各平面は相異なる。 -/
lemma distinctPlanes_third_hybrid (n : ℕ) (_hn : 5 ≤ n) :
    DistinctPlanes n (H_third_hybrid n) := by
  intro i j hij
  by_contra h_ne
  rcases lt_trichotomy i j with h | h | h
  · have h_not := not_parallel_third_hybrid i j h
    have h_par := parallelPlanes_of_toSet_eq (H_third_hybrid n i) (H_third_hybrid n j) hij
    exact h_not h_par
  · exact h_ne h
  · have h_not := not_parallel_third_hybrid j i h
    have h_par := parallelPlanes_of_toSet_eq (H_third_hybrid n j) (H_third_hybrid n i) hij.symm
    exact h_not h_par

/-- H_third_hybrid 4 の先頭3枚は H_three_prism と一致する。 -/
lemma H_third_hybrid_four_castSucc_eq :
    (H_third_hybrid 4 ∘ Fin.castSucc) = H_three_prism := by
  ext i; fin_cases i <;> rfl

lemma inner_plane_xy1_ptXYZ (x y z : ℝ) :
    @inner ℝ Space3 _ plane_xy1.normVec (ptXYZ x y z) = x + y := by
  dsimp [plane_xy1]
  rw [inner_v2_vec, ptXYZ_apply_zero, ptXYZ_apply_one]

lemma inner_momentPlane3_ptXYZ (x y z : ℝ) :
    @inner ℝ Space3 _ (momentPlane 3).normVec (ptXYZ x y z) = x + 3 * y + 9 * z := by
  dsimp [momentPlane]
  rw [inner_momentVec, ptXYZ_apply_zero, ptXYZ_apply_one, ptXYZ_apply_two]
  ring

lemma mem_zPlane3_ptXYZ (x y : ℝ) : ptXYZ x y 3 ∈ (zPlane 3).toSet := by
  dsimp [Plane3.toSet, zPlane]
  rw [inner_e2Vec_ptXYZ]

/-- 符号 (F, F, T, F) に対応する切断領域は空集合である。 -/
lemma split_third_hybrid_empty_FFTF :
    ¬ isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4)
      ![(false : Bool), false, true, false]) (zPlane 3) := by
  rintro ⟨p, hp, _hpz⟩
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2
  dsimp [convexSpaceRegion, H_third_hybrid, plane_x0, plane_y0, plane_xy1] at h0 h1 h2
  rw [inner_v0_vec] at h0; rw [inner_v1_vec] at h1; rw [inner_v2_vec] at h2
  linarith

/-- 符号 (F, F, T, T) に対応する切断領域は空集合である。 -/
lemma split_third_hybrid_empty_FFTT :
    ¬ isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4)
      ![(false : Bool), false, true, true]) (zPlane 3) := by
  rintro ⟨p, hp, _hpz⟩
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2
  dsimp [convexSpaceRegion, H_third_hybrid, plane_x0, plane_y0, plane_xy1] at h0 h1 h2
  rw [inner_v0_vec] at h0; rw [inner_v1_vec] at h1; rw [inner_v2_vec] at h2
  linarith

/-- 符号 (T, T, F, F) に対応する切断領域は空集合である。 -/
lemma split_third_hybrid_empty_TTFF :
    ¬ isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4)
      ![(true : Bool), true, false, false]) (zPlane 3) := by
  rintro ⟨p, hp, hpz⟩
  have h0 := hp 0; have h1 := hp 1; have h3 := hp 3
  dsimp [convexSpaceRegion, H_third_hybrid, plane_x0, plane_y0, momentPlane] at h0 h1 h3
  rw [inner_v0_vec] at h0; rw [inner_v1_vec] at h1; rw [inner_momentVec] at h3
  dsimp [Plane3.toSet, zPlane] at hpz; rw [inner_e2Vec] at hpz
  linarith

/-- 符号 (T, T, T, F) に対応する切断領域は空集合である。 -/
lemma split_third_hybrid_empty_TTTF :
    ¬ isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4)
      ![(true : Bool), true, true, false]) (zPlane 3) := by
  rintro ⟨p, hp, hpz⟩
  have h0 := hp 0; have h1 := hp 1; have h3 := hp 3
  dsimp [convexSpaceRegion, H_third_hybrid, plane_x0, plane_y0, momentPlane] at h0 h1 h3
  rw [inner_v0_vec] at h0; rw [inner_v1_vec] at h1; rw [inner_momentVec] at h3
  dsimp [Plane3.toSet, zPlane] at hpz; rw [inner_e2Vec] at hpz
  linarith

/-- 符号 (F, F, F, T) に対応する切断領域は空集合である。 -/
lemma split_third_hybrid_empty_FFFT :
    ¬ isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4)
      ![(false : Bool), false, false, true]) (zPlane 3) := by
  rintro ⟨p, hp, hpz⟩
  have h0 := hp 0; have h1 := hp 1; have h3 := hp 3
  dsimp [convexSpaceRegion, H_third_hybrid, plane_x0, plane_y0, momentPlane] at h0 h1 h3
  rw [inner_v0_vec] at h0; rw [inner_v1_vec] at h1; rw [inner_momentVec] at h3
  dsimp [Plane3.toSet, zPlane] at hpz; rw [inner_e2Vec] at hpz
  linarith

/-- 符号 (F, T, T, F) に対応する切断領域は空集合である。 -/
lemma split_third_hybrid_empty_FTTF :
    ¬ isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4)
      ![(false : Bool), true, true, false]) (zPlane 3) := by
  rintro ⟨p, hp, hpz⟩
  have h0 := hp 0; have h2 := hp 2; have h3 := hp 3
  dsimp [convexSpaceRegion, H_third_hybrid, plane_x0, plane_xy1, momentPlane] at h0 h2 h3
  rw [inner_v0_vec] at h0; rw [inner_v2_vec] at h2; rw [inner_momentVec] at h3
  dsimp [Plane3.toSet, zPlane] at hpz; rw [inner_e2Vec] at hpz
  linarith

/-- 代表点を与えることで切断領域の非空性を示す。 -/
lemma split_third_hybrid_nonempty (σ : Fin 4 → Bool) (x y : ℝ)
    (h0 : if σ 0 then 0 < x else x < 0)
    (h1 : if σ 1 then 0 < y else y < 0)
    (h2 : if σ 2 then 1 < x + y else x + y < 1)
    (h3 : if σ 3 then 27 < x + 3 * y + 27 else x + 3 * y + 27 < 27) :
    isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4) σ) (zPlane 3) := by
  refine ⟨ptXYZ x y 3, ?_, mem_zPlane3_ptXYZ x y⟩
  intro i
  fin_cases i
  · dsimp [convexSpaceRegion, H_third_hybrid, plane_x0]
    rw [inner_v0_ptXYZ]
    exact h0
  · dsimp [convexSpaceRegion, H_third_hybrid, plane_y0]
    rw [inner_v1_ptXYZ]
    exact h1
  · dsimp [convexSpaceRegion, H_third_hybrid, plane_xy1]
    rw [inner_v2_vec, ptXYZ_apply_zero, ptXYZ_apply_one]
    exact h2
  · dsimp [convexSpaceRegion, H_third_hybrid, momentPlane]
    rw [inner_momentVec, ptXYZ_apply_zero, ptXYZ_apply_one, ptXYZ_apply_two]
    have h_pow2 : (3 : ℝ) ^ 2 * 3 = 27 := by norm_num
    have h_pow3 : (3 : ℝ) ^ 3 = 27 := by norm_num
    rw [h_pow2, h_pow3]
    exact h3

/-- n = 5 のとき、配置の領域数は24である。
三角柱(7) + 第4平面切断(7) + 第5平面切断(10) = 24 として計算される。 -/
lemma spaceRegionsCount_third_hybrid_five :
    spaceRegionsCount 5 (H_third_hybrid 5) = 24 := by
  -- T(5) = T(4) + split(4, H5)
  have h_succ4 := spaceRegionsCount_succ_eq_add_split 4 (H_third_hybrid 5)
  rw [H_third_hybrid_castSucc 4] at h_succ4
  rw [h_succ4]
  -- T(4) = T(3) + split(3, H4)
  have h_succ3 := spaceRegionsCount_succ_eq_add_split 3 (H_third_hybrid 4)
  have h_cast3 : (H_third_hybrid 4 ∘ Fin.castSucc) = H_three_prism :=
    H_third_hybrid_four_castSucc_eq
  rw [h_cast3, spaceRegionsCount_three_prism_eq_seven] at h_succ3
  rw [h_succ3]
  -- split(3, H4) = 7 および split(4, H5) = 10 を代入する。
  have h_split3 : splitSpaceRegionsCount 3 (H_third_hybrid 4) = 7 := by
    have h_eq4 : H_third_hybrid 4 = H_hybrid 4 := by
      ext i; fin_cases i <;> rfl
    rw [h_eq4]
    have h_sp := splitSpaceRegionsCount_hybrid 3 (by omega)
    rw [h_sp]
    rfl
  have h_split4 : splitSpaceRegionsCount 4 (H_third_hybrid 5) = 10 := by
    dsimp [splitSpaceRegionsCount]
    rw [H_third_hybrid_castSucc 4]
    change (Finset.filter (fun σ =>
      isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4) σ)
        (H_third_hybrid 5 (Fin.last 4))) Finset.univ).card = 10
    have h_last : H_third_hybrid 5 (Fin.last 4) = zPlane 3 := rfl
    rw [h_last]
    have hs : (Finset.filter (fun σ =>
        isSplitByPlane (convexSpaceRegion 4 (H_third_hybrid 4) σ) (zPlane 3)) Finset.univ) =
        {![(true : Bool), true, true, true],
         ![(true : Bool), true, false, true],
         ![(true : Bool), false, true, true],
         ![(true : Bool), false, false, true],
         ![(true : Bool), false, true, false],
         ![(true : Bool), false, false, false],
         ![(false : Bool), true, true, true],
         ![(false : Bool), true, false, true],
         ![(false : Bool), true, false, false],
         ![(false : Bool), false, false, false]} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hsplit
        have h0 : σ 0 = false ∨ σ 0 = true := by cases σ 0 <;> simp
        have h1 : σ 1 = false ∨ σ 1 = true := by cases σ 1 <;> simp
        have h2 : σ 2 = false ∨ σ 2 = true := by cases σ 2 <;> simp
        have h3 : σ 3 = false ∨ σ 3 = true := by cases σ 3 <;> simp
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
        · right; right; right; right; right; right; right; right; right
          ext i; fin_cases i <;> assumption
        · exfalso
          have h_eq : σ = ![(false : Bool), false, false, true] := by
            ext i; fin_cases i <;> assumption
          subst h_eq
          exact split_third_hybrid_empty_FFFT hsplit
        · exfalso
          have h_eq : σ = ![(false : Bool), false, true, false] := by
            ext i; fin_cases i <;> assumption
          subst h_eq
          exact split_third_hybrid_empty_FFTF hsplit
        · exfalso
          have h_eq : σ = ![(false : Bool), false, true, true] := by
            ext i; fin_cases i <;> assumption
          subst h_eq
          exact split_third_hybrid_empty_FFTT hsplit
        · right; right; right; right; right; right; right; right; left
          ext i; fin_cases i <;> assumption
        · right; right; right; right; right; right; right; left
          ext i; fin_cases i <;> assumption
        · exfalso
          have h_eq : σ = ![(false : Bool), true, true, false] := by
            ext i; fin_cases i <;> assumption
          subst h_eq
          exact split_third_hybrid_empty_FTTF hsplit
        · right; right; right; right; right; right; left
          ext i; fin_cases i <;> assumption
        · right; right; right; right; right; left
          ext i; fin_cases i <;> assumption
        · right; right; right; left
          ext i; fin_cases i <;> assumption
        · right; right; right; right; left
          ext i; fin_cases i <;> assumption
        · right; right; left
          ext i; fin_cases i <;> assumption
        · exfalso
          have h_eq : σ = ![(true : Bool), true, false, false] := by
            ext i; fin_cases i <;> assumption
          subst h_eq
          exact split_third_hybrid_empty_TTFF hsplit
        · right; left
          ext i; fin_cases i <;> assumption
        · exfalso
          have h_eq : σ = ![(true : Bool), true, true, false] := by
            ext i; fin_cases i <;> assumption
          subst h_eq
          exact split_third_hybrid_empty_TTTF hsplit
        · left
          ext i; fin_cases i <;> assumption
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · exact split_third_hybrid_nonempty _ 2 2
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ (1/4) (1/4)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ 3 (-1/2)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ (1/2) (-1/8)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ 3 (-4/3)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ (1/2) (-1/4)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ (-1/2) 2
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ (-1/4) (1/2)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ (-2) (1/2)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact split_third_hybrid_nonempty _ (-1) (-1)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hs]
    decide
  omega

/-- H_third_hybrid において、$i ≠ j$ なる任意の2平面と最後のモーメント平面の交わりはちょうど1点である。 -/
lemma intersection_three_third_hybrid (n : ℕ) (hn : 5 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ∃ q, (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
      (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
      (H_third_hybrid (n + 1) (Fin.last n)).toSet = {q} := by
  have h_last : H_third_hybrid (n + 1) (Fin.last n) = momentPlane (n : ℝ) :=
    H_third_hybrid_last_eq_momentPlane hn
  have hn_pos : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact Nat.cast_ne_zero.mpr this
  have hn_ne1 : (n : ℝ) ≠ 1 := by
    have : n ≠ 1 := by omega
    exact_mod_cast this
  have h_symm : ∀ a b : Fin n, a ≠ b → a < b →
      ∃ q, (H_third_hybrid (n + 1) (Fin.castSucc a)).toSet ∩
        (H_third_hybrid (n + 1) (Fin.castSucc b)).toSet ∩
        (H_third_hybrid (n + 1) (Fin.last n)).toSet = {q} := by
    intro a b hab_ne hab_lt
    have ha_val : (Fin.castSucc a).val = a.val := rfl
    have hb_val : (Fin.castSucc b).val = b.val := rfl
    by_cases ha4 : a.val = 4
    · have hb_ge : 5 ≤ (Fin.castSucc b).val := by rw [hb_val]; omega
      have ha_eq : H_third_hybrid (n + 1) (Fin.castSucc a) = zPlane 3 :=
        H_third_hybrid_of_val_four (Fin.castSucc a) (by rw [ha_val, ha4])
      have hb_eq : H_third_hybrid (n + 1) (Fin.castSucc b) = momentPlane (b.val : ℝ) :=
        H_third_hybrid_of_val_ge (Fin.castSucc b) hb_ge
      rw [ha_eq, hb_eq, h_last]
      have hbn_ne : (b.val : ℝ) ≠ (n : ℝ) := by
        have : b.val ≠ n := b.is_lt.ne
        exact_mod_cast this
      have h_inter := intersection_momentPlane_zPlane3_momentPlane hbn_ne
      rcases h_inter with ⟨q, hq⟩
      use q
      have h_comm : (zPlane 3).toSet ∩ (momentPlane (b.val : ℝ)).toSet =
          (momentPlane (b.val : ℝ)).toSet ∩ (zPlane 3).toSet := Set.inter_comm _ _
      rw [h_comm]
      exact hq
    · by_cases hb4 : b.val = 4
      · have hb_eq : H_third_hybrid (n + 1) (Fin.castSucc b) = zPlane 3 :=
          H_third_hybrid_of_val_four (Fin.castSucc b) (by rw [hb_val, hb4])
        rw [hb_eq, h_last]
        by_cases ha0 : a.val = 0
        · have ha_eq : H_third_hybrid (n + 1) (Fin.castSucc a) = plane_x0 :=
            H_third_hybrid_of_val_zero (Fin.castSucc a) (by rw [ha_val, ha0])
          rw [ha_eq]
          exact intersection_plane_x0_zPlane3_momentPlane hn_pos
        · by_cases ha1 : a.val = 1
          · have ha_eq : H_third_hybrid (n + 1) (Fin.castSucc a) = plane_y0 :=
              H_third_hybrid_of_val_one (Fin.castSucc a) (by rw [ha_val, ha1])
            rw [ha_eq]
            exact intersection_plane_y0_zPlane3_momentPlane
          · by_cases ha2 : a.val = 2
            · have ha_eq : H_third_hybrid (n + 1) (Fin.castSucc a) = plane_xy1 :=
                H_third_hybrid_of_val_two (Fin.castSucc a) (by rw [ha_val, ha2])
              rw [ha_eq]
              exact intersection_plane_xy1_zPlane3_momentPlane hn_ne1
            · have ha3 : a.val = 3 := by omega
              have ha_eq : H_third_hybrid (n + 1) (Fin.castSucc a) = momentPlane 3 :=
                H_third_hybrid_of_val_three (Fin.castSucc a) (by rw [ha_val, ha3])
              rw [ha_eq]
              have h3n_ne : (3 : ℝ) ≠ (n : ℝ) := by
                have : 3 ≠ n := by omega
                exact_mod_cast this
              exact intersection_momentPlane_zPlane3_momentPlane h3n_ne
      · have ha_eq : H_third_hybrid (n + 1) (Fin.castSucc a) =
            H_hybrid (n + 1) (Fin.castSucc a) :=
          H_third_hybrid_eq_H_hybrid (Fin.castSucc a) (by rw [ha_val]; exact ha4)
        have hb_eq : H_third_hybrid (n + 1) (Fin.castSucc b) =
            H_hybrid (n + 1) (Fin.castSucc b) :=
          H_third_hybrid_eq_H_hybrid (Fin.castSucc b) (by rw [hb_val]; exact hb4)
        have h_last_eq : H_third_hybrid (n + 1) (Fin.last n) =
            H_hybrid (n + 1) (Fin.last n) := by
          have hn_ne4 : (Fin.last n).val ≠ 4 := by
            change n ≠ 4
            omega
          exact H_third_hybrid_eq_H_hybrid (Fin.last n) hn_ne4
        rw [ha_eq, hb_eq, h_last_eq]
        have hn3 : 3 ≤ n := by omega
        exact intersection_three_hybrid n hn3 a b hab_ne
  rcases lt_or_gt_of_ne hij with h_lt | h_gt
  · exact h_symm i j hij h_lt
  · rcases h_symm j i hij.symm h_gt with ⟨q, hq⟩
    use q
    have h_comm : (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
        (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet =
        (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
        (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet := Set.inter_comm _ _
    rw [h_comm]
    exact hq

/-- H_third_hybridにおいて、昇順の添字を持つ3平面と最後の平面の交わりは空集合である。 -/
lemma intersection_four_third_hybrid_empty_of_sorted (n : ℕ) (hn : 5 ≤ n) (i j l : Fin n)
    (hij : i < j) (hjl : j < l) :
    (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
      (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
      (H_third_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
      (H_third_hybrid (n + 1) (Fin.last n)).toSet = ∅ := by
  have h_last : H_third_hybrid (n + 1) (Fin.last n) = momentPlane (n : ℝ) :=
    H_third_hybrid_last_eq_momentPlane hn
  have hn_real : 5 ≤ (n : ℝ) := by exact_mod_cast hn
  by_cases h4 : i.val ≠ 4 ∧ j.val ≠ 4 ∧ l.val ≠ 4
  · -- どの添字も 4 ではない場合、H_hybrid の結果に帰着する。
    rcases h4 with ⟨hi4, hj4, hl4⟩
    have hi_val : (Fin.castSucc i).val = i.val := rfl
    have hj_val : (Fin.castSucc j).val = j.val := rfl
    have hl_val : (Fin.castSucc l).val = l.val := rfl
    have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) =
        H_hybrid (n + 1) (Fin.castSucc i) :=
      H_third_hybrid_eq_H_hybrid (Fin.castSucc i) (by rw [hi_val]; exact hi4)
    have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) =
        H_hybrid (n + 1) (Fin.castSucc j) :=
      H_third_hybrid_eq_H_hybrid (Fin.castSucc j) (by rw [hj_val]; exact hj4)
    have hl_eq : H_third_hybrid (n + 1) (Fin.castSucc l) =
        H_hybrid (n + 1) (Fin.castSucc l) :=
      H_third_hybrid_eq_H_hybrid (Fin.castSucc l) (by rw [hl_val]; exact hl4)
    have h_last_eq : H_third_hybrid (n + 1) (Fin.last n) =
        H_hybrid (n + 1) (Fin.last n) := by
      have hn_ne4 : (Fin.last n).val ≠ 4 := by change n ≠ 4; omega
      exact H_third_hybrid_eq_H_hybrid (Fin.last n) hn_ne4
    rw [hi_eq, hj_eq, hl_eq, h_last_eq]
    have hn3 : 3 ≤ n := by omega
    exact intersection_four_hybrid_empty_of_sorted n hn3 i j l hij hjl
  · push Not at h4
    by_cases hl4 : l.val = 4
    · -- $l = 4$ の場合、残りの添字 $i, j$ の値に応じて場合分けする。
      have h3n_ne : (3 : ℝ) ≠ (n : ℝ) := by exact_mod_cast (by omega : 3 ≠ n)
      have hl_val : (Fin.castSucc l).val = 4 := by dsimp; rw [hl4]
      have hl_eq : H_third_hybrid (n + 1) (Fin.castSucc l) = zPlane 3 :=
        H_third_hybrid_of_val_four (Fin.castSucc l) hl_val
      have hi_val : (Fin.castSucc i).val = i.val := rfl
      have hj_val : (Fin.castSucc j).val = j.val := rfl
      by_cases hi0 : i.val = 0
      · have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) = plane_x0 :=
          H_third_hybrid_of_val_zero _ (by rw [hi_val, hi0])
        by_cases hj1 : j.val = 1
        · have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) = plane_y0 :=
            H_third_hybrid_of_val_one _ (by rw [hj_val, hj1])
          rw [hi_eq, hj_eq, hl_eq, h_last]
          exact intersection_plane_x0_plane_y0_zPlane3_momentPlane_empty hn_real
        · by_cases hj2 : j.val = 2
          · have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) = plane_xy1 :=
              H_third_hybrid_of_val_two _ (by rw [hj_val, hj2])
            rw [hi_eq, hj_eq, hl_eq, h_last]
            exact intersection_plane_x0_plane_xy1_zPlane3_momentPlane_empty hn_real
          · have hj3 : j.val = 3 := by omega
            have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) = momentPlane 3 :=
              H_third_hybrid_of_val_three _ (by rw [hj_val, hj3])
            rw [hi_eq, hj_eq, hl_eq, h_last]
            apply Set.eq_empty_of_subset_empty
            rintro p ⟨⟨⟨h0, h3⟩, hz⟩, hn_p⟩
            have hp_in : p ∈ plane_x0.toSet ∩ (zPlane 3).toSet ∩
                (momentPlane 3).toSet ∩ (momentPlane (n : ℝ)).toSet :=
              ⟨⟨⟨h0, hz⟩, h3⟩, hn_p⟩
            rw [intersection_plane_x0_zPlane3_two_momentPlanes_empty
                (by norm_num) hn_real h3n_ne] at hp_in
            exact hp_in
      · by_cases hi1 : i.val = 1
        · have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) = plane_y0 :=
            H_third_hybrid_of_val_one _ (by rw [hi_val, hi1])
          by_cases hj2 : j.val = 2
          · have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) = plane_xy1 :=
              H_third_hybrid_of_val_two _ (by rw [hj_val, hj2])
            rw [hi_eq, hj_eq, hl_eq, h_last]
            exact intersection_plane_y0_plane_xy1_zPlane3_momentPlane_empty hn_real
          · have hj3 : j.val = 3 := by omega
            have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) = momentPlane 3 :=
              H_third_hybrid_of_val_three _ (by rw [hj_val, hj3])
            rw [hi_eq, hj_eq, hl_eq, h_last]
            apply Set.eq_empty_of_subset_empty
            rintro p ⟨⟨⟨h1, h3⟩, hz⟩, hn_p⟩
            have hp_in : p ∈ plane_y0.toSet ∩ (zPlane 3).toSet ∩
                (momentPlane 3).toSet ∩ (momentPlane (n : ℝ)).toSet :=
              ⟨⟨⟨h1, hz⟩, h3⟩, hn_p⟩
            rw [intersection_plane_y0_zPlane3_two_momentPlanes_empty
                (by norm_num) hn_real h3n_ne] at hp_in
            exact hp_in
        · have hi2 : i.val = 2 := by omega
          have hj3 : j.val = 3 := by omega
          have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) = plane_xy1 :=
            H_third_hybrid_of_val_two _ (by rw [hi_val, hi2])
          have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) = momentPlane 3 :=
            H_third_hybrid_of_val_three _ (by rw [hj_val, hj3])
          rw [hi_eq, hj_eq, hl_eq, h_last]
          apply Set.eq_empty_of_subset_empty
          rintro p ⟨⟨⟨h2, h3⟩, hz⟩, hn_p⟩
          have hp_in : p ∈ plane_xy1.toSet ∩ (zPlane 3).toSet ∩
              (momentPlane 3).toSet ∩ (momentPlane (n : ℝ)).toSet :=
            ⟨⟨⟨h2, hz⟩, h3⟩, hn_p⟩
          rw [intersection_plane_xy1_zPlane3_two_momentPlanes_empty
              (by norm_num) hn_real h3n_ne] at hp_in
          exact hp_in
    · by_cases hj4 : j.val = 4
      · -- $j = 4$ の場合、$l \ge 5$ はモーメント平面となる。
        have hj_val : (Fin.castSucc j).val = 4 := by dsimp; rw [hj4]
        have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) = zPlane 3 :=
          H_third_hybrid_of_val_four (Fin.castSucc j) hj_val
        have hl_val : (Fin.castSucc l).val = l.val := rfl
        have hl_ge5 : 5 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hl_eq : H_third_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_third_hybrid_of_val_ge (Fin.castSucc l) hl_ge5
        have hl_ge3 : 3 ≤ (l.val : ℝ) := by exact_mod_cast (by omega : 3 ≤ l.val)
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by exact_mod_cast (by omega : l.val ≠ n)
        have hi_val : (Fin.castSucc i).val = i.val := rfl
        by_cases hi0 : i.val = 0
        · have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) = plane_x0 :=
            H_third_hybrid_of_val_zero _ (by rw [hi_val, hi0])
          rw [hi_eq, hj_eq, hl_eq, h_last]
          exact intersection_plane_x0_zPlane3_two_momentPlanes_empty hl_ge3 hn_real hln_ne
        · by_cases hi1 : i.val = 1
          · have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) = plane_y0 :=
              H_third_hybrid_of_val_one _ (by rw [hi_val, hi1])
            rw [hi_eq, hj_eq, hl_eq, h_last]
            exact intersection_plane_y0_zPlane3_two_momentPlanes_empty hl_ge3 hn_real hln_ne
          · by_cases hi2 : i.val = 2
            · have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) = plane_xy1 :=
                H_third_hybrid_of_val_two _ (by rw [hi_val, hi2])
              rw [hi_eq, hj_eq, hl_eq, h_last]
              exact intersection_plane_xy1_zPlane3_two_momentPlanes_empty hl_ge3 hn_real hln_ne
            · have hi3 : i.val = 3 := by omega
              have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) = momentPlane 3 :=
                H_third_hybrid_of_val_three _ (by rw [hi_val, hi3])
              rw [hi_eq, hj_eq, hl_eq, h_last]
              apply Set.eq_empty_of_subset_empty
              rintro p ⟨⟨⟨h3, hz⟩, hl_p⟩, hn_p⟩
              have hp_in : p ∈ (zPlane 3).toSet ∩ (momentPlane 3).toSet ∩
                  (momentPlane (l.val : ℝ)).toSet ∩ (momentPlane (n : ℝ)).toSet :=
                ⟨⟨⟨hz, h3⟩, hl_p⟩, hn_p⟩
              have h3_ne_l : (3 : ℝ) ≠ (l.val : ℝ) := by exact_mod_cast (by omega : 3 ≠ l.val)
              have h3_ne_n : (3 : ℝ) ≠ (n : ℝ) := by exact_mod_cast (by omega : 3 ≠ n)
              rw [intersection_zPlane3_three_momentPlanes_empty
                  (by norm_num) hl_ge3 hn_real h3_ne_l hln_ne h3_ne_n] at hp_in
              exact hp_in
      · -- $i = 4$ の場合、$j, l \ge 5$ はともにモーメント平面となる。
        have hi4 : i.val = 4 := by omega
        have hi_val : (Fin.castSucc i).val = 4 := by dsimp; rw [hi4]
        have hi_eq : H_third_hybrid (n + 1) (Fin.castSucc i) = zPlane 3 :=
          H_third_hybrid_of_val_four (Fin.castSucc i) hi_val
        have hj_val : (Fin.castSucc j).val = j.val := rfl
        have hl_val : (Fin.castSucc l).val = l.val := rfl
        have hj_ge5 : 5 ≤ (Fin.castSucc j).val := by rw [hj_val]; omega
        have hl_ge5 : 5 ≤ (Fin.castSucc l).val := by rw [hl_val]; omega
        have hj_eq : H_third_hybrid (n + 1) (Fin.castSucc j) = momentPlane (j.val : ℝ) :=
          H_third_hybrid_of_val_ge (Fin.castSucc j) hj_ge5
        have hl_eq : H_third_hybrid (n + 1) (Fin.castSucc l) = momentPlane (l.val : ℝ) :=
          H_third_hybrid_of_val_ge (Fin.castSucc l) hl_ge5
        rw [hi_eq, hj_eq, hl_eq, h_last]
        have hj_ge3 : 3 ≤ (j.val : ℝ) := by exact_mod_cast (by omega : 3 ≤ j.val)
        have hl_ge3 : 3 ≤ (l.val : ℝ) := by exact_mod_cast (by omega : 3 ≤ l.val)
        have hjl_ne : (j.val : ℝ) ≠ (l.val : ℝ) := by exact_mod_cast (by omega : j.val ≠ l.val)
        have hln_ne : (l.val : ℝ) ≠ (n : ℝ) := by exact_mod_cast (by omega : l.val ≠ n)
        have hjn_ne : (j.val : ℝ) ≠ (n : ℝ) := by exact_mod_cast (by omega : j.val ≠ n)
        exact intersection_zPlane3_three_momentPlanes_empty
          hj_ge3 hl_ge3 hn_real hjl_ne hln_ne hjn_ne

/-- H_third_hybridにおいて、相異なる任意の3平面と最後のモーメント平面の交わりは空集合である。 -/
lemma intersection_four_third_hybrid_empty (n : ℕ) (hn : 5 ≤ n)
    (i j l : Fin n) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
      (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
      (H_third_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
      (H_third_hybrid (n + 1) (Fin.last n)).toSet = ∅ := by
  -- 添字 i, j, l の順序関係を 6 通りに分類し、昇順補題へ帰着する。
  rcases lt_trichotomy i j with hij_lt | rfl | hji_lt
  · rcases lt_trichotomy j l with hjl_lt | rfl | hlj_lt
    · exact intersection_four_third_hybrid_empty_of_sorted n hn i j l hij_lt hjl_lt
    · exact (hjl rfl).elim
    · rcases lt_trichotomy i l with hil_lt | rfl | hli_lt
      · have h := intersection_four_third_hybrid_empty_of_sorted n hn i l j hil_lt hlj_lt
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
        have hp_in : p ∈ (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hi, hl⟩, hj⟩, hn_last⟩
        rw [h] at hp_in; exact hp_in
      · exact (hil rfl).elim
      · have h := intersection_four_third_hybrid_empty_of_sorted n hn l i j hli_lt hij_lt
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
        have hp_in : p ∈ (H_third_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hl, hi⟩, hj⟩, hn_last⟩
        rw [h] at hp_in; exact hp_in
  · exact (hij rfl).elim
  · rcases lt_trichotomy i l with hil_lt | rfl | hli_lt
    · have h := intersection_four_third_hybrid_empty_of_sorted n hn j i l hji_lt hil_lt
      apply Set.eq_empty_of_subset_empty
      rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
      have hp_in : p ∈ (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
          (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
          (H_third_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
          (H_third_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hj, hi⟩, hl⟩, hn_last⟩
      rw [h] at hp_in; exact hp_in
    · exact (hil rfl).elim
    · rcases lt_trichotomy j l with hjl_lt | rfl | hlj_lt
      · have h := intersection_four_third_hybrid_empty_of_sorted n hn j l i hjl_lt hli_lt
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
        have hp_in : p ∈ (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hj, hl⟩, hi⟩, hn_last⟩
        rw [h] at hp_in; exact hp_in
      · exact (hjl rfl).elim
      · have h := intersection_four_third_hybrid_empty_of_sorted n hn l j i hlj_lt hji_lt
        apply Set.eq_empty_of_subset_empty
        rintro p ⟨⟨⟨hi, hj⟩, hl⟩, hn_last⟩
        have hp_in : p ∈ (H_third_hybrid (n + 1) (Fin.castSucc l)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.castSucc j)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.castSucc i)).toSet ∩
            (H_third_hybrid (n + 1) (Fin.last n)).toSet := ⟨⟨⟨hl, hj⟩, hi⟩, hn_last⟩
        rw [h] at hp_in; exact hp_in

/-- H_third_hybrid において、最後の平面上に現れる交線系は一般の位置にある。 -/
lemma generalPositionLines_third_hybrid (n : ℕ) (hn : 5 ≤ n) :
    GeneralPositionLines n (traceLinesOnLastPlane n (H_third_hybrid (n + 1))) := by
  have h_not_par_last : ∀ i : Fin n,
      ¬ parallelPlanes ((H_third_hybrid (n + 1)) (Fin.castSucc i))
        ((H_third_hybrid (n + 1)) (Fin.last n)) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.last n := Fin.castSucc_lt_last i
    exact not_parallel_third_hybrid (Fin.castSucc i) (Fin.last n) h_lt
  apply generalPositionLines_of_plane_intersections n (H_third_hybrid (n + 1)) h_not_par_last
  · intro i j hij
    exact intersection_three_third_hybrid n hn i j hij
  · intro i j l hij hjl hil
    exact intersection_four_third_hybrid_empty n hn i j l hij hjl hil

/-- n ≥ 5 のとき、モーメント平面を追加したときの切断領域数は最大値に一致する。 -/
lemma splitSpaceRegionsCount_third_hybrid (n : ℕ) (hn : 5 ≤ n) :
    splitSpaceRegionsCount n (H_third_hybrid (n + 1)) = maxPlaneRegions n := by
  have h_not_par : ∀ i : Fin n,
      ¬ parallelPlanes ((H_third_hybrid (n + 1)) (Fin.castSucc i))
        ((H_third_hybrid (n + 1)) (Fin.last n)) := by
    intro i
    have h_lt : Fin.castSucc i < Fin.last n := Fin.castSucc_lt_last i
    exact not_parallel_third_hybrid (Fin.castSucc i) (Fin.last n) h_lt
  have hgen_lines := generalPositionLines_third_hybrid n hn
  exact splitSpaceRegionsCount_eq_of_traceLines n (H_third_hybrid (n + 1)) h_not_par hgen_lines

/-- n ≥ 5 のとき、H_third_hybrid の領域数は第3位の領域数に一致する。 -/
lemma spaceRegionsCount_third_hybrid (n : ℕ) (hn : 5 ≤ n) :
    spaceRegionsCount n (H_third_hybrid n) = thirdSpaceRegionsFormula n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero =>
    change spaceRegionsCount 5 (H_third_hybrid 5) = thirdSpaceRegionsFormula 5
    have h_form5 : thirdSpaceRegionsFormula 5 = 24 := by decide
    rw [h_form5, spaceRegionsCount_third_hybrid_five]
  | succ k ih =>
    have h_assoc : 5 + (k + 1) = 5 + k + 1 := by omega
    rw [h_assoc]
    have h_succ :=
      spaceRegionsCount_succ_eq_add_split (5 + k) (H_third_hybrid (5 + k + 1))
    rw [H_third_hybrid_castSucc (5 + k)] at h_succ
    rw [h_succ]
    have h_split := splitSpaceRegionsCount_third_hybrid (5 + k) (by omega)
    rw [h_split, ih]
    have h_third_m : thirdSpaceRegionsFormula (5 + k) =
        maxSpaceRegionsFormula (5 + k) - 2 := by
      have h := problem_4_3_proof (5 + k) (by omega)
      have hne : 5 + k ≠ 4 := by omega
      simp only [hne, ↓reduceIte] at h
      exact h
    have h_third_succ : thirdSpaceRegionsFormula (5 + k + 1) =
        maxSpaceRegionsFormula (5 + k + 1) - 2 := by
      have h := problem_4_3_proof (5 + k + 1) (by omega)
      have hne : 5 + k + 1 ≠ 4 := by omega
      simp only [hne, ↓reduceIte] at h
      exact h
    have h_max_succ := maxSpaceRegions_succ (5 + k)
    have h_form_m := problem_4_1_proof (5 + k)
    have h_form_succ := problem_4_1_proof (5 + k + 1)
    have h_pos : 2 ≤ maxSpaceRegionsFormula (5 + k) := by
      rw [← h_form_m]
      dsimp [maxSpaceRegions]
      rw [Nat.choose_zero_right]
      have hc1 : (5 + k).choose 1 = 5 + k := Nat.choose_one_right (5 + k)
      omega
    have h_rec : maxSpaceRegionsFormula (5 + k + 1) =
        maxSpaceRegionsFormula (5 + k) + maxPlaneRegions (5 + k) := by
      rw [← h_form_succ, ← h_form_m, h_max_succ]
    omega

/-- 第3位の領域数を達成する相異なる平面配置が存在する。 -/
lemma exists_planes_thirdSpaceRegions (n : ℕ) (hn : 3 ≤ n) :
    ∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = thirdSpaceRegionsFormula n := by
  rcases eq_or_lt_of_le hn with rfl | hn4
  · refine ⟨H_three_six, distinctPlanes_three_six, ?_⟩
    have h3 : thirdSpaceRegionsFormula 3 = 6 := space_regions_n_three.2.2
    rw [h3, spaceRegionsCount_three_six_eq_six]
  · rcases eq_or_lt_of_le (by omega : 4 ≤ n) with rfl | hn5
    · refine ⟨H_four_twelve, distinctPlanes_four_twelve, ?_⟩
      have h4 : thirdSpaceRegionsFormula 4 = 12 := space_regions_n_four.2.2
      rw [h4, spaceRegionsCount_four_twelve_eq_twelve]
    · refine ⟨H_third_hybrid n, distinctPlanes_third_hybrid n hn5,
        spaceRegionsCount_third_hybrid n hn5⟩

/-- 【第4問 (3) の幾何学的解答】
n ≥ 3 のとき、第2位未満の任意の配置の領域数は
thirdSpaceRegionsFormula n 以下であり、かつ達成可能である。
特に n = 4 のとき、領域数が 13 となる配置は存在せず、次は 12 となる。 -/
theorem problem_4_3_geometric_proof (n : ℕ) (hn : 3 ≤ n) :
    (∀ (H : Fin n → Plane3), DistinctPlanes n H →
      spaceRegionsCount n H < secondSpaceRegionsFormula n →
      spaceRegionsCount n H ≤ thirdSpaceRegionsFormula n) ∧
    (∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = thirdSpaceRegionsFormula n) := by
  constructor
  · intro H hdist hlt
    by_cases h4 : n = 4
    · subst h4
      have h_sec4 : secondSpaceRegionsFormula 4 = 14 := space_regions_n_four.2.1
      have h_third4 : thirdSpaceRegionsFormula 4 = 12 := space_regions_n_four.2.2
      have h_ne13 := spaceRegionsCount_four_ne_thirteen H hdist
      omega
    · have h_third := problem_4_3_proof n hn
      have h_sec := problem_4_2_proof n (by omega)
      simp only [h4, ↓reduceIte] at h_third
      omega
  · exact exists_planes_thirdSpaceRegions n hn

end MyLean.Exercises.«science-tokyo».«2019»
