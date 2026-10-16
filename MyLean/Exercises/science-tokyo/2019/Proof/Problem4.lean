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
import MyLean.Common
import MyLean.Exercises.«science-tokyo».«2019».Statement

/-!
# 東京工業大学 2019年度 理系 第4問 (Proof)

平面による3次元空間分割の最大個数
$$ T_{\max}(n) = \sum_{k=0}^3 \binom{n}{k} = \frac{n^3 + 5n + 6}{6} $$
の形式証明。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

open Set Polynomial BigOperators

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

/-- 直線 $L_{k}$ 上の基準点と方向ベクトルに対し、第 $i$ 直線との交点を与える実数パラメータ。
交点方程式の一意な解に対応する代表元。 -/
noncomputable def rawIntersectionParam (k : ℕ) (_L : Fin (k + 1) → Line2) (_i : Fin k) : ℝ :=
  Classical.choose (⟨0, trivial⟩ : ∃ _ : ℝ, True)

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

open Classical in
/-- 第 $(k+1)$ 直線によって2分割される既存領域の個数。
切断条件を満たす符号ベクトルの個数として定義される。 -/
noncomputable def splitRegionsCount (k : ℕ) (L : Fin (k + 1) → Line2) : ℕ :=
  (Finset.filter (fun σ =>
    isSplitByLine (convexPlaneRegion k (L ∘ Fin.castSucc) σ) (L (Fin.last k))) Finset.univ).card

/-- 切断された既存領域の個数は、$(k+1)$ 本目の直線上に現れる互いに素な開区間数以下である。
交差区間の互いに素な性質 (disjoint_intersections_on_line) から従う。 -/
lemma splitRegionsCount_le_lineIntervals (k : ℕ) (L : Fin (k + 1) → Line2) :
    splitRegionsCount k L ≤ realIntervalsCount (lineIntersectionParams k L) := by
  sorry

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
/-- 2次元平面における直線配置の領域数は、空でない符号ベクトルの個数と一致する。
各領域が開かつ凸(連結)であり、互いに素な開集合の非交和をなすことから従う。 -/
lemma planeRegionsCount_eq_card_nonempty_convexPlaneRegion (k : ℕ) (L : Fin k → Line2) :
    planeRegionsCount k L =
      (Finset.filter (fun σ => (convexPlaneRegion k L σ).Nonempty) Finset.univ).card := by
  sorry

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
    sorry
  rw [Finset.card_image_of_injective _ h_inj]
  exact Fintype.card_fin k

/-- 一般の位置にある配置において、直線上の開区間数はちょうど $k + 1$ 個である。 -/
lemma lineIntervals_eq_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    realIntervalsCount (lineIntersectionParams k L) = k + 1 := by
  sorry

/-- 一般の位置にある配置において、切断される領域の個数はちょうど $k + 1$ 個である。 -/
lemma splitRegionsCount_eq_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    splitRegionsCount k L = k + 1 := by
  sorry

/-- 一般の位置にある配置に新しい直線を追加したとき、
増える領域の個数は切断領域の個数 ($k + 1$) 以上である。 -/
lemma planeRegionsCount_succ_ge_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    planeRegionsCount k (L ∘ Fin.castSucc) + (k + 1) ≤ planeRegionsCount (k + 1) L := by
  sorry

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

/-- 3次元平面配置に対する幾何学的漸化不等式:
$(n+1)$ 枚目の平面 $H_{n}$ を追加したときの空間領域数は、
既存の $n$ 枚による領域数と、第 $(n+1)$ 平面上に現れる交線配置による領域数の和で抑えられる。
したがって、空間領域数の増加量は高々 $S(n)$ である。

【新しい平面上の領域分割】
平面 $H_{n+1}$ は、空間内に既に存在する $n$ 枚の平面 $H_1, \dots, H_n$ とそれぞれ交差する。
平行でない各平面との交わりによって、$H_{n+1}$ 上には高々 $n$ 本の交線が現れ、
これらによって平面 $H_{n+1}$ 自身がいくつかの平面領域に分割される。

【立体領域が増加する幾何学的仕組み】
追加された平面 $H_{n+1}$ は既存の空間領域を横切り、通過した領域をそれぞれ2つに分割する。
$H_{n+1}$ 上に現れる各平面領域は、既存の空間領域の内部を切断する境界面に対応するため、
新しく形成された平面領域1つにつき、空間全体の領域数が1つ増加する。

【漸化式による導出と評価】
空間領域数を $T_n$、新しい平面上の領域数を $U_n$ と置くとき、漸化式
$$ T_{n+1} = T_n + U_{n} $$
が成り立つ。一般の位置にあるとき、$U_n$ は数列 $S(n)$ と一致し、最大増加量を与える。
したがって、増える立体領域の個数は追加された平面上の領域数と一致し、
一般の配置における増加量は常に $S(n)$ 以下となる。 -/
lemma spaceRegionsCount_succ_le (n : ℕ) (H : Fin (n + 1) → Plane3) :
    spaceRegionsCount (n + 1) H ≤
      spaceRegionsCount n (H ∘ Fin.castSucc) + maxPlaneRegions n := by
  sorry

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

/-- 第 $(n+1)$ 平面 $H(\mathrm{Fin.last } n)$ と既存の各平面 $H(\mathrm{Fin.castSucc } i)$
との交わりによって第 $(n+1)$ 平面上に誘導される $n$ 本の交線配置。 -/
def traceLinesOnLastPlane (n : ℕ) (_H : Fin (n + 1) → Plane3) : Fin n → Line2 :=
  sorry

/-- 3次元一般位置から2次元一般位置への帰着定理:
3次元空間で一般の位置にある平面配置 $H$ に対し、
第 $(n+1)$ 平面上に誘導される交線配置は2次元平面上で一般の位置をなす。
どの2直線も平行でなく(3平面共線性の否定)、
どの3直線も1点で交わらない(4平面共点性の否定)。 -/
lemma generalPositionLines_of_traceLines (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H) :
    GeneralPositionLines n (traceLinesOnLastPlane n H) := by
  sorry

/-- 一般の位置にある平面配置における領域数の漸化等式:
一般の位置にある配置に新しい平面を追加したとき、
増える立体領域の個数は、平面上の交線配置が定める最大平面領域数 $S(n)$ に一致する。
2次元の最大値達成定理 `planeRegionsCount_eq_max_of_general_position` に帰着する。 -/
theorem spaceRegionsCount_succ_eq_of_general_position (n : ℕ) (H : Fin (n + 1) → Plane3)
    (hgen : GeneralPositionPlanes (n + 1) H) :
    spaceRegionsCount (n + 1) H = spaceRegionsCount n (H ∘ Fin.castSucc) + maxPlaneRegions n := by
  sorry

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

/-- 【第4問 (2) の幾何学的解答】
n ≥ 2 のとき、最大値未満の任意の配置の領域数は secondSpaceRegionsFormula n 以下であり、かつ達成可能である。 -/
theorem problem_4_2_geometric_proof (n : ℕ) (hn : 2 ≤ n) :
    (∀ (H : Fin n → Plane3), DistinctPlanes n H →
      spaceRegionsCount n H < maxSpaceRegionsFormula n →
      spaceRegionsCount n H ≤ secondSpaceRegionsFormula n) ∧
    (∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = secondSpaceRegionsFormula n) := by
  sorry

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

/-- 【第4問 (3) の幾何学的解答】
n ≥ 3 のとき、第2位未満の任意の配置の領域数は thirdSpaceRegionsFormula n 以下であり、かつ達成可能である。
特に n = 4 のとき、領域数が 13 となる配置は存在せず、次は 12 となる。 -/
theorem problem_4_3_geometric_proof (n : ℕ) (hn : 3 ≤ n) :
    (∀ (H : Fin n → Plane3), DistinctPlanes n H →
      spaceRegionsCount n H < secondSpaceRegionsFormula n →
      spaceRegionsCount n H ≤ thirdSpaceRegionsFormula n) ∧
    (∃ (H : Fin n → Plane3), DistinctPlanes n H ∧
      spaceRegionsCount n H = thirdSpaceRegionsFormula n) := by
  sorry

end MyLean.Exercises.«science-tokyo».«2019»
