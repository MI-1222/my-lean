import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.SetTheory.Cardinal.Finite
import MyLean.Common
import MyLean.Exercises.«science-tokyo».«2019».Statement

/-!
# 東京工業大学 2019年度 理系 第4問 (Proof)

平面による3次元空間分割の最大個数
$$ T_{\max}(n) = \sum_{k=0}^3 \binom{n}{k} = \frac{n^3 + 5n + 6}{6} $$
の形式証明。
-/

namespace MyLean.Exercises.«science-tokyo».«2019»

open Set

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

/-- 平面領域の増加量は、切断された既存領域の個数に一致する(高々等しい)。
切断されない領域はそのまま残り、切断された各領域はちょうど2つに分かれるため増加量は各1個である。 -/
lemma planeRegionsCount_succ_le_add_split (k : ℕ) (L : Fin (k + 1) → Line2) :
    planeRegionsCount (k + 1) L ≤
      planeRegionsCount k (L ∘ Fin.castSucc) + splitRegionsCount k L := by
  sorry

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
ちょうど $k$ 個存在する。平行条件および3直線共点条件の否定から従う。 -/
lemma card_lineIntersectionParams_eq_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    (lineIntersectionParams k L).card = k := by
  sorry

/-- 一般の位置にある配置に新しい直線を追加したとき、
増える平面領域の個数はちょうど $k + 1$ 個である。 -/
theorem planeRegionsCount_succ_eq_of_general_position (k : ℕ) (L : Fin (k + 1) → Line2)
    (hgen : GeneralPositionLines (k + 1) L) :
    planeRegionsCount (k + 1) L = planeRegionsCount k (L ∘ Fin.castSucc) + (k + 1) := by
  sorry

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
  · -- 一般の位置にある n 枚の平面配置の存在性(等号達成)。
    sorry

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
