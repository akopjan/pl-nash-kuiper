module

public import BrehmApprox.SimplexFaces
public import Mathlib.Analysis.Convex.Caratheodory

/-!
# Stellar subdivision at a point of a simplex

The coverage argument is the minimum-ratio construction in barycentric
coordinates. It applies to a point in any face, not only to an interior point.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance stellarDecidableEq : DecidableEq E := Classical.decEq E

/-- A point in a finite convex hull belongs to a cone from `p` over a facet
whose omitted vertex has positive barycentric weight at `p`. -/
theorem mem_stellar_cone_of_weights
    (V : Finset E) (p : E) (w : E → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) (hw1 : ∑ v ∈ V, w v = 1)
    (hwp : ∑ v ∈ V, w v • v = p) {x : E}
    (hx : x ∈ convexHull ℝ (V : Set E)) :
    ∃ v ∈ V, 0 < w v ∧ x ∈ convexHull ℝ ((insert p (V.erase v) : Finset E) : Set E) := by
  classical
  obtain ⟨u, hu, hu1, hux⟩ := Finset.mem_convexHull'.mp hx
  let A := V.filter fun v => 0 < w v
  have hA : A.Nonempty := by
    have hs : 0 < ∑ v ∈ V, w v := by rw [hw1]; norm_num
    obtain ⟨v, hv, hwv⟩ := (Finset.sum_pos_iff_of_nonneg hw).mp hs
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hwv⟩⟩
  obtain ⟨v, hvA, hmin⟩ := A.exists_min_image (fun v => u v / w v) hA
  obtain ⟨hv, hwv⟩ := Finset.mem_filter.mp hvA
  let α : ℝ := u v / w v
  have hα0 : 0 ≤ α := div_nonneg (hu v hv) hwv.le
  let k : E → ℝ := fun z => u z - α * w z
  have hk (z : E) (hz : z ∈ V) : 0 ≤ k z := by
    by_cases hwz : 0 < w z
    · have hm := hmin z (Finset.mem_filter.mpr ⟨hz, hwz⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ hwz).mp hm)
    · have hwz0 : w z = 0 := le_antisymm (le_of_not_gt hwz) (hw z hz)
      simpa only [k, hwz0, mul_zero, sub_zero] using hu z hz
  have hkv : k v = 0 := by simp [k, α, hwv.ne']
  have hksum : ∑ z ∈ V, k z = 1 - α := by
    simp only [k, Finset.sum_sub_distrib, ← Finset.mul_sum, hu1, hw1, mul_one]
  have hα1 : α ≤ 1 := by
    have hnonneg := Finset.sum_nonneg hk
    rw [hksum] at hnonneg
    linarith
  have hkrep : ∑ z ∈ V, k z • z = x - α • p := by
    simp only [k, sub_smul, mul_smul, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hux, hwp]
  refine ⟨v, hv, hwv, ?_⟩
  by_cases hα : α = 1
  · have hkzero (z : E) (hz : z ∈ V) : k z = 0 := by
      have hle : k z ≤ ∑ y ∈ V, k y := Finset.single_le_sum hk hz
      rw [hksum, hα, sub_self] at hle
      exact le_antisymm hle (hk z hz)
    have hxp : x = p := by
      have hsumzero : ∑ z ∈ V, k z • z = 0 := by
        apply Finset.sum_eq_zero
        intro z hz
        rw [hkzero z hz, zero_smul]
      rw [hkrep, hα, one_smul] at hsumzero
      exact sub_eq_zero.mp hsumzero
    rw [hxp]
    exact subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
  · have hden : 0 < 1 - α := sub_pos.mpr (lt_of_le_of_ne hα1 hα)
    let y : E := ∑ z ∈ V.erase v, (k z / (1 - α)) • z
    have hysum : ∑ z ∈ V.erase v, k z / (1 - α) = 1 := by
      rw [← Finset.sum_div, Finset.sum_erase_eq_sub hv, hkv, sub_zero, hksum,
        div_self hden.ne']
    have hy : y ∈ convexHull ℝ (V.erase v : Set E) :=
      Finset.mem_convexHull'.mpr ⟨fun z => k z / (1 - α),
        fun z hz => div_nonneg (hk z (Finset.mem_of_mem_erase hz)) hden.le, hysum, rfl⟩
    have hscale : (1 - α) • y = x - α • p := by
      dsimp [y]
      rw [Finset.smul_sum]
      simp_rw [smul_smul, mul_div_cancel₀ _ hden.ne']
      rw [Finset.sum_erase_eq_sub hv, hkv, zero_smul, sub_zero, hkrep]
    have hpC : p ∈ convexHull ℝ ((insert p (V.erase v) : Finset E) : Set E) :=
      subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
    have hyC : y ∈ convexHull ℝ ((insert p (V.erase v) : Finset E) : Set E) :=
      convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hy
    have hcombo := (convex_convexHull ℝ ((insert p (V.erase v) : Finset E) : Set E)) hpC hyC
      hα0 hden.le (show α + (1 - α) = 1 by ring)
    have hxcombo : α • p + (1 - α) • y = x := by rw [hscale]; abel
    rwa [hxcombo] at hcombo

/-- A positive barycentric coordinate excludes the affine span of the opposite
facet. This is the nondegeneracy required for stellar cones. -/
theorem not_mem_affineSpan_erase_of_positive_weight
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    (p : E) (w : E → ℝ) (hw1 : ∑ v ∈ V, w v = 1)
    (hwp : ∑ v ∈ V, w v • v = p) {v : E} (hv : v ∈ V) (hwv : 0 < w v) :
    p ∉ affineSpan ℝ (V.erase v : Set E) := by
  classical
  let i : V := ⟨v, hv⟩
  have hsum : ∑ j : V, w j.val = 1 := by rw [Finset.sum_coe_sort V w, hw1]
  have hcombo : Finset.univ.affineCombination ℝ ((↑) : V → E) (fun j => w j.val) = p := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
      Finset.sum_coe_sort V (fun z => w z • z), hwp]
  have himage : ((↑) : V → E) '' {j : V | j ≠ i} = (V.erase v : Set E) := by
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨fun he => hj (Subtype.ext he), j.property⟩
    · rintro ⟨hzv, hz⟩
      exact ⟨⟨z, hz⟩, fun he => hzv (congrArg Subtype.val he), rfl⟩
  intro hp
  have hzero := hV.eq_zero_of_affineCombination_mem_affineSpan hsum
    (show Finset.univ.affineCombination ℝ ((↑) : V → E) (fun j => w j.val) ∈
      affineSpan ℝ (((↑) : V → E) '' {j : V | j ≠ i}) by rw [hcombo, himage]; exact hp)
    (i := i) (Finset.mem_univ _) (by simp)
  exact hwv.ne' hzero

/-- Stellar cones over faces avoiding the center cover the original simplex. -/
theorem exists_stellar_face_avoiding_center
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    {p x : E} (hp : p ∈ convexHull ℝ (V : Set E))
    (hx : x ∈ convexHull ℝ (V : Set E)) :
    ∃ U : Finset E, U ⊆ V ∧ p ∉ convexHull ℝ (U : Set E) ∧
      x ∈ convexHull ℝ ((insert p U : Finset E) : Set E) := by
  obtain ⟨w, hw, hw1, hwp⟩ := Finset.mem_convexHull'.mp hp
  obtain ⟨v, hv, hwv, hxU⟩ := mem_stellar_cone_of_weights V p w hw hw1 hwp hx
  refine ⟨V.erase v, Finset.erase_subset _ _, ?_, hxU⟩
  exact fun h => not_mem_affineSpan_erase_of_positive_weight V hV p w hw1 hwp hv hwv
    (convexHull_subset_affineSpan (V.erase v : Set E) h)

/-- Each maximal stellar cone is a genuine simplex. -/
theorem affineIndependent_stellar_cone
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    (p : E) (w : E → ℝ) (hw1 : ∑ v ∈ V, w v = 1)
    (hwp : ∑ v ∈ V, w v • v = p) {v : E} (hv : v ∈ V) (hwv : 0 < w v) :
    AffineIndependent ℝ ((↑) : (insert p (V.erase v) : Finset E) → E) := by
  classical
  let i : V := ⟨v, hv⟩
  let q : V → E := Function.update ((↑) : V → E) i p
  have himage : ((↑) : V → E) '' {j : V | j ≠ i} = (V.erase v : Set E) := by
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨fun he => hj (Subtype.ext he), j.property⟩
    · rintro ⟨hzv, hz⟩
      exact ⟨⟨z, hz⟩, fun he => hzv (congrArg Subtype.val he), rfl⟩
  have hq : AffineIndependent ℝ q :=
    hV.affineIndependent_update_of_notMem_affineSpan (i := i) (by
      rw [himage]
      exact not_mem_affineSpan_erase_of_positive_weight V hV p w hw1 hwp hv hwv)
  have hrange : Set.range q = ((insert p (V.erase v) : Finset E) : Set E) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hj : j = i
      · subst j
        simp [q]
      · simp only [q, Function.update_of_ne hj]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨fun he => hj (Subtype.ext he), j.property⟩)
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ⟨i, Function.update_self _ _ _⟩
      · obtain ⟨hzv, hz⟩ := Finset.mem_erase.mp hz
        refine ⟨⟨z, hz⟩, ?_⟩
        exact Function.update_of_ne (fun he => hzv (congrArg Subtype.val he)) _ _
  have hqr := hq.range
  change AffineIndependent ℝ ((↑) : Set.range q → E) at hqr
  rw [hrange] at hqr
  exact hqr

private theorem stellar_weights_lift
    (V : Finset E) (p : E) (hp : p ∉ V) (w : E → ℝ)
    (hw1 : ∑ z ∈ V, w z = 1) (hwp : ∑ z ∈ V, w z • z = p)
    (i : E) (a : E → ℝ) {x : E}
    (ha1 : ∑ z ∈ insert p (V.erase i), a z = 1)
    (hax : ∑ z ∈ insert p (V.erase i), a z • z = x) :
    (∑ z ∈ V, (a p * w z + if z = i then 0 else a z)) = 1 ∧
    (∑ z ∈ V, (a p * w z + if z = i then 0 else a z) • z) = x := by
  have hp' : p ∉ V.erase i := fun h => hp (Finset.mem_of_mem_erase h)
  rw [Finset.sum_insert hp'] at ha1 hax
  have hs : ∑ z ∈ V, (if z = i then (0 : ℝ) else a z) = ∑ z ∈ V.erase i, a z := by
    simp [Finset.sum_ite, Finset.filter_ne']
  have hv : ∑ z ∈ V, (if z = i then (0 : ℝ) else a z) • z =
      ∑ z ∈ V.erase i, a z • z := by
    simp [Finset.sum_ite, ite_smul, Finset.filter_ne']
  constructor
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hw1, mul_one, hs]
    exact ha1
  · simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, hwp, hv]
    exact hax

/-- Maximal stellar cones meet along their common vertex faces. -/
theorem stellar_cone_intersection
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    (p : E) (hp : p ∉ V) (w : E → ℝ)
    (_hw : ∀ v ∈ V, 0 ≤ w v) (hw1 : ∑ v ∈ V, w v = 1)
    (hwp : ∑ v ∈ V, w v • v = p)
    {i j : E} (hi : i ∈ V) (hj : j ∈ V) (hwi : 0 < w i) (hwj : 0 < w j) :
    convexHull ℝ ((insert p (V.erase i) : Finset E) : Set E) ∩
      convexHull ℝ ((insert p (V.erase j) : Finset E) : Set E) =
    convexHull ℝ ((insert p ((V.erase i).erase j) : Finset E) : Set E) := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, ha1, hax⟩ := Finset.mem_convexHull'.mp hx.1
    obtain ⟨b, hb, hb1, hbx⟩ := Finset.mem_convexHull'.mp hx.2
    obtain ⟨hasum, harep⟩ := stellar_weights_lift V p hp w hw1 hwp i a ha1 hax
    obtain ⟨hbsum, hbrep⟩ := stellar_weights_lift V p hp w hw1 hwp j b hb1 hbx
    have heq := hV.eq_of_sum_eq_sum_subtype (hasum.trans hbsum.symm) (harep.trans hbrep.symm)
    have hei := heq i hi
    have hej := heq j hj
    simp only [ite_true, add_zero, ite_eq_right hij, ite_eq_right (Ne.symm hij)] at hei hej
    have hai : 0 ≤ a j := ha j (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩))
    have hbj : 0 ≤ b i := hb i (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hij, hi⟩))
    have hapbp : a p = b p := by
      have hab : b p ≤ a p := (mul_le_mul_iff_left₀ hwi).mp (by nlinarith [hei])
      have hba : a p ≤ b p := (mul_le_mul_iff_left₀ hwj).mp (by nlinarith [hej])
      exact le_antisymm hba hab
    have haj : a j = 0 := by rw [hapbp] at hej; linarith
    have hjS : j ∈ insert p (V.erase i) :=
      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩)
    have hjp : j ≠ p := by intro h; exact hp (h ▸ hj)
    have herase : (insert p (V.erase i)).erase j = insert p ((V.erase i).erase j) :=
      Finset.erase_insert_of_ne hjp.symm
    apply Finset.mem_convexHull'.mpr
    refine ⟨a, ?_, ?_, ?_⟩
    · intro z hz
      rw [← herase] at hz
      exact ha z (Finset.mem_of_mem_erase hz)
    · rw [← herase, Finset.sum_erase_eq_sub hjS, haj, sub_zero, ha1]
    · rw [← herase, Finset.sum_erase_eq_sub hjS, haj, zero_smul, sub_zero, hax]
  · intro x hx
    constructor
    · apply convexHull_mono (Finset.coe_subset.mpr ?_) hx
      exact Finset.insert_subset_insert _ (Finset.erase_subset _ _)
    · apply convexHull_mono (Finset.coe_subset.mpr ?_) hx
      apply Finset.insert_subset_insert
      exact Finset.erase_subset_erase _ (Finset.erase_subset _ _)

 /-- Common-face intersections pass from maximal simplices to all subfaces. -/
theorem convexHull_subfaces_intersection
    {A B U W : Finset E}
    (hA : AffineIndependent ℝ ((↑) : A → E))
    (hB : AffineIndependent ℝ ((↑) : B → E))
    (hAB : convexHull ℝ (A : Set E) ∩ convexHull ℝ (B : Set E) =
      convexHull ℝ ((A ∩ B : Finset E) : Set E))
    (hUA : U ⊆ A) (hWB : W ⊆ B) :
    convexHull ℝ (U : Set E) ∩ convexHull ℝ (W : Set E) =
      convexHull ℝ ((U ∩ W : Finset E) : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxAB : x ∈ convexHull ℝ ((A ∩ B : Finset E) : Set E) := by
      rw [← hAB]
      exact ⟨convexHull_mono (Finset.coe_subset.mpr hUA) hx.1,
        convexHull_mono (Finset.coe_subset.mpr hWB) hx.2⟩
    have hxUB : x ∈ convexHull ℝ ((U ∩ (A ∩ B) : Finset E) : Set E) := by
      rw [Finset.coe_inter, hA.convexHull_inter hUA Finset.inter_subset_left]
      exact ⟨hx.1, hxAB⟩
    have hUB : U ∩ (A ∩ B) ⊆ B := fun z hz =>
      (Finset.mem_inter.mp (Finset.mem_inter.mp hz).2).2
    have hxUW : x ∈ convexHull ℝ (((U ∩ (A ∩ B)) ∩ W : Finset E) : Set E) := by
      rw [Finset.coe_inter, hB.convexHull_inter hUB hWB]
      exact ⟨hxUB, hx.2⟩
    have he : (U ∩ (A ∩ B)) ∩ W = U ∩ W := by
      ext z
      simp only [Finset.mem_inter]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · exact fun h => ⟨⟨h.1, hUA h.1, hWB h.2⟩, h.2⟩
    rwa [he] at hxUW
  · intro x hx
    exact ⟨convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_left) hx,
      convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_right) hx⟩

/-- All faces of the maximal cones of a stellar subdivision. -/
def stellarFaces (V : Finset E) (p : E) (w : E → ℝ) : Finset (Finset E) :=
  (V.filter fun v => 0 < w v).biUnion fun v => (insert p (V.erase v)).powerset

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_stellarFaces_iff {V : Finset E} {p : E} {w : E → ℝ} {U : Finset E} :
    U ∈ stellarFaces V p w ↔ ∃ v ∈ V, 0 < w v ∧ U ⊆ insert p (V.erase v) := by
  simp only [stellarFaces, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨v, ⟨hv, hw⟩, hU⟩
    exact ⟨v, hv, hw, hU⟩
  · rintro ⟨v, hv, hw, hU⟩
    exact ⟨v, ⟨hv, hw⟩, hU⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem stellarFaces_faces {V : Finset E} {p : E} {w : E → ℝ} {U W : Finset E}
    (hU : U ∈ stellarFaces V p w) (hWU : W ⊆ U) : W ∈ stellarFaces V p w := by
  obtain ⟨v, hv, hwv, hUV⟩ := mem_stellarFaces_iff.mp hU
  exact mem_stellarFaces_iff.mpr ⟨v, hv, hwv, hWU.trans hUV⟩

theorem stellarFaces_independent
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    (p : E) (w : E → ℝ) (hw1 : ∑ v ∈ V, w v = 1)
    (hwp : ∑ v ∈ V, w v • v = p)
    {U : Finset E} (hU : U ∈ stellarFaces V p w) :
    AffineIndependent ℝ ((↑) : U → E) := by
  obtain ⟨v, hv, hwv, hUV⟩ := mem_stellarFaces_iff.mp hU
  exact (affineIndependent_stellar_cone V hV p w hw1 hwp hv hwv).mono
    (Finset.coe_subset.mpr hUV)

theorem stellarFaces_cover
    (V : Finset E) (p : E) (w : E → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) (hw1 : ∑ v ∈ V, w v = 1)
    (hwp : ∑ v ∈ V, w v • v = p) {x : E}
    (hx : x ∈ convexHull ℝ (V : Set E)) :
    ∃ U ∈ stellarFaces V p w, x ∈ convexHull ℝ (U : Set E) := by
  obtain ⟨v, hv, hwv, hxv⟩ := mem_stellar_cone_of_weights V p w hw hw1 hwp hx
  exact ⟨insert p (V.erase v), mem_stellarFaces_iff.mpr ⟨v, hv, hwv, Finset.Subset.refl _⟩, hxv⟩

theorem stellarFaces_intersection
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    (p : E) (hp : p ∉ V) (w : E → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) (hw1 : ∑ v ∈ V, w v = 1)
    (hwp : ∑ v ∈ V, w v • v = p)
    {U W : Finset E} (hU : U ∈ stellarFaces V p w) (hW : W ∈ stellarFaces V p w) :
    convexHull ℝ (U : Set E) ∩ convexHull ℝ (W : Set E) =
      convexHull ℝ ((U ∩ W : Finset E) : Set E) := by
  obtain ⟨i, hi, hwi, hUi⟩ := mem_stellarFaces_iff.mp hU
  obtain ⟨j, hj, hwj, hWj⟩ := mem_stellarFaces_iff.mp hW
  apply convexHull_subfaces_intersection
    (affineIndependent_stellar_cone V hV p w hw1 hwp hi hwi)
    (affineIndependent_stellar_cone V hV p w hw1 hwp hj hwj) ?_ hUi hWj
  have he : insert p (V.erase i) ∩ insert p (V.erase j) = insert p ((V.erase i).erase j) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    tauto
  rw [he]
  exact stellar_cone_intersection V hV p hp w hw hw1 hwp hi hj hwi hwj

/-- A face avoiding a point of a simplex forms a nondegenerate cone with
that point. The point may already be an old vertex. -/
theorem affineIndependent_insert_of_hull_face_avoidance
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    {p : E} (hp : p ∈ convexHull ℝ (V : Set E))
    {U : Finset E} (hUV : U ⊆ V)
    (hpU : p ∉ convexHull ℝ (U : Set E)) :
    AffineIndependent ℝ (fun x : (insert p U : Finset E) => x.val) := by
  obtain ⟨w, hw, hw1, hwp⟩ := Finset.mem_convexHull'.mp hp
  have hv : ∃ v ∈ V, 0 < w v ∧ v ∉ U := by
    by_contra! h
    have hz (v : E) (hv : v ∈ V) (hvU : v ∉ U) : w v = 0 := by
      exact le_antisymm (le_of_not_gt (fun hh => hvU (h v hv hh))) (hw v hv)
    apply hpU
    apply Finset.mem_convexHull'.mpr
    refine ⟨w, fun v hv => hw v (hUV hv), ?_, ?_⟩
    · exact (Finset.sum_subset hUV hz).trans hw1
    · exact (Finset.sum_subset hUV (fun v hv hvU => by rw [hz v hv hvU, zero_smul])).trans hwp
  obtain ⟨v, hv, hwv, hvU⟩ := hv
  apply (affineIndependent_stellar_cone V hV p w hw1 hwp hv hwv).mono
  apply Finset.coe_subset.mpr
  apply Finset.insert_subset_insert
  intro z hz
  exact Finset.mem_erase.mpr ⟨fun he => hvU (he ▸ hz), hUV hz⟩

theorem insert_mem_stellarFaces_of_face_avoidance
    (V : Finset E) (p : E) (w : E → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) (hw1 : ∑ v ∈ V, w v = 1)
    (hwp : ∑ v ∈ V, w v • v = p)
    {U : Finset E} (hUV : U ⊆ V)
    (hpU : p ∉ convexHull ℝ (U : Set E)) :
    insert p U ∈ stellarFaces V p w := by
  have hv : ∃ v ∈ V, 0 < w v ∧ v ∉ U := by
    by_contra! h
    have hz (v : E) (hv : v ∈ V) (hvU : v ∉ U) : w v = 0 :=
      le_antisymm (le_of_not_gt (fun hh => hvU (h v hv hh))) (hw v hv)
    apply hpU
    exact Finset.mem_convexHull'.mpr ⟨w, fun v hv => hw v (hUV hv),
      (Finset.sum_subset hUV hz).trans hw1,
      (Finset.sum_subset hUV (fun v hv hvU => by rw [hz v hv hvU, zero_smul])).trans hwp⟩
  obtain ⟨v, hv, hwv, hvU⟩ := hv
  apply mem_stellarFaces_iff.mpr
  refine ⟨v, hv, hwv, Finset.insert_subset_insert p ?_⟩
  intro z hz
  exact Finset.mem_erase.mpr ⟨fun he => hvU (he ▸ hz), hUV hz⟩

/-- Cones from an arbitrary point over two avoiding faces intersect in
the cone over their common face. This is the spherical-link gluing law. -/
theorem cones_over_avoiding_faces_intersection
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    {p : E} (hp : p ∈ convexHull ℝ (V : Set E))
    {U W : Finset E} (hUV : U ⊆ V) (hWV : W ⊆ V)
    (hpU : p ∉ convexHull ℝ (U : Set E)) (hpW : p ∉ convexHull ℝ (W : Set E)) :
    convexHull ℝ ((insert p U : Finset E) : Set E) ∩
      convexHull ℝ ((insert p W : Finset E) : Set E) =
    convexHull ℝ ((insert p (U ∩ W) : Finset E) : Set E) := by
  have hinter : insert p U ∩ insert p W = insert p (U ∩ W) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert]
    tauto
  by_cases hpV : p ∈ V
  · have hPU : insert p U ⊆ V := Finset.insert_subset_iff.mpr ⟨hpV, hUV⟩
    have hPW : insert p W ⊆ V := Finset.insert_subset_iff.mpr ⟨hpV, hWV⟩
    have he := hV.convexHull_inter hPU hPW
    rw [← Finset.coe_inter, hinter] at he
    exact he.symm
  · obtain ⟨w, hw, hw1, hwp⟩ := Finset.mem_convexHull'.mp hp
    have hU := insert_mem_stellarFaces_of_face_avoidance V p w hw hw1 hwp hUV hpU
    have hW := insert_mem_stellarFaces_of_face_avoidance V p w hw hw1 hwp hWV hpW
    have he := stellarFaces_intersection V hV p hpV w hw hw1 hwp hU hW
    rwa [hinter] at he

end BrehmApprox
