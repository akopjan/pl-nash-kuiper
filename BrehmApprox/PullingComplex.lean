module

public import BrehmApprox.LexicographicTriangulation
public import BrehmApprox.ExtremeBarycentricSupport

/-!
# Compatible finite pulling complexes

The vertex order is fixed in the ambient space. A polytope is triangulated
by lexicographically minimal barycentric coordinates. The resulting face
sets include the empty simplex and agree along common extreme faces.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators

namespace BrehmApprox.Pulling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

local instance pullingComplexLocalInstance1 : DecidableEq E := Classical.decEq E

def faces (V : Finset E) : Finset (Finset E) :=
  (Finset.univ.filter (fun S : Finset V => IsFace ((↑) : V → E) S)).image
    (fun S => S.image ((↑) : V → E))

theorem mem_faces_iff {V S : Finset E} : S ∈ faces V ↔
    ∃ T : Finset V, IsFace ((↑) : V → E) T ∧ T.image ((↑) : V → E) = S := by
  simp [faces]

theorem face_subset {V S : Finset E} (hS : S ∈ faces V) : S ⊆ V := by
  obtain ⟨T, _, rfl⟩ := mem_faces_iff.mp hS
  intro x hx
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
  exact t.property

theorem face_independent {V S : Finset E} (hS : S ∈ faces V) :
    AffineIndependent ℝ ((↑) : S → E) := by
  obtain ⟨T, hT, rfl⟩ := mem_faces_iff.mp hS
  have h := (isFace_independent hT).range
  have hrange : Set.range (fun i : T => (i.val : E)) =
      (T.image ((↑) : V → E) : Set E) := by ext x; simp
  rw [hrange] at h
  exact h

theorem face_downward {V S T : Finset E} (hS : S ∈ faces V) (hTS : T ⊆ S) :
    T ∈ faces V := by
  obtain ⟨A, hA, rfl⟩ := mem_faces_iff.mp hS
  let B : Finset V := A.filter (fun i => (i : E) ∈ T)
  refine mem_faces_iff.mpr ⟨B, isFace_mono hA (Finset.filter_subset _ _), ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hi).2
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hTS hx)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩

theorem empty_mem_faces (V : Finset E) : ∅ ∈ faces V := by
  refine mem_faces_iff.mpr ⟨∅, ?_, by simp⟩
  intro w hw
  have hwzero : w = 0 := funext (fun i => hw.2 i (Finset.notMem_empty i))
  have hsum := hw.1.2
  rw [hwzero] at hsum
  simp at hsum

theorem faces_cover (V : Finset E) :
    convexHull ℝ (V : Set E) = ⋃ S ∈ faces V, convexHull ℝ (S : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hrange : Set.range ((↑) : V → E) = (V : Set E) := Subtype.range_coe_subtype
    rw [← hrange] at hx
    obtain ⟨T, hT, hxT⟩ := exists_face_mem_hull ((↑) : V → E) hx
    exact Set.mem_iUnion₂.mpr ⟨T.image ((↑) : V → E), mem_faces_iff.mpr ⟨T, hT, rfl⟩, hxT⟩
  · rintro x hx
    obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr (face_subset hS)) hxS

theorem face_intersection {V S T : Finset E} (hS : S ∈ faces V) (hT : T ∈ faces V) :
    convexHull ℝ (S : Set E) ∩ convexHull ℝ (T : Set E) = convexHull ℝ (S ∩ T : Set E) := by
  obtain ⟨A, hA, rfl⟩ := mem_faces_iff.mp hS
  obtain ⟨B, hB, rfl⟩ := mem_faces_iff.mp hT
  rw [isFace_hulls_inter hA hB]
  apply congrArg (convexHull ℝ)
  ext x
  simp only [Finset.mem_coe, Finset.mem_image, Set.mem_inter_iff, Finset.mem_inter]
  constructor
  · rintro ⟨i, ⟨hiA, hiB⟩, rfl⟩
    exact ⟨⟨i, hiA, rfl⟩, ⟨i, hiB, rfl⟩⟩
  · rintro ⟨⟨i, hiA, hi⟩, ⟨j, hjB, hj⟩⟩
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    subst j
    exact ⟨i, ⟨hiA, hjB⟩, hi⟩

/-- Extend a coefficient vector by zero outside its vertex set. -/
def extend (V : Finset E) (w : V → ℝ) (x : E) : ℝ :=
  if hx : x ∈ V then w ⟨x, hx⟩ else 0

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
@[simp] theorem extend_coe (V : Finset E) (w : V → ℝ) (i : V) : extend V w i.val = w i := by
  simp only [extend, dite_eq_left i.property]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
theorem extend_of_notMem (V : Finset E) (w : V → ℝ) {x : E} (hx : x ∉ V) :
    extend V w x = 0 := by simp only [extend, dite_eq_right hx]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extend_lex_lt_iff (V : Finset E) (u v : V → ℝ) :
    Pi.Lex (· < ·) (· < ·) (extend V u) (extend V v) ↔
      toLex u < toLex v := by
  change Pi.Lex (· < ·) (· < ·) (extend V u) (extend V v) ↔ Pi.Lex (· < ·) (· < ·) u v
  constructor
  · rintro ⟨x, hx, hxlt⟩
    have hxV : x ∈ V := by
      by_contra hxV
      rw [extend_of_notMem V u hxV, extend_of_notMem V v hxV] at hxlt
      exact lt_irrefl _ hxlt
    refine ⟨⟨x, hxV⟩, fun j hj => ?_, ?_⟩
    · simpa only [extend_coe] using hx j.val hj
    · simpa only [extend, dite_eq_left hxV] using hxlt
  · rintro ⟨i, hi, hilt⟩
    refine ⟨i.val, fun x hx => ?_, by simpa only [extend_coe] using hilt⟩
    by_cases hxV : x ∈ V
    · simpa only [extend, dite_eq_left hxV] using hi ⟨x, hxV⟩ hx
    · rw [extend_of_notMem V u hxV, extend_of_notMem V v hxV]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
theorem extend_injective (V : Finset E) : Function.Injective (extend V) := by
  intro u v h
  funext i
  simpa only [extend_coe] using congrFun h i.val

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
theorem sum_eq_sum_of_support {A : Type*} [AddCommMonoid A]
    (V W : Finset E) (f : E → A)
    (hV : ∀ x ∉ V, f x = 0) (hW : ∀ x ∉ W, f x = 0) :
    ∑ x ∈ V, f x = ∑ x ∈ W, f x := by
  calc
    ∑ x ∈ V, f x = ∑ x ∈ V ∪ W, f x :=
      Finset.sum_subset Finset.subset_union_left (fun x _ hx => hV x hx)
    _ = ∑ x ∈ W, f x :=
      (Finset.sum_subset Finset.subset_union_right (fun x _ hx => hW x hx)).symm

def restrict (V W : Finset E) (w : W → ℝ) : V → ℝ := fun i => extend W w i.val

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
theorem extend_restrict {V W : Finset E} {w : W → ℝ}
    (hw : ∀ i : W, i.val ∉ V → w i = 0) :
    extend V (restrict V W w) = extend W w := by
  funext x
  by_cases hxV : x ∈ V
  · exact extend_coe V (restrict V W w) ⟨x, hxV⟩
  · rw [extend_of_notMem V _ hxV]
    by_cases hxW : x ∈ W
    · simpa only [extend, dite_eq_left hxW] using (hw ⟨x, hxW⟩ hxV).symm
    · rw [extend_of_notMem W _ hxW]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
theorem restrict_simplex {V W : Finset E} {w : W → ℝ}
    (hw : w ∈ simplexWeights W) (hout : ∀ i : W, i.val ∉ V → w i = 0) :
    restrict V W w ∈ simplexWeights V := by
  have hzeroV : ∀ x ∉ V, extend W w x = 0 := by
    intro x hx
    by_cases hxW : x ∈ W
    · simpa only [extend, dite_eq_left hxW] using hout ⟨x, hxW⟩ hx
    · exact extend_of_notMem W w hxW
  refine ⟨?_, ?_⟩
  · intro i
    dsimp [restrict, extend]
    split_ifs with hi
    · exact hw.1 ⟨i.val, hi⟩
    · exact le_rfl
  · calc
      ∑ i : V, restrict V W w i = ∑ x ∈ V, extend W w x := Finset.sum_coe_sort _ _
      _ = ∑ x ∈ W, extend W w x :=
        sum_eq_sum_of_support V W _ hzeroV (fun x hx => extend_of_notMem W w hx)
      _ = ∑ i : W, w i := by rw [← Finset.sum_coe_sort W]; simp only [extend_coe]
      _ = 1 := hw.2

omit [LinearOrder E] in
theorem restrict_barycenter {V W : Finset E} {w : W → ℝ}
    (hout : ∀ i : W, i.val ∉ V → w i = 0) :
    barycenter ((↑) : V → E) (restrict V W w) = barycenter ((↑) : W → E) w := by
  have hzeroV : ∀ x ∉ V, extend W w x • x = 0 := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [show extend W w x = 0 by simpa only [extend, dite_eq_left hxW] using hout ⟨x, hxW⟩ hx,
        zero_smul]
    · rw [extend_of_notMem W w hxW, zero_smul]
  calc
    barycenter ((↑) : V → E) (restrict V W w) = ∑ x ∈ V, extend W w x • x := by
      exact Finset.sum_coe_sort V (fun x => extend W w x • x)
    _ = ∑ x ∈ W, extend W w x • x :=
      sum_eq_sum_of_support V W _ hzeroV (fun x hx => by rw [extend_of_notMem W w hx, zero_smul])
    _ = barycenter ((↑) : W → E) w := by
      rw [← Finset.sum_coe_sort W]
      simp only [extend_coe, barycenter]

theorem minimal_cross_equal {V W : Finset E} {u : V → ℝ} {v : W → ℝ}
    (hu : Minimal ((↑) : V → E) u) (hv : Minimal ((↑) : W → E) v)
    (hbar : barycenter ((↑) : V → E) u = barycenter ((↑) : W → E) v)
    (huout : ∀ i : V, i.val ∉ W → u i = 0)
    (hvout : ∀ i : W, i.val ∉ V → v i = 0) : extend V u = extend W v := by
  have hu_le := hu.2 (restrict V W v) (restrict_simplex hv.1 hvout)
    ((restrict_barycenter hvout).trans hbar.symm)
  have hv_le := hv.2 (restrict W V u) (restrict_simplex hu.1 huout)
    ((restrict_barycenter huout).trans hbar)
  have hnotuv : ¬Pi.Lex (· < ·) (· < ·) (extend V u) (extend W v) := by
    intro huv
    rw [← extend_restrict huout] at huv
    exact not_lt_of_ge hv_le ((extend_lex_lt_iff W _ _).mp huv)
  have hnotvu : ¬Pi.Lex (· < ·) (· < ·) (extend W v) (extend V u) := by
    intro hvu
    rw [← extend_restrict hvout] at hvu
    exact not_lt_of_ge hu_le ((extend_lex_lt_iff V _ _).mp hvu)
  let U := V ∪ W
  have heu : extend U (restrict U V u) = extend V u :=
    extend_restrict (fun i hi => (hi (Finset.mem_union_left W i.property)).elim)
  have hev : extend U (restrict U W v) = extend W v :=
    extend_restrict (fun i hi => (hi (Finset.mem_union_right V i.property)).elim)
  rcases lt_trichotomy (toLex (restrict U V u)) (toLex (restrict U W v)) with hlt | heq | hgt
  · have h := (extend_lex_lt_iff U _ _).mpr hlt
    rw [heu, hev] at h
    exact (hnotuv h).elim
  · calc
      extend V u = extend U (restrict U V u) := heu.symm
      _ = extend U (restrict U W v) := congrArg (extend U) (congrArg ofLex heq)
      _ = extend W v := hev
  · have h := (extend_lex_lt_iff U _ _).mpr hgt
    rw [heu, hev] at h
    exact (hnotvu h).elim

theorem exists_minimal_of_mem_face {V S : Finset E} (hS : S ∈ faces V) {x : E}
    (hx : x ∈ convexHull ℝ (S : Set E)) :
    ∃ u : V → ℝ, Minimal ((↑) : V → E) u ∧ barycenter ((↑) : V → E) u = x ∧
      ∀ i : V, i.val ∉ S → u i = 0 := by
  obtain ⟨T, hT, rfl⟩ := mem_faces_iff.mp hS
  rw [convexHull_eq_barycenter_image] at hx
  obtain ⟨u, hu, hux⟩ := hx
  refine ⟨u, hT u hu, hux, ?_⟩
  intro i hi
  exact hu.2 i (fun hiT => hi (Finset.mem_image.mpr ⟨i, hiT, rfl⟩))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
theorem extend_zero_outside {V S : Finset E} {u : V → ℝ}
    (hu : ∀ i : V, i.val ∉ S → u i = 0) {x : E} (hx : x ∉ S) :
    extend V u x = 0 := by
  by_cases hxV : x ∈ V
  · have h := hu ⟨x, hxV⟩ hx
    simpa only [extend, dite_eq_left hxV] using h
  · exact extend_of_notMem V u hxV

set_option maxHeartbeats 1000000 in
/-- Pulling triangulations in one vertex order agree across a common extreme
face. The vertex hypotheses say that shared geometric vertices are shared
as elements of the two finite vertex sets. -/
theorem faces_intersection_of_extreme {V W S T : Finset E}
    (hVW : IsExtreme ℝ (convexHull ℝ (V : Set E))
      (convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E)))
    (hWV : IsExtreme ℝ (convexHull ℝ (W : Set E))
      (convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E)))
    (hverticesV : ∀ x ∈ V, x ∈ convexHull ℝ (W : Set E) → x ∈ W)
    (hverticesW : ∀ x ∈ W, x ∈ convexHull ℝ (V : Set E) → x ∈ V)
    (hS : S ∈ faces V) (hT : T ∈ faces W) :
    convexHull ℝ (S : Set E) ∩ convexHull ℝ (T : Set E) = convexHull ℝ (S ∩ T : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u, hu, hux, husupport⟩ := exists_minimal_of_mem_face hS hx.1
    obtain ⟨v, hv, hvx, hvsupport⟩ := exists_minimal_of_mem_face hT hx.2
    have hxV : x ∈ convexHull ℝ (V : Set E) :=
      convexHull_mono (Finset.coe_subset.mpr (face_subset hS)) hx.1
    have hxW : x ∈ convexHull ℝ (W : Set E) :=
      convexHull_mono (Finset.coe_subset.mpr (face_subset hT)) hx.2
    have huout : ∀ i : V, i.val ∉ W → u i = 0 := by
      intro i hi
      by_contra hui
      have hup : 0 < u i := lt_of_le_of_ne (hu.1.1 i) (Ne.symm hui)
      have hm : (i : E) ∈ convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E) :=
        BrehmApprox.IsExtreme.mem_of_positive_weight hVW (convex_convexHull ℝ _)
          ((↑) : V → E) u (fun j => subset_convexHull ℝ _ j.property) hu.1.1 hu.1.2
          (by change barycenter ((↑) : V → E) u ∈ _; rw [hux]; exact ⟨hxV, hxW⟩) i hup
      exact hi (hverticesV i.val i.property hm.2)
    have hvout : ∀ i : W, i.val ∉ V → v i = 0 := by
      intro i hi
      by_contra hvi
      have hvp : 0 < v i := lt_of_le_of_ne (hv.1.1 i) (Ne.symm hvi)
      have hm : (i : E) ∈ convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E) :=
        BrehmApprox.IsExtreme.mem_of_positive_weight hWV (convex_convexHull ℝ _)
          ((↑) : W → E) v (fun j => subset_convexHull ℝ _ j.property) hv.1.1 hv.1.2
          (by change barycenter ((↑) : W → E) v ∈ _; rw [hvx]; exact ⟨hxV, hxW⟩) i hvp
      exact hi (hverticesW i.val i.property hm.1)
    have hext := minimal_cross_equal hu hv (hux.trans hvx.symm) huout hvout
    have hsupp : (support u).image ((↑) : V → E) ⊆ S ∩ T := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hui : u i ≠ 0 := mem_support.mp hi
      have hiS : i.val ∈ S := by by_contra hiS; exact hui (husupport i hiS)
      have hiT : i.val ∈ T := by
        by_contra hiT
        have hzero := extend_zero_outside hvsupport hiT
        rw [← hext, extend_coe] at hzero
        exact hui hzero
      exact Finset.mem_inter.mpr ⟨hiS, hiT⟩
    rw [← hux]
    simpa only [Finset.coe_inter] using convexHull_mono (Finset.coe_subset.mpr hsupp)
      (barycenter_mem_convexHull ⟨hu.1, support_subset_iff.mp (Finset.Subset.refl _)⟩)
  · exact Set.subset_inter
      (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right)

end BrehmApprox.Pulling
