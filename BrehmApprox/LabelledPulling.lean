module

public import BrehmApprox.PullingComplex

/-!
# Pulling triangulations with source labels

Vertices are ordered in a common source type, while their affine coordinates
may identify vertices belonging to different sheets of a folding. Pulling
triangulations still agree on genuine common faces of the source.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators

namespace BrehmApprox.LabelledPulling

variable {P E : Type*} [LinearOrder P] [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance labelledPullingDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

open Pulling

def faces (q : P → E) (V : Finset P) : Finset (Finset P) :=
  (Finset.univ.filter (fun S : Finset V => IsFace (fun v : V => q v.val) S)).image
    (fun S => S.image ((↑) : V → P))

theorem mem_faces_iff {q : P → E} {V S : Finset P} : S ∈ faces q V ↔
    ∃ T : Finset V, IsFace (fun v : V => q v.val) T ∧ T.image ((↑) : V → P) = S := by
  simp [faces]

theorem face_subset {q : P → E} {V S : Finset P} (hS : S ∈ faces q V) : S ⊆ V := by
  obtain ⟨T, _, rfl⟩ := mem_faces_iff.mp hS
  intro x hx
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
  exact t.property

theorem face_downward {q : P → E} {V S T : Finset P}
    (hS : S ∈ faces q V) (hTS : T ⊆ S) : T ∈ faces q V := by
  obtain ⟨A, hA, rfl⟩ := mem_faces_iff.mp hS
  let B : Finset V := A.filter (fun i => i.val ∈ T)
  refine mem_faces_iff.mpr ⟨B, isFace_mono hA (Finset.filter_subset _ _), ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hi).2
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hTS hx)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩

theorem face_independent {q : P → E} {V S : Finset P} (hS : S ∈ faces q V) :
    AffineIndependent ℝ ((↑) : S.image q → E) := by
  obtain ⟨T, hT, rfl⟩ := mem_faces_iff.mp hS
  have h := (isFace_independent hT).range
  have heq : Set.range (fun i : T => q i.val.val) =
      ((T.image ((↑) : V → P)).image q : Set E) := by
    ext x
    simp
  change AffineIndependent ℝ ((↑) : Set.range (fun i : T => q i.val.val) → E) at h
  rw [heq] at h
  exact h

theorem faces_cover (q : P → E) (V : Finset P) :
    convexHull ℝ (V.image q : Set E) =
      ⋃ S ∈ faces q V, convexHull ℝ (S.image q : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hrange : Set.range (fun v : V => q v.val) = (V.image q : Set E) := by
      ext y
      simp
    rw [← hrange] at hx
    obtain ⟨T, hT, hxT⟩ := exists_face_mem_hull (fun v : V => q v.val) hx
    refine Set.mem_iUnion₂.mpr
      ⟨T.image ((↑) : V → P), mem_faces_iff.mpr ⟨T, hT, rfl⟩, ?_⟩
    simpa only [Finset.image_image, Function.comp_def] using hxT
  · intro x hx
    obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr
      (Finset.image_subset_image (face_subset hS))) hxS

omit [LinearOrder P] in
theorem restrict_barycenter (q : P → E) {V W : Finset P} {w : W → ℝ}
    (hout : ∀ i : W, i.val ∉ V → w i = 0) :
    barycenter (fun i : V => q i.val) (restrict V W w) =
      barycenter (fun i : W => q i.val) w := by
  have hzeroV : ∀ x ∉ V, extend W w x • q x = 0 := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [show extend W w x = 0 by
        simpa only [extend, dite_eq_left hxW] using hout ⟨x, hxW⟩ hx, zero_smul]
    · rw [extend_of_notMem W w hxW, zero_smul]
  calc
    _ = ∑ x ∈ V, extend W w x • q x := Finset.sum_coe_sort _ _
    _ = ∑ x ∈ W, extend W w x • q x :=
      sum_eq_sum_of_support V W _ hzeroV (fun x hx => by
        rw [extend_of_notMem W w hx, zero_smul])
    _ = _ := by
      rw [← Finset.sum_coe_sort W]
      simp only [extend_coe, barycenter]

theorem minimal_cross_equal (q : P → E) {V W : Finset P} {u : V → ℝ} {v : W → ℝ}
    (hu : Minimal (fun i : V => q i.val) u)
    (hv : Minimal (fun i : W => q i.val) v)
    (hbar : barycenter (fun i : V => q i.val) u = barycenter (fun i : W => q i.val) v)
    (huout : ∀ i : V, i.val ∉ W → u i = 0)
    (hvout : ∀ i : W, i.val ∉ V → v i = 0) : extend V u = extend W v := by
  have hu_le := hu.2 (restrict V W v) (restrict_simplex hv.1 hvout)
    ((restrict_barycenter q hvout).trans hbar.symm)
  have hv_le := hv.2 (restrict W V u) (restrict_simplex hu.1 huout)
    ((restrict_barycenter q huout).trans hbar)
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

theorem exists_minimal_of_mem_face {q : P → E} {V S : Finset P}
    (hS : S ∈ faces q V) {x : E} (hx : x ∈ convexHull ℝ (S.image q : Set E)) :
    ∃ u : V → ℝ, Minimal (fun i : V => q i.val) u ∧
      barycenter (fun i : V => q i.val) u = x ∧
      ∀ i : V, i.val ∉ S → u i = 0 := by
  obtain ⟨T, hT, rfl⟩ := mem_faces_iff.mp hS
  simp only [Finset.image_image, Function.comp_def] at hx
  rw [convexHull_eq_barycenter_image (fun i : V => q i.val) T] at hx
  obtain ⟨u, hu, hux⟩ := hx
  refine ⟨u, hT u hu, hux, ?_⟩
  intro i hi
  exact hu.2 i (fun hiT => hi (Finset.mem_image.mpr ⟨i, hiT, rfl⟩))

/-- Two labelled pulling simplices agree over a genuine common extreme face.
No global injectivity of the coordinate map is needed. -/
theorem intersection_over_extreme {q : P → E} {V W S T : Finset P} {D : Set E}
    (hVD : _root_.IsExtreme ℝ (convexHull ℝ (V.image q : Set E)) D)
    (hWD : _root_.IsExtreme ℝ (convexHull ℝ (W.image q : Set E)) D)
    (hverticesV : ∀ p ∈ V, q p ∈ D → p ∈ W)
    (hverticesW : ∀ p ∈ W, q p ∈ D → p ∈ V)
    (hS : S ∈ faces q V) (hT : T ∈ faces q W)
    {x : E} (hxS : x ∈ convexHull ℝ (S.image q : Set E))
    (hxT : x ∈ convexHull ℝ (T.image q : Set E)) (hxD : x ∈ D) :
    x ∈ convexHull ℝ ((S ∩ T).image q : Set E) := by
  obtain ⟨u, hu, hux, husupport⟩ := exists_minimal_of_mem_face hS hxS
  obtain ⟨v, hv, hvx, hvsupport⟩ := exists_minimal_of_mem_face hT hxT
  have huout : ∀ i : V, i.val ∉ W → u i = 0 := by
    intro i hi
    by_contra hui
    have hup : 0 < u i := lt_of_le_of_ne (hu.1.1 i) (Ne.symm hui)
    have hm : q i.val ∈ D :=
      BrehmApprox.IsExtreme.mem_of_positive_weight hVD (convex_convexHull ℝ _)
        (fun j : V => q j.val) u
        (fun j => subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩))
        hu.1.1 hu.1.2 (by change barycenter _ u ∈ D; rwa [hux]) i hup
    exact hi (hverticesV i.val i.property hm)
  have hvout : ∀ i : W, i.val ∉ V → v i = 0 := by
    intro i hi
    by_contra hvi
    have hvp : 0 < v i := lt_of_le_of_ne (hv.1.1 i) (Ne.symm hvi)
    have hm : q i.val ∈ D :=
      BrehmApprox.IsExtreme.mem_of_positive_weight hWD (convex_convexHull ℝ _)
        (fun j : W => q j.val) v
        (fun j => subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩))
        hv.1.1 hv.1.2 (by change barycenter _ v ∈ D; rwa [hvx]) i hvp
    exact hi (hverticesW i.val i.property hm)
  have hext := minimal_cross_equal q hu hv (hux.trans hvx.symm) huout hvout
  have hsupp : (support u).image (fun i : V => q i.val) ⊆ (S ∩ T).image q := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hui : u i ≠ 0 := mem_support.mp hi
    have hiS : i.val ∈ S := by by_contra hiS; exact hui (husupport i hiS)
    have hiT : i.val ∈ T := by
      by_contra hiT
      have hzero := extend_zero_outside hvsupport hiT
      rw [← hext, extend_coe] at hzero
      exact hui hzero
    exact Finset.mem_image.mpr ⟨i.val, Finset.mem_inter.mpr ⟨hiS, hiT⟩, rfl⟩
  rw [← hux]
  exact convexHull_mono (Finset.coe_subset.mpr hsupp)
    (barycenter_mem_convexHull ⟨hu.1, support_subset_iff.mp (Finset.Subset.refl _)⟩)

end BrehmApprox.LabelledPulling
