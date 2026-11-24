module

public import PLGeometry.Definitions
public import BrehmApprox.EuclideanGlobalMotions
public import BrehmApprox.AffineSelectionCells
public import BrehmApprox.PolytopeCoverTransport
public import BrehmApprox.PullingPolytopeFamily
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Brehm extension with an actual compatible triangulation

The finite affine-motion extension is cut by its equality arrangement and a
locally finite integer-cube tiling. Pulling triangulations with one vertex
order agree on every common face. This gives the concrete PL-isometry
predicate used in the Challenge.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry

variable {n : ℕ} {I : Type*}

local instance euclideanExtensionDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def euclideanTriangulationOfCover
    [LinearOrder (EuclideanSpace ℝ (Fin n))]
    (K : PolytopeCover (EuclideanSpace ℝ (Fin n)) I) :
    Triangulation .euclidean n (EuclideanSpace ℝ (Fin n)) where
  simplices := Pulling.familyFaces K.cell K.polytope
  cell σ := convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin n)))
  chart _ := id
  cover x := by
    have hx : x ∈ ⋃ i, K.cell i := Set.mem_iUnion.mpr (K.cover x)
    rw [Pulling.family_faces_cover K.cell K.polytope] at hx
    obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨σ, hσ, hxσ⟩
  locallyFinite := Pulling.family_faces_locallyFinite K.cell K.polytope K.locallyFinite
  vertices_mem σ _ := subset_convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin n)))
  simplex σ hσ := by
    unfold simplexVertices
    apply Pulling.family_face_independent K.cell K.polytope
    convert hσ using 1 <;> ext x <;> simp
  image_cell σ _ := by simp [hull]
  isometry_cell _ _ _ _ _ _ := rfl
  faces σ hσ τ hτσ := Pulling.family_face_downward K.cell K.polytope hσ hτσ
  image_face σ hσ τ hτσ := by simp [hull]
  intersection σ hσ τ hτ := by
    simpa only [Finset.coe_inter] using
      Pulling.family_faces_intersection K.cell K.polytope K.face_inter hσ hτ

theorem plIsometry_euclidean_of_finite_motions
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : Continuous f) (hm : FiniteEuclideanMotions f) : PLIsometry .euclidean n f := by
  classical
  letI : LinearOrder (EuclideanSpace ℝ (Fin n)) :=
    IsWellOrder.linearOrder (WellOrderingRel : EuclideanSpace ℝ (Fin n) → _ → Prop)
  obtain ⟨S, hS⟩ := hm
  let a : S → EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun r => r.val.toAffineMap
  have hsel : ∀ x, ∃ r : S, f x = a r x := by
    intro x
    obtain ⟨r, hr, heq⟩ := hS x
    exact ⟨⟨r, hr⟩, heq⟩
  let K := euclideanCubeCover n
  let A := K.arrangement (affineEqualityLinear a) (affineEqualityBound a)
  let T := euclideanTriangulationOfCover A
  refine ⟨hf, T, ?_⟩
  intro σ hσ x hx y hy
  obtain ⟨p, hp⟩ := hσ
  have hsub := Pulling.family_face_subset_cell A.cell A.polytope hp
  obtain ⟨r, hr⟩ := affine_selection_eqOn_arrangement K a hf hsel p
  rw [hr (hsub hx), hr (hsub hy)]
  exact r.val.isometry.dist_eq x y

/-- The Euclidean component of the Brehm–Akopyan–Tarasov statement. -/
theorem brehm_euclidean (n : ℕ)
    (A : Finset (Model .euclidean n)) (f : Model .euclidean n → Model .euclidean n)
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ dist x y) :
    ∃ F : Model .euclidean n → Model .euclidean n,
      LipschitzWith 1 F ∧ PLIsometry .euclidean n F ∧ ∀ x ∈ A, F x = f x := by
  obtain ⟨F, hF, hm, heq⟩ := euclidean_finite_extension_global_motions n A f hf
  have hLip : LipschitzWith 1 F := BrehmApprox.short_iff_lipschitz.mp hF
  exact ⟨F, hLip, plIsometry_euclidean_of_finite_motions hLip.continuous hm, heq⟩

end ArchivePLGeometry
