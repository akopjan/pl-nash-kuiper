module

public import BrehmApprox.EuclideanRigidity
public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Compact Euclidean polytope neighborhoods

Every finite Euclidean polytope has arbitrarily small full-dimensional
polytope neighborhoods. The construction is the proved finite-dimensional
convex-neighborhood theorem from mathlib, with all compactness and finite
determination consequences supplied explicitly.
-/

@[expose] public section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An actual finite convex Euclidean polytope, including the empty polytope. -/
def EuclideanPolytope (A : Set E) : Prop :=
  ∃ V : Finset E, A = convexHull ℝ (V : Set E)

lemma isCompact_euclideanPolytope {A : Set E} (hA : EuclideanPolytope A) : IsCompact A := by
  obtain ⟨V, rfl⟩ := hA
  exact V.finite_toSet.isCompact_convexHull ℝ

lemma determinedOn_euclideanPolytope {A : Set E} {g : E → E}
    (hA : EuclideanPolytope A) (hg : LocallyEuclideanPL g) : DeterminedOn A g := by
  obtain ⟨V, rfl⟩ := hA
  exact determinedOn_euclideanPL (hg V)

variable [FiniteDimensional ℝ E]

/-- A finite polytope can be thickened to another finite polytope inside any
given open neighborhood; containment in the interior is in the ambient space. -/
theorem euclidean_convexHull_neighborhood (V : Finset E) {U : Set E}
    (hU : IsOpen U) (hVU : convexHull ℝ (V : Set E) ⊆ U) :
    ∃ W : Finset E, convexHull ℝ (V : Set E) ⊆ interior (convexHull ℝ (W : Set E)) ∧
      convexHull ℝ (W : Set E) ⊆ U :=
  (convex_convexHull ℝ (V : Set E)).exists_subset_interior_convexHull_finset_of_isCompact
    (V.finite_toSet.isCompact_convexHull ℝ) (hU.mem_nhdsSet.mpr hVU)

/-- The admissible neighborhood-basis statement needed by the finite collar
construction. Its witnesses are actual compact convex polytopes. -/
theorem euclidean_polytope_neighborhood_basis {A : Set E}
    (hA : EuclideanPolytope A) {U : Set E} (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ W : Set E, EuclideanPolytope W ∧ IsCompact W ∧ A ⊆ interior W ∧ W ⊆ U := by
  obtain ⟨V, rfl⟩ := hA
  obtain ⟨W, hVW, hWU⟩ := euclidean_convexHull_neighborhood V hU hAU
  exact ⟨convexHull ℝ (W : Set E), ⟨W, rfl⟩,
    W.finite_toSet.isCompact_convexHull ℝ, hVW, hWU⟩

end BrehmApprox
