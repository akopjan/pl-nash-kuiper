module

public import BrehmApprox.PolytopeIntersection
public import BrehmApprox.ExtremeBarycentricSupport

/-!
# Canonical vertices of a finite polytope

Extreme points give a finite generating set that is independent of the
chosen presentation. Taking vertices commutes with passage to a face.
-/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance polytopeVerticesLocalInstance1 : DecidableEq E := Classical.decEq E

def IsFinitePolytope (C : Set E) : Prop :=
  ∃ V : Finset E, C = convexHull ℝ (V : Set E)

theorem IsFinitePolytope.finite_extremePoints {C : Set E} (hC : IsFinitePolytope C) :
    (C.extremePoints ℝ).Finite := by
  obtain ⟨V, rfl⟩ := hC
  exact V.finite_toSet.subset extremePoints_convexHull_subset

def polytopeVertices (C : Set E) (hC : IsFinitePolytope C) : Finset E :=
  hC.finite_extremePoints.toFinset

@[simp] theorem coe_polytopeVertices (C : Set E) (hC : IsFinitePolytope C) :
    (polytopeVertices C hC : Set E) = C.extremePoints ℝ := Set.Finite.coe_toFinset _

theorem IsFinitePolytope.convex {C : Set E} (hC : IsFinitePolytope C) : Convex ℝ C := by
  obtain ⟨V, rfl⟩ := hC
  exact convex_convexHull ℝ _

theorem IsFinitePolytope.isCompact {C : Set E} (hC : IsFinitePolytope C) : IsCompact C := by
  obtain ⟨V, rfl⟩ := hC
  exact V.finite_toSet.isCompact_convexHull ℝ

theorem convexHull_polytopeVertices (C : Set E) (hC : IsFinitePolytope C) :
    convexHull ℝ (polytopeVertices C hC : Set E) = C := by
  rw [coe_polytopeVertices]
  have hclosed := hC.finite_extremePoints.isClosed_convexHull (𝕜 := ℝ)
  simpa only [hclosed.closure_eq] using closure_convexHull_extremePoints hC.isCompact hC.convex

theorem polytopeVertices_face {C D : Set E} (hC : IsFinitePolytope C)
    (hD : IsFinitePolytope D) (hface : _root_.IsExtreme ℝ C D) :
    (polytopeVertices D hD : Set E) = D ∩ (polytopeVertices C hC : Set E) := by
  simp only [coe_polytopeVertices]
  exact hface.extremePoints_eq

theorem polytopeVertices_inter {C D : Set E} (hC : IsFinitePolytope C)
    (hD : IsFinitePolytope D) (hCD : IsFinitePolytope (C ∩ D))
    (hleft : _root_.IsExtreme ℝ C (C ∩ D))
    (hright : _root_.IsExtreme ℝ D (C ∩ D)) :
    polytopeVertices (C ∩ D) hCD = polytopeVertices C hC ∩ polytopeVertices D hD := by
  classical
  apply Finset.coe_injective
  simp only [Finset.coe_inter, coe_polytopeVertices]
  apply Set.Subset.antisymm
  · exact fun _ hx => ⟨hleft.extremePoints_subset_extremePoints hx,
      hright.extremePoints_subset_extremePoints hx⟩
  · intro x hx
    rw [hleft.extremePoints_eq]
    exact ⟨⟨extremePoints_subset hx.1, extremePoints_subset hx.2⟩, hx.1⟩

end BrehmApprox
