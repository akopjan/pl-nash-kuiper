module

public import PLGeometry.ProtectedVoronoiPolytope

/-!
# Projective transport of source simplices

Canonical barycentric coordinates preserve convex hulls and independence.
These two properties let the compatible affine Voronoi triangulation be
read as a genuine geodesic triangulation in every old chart.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

open Set BrehmApprox

universe u v

local instance projectiveVoronoiAtlasDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual barycentric atlas, including projective simplex transport. -/
structure ProjectiveVoronoiAtlas extends VoronoiAtlas T E where
  simplex_transfer : ∀ σ ∈ T.simplices, ∀ V : Finset P, (V : Set P) ⊆ T.cell σ →
    AffineIndependent ℝ ((↑) : V.image coord → E) →
    simplexVertices κ n (V.image (T.chart σ))
  hull_transfer : ∀ σ ∈ T.simplices, ∀ V : Finset P, (V : Set P) ⊆ T.cell σ →
    T.chart σ '' (coord ⁻¹' convexHull ℝ (V.image coord : Set E)) =
      hull κ n (V.image (T.chart σ))

end ArchivePLGeometry
