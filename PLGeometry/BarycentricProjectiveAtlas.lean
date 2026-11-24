module

public import PLGeometry.BarycentricVoronoiAtlas
public import PLGeometry.ChartedProjectiveTransport
public import PLGeometry.ProjectiveVoronoiAtlas

/-! # The full canonical projective Voronoi atlas -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

/-- Every finite charted complex has the genuine projective atlas used by
the protected Voronoi construction. -/
def barycentricProjectiveAtlas : ProjectiveVoronoiAtlas T (T.Vertex → ℝ) where
  toVoronoiAtlas := T.barycentricVoronoiAtlas
  simplex_transfer _ hσ V hV hi := T.barycentric_simplex_transfer hσ V hV hi
  hull_transfer _ hσ V hV := T.barycentric_hull_transfer hσ V hV

end ArchivePLGeometry.FiniteChartedComplex
