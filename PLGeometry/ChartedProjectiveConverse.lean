module

public import PLGeometry.ModelProjectiveConverse
public import PLGeometry.ChartedBarycentricLinear

/-! # Independence of the global coordinates of a geodesic simplex -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

theorem barycentricCoords_independent_of_model {J : Type*} [Fintype J]
    {σ : Finset P} (hσ : σ ∈ T.simplices) (v : J → T.cell σ)
    (hi : ModelBarycentric.Independent κ n (fun j => T.chart σ (v j).val)) :
    AffineIndependent ℝ (fun j => T.barycentricCoords (v j).val) := by
  have hw := ModelBarycentric.affineIndependent_of_independent
    (fun i : σ => T.chart σ i.val) (fun j => T.chart σ (v j).val)
    (fun j => T.cellWeights σ hσ (v j)) (fun j => T.cellWeights_represents σ hσ (v j)) hi
  apply AffineIndependent.of_comp (T.coordinateRestriction σ hσ).toAffineMap
  change AffineIndependent ℝ (fun j => T.coordinateRestriction σ hσ (T.barycentricCoords (v j).val))
  simpa only [T.restriction_barycentricCoords] using hw

end ArchivePLGeometry.FiniteChartedComplex
