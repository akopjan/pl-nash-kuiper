module

public import PLGeometry.BarycentricDistanceCuts
public import PLGeometry.ChartedBarycentricEmbedding
public import PLGeometry.BarycentricPolytopes
public import PLGeometry.ProtectedVoronoiPolytope

/-! # The canonical Voronoi atlas of a finite charted complex -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

def barycentricRestriction (σ : Finset P) (hσ : σ ∈ T.simplices) :
    (T.Vertex → ℝ) →ₗ[ℝ] (σ → ℝ) where
  toFun w v := w ⟨v.val, T.vertex_mem hσ v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem barycentricRestriction_coords {σ : Finset P} (hσ : σ ∈ T.simplices)
    {x : P} (hx : x ∈ T.cell σ) :
    T.barycentricRestriction σ hσ (T.barycentricCoords x) = (T.cellWeights σ hσ ⟨x, hx⟩).val := by
  rw [T.barycentricCoords_eq hσ hx]
  funext v
  change T.localCoords σ hσ ⟨x, hx⟩ ⟨v.val, T.vertex_mem hσ v.property⟩ = _
  simp only [localCoords, dite_eq_left v.property]

/-- On each source simplex, distance comparison and equality use one affine cut. -/
theorem barycentric_distanceCut (σ : Finset P) (hσ : σ ∈ T.simplices) (a b : P) :
    ∃ ℓ : (T.Vertex → ℝ) →ₗ[ℝ] ℝ, ∃ c : ℝ, ∀ x ∈ T.cell σ,
      (dist (T.chart σ x) (T.chart σ a) ≤ dist (T.chart σ x) (T.chart σ b) ↔
        ℓ (T.barycentricCoords x) ≤ c) ∧
      (dist (T.chart σ x) (T.chart σ a) = dist (T.chart σ x) (T.chart σ b) ↔
        ℓ (T.barycentricCoords x) = c) := by
  obtain ⟨ℓ, c, hcut⟩ := ModelBarycentric.exists_distance_cut κ n
    (fun v : σ => T.chart σ v.val) (T.chart σ a) (T.chart σ b)
  refine ⟨ℓ.comp (T.barycentricRestriction σ hσ), c, ?_⟩
  intro x hx
  simpa only [LinearMap.comp_apply, T.barycentricRestriction_coords hσ hx] using
    hcut (T.cellWeights σ hσ ⟨x, hx⟩).val (T.chart σ x)
      (T.cellWeights_represents σ hσ ⟨x, hx⟩)

/-- Canonical coordinates realize all source cells and Voronoi cuts as actual
finite Euclidean polytopes with common extreme faces. -/
def barycentricVoronoiAtlas : VoronoiAtlas T (T.Vertex → ℝ) where
  coord := T.barycentricCoords
  injective := T.barycentricCoords_injective
  continuous := T.continuous_barycentricCoords
  cell_polytope σ hσ := by
    rw [T.barycentricCoords_image_cell hσ]
    exact Barycentric.weightsOn_polytope _
  face_extreme σ hσ τ hτ := by
    rw [T.barycentricCoords_image_cell hσ, T.barycentricCoords_image_cell hτ]
    exact Barycentric.weightsOn_inter_extreme _ _
  distanceCut σ hσ a _ b _ := T.barycentric_distanceCut σ hσ a b

end ArchivePLGeometry.FiniteChartedComplex
