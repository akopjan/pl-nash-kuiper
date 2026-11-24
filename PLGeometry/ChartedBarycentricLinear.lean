module

public import PLGeometry.ChartedBarycentricEmbedding

/-! # Linear restriction and extension of source barycentric coordinates -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry

theorem linear_maps_convexHull_range {J E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (v : J → E) {x : E} (hx : x ∈ convexHull ℝ (Set.range v)) :
    L x ∈ convexHull ℝ (Set.range (fun j => L (v j))) := by
  have hm := Set.mem_image_of_mem L hx
  rw [L.image_convexHull] at hm
  have he : L '' Set.range v = Set.range (fun j => L (v j)) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨v j, ⟨j, rfl⟩, rfl⟩
  rwa [he] at hm

namespace FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance chartedBarycentricLinearDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def coordinateExtension (σ : Finset P) : (σ → ℝ) →ₗ[ℝ] (T.Vertex → ℝ) where
  toFun w v := if hv : v.val ∈ σ then w ⟨v.val, hv⟩ else 0
  map_add' w z := by
    funext v
    by_cases hv : v.val ∈ σ <;> simp [hv]
  map_smul' a w := by
    funext v
    by_cases hv : v.val ∈ σ <;> simp [hv]

def coordinateRestriction (σ : Finset P) (hσ : σ ∈ T.simplices) :
    (T.Vertex → ℝ) →ₗ[ℝ] (σ → ℝ) where
  toFun w v := w ⟨v.val, T.vertex_mem hσ v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restriction_extension (σ : Finset P) (hσ : σ ∈ T.simplices) (w : σ → ℝ) :
    T.coordinateRestriction σ hσ (T.coordinateExtension σ w) = w := by
  funext v
  simp only [coordinateRestriction, coordinateExtension, LinearMap.coe_mk, AddHom.coe_mk,
    dite_eq_left v.property]

theorem barycentricCoords_eq_extension {σ : Finset P} (hσ : σ ∈ T.simplices) (x : T.cell σ) :
    T.barycentricCoords x.val = T.coordinateExtension σ (T.cellWeights σ hσ x).val :=
  T.barycentricCoords_eq hσ x.property

@[simp] theorem restriction_barycentricCoords {σ : Finset P} (hσ : σ ∈ T.simplices)
    (x : T.cell σ) :
    T.coordinateRestriction σ hσ (T.barycentricCoords x.val) = (T.cellWeights σ hσ x).val := by
  rw [T.barycentricCoords_eq_extension hσ x, T.restriction_extension]

theorem barycentricCoords_convexHull_iff {J : Type*} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (v : J → T.cell σ) (x : T.cell σ) :
    T.barycentricCoords x.val ∈ convexHull ℝ (Set.range (fun j => T.barycentricCoords (v j).val)) ↔
      (T.cellWeights σ hσ x).val ∈ convexHull ℝ (Set.range (fun j => (T.cellWeights σ hσ (v j)).val)) := by
  constructor
  · intro hx
    have h := linear_maps_convexHull_range (T.coordinateRestriction σ hσ)
      (fun j => T.barycentricCoords (v j).val) hx
    simpa only [T.restriction_barycentricCoords hσ] using h
  · intro hx
    have h := linear_maps_convexHull_range (T.coordinateExtension σ)
      (fun j => (T.cellWeights σ hσ (v j)).val) hx
    simpa only [← T.barycentricCoords_eq_extension hσ] using h

theorem cellWeights_independent_of_coords {J : Type*} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (v : J → T.cell σ)
    (hi : AffineIndependent ℝ (fun j => T.barycentricCoords (v j).val)) :
    AffineIndependent ℝ (fun j => (T.cellWeights σ hσ (v j)).val) := by
  apply AffineIndependent.of_comp (T.coordinateExtension σ).toAffineMap
  change AffineIndependent ℝ (fun j => T.coordinateExtension σ (T.cellWeights σ hσ (v j)).val)
  simpa only [← T.barycentricCoords_eq_extension hσ] using hi

end FiniteChartedComplex
end ArchivePLGeometry
