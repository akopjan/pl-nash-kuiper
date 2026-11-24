module

public import PLGeometry.VertexFolding

/-! # Actual model geometry of isometric images of charted cells -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance chartedCellRigidityDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance chartedCellRigidityModelEq : DecidableEq (Model κ n) := Classical.decEq _

theorem exists_cell_model_embedding (σ : Finset P) (hσ : σ ∈ T.simplices)
    (q : P → Model κ n)
    (hq : ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist (T.chart σ x) (T.chart σ y)) :
    ∃ R : ModelEmbedding κ n n, ∀ x ∈ T.cell σ, R.toFun (T.chart σ x) = q x := by
  obtain ⟨R, hR⟩ := exists_model_vertex_motion κ n
    (fun x : σ => T.chart σ x.val) (fun x : σ => q x.val)
    (T.vertexModel_independent σ hσ) (fun x y =>
      (hq x.val (T.vertices_mem σ hσ x.property) y.val (T.vertices_mem σ hσ y.property)).symm)
  have hV : (σ.image (T.chart σ)).image R.toFun = σ.image q := by
    rw [Finset.image_image]
    exact Finset.image_congr (fun x hx => hR ⟨x, hx⟩)
  refine ⟨R, ?_⟩
  intro x hx
  have hm : R.toFun (T.chart σ x) ∈ hull κ n (σ.image q) := by
    rw [← hV, ← R.image_hull, ← T.image_cell σ hσ]
    exact Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hx)
  apply eq_of_mem_hull_of_dist_eq κ n hm
  intro v hv
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  rw [← hR ⟨y, hy⟩, R.isometry.dist_eq, hR ⟨y, hy⟩]
  exact (hq x hx y (T.vertices_mem σ hσ hy)).symm

theorem folding_cell_geometry (σ : Finset P) (hσ : σ ∈ T.simplices)
    (q : P → Model κ n)
    (hq : ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist (T.chart σ x) (T.chart σ y)) :
    simplexVertices κ n (σ.image q) ∧ q '' T.cell σ = hull κ n (σ.image q) := by
  obtain ⟨R, hR⟩ := T.exists_cell_model_embedding σ hσ q hq
  have hV : (σ.image (T.chart σ)).image R.toFun = σ.image q := by
    rw [Finset.image_image]
    exact Finset.image_congr (fun x hx => hR x (T.vertices_mem σ hσ hx))
  constructor
  · rw [← hV]
    exact R.simplex_image _ (T.simplex σ hσ)
  · calc
      q '' T.cell σ = R.toFun '' (T.chart σ '' T.cell σ) := by
        rw [Set.image_image]
        exact Set.image_congr (fun x hx => (hR x hx).symm)
      _ = R.toFun '' hull κ n (σ.image (T.chart σ)) := by rw [T.image_cell σ hσ]
      _ = hull κ n ((σ.image (T.chart σ)).image R.toFun) := R.image_hull _
      _ = hull κ n (σ.image q) := by rw [hV]

end ArchivePLGeometry.FiniteChartedComplex
