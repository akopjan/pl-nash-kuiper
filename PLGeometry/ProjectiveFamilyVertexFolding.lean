module

public import PLGeometry.ProjectiveSimplicialRefinement
public import PLGeometry.VertexFolding

/-! # Extending vertex isometries on projective simplex families -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveSimplexFamily

universe u v w
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : ProjectiveVoronoiAtlas T E} {I : Type w}
    (F : ProjectiveSimplexFamily A I)

local instance projectiveFamilyVertexDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem cell_subset_oldCell {σ τ : Finset P} (hτ : τ ∈ T.simplices)
    (hστ : (σ : Set P) ⊆ T.cell τ) : F.cell σ ⊆ T.cell τ := by
  intro x hx
  have hm : A.coord x ∈ A.coord '' T.cell τ := by
    apply convexHull_min ?_ (A.cell_polytope τ hτ).convex hx
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨y, hστ hy, rfl⟩
  obtain ⟨y, hy, he⟩ := hm
  exact A.injective he ▸ hy

theorem family_chart_metric {σ τ : Finset P} (hσ : σ ∈ F.simplices)
    (hτ : τ ∈ T.simplices) (hστ : (σ : Set P) ⊆ T.cell τ)
    {x y : P} (hx : x ∈ F.cell σ) (hy : y ∈ F.cell σ) :
    dist (F.chart σ x) (F.chart σ y) = dist (T.chart τ x) (T.chart τ y) :=
  T.metric_coherence _ (F.oldFace_spec hσ).1 τ hτ x
    ⟨F.cell_subset_old hσ hx, F.cell_subset_oldCell hτ hστ hx⟩ y
    ⟨F.cell_subset_old hσ hy, F.cell_subset_oldCell hτ hστ hy⟩

theorem isVertexIsometry_of_family [Finite I] (v : P → Model κ n)
    (hv : ∀ i, ∃ τ ∈ T.simplices, (F.vertices i : Set P) ⊆ T.cell τ ∧
      ∀ x ∈ F.vertices i, ∀ y ∈ F.vertices i,
        dist (v x) (v y) = dist (T.chart τ x) (T.chart τ y)) :
    F.toChartedComplex.IsVertexIsometry v := by
  intro σ hσ x hx y hy
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨τ, hτ, hcell, hdist⟩ := hv i
  exact (hdist x (hi hx) y (hi hy)).trans
    (F.family_chart_metric ⟨i, hi⟩ hτ
      ((Finset.coe_subset.mpr hi).trans hcell)
      (F.vertices_mem σ hx) (F.vertices_mem σ hy)).symm

end ArchivePLGeometry.ProjectiveSimplexFamily
