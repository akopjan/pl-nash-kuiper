module

public import Compatibility.SourceAtlas
public import Compatibility.SourceShortness
public import PLGeometry.ChartedRefinement

/-! Shortness passes from the exact Challenge to every charted refinement. -/

@[expose] public section
noncomputable section

open scoped NNReal

namespace PLGeometry

theorem Lipschitz.archive_cellwise {κ : Geometry} {d m n : ℕ}
    {K : Polyhedron κ d m} {f : ↥K.K.space → Model κ n} {L : ℝ≥0}
    (hf : Lipschitz K f L)
    (σ : Finset ↥K.K.space) (hσ : σ ∈ K.toArchiveChartedComplex.simplices)
    (x : ↥K.K.space) (hx : x ∈ K.toArchiveChartedComplex.cell σ)
    (y : ↥K.K.space) (hy : y ∈ K.toArchiveChartedComplex.cell σ) :
    dist (modelEquiv κ n (f x)) (modelEquiv κ n (f y)) ≤
      (L : ℝ) * dist (K.toArchiveChartedComplex.chart σ x)
        (K.toArchiveChartedComplex.chart σ y) := by
  classical
  change σ = ∅ ∨ σ.image Subtype.val ∈ K.K.faces at hσ
  change x.val ∈ cell (σ.image Subtype.val) at hx
  change y.val ∈ cell (σ.image Subtype.val) at hy
  rcases hσ with rfl | hσ
  · simp [cell] at hx
  · rw [K.sourceChart_dist hσ]
    exact hf.modelEquiv_cellwise _ hσ x y hx hy

theorem Lipschitz.archive_refinement_cellwise {κ : Geometry} {d m n : ℕ}
    {K : Polyhedron κ d m} {f : ↥K.K.space → Model κ n} {L : ℝ≥0}
    (hf : Lipschitz K f L)
    {U : ArchivePLGeometry.FiniteChartedComplex κ.toArchive d ↥K.K.space}
    (hU : U.Refines K.toArchiveChartedComplex)
    (σ : Finset ↥K.K.space) (hσ : σ ∈ U.simplices)
    (x : ↥K.K.space) (hx : x ∈ U.cell σ)
    (y : ↥K.K.space) (hy : y ∈ U.cell σ) :
    dist (modelEquiv κ n (f x)) (modelEquiv κ n (f y)) ≤
      (L : ℝ) * dist (U.chart σ x) (U.chart σ y) := by
  classical
  obtain ⟨τ, hτ, hsub, heq⟩ := hU.cell σ hσ
  rw [heq x hx y hy]
  exact hf.archive_cellwise τ hτ x (hsub hx) y (hsub hy)

end PLGeometry
