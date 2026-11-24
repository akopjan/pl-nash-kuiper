module

public import Compatibility.EmbeddedRefinement
public import Compatibility.SourceComponents
public import PLGeometry.ChartedRefinement

/-! The metric and containment data needed to realize each component
refinement as a subdivision of the original embedded complex. -/

@[expose] public section
noncomputable section

namespace PLGeometry.Polyhedron

variable {κ : Geometry} {d m : ℕ} (K : Polyhedron κ d m)

theorem component_refinement
    (U : ArchivePLGeometry.FiniteChartedComplex κ.toArchive d ↥K.K.space)
    (hU : U.Refines K.toArchiveChartedComplex)
    (c : U.ComponentIndex)
    (V : ArchivePLGeometry.FiniteChartedComplex κ.toArchive d (U.IndexedComponent c))
    (hV : V.Refines (U.componentChartedComplex c.out))
    (τ₀ : Finset (E m)) (hτ₀ : τ₀ ∈ K.K.faces) :
    ∀ σ ∈ V.simplices, ∃ (τ : Finset (E m)) (hτ : τ ∈ K.K.faces),
      (∀ x ∈ V.cell σ, x.val.val ∈ cell τ) ∧
      ∀ x ∈ V.cell σ, ∀ y ∈ V.cell σ,
        dist (V.chart σ x) (V.chart σ y) =
          modelDist κ d ((K.simplex τ hτ).toModel x.val.val)
            ((K.simplex τ hτ).toModel y.val.val) := by
  classical
  letI : DecidableEq ↥K.K.space := Classical.decEq _
  intro σ hσ
  obtain ⟨ρ, hρ, hVsub, hVmetric⟩ := hV.cell σ hσ
  change ρ.image Subtype.val ∈ U.simplices at hρ
  obtain ⟨η, hη, hUsub, hUmetric⟩ := hU.cell (ρ.image Subtype.val) hρ
  change η = ∅ ∨ η.image Subtype.val ∈ K.K.faces at hη
  have hsub (x : U.IndexedComponent c) (hx : x ∈ V.cell σ) :
      x.val ∈ U.cell (ρ.image Subtype.val) := hVsub hx
  rcases hη with rfl | hη
  · have hempty (x : U.IndexedComponent c) (hx : x ∈ V.cell σ) : False := by
      have h := hUsub (hsub x hx)
      change x.val ∈ K.sourceCell ∅ at h
      rw [K.sourceCell_empty] at h
      exact h
    refine ⟨τ₀, hτ₀, ?_, ?_⟩
    · intro x hx
      exact (hempty x hx).elim
    · intro x hx y hy
      exact (hempty x hx).elim
  · refine ⟨η.image Subtype.val, hη, ?_, ?_⟩
    · intro x hx
      exact hUsub (hsub x hx)
    · intro x hx y hy
      calc
        dist (V.chart σ x) (V.chart σ y) =
            dist ((U.componentChartedComplex c.out).chart ρ x)
              ((U.componentChartedComplex c.out).chart ρ y) := hVmetric x hx y hy
        _ = dist (U.chart (ρ.image Subtype.val) x.val)
              (U.chart (ρ.image Subtype.val) y.val) := rfl
        _ = dist (K.toArchiveChartedComplex.chart η x.val)
              (K.toArchiveChartedComplex.chart η y.val) :=
          hUmetric x.val (hsub x hx) y.val (hsub y hy)
        _ = modelDist κ d ((K.simplex (η.image Subtype.val) hη).toModel x.val.val)
              ((K.simplex (η.image Subtype.val) hη).toModel y.val.val) :=
          K.sourceChart_dist hη x.val y.val

end PLGeometry.Polyhedron
