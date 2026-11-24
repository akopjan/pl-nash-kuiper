module

public import Compatibility.ConnectedApproximation
public import Compatibility.SourceComponents

/-!
# Approximation on each cell component

Global cellwise bounds restrict to every connected cell component. Applying
the connected approximation theorem gives a finite charted refinement on that
component, with the same pointwise error bound.
-/

@[expose] public section
noncomputable section

namespace PLGeometry.Compatibility

universe u

theorem approximate_component {κ : ArchivePLGeometry.Geometry} {n : ℕ}
    {P : Type u} [TopologicalSpace P] [T2Space P]
    (U : ArchivePLGeometry.FiniteChartedComplex κ n P)
    (q : P → ArchivePLGeometry.Model κ n) (hq : Continuous q)
    (hiso : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (q x) (q y) = dist (U.chart σ x) (U.chart σ y))
    (o : ArchivePLGeometry.Model κ n) (hsmall : ∀ x, dist (q x) o < Real.pi / 2)
    (f : P → ArchivePLGeometry.Model κ n)
    (hf : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (f x) (f y) ≤ dist (U.chart σ x) (U.chart σ y))
    (hsphere : κ = .spherical →
      ((∃ L : NNReal, L < 1 ∧
        ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
          dist (f x) (f y) ≤ (L : ℝ) * dist (U.chart σ x) (U.chart σ y)) ∨
        ∃ c : ArchivePLGeometry.Model κ n, ∀ x, dist (f x) c < Real.pi / 2))
    (c : U.ComponentIndex) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : U.IndexedComponent c → ArchivePLGeometry.Model κ n, Continuous g ∧
      ∃ V : ArchivePLGeometry.FiniteChartedComplex κ n (U.IndexedComponent c),
        V.Refines (U.componentChartedComplex c.out) ∧
        (∀ σ ∈ V.simplices, ∀ x ∈ V.cell σ, ∀ y ∈ V.cell σ,
          dist (g x) (g y) = dist (V.chart σ x) (V.chart σ y)) ∧
        ∀ x, dist (g x) (f x.val) < ε := by
  classical
  apply approximate_connected (U.componentChartedComplex c.out)
    (fun x => q x.val) (hq.comp continuous_subtype_val)
    (U.component_folding_isometric q hiso c.out)
    (U.componentChartedComplex_connected c.out) o (fun x => hsmall x.val)
    (fun x => f x.val) ?_ ?_ hε
  · intro σ hσ x hx y hy
    exact hf _ hσ x.val hx y.val hy
  · intro hκ
    rcases hsphere hκ with ⟨L, hL, hshort⟩ | ⟨a, ha⟩
    · refine Or.inl ⟨L, hL, ?_⟩
      intro σ hσ x hx y hy
      exact hshort _ hσ x.val hx y.val hy
    · exact Or.inr ⟨a, fun x => ha x.val⟩

end PLGeometry.Compatibility
