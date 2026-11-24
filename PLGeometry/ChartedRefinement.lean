module

public import PLGeometry.ChartedComplex

/-!
# Metric transport through finite charted refinements

The auxiliary charted-complex construction returns an actual refinement and
an isometry on each new cell. When the original complex is a metric
triangulation, these data give exactly the PL-isometry in the Challenge.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u

namespace FiniteChartedComplex

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]

structure Refines (U T : FiniteChartedComplex κ n P) : Prop where
  cell : ∀ σ ∈ U.simplices, ∃ τ ∈ T.simplices,
    U.cell σ ⊆ T.cell τ ∧
    ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (U.chart σ x) (U.chart σ y) = dist (T.chart τ x) (T.chart τ y)

theorem Refines.refl (T : FiniteChartedComplex κ n P) : T.Refines T :=
  ⟨fun σ hσ => ⟨σ, hσ, Set.Subset.rfl, fun _ _ _ _ => rfl⟩⟩

theorem Refines.trans {T U V : FiniteChartedComplex κ n P}
    (hVU : V.Refines U) (hUT : U.Refines T) : V.Refines T := by
  constructor
  intro σ hσ
  obtain ⟨τ, hτ, hστ, hdστ⟩ := hVU.cell σ hσ
  obtain ⟨ρ, hρ, hτρ, hdτρ⟩ := hUT.cell τ hτ
  exact ⟨ρ, hρ, hστ.trans hτρ, fun x hx y hy =>
    (hdστ x hx y hy).trans (hdτρ x (hστ hx) y (hστ hy))⟩

/-- A finite folding of a charted complex. Each refined cell has its genuine
model metric; no global ambient folding occurs in the hypotheses. -/
def HasFiniteFolding (T : FiniteChartedComplex κ n P) : Prop :=
  ∃ U : FiniteChartedComplex κ n P, U.Refines T ∧
    ∃ q : P → Model κ n, Continuous q ∧
      ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
        dist (q x) (q y) = dist (U.chart σ x) (U.chart σ y)

end FiniteChartedComplex

namespace Triangulation

variable {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]
    (T : Triangulation κ n P) (hfin : T.simplices.Finite)

theorem metric_of_charted_refinement
    (U : FiniteChartedComplex κ n P)
    (hU : U.Refines (T.toFiniteChartedComplex hfin)) :
    ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (U.chart σ x) (U.chart σ y) = dist x y := by
  intro σ hσ x hx y hy
  obtain ⟨τ, hτ, hsub, heq⟩ := hU.cell σ hσ
  exact (heq x hx y hy).trans (T.isometry_cell τ hτ x (hsub hx) y (hsub hy))

theorem plIsometry_of_charted_refinement
    (U : FiniteChartedComplex κ n P)
    (hU : U.Refines (T.toFiniteChartedComplex hfin))
    (q : P → Model κ n) (hq : Continuous q)
    (hiso : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (q x) (q y) = dist (U.chart σ x) (U.chart σ y)) : PLIsometry κ n q := by
  let hmetric := T.metric_of_charted_refinement hfin U hU
  refine ⟨hq, U.toTriangulation hmetric, ?_⟩
  intro σ hσ x hx y hy
  exact (hiso σ hσ x hx y hy).trans (hmetric σ hσ x hx y hy)

theorem exists_plIsometry_of_finite_folding
    (hfold : (T.toFiniteChartedComplex hfin).HasFiniteFolding) :
    ∃ q : P → Model κ n, PLIsometry κ n q := by
  obtain ⟨U, hU, q, hq, hiso⟩ := hfold
  exact ⟨q, T.plIsometry_of_charted_refinement hfin U hU q hq hiso⟩

end Triangulation

end ArchivePLGeometry
