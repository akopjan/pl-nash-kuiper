module

public import PLGeometry.AngularFoldingStep

/-! # Dimension induction for small finite geodesic foldings -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

/-- The geometric induction uses protected nets in the current dimension
and spherical folding in the preceding dimension. -/
theorem finite_folding_induction
    (hnets : ∀ {κ : Geometry} {m : ℕ} {Q : Type u} [TopologicalSpace Q] [T2Space Q]
      (T : FiniteChartedComplex κ m Q) {η : ℝ}, 0 < η →
        ∃ S : Finset Q, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S) :
    ∀ (m : ℕ) {κ : Geometry} {Q : Type u} [TopologicalSpace Q] [T2Space Q]
      (T : FiniteChartedComplex κ m Q), T.HasSmallFiniteFolding := by
  intro m
  induction m with
  | zero =>
    intro κ Q _ _ T
    exact T.hasSmallFiniteFolding_zero
  | succ m ih =>
    intro κ Q _ _ T
    apply T.hasSmallFiniteFolding_of_protected_nets (fun δ hδ => hnets T hδ)
    intro R _ _ D
    exact (ih D).hasFiniteFolding (GeodesicSphere.northPole m)

end ArchivePLGeometry.FiniteChartedComplex
