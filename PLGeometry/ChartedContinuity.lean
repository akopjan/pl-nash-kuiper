module

public import PLGeometry.ChartedComplex

/-! # Continuity from the metrics of finitely many charted cells -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u v
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {Y : Type v} [MetricSpace Y] (T : FiniteChartedComplex κ n P)

theorem continuousOn_of_cell_isometry
    (σ : Finset P) (hσ : σ ∈ T.simplices) (q : P → Y)
    (hq : ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist (T.chart σ x) (T.chart σ y)) :
    ContinuousOn q (T.cell σ) := by
  classical
  let H := T.cellHomeomorph σ hσ
  let F : hull κ n (σ.image (T.chart σ)) → Y := fun z => q (H.symm z).val
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro x y
    rw [show F x = q (H.symm x).val from rfl, show F y = q (H.symm y).val from rfl,
      hq _ (H.symm x).property _ (H.symm y).property]
    have hx : T.chart σ (H.symm x).val = x.val := by
      rw [← T.cellHomeomorph_apply σ hσ]
      exact congrArg Subtype.val (H.apply_symm_apply x)
    have hy : T.chart σ (H.symm y).val = y.val := by
      rw [← T.cellHomeomorph_apply σ hσ]
      exact congrArg Subtype.val (H.apply_symm_apply y)
    rw [hx, hy]
    rfl
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (T.cell σ).domRestrict q = F ∘ H := by
    funext x
    simp only [Function.comp_apply, F, H.symm_apply_apply, Set.domRestrict_apply]
  rw [he]
  exact hF.continuous.comp H.continuous

/-- A map preserving the model metric on every cell is globally continuous. -/
theorem continuous_of_cell_isometries (q : P → Y)
    (hq : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist (T.chart σ x) (T.chart σ y)) : Continuous q := by
  letI : Finite T.simplices := T.finite_simplices.to_subtype
  apply (locallyFinite_of_finite (fun σ : T.simplices => T.cell σ.val)).continuous
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨σ, hσ, hx⟩ := T.cover x
    exact ⟨⟨σ, hσ⟩, hx⟩
  · intro σ
    exact T.closed_cell σ.val σ.property
  · intro σ
    exact T.continuousOn_of_cell_isometry σ.val σ.property q (hq σ.val σ.property)

end ArchivePLGeometry.FiniteChartedComplex
