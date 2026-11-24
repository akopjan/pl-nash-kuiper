module

public import PLGeometry.ProtectedNets
public import PLGeometry.FiniteFoldingBase

/-! # Protected nets in finite and zero-dimensional sources -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance protectedNetFiniteDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem exists_protected_net_of_finite [Finite P] {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  letI := Fintype.ofFinite P
  refine ⟨Finset.univ, ?_, ?_⟩
  · intro σ hσ x hx
    exact ⟨x, Finset.mem_univ _, hx, by simpa only [dist_self] using hη⟩
  · intro σ hσ τ hτ x hx a ha
    have hd := ha.2 x ⟨Finset.mem_univ _, hx.1⟩
    dsimp only at hd
    rw [dist_self] at hd
    have he : x = a := T.chart_injectiveOn σ hσ hx.1 ha.1.2
      (dist_eq_zero.mp (le_antisymm hd dist_nonneg))
    exact he ▸ hx.2

theorem finite_of_subsingleton_cells
    (hcell : ∀ σ ∈ T.simplices, (T.cell σ).Subsingleton) : Finite P := by
  have hu : (⋃ σ ∈ T.simplices, T.cell σ).Finite :=
    T.finite_simplices.biUnion (fun σ hσ => (hcell σ hσ).finite)
  apply Set.finite_univ_iff.mp
  apply hu.subset
  intro x _
  obtain ⟨σ, hσ, hx⟩ := T.cover x
  exact Set.mem_iUnion₂.mpr ⟨σ, hσ, hx⟩

theorem exists_protected_net_zero (T : FiniteChartedComplex κ 0 P)
    {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  letI : Finite P := T.finite_of_subsingleton_cells T.zero_cell_subsingleton
  exact T.exists_protected_net_of_finite hη

end ArchivePLGeometry.FiniteChartedComplex
