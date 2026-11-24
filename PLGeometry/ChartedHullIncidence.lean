module

public import PLGeometry.ChartedProjectiveTransport

/-! # Geodesic hulls preserve common source faces -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance chartedHullIncidenceDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance chartedHullIncidenceModelEq : DecidableEq (Model κ n) := Classical.decEq _

theorem mem_common_cell_of_hull_chart
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
    (V : Finset P) (hV : ∀ v ∈ V, v ∈ T.cell σ ∩ T.cell τ)
    {x : P} (hx : x ∈ T.cell σ)
    (hqx : T.chart σ x ∈ hull κ n (V.image (T.chart σ))) : x ∈ T.cell τ := by
  have he := T.image_face σ hσ (σ ∩ τ) Finset.inter_subset_left
  have hsub : hull κ n (V.image (T.chart σ)) ⊆ hull κ n ((σ ∩ τ).image (T.chart σ)) := by
    apply hull_transitive
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hvc : v ∈ T.cell (σ ∩ τ) := by
      rw [← T.intersection σ hσ τ hτ]
      exact hV v hv
    have hm := Set.mem_image_of_mem (T.chart σ) hvc
    rw [he] at hm
    exact hm
  have hm := hsub hqx
  rw [← he] at hm
  obtain ⟨y, hy, hxy⟩ := hm
  have hy' : y ∈ T.cell σ ∩ T.cell τ := by rwa [T.intersection σ hσ τ hτ]
  exact T.chart_injectiveOn σ hσ hy'.1 hx hxy ▸ hy'.2

end ArchivePLGeometry.FiniteChartedComplex
