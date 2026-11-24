module

public import PLGeometry.ChartedComplex

/-!
# Vertex and face incidence in a charted complex
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u

local instance chartedIncidenceDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem hull_empty (κ : Geometry) (n : ℕ) : hull κ n ∅ = ∅ := by
  cases κ with
  | euclidean => simp [hull]
  | spherical =>
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨w, _, a, ha, he⟩ := hx
    simp only [Finset.sum_empty] at he
    exact smul_ne_zero ha.ne' x.val_ne_zero he.symm
  | hyperbolic =>
    ext x
    change x ∈ BrehmApprox.hyperbolicCell ∅ ↔ False
    rw [BrehmApprox.mem_hyperbolicCell_iff_klein_mem_convexHull]
    simp

theorem hull_singleton (κ : Geometry) (n : ℕ) (v : Model κ n) :
    hull κ n {v} = {v} := by
  cases κ with
  | euclidean => simp [hull]
  | spherical =>
    ext x
    constructor
    · intro hx
      have hs : BrehmApprox.Short (fun _ : GeodesicSphere n => v) :=
        fun _ _ => by simpa only [dist_self] using dist_nonneg
      have he := BrehmApprox.short_eq_on_sphericalCell_of_fixed hs {v}
        (fun y hy => (Finset.mem_singleton.mp hy).symm) x hx
      exact he.symm
    · intro hx
      subst x
      exact BrehmApprox.mem_sphericalCell_of_mem (Finset.mem_singleton_self _)
  | hyperbolic =>
    ext x
    change x ∈ BrehmApprox.hyperbolicCell {v} ↔ x = v
    rw [BrehmApprox.mem_hyperbolicCell_iff_klein_mem_convexHull]
    simp only [Finset.image_singleton, Finset.coe_singleton, convexHull_singleton,
      Set.mem_singleton_iff, BrehmApprox.HyperbolicSpace.klein_injective.eq_iff]

namespace FiniteChartedComplex

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

theorem cell_empty (h : (∅ : Finset P) ∈ T.simplices) : T.cell ∅ = ∅ := by
  have he := T.image_cell ∅ h
  rw [Finset.image_empty, hull_empty] at he
  exact Set.image_eq_empty.mp he

theorem cell_singleton {v : P} (h : ({v} : Finset P) ∈ T.simplices) :
    T.cell {v} = {v} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hmem := Set.mem_image_of_mem (T.chart {v}) hx
    rw [T.image_cell {v} h, Finset.image_singleton, hull_singleton] at hmem
    exact T.chart_injectiveOn {v} h hx
      (T.vertices_mem {v} h (Finset.mem_singleton_self v)) hmem
  · simpa only [Finset.coe_singleton] using T.vertices_mem {v} h

/-- The finite set of all original vertices. -/
def vertexSet : Set P := ⋃ σ ∈ T.simplices, (σ : Set P)

theorem finite_vertexSet : T.vertexSet.Finite :=
  T.finite_simplices.biUnion (fun σ _ => σ.finite_toSet)

theorem singleton_mem_of_vertex {v : P} (hv : v ∈ T.vertexSet) :
    ({v} : Finset P) ∈ T.simplices := by
  obtain ⟨σ, hσ, hvσ⟩ := Set.mem_iUnion₂.mp hv
  exact T.faces σ hσ {v} (Finset.singleton_subset_iff.mpr hvσ)

end FiniteChartedComplex

end ArchivePLGeometry
