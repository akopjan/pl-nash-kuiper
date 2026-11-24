module

public import PLGeometry.ChartedRefinement
public import PLGeometry.ChartedIncidence
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite foldings and the zero-dimensional case

The inductive construction folds every finite charted complex into an
arbitrarily small ball of its model space. In dimension zero each cell is
a point, so the constant map already has the required property.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u
local instance foldingBaseDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- A nondegenerate zero-dimensional model simplex is a point or is empty. -/
theorem zero_simplex_hull_subsingleton (κ : Geometry) (V : Finset (Model κ 0))
    (hV : simplexVertices κ 0 V) : (hull κ 0 V).Subsingleton := by
  cases κ with
  | euclidean =>
    intro x _ y _
    exact Subsingleton.elim x y
  | hyperbolic =>
    intro x _ y _
    apply BrehmApprox.HyperbolicSpace.ext
    exact Subsingleton.elim x.point y.point
  | spherical =>
    have hcard : V.card ≤ 1 := by
      have h := hV.2.fintype_card_le_finrank
      simpa only [Finset.coe_sort_coe, Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin, Nat.zero_add] using h
    rcases V.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · rw [hull_empty]
      exact Set.subsingleton_empty
    · have hVeq : V = {v} := by
        ext w
        constructor
        · intro hw
          exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hcard w hw v hv)
        · intro hw
          exact Finset.mem_singleton.mp hw ▸ hv
      rw [hVeq, hull_singleton]
      exact Set.subsingleton_singleton

namespace FiniteChartedComplex

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]

/-- A finite folding whose entire image lies in a prescribed model ball. -/
def HasSmallFiniteFolding (T : FiniteChartedComplex κ n P) : Prop :=
  ∀ (o : Model κ n) (η : ℝ), 0 < η →
    ∃ U : FiniteChartedComplex κ n P, U.Refines T ∧
      ∃ q : P → Model κ n, Continuous q ∧
        (∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
          dist (q x) (q y) = dist (U.chart σ x) (U.chart σ y)) ∧
        ∀ x, dist (q x) o < η

theorem HasSmallFiniteFolding.hasFiniteFolding {T : FiniteChartedComplex κ n P}
    (hT : T.HasSmallFiniteFolding) (o : Model κ n) : T.HasFiniteFolding := by
  obtain ⟨U, hU, q, hq, hiso, _⟩ := hT o 1 zero_lt_one
  exact ⟨U, hU, q, hq, hiso⟩

/-- Every cell in a zero-dimensional charted complex is a singleton or empty. -/
theorem zero_cell_subsingleton (T : FiniteChartedComplex κ 0 P)
    (σ : Finset P) (hσ : σ ∈ T.simplices) : (T.cell σ).Subsingleton := by
  intro x hx y hy
  apply T.chart_injectiveOn σ hσ hx hy
  apply zero_simplex_hull_subsingleton κ _ (T.simplex σ hσ)
  · rw [← T.image_cell σ hσ]
    exact Set.mem_image_of_mem _ hx
  · rw [← T.image_cell σ hσ]
    exact Set.mem_image_of_mem _ hy

theorem hasSmallFiniteFolding_zero (T : FiniteChartedComplex κ 0 P) :
    T.HasSmallFiniteFolding := by
  intro o η hη
  refine ⟨T, Refines.refl T, fun _ => o, continuous_const, ?_, ?_⟩
  · intro σ hσ x hx y hy
    rw [T.zero_cell_subsingleton σ hσ hx hy]
    simp only [dist_self]
  · intro x
    simpa only [dist_self] using hη

end FiniteChartedComplex
end ArchivePLGeometry
