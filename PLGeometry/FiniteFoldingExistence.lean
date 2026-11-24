module

public import PLGeometry.FiniteFoldingInduction
public import PLGeometry.ProtectedNetExistence

/-!
# Small finite foldings of every finite polyhedron

The protected-net construction and the angular dimension induction give
genuine finite geodesic refinements in each constant-curvature geometry.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u

namespace FiniteChartedComplex

/-- Every finite charted complex admits a finite folding into an arbitrarily
small ball of its model space. -/
theorem hasSmallFiniteFolding {κ : Geometry} {n : ℕ} {P : Type u}
    [TopologicalSpace P] [T2Space P] (T : FiniteChartedComplex κ n P) :
    T.HasSmallFiniteFolding := by
  apply finite_folding_induction ?_ n T
  intro κ' m Q _ _ D η hη
  exact D.exists_protected_net hη

end FiniteChartedComplex

/-- The small folding of a finite intrinsic polyhedron is a PL-isometry
with respect to its actual source metric. -/
theorem IsFinitePolyhedron.exists_small_plIsometry {κ : Geometry} {n : ℕ}
    {P : Type u} [MetricSpace P] (hP : IsFinitePolyhedron κ n P)
    (o : Model κ n) {η : ℝ} (hη : 0 < η) :
    ∃ q : P → Model κ n, PLIsometry κ n q ∧ ∀ x, dist (q x) o < η := by
  obtain ⟨T, hfin, _⟩ := hP
  obtain ⟨U, hU, q, hq, hiso, hsmall⟩ :=
    (T.toFiniteChartedComplex hfin).hasSmallFiniteFolding o η hη
  exact ⟨q, T.plIsometry_of_charted_refinement hfin U hU q hq hiso, hsmall⟩

end ArchivePLGeometry
