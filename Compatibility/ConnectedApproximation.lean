module

public import Compatibility.IntrinsicMetric
public import Compatibility.PLRefinement
public import PLGeometry.PLNashKuiper

/-!
# Approximation on a connected charted complex

The proved intrinsic metric construction makes the given folded source a
finite intrinsic polyhedron. Cellwise shortness becomes global shortness.
The completed approximation theorem is then followed by a finite refinement
of the original charted cells. The original topology is retained throughout.
-/

@[expose] public section
noncomputable section

namespace PLGeometry.Compatibility

universe u

theorem approximate_connected {κ : ArchivePLGeometry.Geometry} {n : ℕ}
    {P : Type u} [TopologicalSpace P] [T2Space P]
    (U : ArchivePLGeometry.FiniteChartedComplex κ n P)
    (q : P → ArchivePLGeometry.Model κ n) (hq : Continuous q)
    (hiso : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (q x) (q y) = dist (U.chart σ x) (U.chart σ y))
    (hc : BrehmApprox.ConnectedCellMetric.Connected
      (fun σ : U.simplices => U.cell σ.val))
    (o : ArchivePLGeometry.Model κ n) (hsmall : ∀ x, dist (q x) o < Real.pi / 2)
    (f : P → ArchivePLGeometry.Model κ n)
    (hf : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (f x) (f y) ≤ dist (U.chart σ x) (U.chart σ y))
    (hsphere : κ = .spherical →
      ((∃ L : NNReal, L < 1 ∧
        ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
          dist (f x) (f y) ≤ (L : ℝ) * dist (U.chart σ x) (U.chart σ y)) ∨
        ∃ c : ArchivePLGeometry.Model κ n, ∀ x, dist (f x) c < Real.pi / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → ArchivePLGeometry.Model κ n, Continuous g ∧
      ∃ V : ArchivePLGeometry.FiniteChartedComplex κ n P,
        V.Refines U ∧
        (∀ σ ∈ V.simplices, ∀ x ∈ V.cell σ, ∀ y ∈ V.cell σ,
          dist (g x) (g y) = dist (V.chart σ x) (V.chart σ y)) ∧
        ∀ x, dist (g x) (f x) < ε := by
  letI := U.foldedIntrinsicMetric q hq hiso hc
  have hm : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (U.chart σ x) (U.chart σ y) = dist x y := by
    intro σ hσ x hx y hy
    exact (U.foldedIntrinsicMetric_on_cell q hq hiso hc σ hσ x hx y hy).symm
  let T : ArchivePLGeometry.Triangulation κ n P := U.toTriangulation hm
  have hP : ArchivePLGeometry.IsFinitePolyhedron κ n P :=
    U.isFinitePolyhedron_foldedIntrinsicMetric q hq hiso hc
  have hT : ArchivePLGeometry.Intrinsic T := hP.intrinsic_triangulation T
  have hLip : ∀ L : NNReal,
      (∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
        dist (f x) (f y) ≤ (L : ℝ) * dist (U.chart σ x) (U.chart σ y)) →
      LipschitzWith L f := by
    intro L hL
    apply T.lipschitzWith_of_cellwise hT
    intro σ hσ x hx y hy
    rw [← hm σ hσ x hx y hy]
    exact hL σ hσ x hx y hy
  have hfglobal : LipschitzWith 1 f := hLip 1 (by
    intro σ hσ x hx y hy
    simpa only [NNReal.coe_one, one_mul] using hf σ hσ x hx y hy)
  have happ : ∃ g : P → ArchivePLGeometry.Model κ n,
      ArchivePLGeometry.PLIsometry κ n g ∧ ∀ x, dist (g x) (f x) < ε := by
    cases κ with
    | euclidean =>
      obtain ⟨g, _, hg, hclose⟩ := ArchivePLGeometry.pl_nash_kuiper_euclidean
        (d := n) (n := n) le_rfl P hP f hfglobal hε
      exact ⟨g, hg, hclose⟩
    | hyperbolic =>
      obtain ⟨g, _, hg, hclose⟩ := ArchivePLGeometry.pl_nash_kuiper_hyperbolic
        (d := n) (n := n) le_rfl P hP f hfglobal hε
      exact ⟨g, hg, hclose⟩
    | spherical =>
      have hs : ArchivePLGeometry.StrictlyShort f ∨
          ∃ c : GeodesicSphere n, ∀ x, dist (f x) c ≤ Real.pi / 2 := by
        rcases hsphere rfl with ⟨L, hL, hshort⟩ | ⟨c, hhem⟩
        · exact Or.inl ⟨L, hL, hLip L hshort⟩
        · exact Or.inr ⟨c, fun x => (hhem x).le⟩
      obtain ⟨g, _, hg, hclose⟩ := ArchivePLGeometry.pl_nash_kuiper_spherical
        (d := n) (n := n) le_rfl P hP f hfglobal hs hε
      exact ⟨g, hg, hclose⟩
  obtain ⟨g, hg, hclose⟩ := happ
  have hqT : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist x y := by
    intro σ hσ x hx y hy
    exact (hiso σ hσ x hx y hy).trans (hm σ hσ x hx y hy)
  obtain ⟨hgcont, W, hW, hsub, hgW⟩ := Refined.refinement_of_plIsometry
    T U.finite_simplices hT q hqT o hsmall hg
  let V := W.toFiniteChartedComplex hW
  refine ⟨g, hgcont, V, ?_, ?_, hclose⟩
  · constructor
    intro σ hσ
    obtain ⟨τ, hστ⟩ := hsub σ hσ
    refine ⟨τ.val, τ.property, hστ, ?_⟩
    intro x hx y hy
    exact (W.isometry_cell σ hσ x hx y hy).trans
      (hm τ.val τ.property x (hστ hx) y (hστ hy)).symm
  · intro σ hσ x hx y hy
    exact (hgW σ hσ x hx y hy).trans (W.isometry_cell σ hσ x hx y hy).symm

end PLGeometry.Compatibility
