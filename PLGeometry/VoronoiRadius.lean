module

public import PLGeometry.ProtectedVoronoi

/-!
# The common radius to a protected nearest site

The radius is independent of the old simplex chart and of the chosen
nearest site. It supplies the globally consistent radial coordinate for
the finite folding construction.
-/

@[expose] public section
noncomputable section

open Set Classical

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

local instance voronoiRadiusDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

theorem voronoiPiece_radius_eq {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S)
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
    {x a b : P} (ha : x ∈ T.voronoiPiece S σ a) (hb : x ∈ T.voronoiPiece S τ b) :
    dist (T.chart σ x) (T.chart σ a) = dist (T.chart τ x) (T.chart τ b) := by
  have haτ := hp σ hσ τ hτ x ⟨ha.1, hb.1⟩ a ha.2
  have ha' : x ∈ T.voronoiPiece S τ a :=
    ⟨hb.1, (T.nearestInCell_iff hnet hp hσ hτ ⟨ha.1, hb.1⟩).mp ha.2⟩
  exact (T.metric_coherence σ hσ τ hτ x ⟨ha.1, hb.1⟩ a ⟨ha.2.1.2, haτ⟩).trans
    (T.voronoiPiece_tie ha' hb)

theorem exists_voronoi_chart {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (x : P) :
    ∃ σ ∈ T.simplices, ∃ a, x ∈ T.voronoiPiece S σ a := by
  obtain ⟨σ, hσ, hx⟩ := T.cover x
  obtain ⟨a, ha⟩ := T.exists_nearestInCell hnet hσ hx
  exact ⟨σ, hσ, a, hx, ha⟩

def nearestRadius {S : Finset P} {η : ℝ} (hnet : T.IsCellwiseNet S η) (x : P) : ℝ :=
  let H := T.exists_voronoi_chart hnet x
  dist (T.chart H.choose x) (T.chart H.choose H.choose_spec.2.choose)

theorem nearestRadius_eq {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S)
    {σ : Finset P} (hσ : σ ∈ T.simplices) {x a : P}
    (hx : x ∈ T.voronoiPiece S σ a) :
    T.nearestRadius hnet x = dist (T.chart σ x) (T.chart σ a) := by
  let H := T.exists_voronoi_chart hnet x
  exact T.voronoiPiece_radius_eq hnet hp H.choose_spec.1 hσ H.choose_spec.2.choose_spec hx

theorem nearestRadius_nonneg {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (x : P) : 0 ≤ T.nearestRadius hnet x := dist_nonneg

theorem nearestRadius_lt {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (x : P) : T.nearestRadius hnet x < η := by
  let H := T.exists_voronoi_chart hnet x
  exact T.voronoiPiece_radius_lt hnet H.choose_spec.1 H.choose_spec.2.choose_spec

theorem nearestRadius_site {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S) {a : P} (ha : a ∈ S) :
    T.nearestRadius hnet a = 0 := by
  obtain ⟨σ, hσ, haσ⟩ := T.cover a
  have hpiece : a ∈ T.voronoiPiece S σ a := by
    refine ⟨haσ, ⟨ha, haσ⟩, ?_⟩
    intro b hb
    simpa only [dist_self] using dist_nonneg (x := T.chart σ a) (y := T.chart σ b)
  rw [T.nearestRadius_eq hnet hp hσ hpiece, dist_self]

theorem nearestRadius_pos_of_notMem {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) {x : P} (hx : x ∉ S) : 0 < T.nearestRadius hnet x := by
  let H := T.exists_voronoi_chart hnet x
  apply dist_pos.mpr
  intro he
  have hxsite := T.chart_injectiveOn _ H.choose_spec.1
    H.choose_spec.2.choose_spec.1 H.choose_spec.2.choose_spec.2.1.2 he
  exact hx (hxsite ▸ H.choose_spec.2.choose_spec.2.1.1)

end ArchivePLGeometry.FiniteChartedComplex
