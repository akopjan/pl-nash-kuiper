module

public import BrehmApprox.SphericalCommonChart
public import BrehmApprox.ChartFoldedTheorem
public import BrehmApprox.ModelTheorems

/-!
# Spherical approximation from an actual sufficiently small initial folding

This endpoint has no reference atlas, collar, flattening map, nearest-face
selection, or Euclidean face transport among its inputs. Those are constructed
from the actual spherical simplex data and the common central chart.

This intermediate theorem takes an initial piecewise-isometric folding into
an explicitly small cap and its genuine finite simplex data. The universal
folding construction is proved in `ArchivePLGeometry.FiniteFoldingExistence`.
The fixed-cap distortion condition records the required strictness margin:
the cap radius is selected after the approximation tolerance when a short
map is first strictified.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

open GeodesicSphere

variable {P : Type*} [MetricSpace P] {n N : ℕ}

/-- The complete spherical approximation construction for a genuinely folded
source with a common cap small enough for the prescribed strict margin.
The finite spherical Brehm theorem used in the construction is proved. -/
theorem spherical_folded_polyhedron_approximation
    (G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N)
    (T : SphericalSimplicialFaceData G.toPolyhedralFaceData)
    (p : GeodesicSphere n) {ρ η : ℝ} (hρ0 : 0 ≤ ρ) (hρη : ρ < η)
    (hηπ : η < Real.pi / 2) (hcap : ∀ x : P, dist p (G.fold x) ≤ ρ)
    {κ : NNReal} (f : P → GeodesicSphere n) (hf : LipschitzWith κ f)
    (hshort : (κ : ℝ) * gnomonicFactor η * (Real.sinc η)⁻¹ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → GeodesicSphere n, LipschitzWith 1 g ∧
      PolyhedralPiecewiseIsometry (sphericalPolytopeModel n) G.fold g ∧
      ∀ x, dist (g x) (f x) < ε := by
  have hη0 : 0 < η := hρ0.trans_lt hρη
  have hcoreCap : ∀ i, ∀ x ∈ G.core i, dist p x ≤ ρ := by
    intro i x hx
    rw [← G.image_cell i] at hx
    obtain ⟨z, _, rfl⟩ := hx
    exact hcap z
  have hp : ∀ i, ∀ v ∈ T.vertices i, 0 < inner ℝ p.val v.val := by
    intro i v hv
    have hvi : v ∈ G.core i := by
      rw [T.core_eq i]
      exact mem_sphericalCell_of_mem hv
    exact (dist_lt_pi_div_two_iff p v).mp ((hcoreCap i v hvi).trans_lt (hρη.trans hηπ))
  let D := T.gnomonicFaceData p hp
  let TE := T.gnomonicSimplicialFaceData p hp
  let A : NNReal := ⟨gnomonicFactor η, gnomonicFactor_nonneg hη0.le hηπ⟩
  let B : NNReal := ⟨(Real.sinc η)⁻¹, zero_le_one.trans (one_le_inv_sinc hη0.le hηπ)⟩
  have hB : 0 < (B : ℝ) := zero_lt_one.trans_le (one_le_inv_sinc hη0.le hηπ)
  have hVhem : Metric.ball p η ⊆ openHemisphere p := by
    intro x hx
    apply (dist_lt_pi_div_two_iff p x).mp
    have hxp : dist p x < η := by simpa only [Metric.mem_ball, dist_comm] using hx
    exact hxp.trans hηπ
  have hcoreV : ∀ i, G.core i ⊆ Metric.ball p η := by
    intro i x hx
    rw [Metric.mem_ball, dist_comm]
    exact (hcoreCap i x hx).trans_lt hρη
  have hΦLip : ∀ x ∈ Metric.ball p η, ∀ y ∈ Metric.ball p η,
      dist (gnomonicTotal p x) (gnomonicTotal p y) ≤ (A : ℝ) * dist x y := by
    intro x hx y hy
    apply gnomonicTotal_dist_le p hη0.le hηπ x y
    · exact (by simpa only [Metric.mem_ball, dist_comm] using hx : dist p x < η).le
    · exact (by simpa only [Metric.mem_ball, dist_comm] using hy : dist p y < η).le
  have hinv : ∀ i, ∀ x ∈ G.core i, ∀ y ∈ G.core i,
      dist x y ≤ (B : ℝ) * dist (gnomonicTotal p x) (gnomonicTotal p y) := by
    intro i x hx y hy
    exact dist_le_gnomonicTotal_dist p hη0 hηπ x y
      ((hcoreCap i x hx).trans hρη.le) ((hcoreCap i y hy).trans hρη.le)
  exact G.chart_folded_approximation D TE (gnomonicTotal p) (Metric.ball p η)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) (T.gnomonicFaceData_core_eq_image p hp)
    Metric.isOpen_ball hcoreV ((continuousOn_gnomonicTotal p).mono hVhem)
    hB hΦLip hinv p f hf hshort (sphericalBrehm n) hε

/-- The geometric interface for actual finite spherical simplex
foldings into arbitrarily small caps. It contains no target map, reference
atlas, flattening map, approximation, or Brehm output. -/
def SphericalSmallFoldable (P : Type*) [MetricSpace P] (n : ℕ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < Real.pi / 2 → ∃ N : ℕ,
    ∃ G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N,
    ∃ _T : SphericalSimplicialFaceData G.toPolyhedralFaceData,
    ∃ p : GeodesicSphere n, ∀ x : P, dist p (G.fold x) ≤ ρ

/-- A strict map can be approximated once arbitrarily small genuine initial
foldings are supplied. The required cap radius is constructed from its fixed
Lipschitz margin. -/
theorem spherical_small_foldable_strict_approximation
    (hP : SphericalSmallFoldable P n)
    (f : P → GeodesicSphere n) {κ : NNReal} (hf : LipschitzWith κ f) (hκ : κ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N,
      ∃ g : P → GeodesicSphere n, LipschitzWith 1 g ∧
        PolyhedralPiecewiseIsometry (sphericalPolytopeModel n) G.fold g ∧
        ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨η, hη0, hηπ, hmargin⟩ := exists_gnomonic_distortion_margin (show (κ : ℝ) < 1 from hκ)
  have hr0 : 0 < η / 2 := by positivity
  have hrη : η / 2 < η := by linarith
  obtain ⟨N, G, T, p, hcap⟩ := hP (η / 2) hr0 (hrη.trans hηπ)
  obtain ⟨g, hg, hPL, hnear⟩ := spherical_folded_polyhedron_approximation G T p
    hr0.le hrη hηπ hcap f hf (hmargin η hη0.le le_rfl) hε
  exact ⟨N, G, g, hg, hPL, hnear⟩

/-- The hemispherical case: strictification and the subsequent choice of a
sufficiently small folding are proved. A closed hemisphere already suffices.
Existence of the initial-folding family remains the explicit geometric input. -/
theorem spherical_small_foldable_hemisphere_approximation
    (hP : SphericalSmallFoldable P n)
    (f : P → GeodesicSphere n) (hf : LipschitzWith 1 f)
    (p : GeodesicSphere n) (himage : ∀ x, f x ∈ closedHemisphere p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N,
      ∃ g : P → GeodesicSphere n, LipschitzWith 1 g ∧
        PolyhedralPiecewiseIsometry (sphericalPolytopeModel n) G.fold g ∧
        ∀ x, dist (g x) (f x) < ε := by
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨u, K, hK, hu, huf⟩ := strictify_lipschitz_with_hemispherical_range hf p himage hε2
  obtain ⟨N, G, g, hg, hPL, hgu⟩ := spherical_small_foldable_strict_approximation hP u hu hK hε2
  refine ⟨N, G, g, hg, hPL, ?_⟩
  intro x
  have h₁ := hgu x
  have h₂ := huf x
  have ht := dist_triangle (g x) (u x) (f x)
  linarith

end BrehmApprox
