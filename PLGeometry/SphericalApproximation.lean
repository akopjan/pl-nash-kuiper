module

public import PLGeometry.FoldedSphericalPL
public import BrehmApprox.SphericalFoldedTheorem

/-! # Spherical approximation with a compatible source triangulation -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

open BrehmApprox GeodesicSphere

variable {P : Type*} [MetricSpace P] {n N : ℕ}

/-- Approximation from an actual spherical folding contained in a cap
small enough for the prescribed contraction margin. -/
theorem spherical_approximation_of_small_folded_geometry
    (G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N)
    (T : SphericalSimplicialFaceData G.toPolyhedralFaceData)
    (p : GeodesicSphere n) {ρ η : ℝ} (hρ0 : 0 ≤ ρ) (hρη : ρ < η)
    (hηπ : η < Real.pi / 2) (hcap : ∀ x : P, dist p (G.fold x) ≤ ρ)
    {κ : NNReal} (f : P → GeodesicSphere n) (hf : LipschitzWith κ f)
    (hshort : (κ : ℝ) * gnomonicFactor η * (Real.sinc η)⁻¹ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → GeodesicSphere n, LipschitzWith 1 g ∧
      PLIsometry .spherical n g ∧ ∀ x, dist (g x) (f x) < ε := by
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
  obtain ⟨g, hg, hm, hnear⟩ := G.chart_folded_approximation_with_maps
    D TE (gnomonicTotal p) (Metric.ball p η)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) (T.gnomonicFaceData_core_eq_image p hp)
    Metric.isOpen_ball hcoreV ((continuousOn_gnomonicTotal p).mono hVhem)
    hB hΦLip hinv p f hf hshort (sphericalBrehm n) hε
  have hhem : ∀ x, G.fold x ∈ openHemisphere p := by
    intro x
    exact (dist_lt_pi_div_two_iff p (G.fold x)).mp
      ((hcap x).trans_lt (hρη.trans hηπ))
  exact ⟨g, hg, plIsometry_spherical_of_model_maps G T p hhem hg.continuous hm, hnear⟩

/-- Strict spherical contractions admit arbitrarily close PL approximations
whenever the source admits arbitrarily small genuine initial foldings. -/
theorem spherical_strict_approximation_of_small_foldable
    (hP : SphericalSmallFoldable P n)
    (f : P → GeodesicSphere n) {κ : NNReal} (hf : LipschitzWith κ f) (hκ : κ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → GeodesicSphere n, LipschitzWith 1 g ∧
      PLIsometry .spherical n g ∧ ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨η, hη0, hηπ, hmargin⟩ := exists_gnomonic_distortion_margin (show (κ : ℝ) < 1 from hκ)
  have hr0 : 0 < η / 2 := by positivity
  have hrη : η / 2 < η := by linarith
  obtain ⟨N, G, T, p, hcap⟩ := hP (η / 2) hr0 (hrη.trans hηπ)
  exact spherical_approximation_of_small_folded_geometry G T p
    hr0.le hrη hηπ hcap f hf (hmargin η hη0.le le_rfl) hε

/-- Short spherical maps with image in a closed hemisphere admit PL
approximation under the same initial-folding condition. -/
theorem spherical_hemisphere_approximation_of_small_foldable
    (hP : SphericalSmallFoldable P n)
    (f : P → GeodesicSphere n) (hf : LipschitzWith 1 f)
    (p : GeodesicSphere n) (himage : ∀ x, f x ∈ closedHemisphere p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → GeodesicSphere n, LipschitzWith 1 g ∧
      PLIsometry .spherical n g ∧ ∀ x, dist (g x) (f x) < ε := by
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨u, K, hK, hu, huf⟩ := strictify_lipschitz_with_hemispherical_range hf p himage hε2
  obtain ⟨g, hg, hPL, hgu⟩ := spherical_strict_approximation_of_small_foldable hP u hu hK hε2
  refine ⟨g, hg, hPL, ?_⟩
  intro x
  have h₁ := hgu x
  have h₂ := huf x
  have ht := dist_triangle (g x) (u x) (f x)
  linarith

end ArchivePLGeometry
