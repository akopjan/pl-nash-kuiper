module

public import PLGeometry.SphericalAngularRegion
public import PLGeometry.SphericalRadialIncidence
public import PLGeometry.SphericalPolarMetric
public import PLGeometry.PolarNetData
public import PLGeometry.PolarMetricModulus

/-! # Complete local polar data for a finite spherical charted complex -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped InnerProductSpace

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalPolarCoordinatesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem sphericalAngularChart_tangent {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    inner ℝ (T.chart σ p).val (T.sphericalAngularChart p σ x).val = 0 := by
  let τ := (T.linkComplex p).support x
  have hτ := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, _, _⟩ := T.linkCoface_spec hτ
  obtain ⟨R, hR⟩ := T.exists_spherical_chart_transition hγ hσ
  have hp := congrArg GeodesicSphere.val (hR p ⟨hpγ, hpσ⟩)
  have hxR := T.sphericalAngularChart_transition hτ hσ hpσ hx R hR x
    ((T.linkComplex p).weightsOn_support x)
  change R (T.chart (T.linkCoface p τ) p).val = (T.chart σ p).val at hp
  rw [hxR, ← hp, R.inner_map_map]
  exact T.sphericalLinkAngularPoint_tangent p x

def sphericalPolarPoint (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.SphericalRadialAdmissible p r)
    (r : ℝ) (x : (T.linkComplex p).Space) : P := by
  classical
  exact if hr : 0 < r ∧ r ≤ 2 * R then T.sphericalRadialSite p (hR r hr.1 hr.2) x else p

theorem sphericalPolarPoint_eq (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.SphericalRadialAdmissible p r)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ 2 * R) (x : (T.linkComplex p).Space) :
    T.sphericalPolarPoint p R hR r x = T.sphericalRadialSite p (hR r hr hrR) x := by
  simp only [sphericalPolarPoint, dite_eq_left (And.intro hr hrR)]

@[simp] theorem sphericalPolarPoint_zero (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.SphericalRadialAdmissible p r)
    (x : (T.linkComplex p).Space) : T.sphericalPolarPoint p R hR 0 x = p := by
  simp only [sphericalPolarPoint, lt_self_iff_false, false_and, dite_false]

theorem sphericalPolarPoint_mem (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.SphericalRadialAdmissible p r)
    (hRπ : 2 * R < Real.pi)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ 2 * R) (x : (T.linkComplex p).Space)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    T.sphericalPolarPoint p R hR r x ∈ T.cell σ ↔ x ∈ T.linkRegion p σ := by
  rw [T.sphericalPolarPoint_eq p R hR hr hrR x]
  exact ⟨T.support_subset_of_sphericalRadialSite_mem p _ hr (hrR.trans_lt hRπ) x hσ hpσ,
    T.sphericalRadialSite_mem_of_support p _ x hσ hpσ⟩

theorem chart_sphericalPolarPoint (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.SphericalRadialAdmissible p r)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ 2 * R)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hx : x ∈ T.linkRegion p σ) :
    (T.chart σ (T.sphericalPolarPoint p R hR r x)).val =
      Real.cos r • (T.chart σ p).val + Real.sin r • (T.sphericalAngularChart p σ x).val := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [T.sphericalPolarPoint_zero, Real.cos_zero, Real.sin_zero,
      one_smul, zero_smul, add_zero]
  · rw [T.sphericalPolarPoint_eq p R hR hr hrR x]
    exact T.chart_sphericalRadialSite_in_coface p _ x hσ hpσ hx

theorem sphericalPolarPoint_reconstruct (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.SphericalRadialAdmissible p r)
    (hRπ : 2 * R < Real.pi)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x : P} (hxσ : x ∈ T.cell σ) (hx0 : 0 < T.radialDistance p x)
    (hxR : T.radialDistance p x < 2 * R) :
    ∃ u ∈ T.linkRegion p σ, T.sphericalPolarPoint p R hR (T.radialDistance p x) u = x := by
  have him := Set.mem_image_of_mem (T.chart σ) hxσ
  rw [T.image_cell σ hσ] at him
  have hne : T.chart σ x ≠ T.chart σ p := by
    intro he
    have hxD := T.radialDistance_eq p hσ hpσ hxσ
    rw [he, dist_self] at hxD
    linarith
  obtain ⟨u, hu, heu⟩ := T.exists_sphericalAngularChart_direction hσ hpσ him hne
  refine ⟨u, hu, ?_⟩
  apply T.chart_injectiveOn σ hσ
    ((T.sphericalPolarPoint_mem p R hR hRπ hx0 hxR.le u hσ hpσ).mpr hu) hxσ
  apply GeodesicSphere.ext
  have h0 : 0 < dist (T.chart σ p) (T.chart σ x) := by
    rwa [T.radialDistance_eq p hσ hpσ hxσ] at hx0
  have hπ : dist (T.chart σ p) (T.chart σ x) < Real.pi := by
    rw [← T.radialDistance_eq p hσ hpσ hxσ]
    exact hxR.trans hRπ
  rw [T.chart_sphericalPolarPoint p R hR hx0.le hxR.le u hσ hpσ hu,
    heu, T.radialDistance_eq p hσ hpσ hxσ]
  have h := GeodesicSphere.radial_decomposition (T.chart σ p) (T.chart σ x) h0 hπ
  rw [GeodesicSphere.radialDirection_eq_normalize] at h
  exact h.symm

def sphericalPolarNetData (p : P) (R : ℝ) (hR0 : 0 < R)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.SphericalRadialAdmissible p r)
    (hRπ : 2 * R < Real.pi)
    (hstar : ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < 2 * R → x ∈ T.openStar p) :
    PolarNetData T p (T.sphericalLink p) where
  radius := R
  radius_pos := hR0
  region := fun _ hσ hpσ => T.sphericalAngularRegion hσ hpσ
  point := T.sphericalPolarPoint p R hR
  point_zero := T.sphericalPolarPoint_zero p R hR
  point_mem := fun _ hσ hpσ r hr hrR x => T.sphericalPolarPoint_mem p R hR hRπ hr hrR x hσ hpσ
  point_radius := by
    intro r hr hrR x
    rcases hr.eq_or_lt with rfl | hr
    · rw [T.sphericalPolarPoint_zero, T.radialDistance_self]
    · rw [T.sphericalPolarPoint_eq p R hR hr (by linarith) x,
        T.radialDistance_sphericalRadialSite p _ hr.le (by linarith) x]
  point_star := by
    intro r hr hrR x
    rcases hr.eq_or_lt with rfl | hr
    · rw [T.sphericalPolarPoint_zero]
      exact T.mem_openStar_self p
    · let hadm := hR r hr (by linarith)
      rw [T.sphericalPolarPoint_eq p R hR hr (by linarith) x]
      obtain ⟨hσ, hpσ, _, _⟩ := T.linkCoface_spec ((T.linkComplex p).support_mem x)
      apply hstar _ hσ hpσ _ (T.sphericalRadialSite_mem p hadm x)
      rw [← T.radialDistance_eq p hσ hpσ (T.sphericalRadialSite_mem p hadm x),
        T.radialDistance_sphericalRadialSite p hadm hr.le (by linarith) x]
      linarith
  reconstruct := fun _ hσ hpσ _ hx hx0 hxR =>
    T.sphericalPolarPoint_reconstruct p R hR hRπ hσ hpσ hx hx0 hxR
  metric_modulus := by
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := exists_conePoint_metric_modulus .spherical
      (GeodesicSphere.northPole (n + 1)) (2 * R) hε
    refine ⟨δ, hδ, ?_⟩
    intro σ hσ hpσ u hu v hv r hr s hs hrs huv
    change dist (T.chart σ (T.sphericalPolarPoint p R hR r u))
      (T.chart σ (T.sphericalPolarPoint p R hR s v)) < ε
    rw [spherical_polar_dist_eq_cone (T.chart σ p) _ _
      (T.sphericalAngularChart p σ u) (T.sphericalAngularChart p σ v) r s
      (T.sphericalAngularChart_tangent hσ hpσ u hu)
      (T.sphericalAngularChart_tangent hσ hpσ v hv)
      (T.chart_sphericalPolarPoint p R hR hr.1 hr.2 u hσ hpσ hu)
      (T.chart_sphericalPolarPoint p R hR hs.1 hs.2 v hσ hpσ hv)]
    exact hd r hr s hs _ _ hrs huv
  strict_comparison := by
    intro σ hσ hpσ u hu v hv w hw r hr hrR s hs hsR hangle
    change dist (T.chart σ (T.sphericalPolarPoint p R hR r u))
        (T.chart σ (T.sphericalPolarPoint p R hR s v)) <
      dist (T.chart σ (T.sphericalPolarPoint p R hR r u))
        (T.chart σ (T.sphericalPolarPoint p R hR s w))
    let X := T.chart σ (T.sphericalPolarPoint p R hR r u)
    let Y := T.chart σ (T.sphericalPolarPoint p R hR s v)
    let Z := T.chart σ (T.sphericalPolarPoint p R hR s w)
    let U := T.sphericalAngularChart p σ u
    let V := T.sphericalAngularChart p σ v
    let W := T.sphericalAngularChart p σ w
    have hcos : Real.cos (dist U W) < Real.cos (dist U V) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi dist_nonneg (GeodesicSphere.dist_le_pi _ _) hangle
    have h₁ := spherical_polar_cos_dist (T.chart σ p) X Y U V r s
      (T.sphericalAngularChart_tangent hσ hpσ u hu)
      (T.sphericalAngularChart_tangent hσ hpσ v hv)
      (T.chart_sphericalPolarPoint p R hR hr.le hrR.le u hσ hpσ hu)
      (T.chart_sphericalPolarPoint p R hR hs.le (by linarith) v hσ hpσ hv)
    have h₂ := spherical_polar_cos_dist (T.chart σ p) X Z U W r s
      (T.sphericalAngularChart_tangent hσ hpσ u hu)
      (T.sphericalAngularChart_tangent hσ hpσ w hw)
      (T.chart_sphericalPolarPoint p R hR hr.le hrR.le u hσ hpσ hu)
      (T.chart_sphericalPolarPoint p R hR hs.le (by linarith) w hσ hpσ hw)
    have hmul := mul_pos (mul_pos
      (Real.sin_pos_of_pos_of_lt_pi hr (hrR.trans hRπ))
      (Real.sin_pos_of_pos_of_lt_pi hs (by linarith))) (sub_pos.mpr hcos)
    change dist X Y < dist X Z
    by_contra hn
    have hrev := Real.cos_le_cos_of_nonneg_of_le_pi
      (dist_nonneg : 0 ≤ dist X Z) (GeodesicSphere.dist_le_pi X Y) (le_of_not_gt hn)
    nlinarith

theorem exists_sphericalPolarNetData (p : P) :
    ∃ D : PolarNetData T p (T.sphericalLink p),
      ∀ σ ∈ T.simplices, p ∈ T.cell σ → ∀ x ∈ T.cell σ,
        dist (T.chart σ p) (T.chart σ x) < 2 * D.radius → x ∈ T.openStar p := by
  obtain ⟨ρ, hρ, hρπ, hrad⟩ := T.exists_uniform_spherical_link_radius p
  obtain ⟨s, hs, hstar⟩ := T.exists_radial_star_radius p
  let R : ℝ := min ρ s / 4
  have hR : 0 < R := div_pos (lt_min hρ hs) (by norm_num)
  have h2ρ : 2 * R ≤ ρ := by
    have hh := min_le_left ρ s
    dsimp only [R]
    linarith [lt_min hρ hs]
  have h2s : 2 * R < s := by
    have hh := min_le_right ρ s
    dsimp only [R]
    linarith [lt_min hρ hs]
  have hA : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.SphericalRadialAdmissible p r :=
    fun r hr hrR => hrad r hr (hrR.trans h2ρ)
  have hS : ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < 2 * R → x ∈ T.openStar p :=
    fun σ hσ hpσ x hx hdist => hstar σ hσ hpσ x hx (hdist.trans h2s)
  exact ⟨T.sphericalPolarNetData p R hR hA (by linarith [Real.pi_pos]) hS, hS⟩

end ArchivePLGeometry.FiniteChartedComplex
