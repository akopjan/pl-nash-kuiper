module

public import PLGeometry.HyperbolicAngularRegion
public import PLGeometry.HyperbolicRadialChart
public import PLGeometry.ModelConeDirections
public import PLGeometry.PolarNetData
public import PLGeometry.PolarMetricModulus

/-! # Complete local polar data for a finite Hyperbolic charted complex -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

local instance hyperbolicPolarCoordinatesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def hyperbolicPolarPoint (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.HyperbolicRadialAdmissible p r)
    (r : ℝ) (x : (T.linkComplex p).Space) : P := by
  classical
  exact if hr : 0 < r ∧ r ≤ 2 * R then T.hyperbolicRadialSite p (hR r hr.1 hr.2) x else p

theorem hyperbolicPolarPoint_eq (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.HyperbolicRadialAdmissible p r)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ 2 * R) (x : (T.linkComplex p).Space) :
    T.hyperbolicPolarPoint p R hR r x = T.hyperbolicRadialSite p (hR r hr hrR) x := by
  simp only [hyperbolicPolarPoint, dite_eq_left (And.intro hr hrR)]

@[simp] theorem hyperbolicPolarPoint_zero (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.HyperbolicRadialAdmissible p r)
    (x : (T.linkComplex p).Space) : T.hyperbolicPolarPoint p R hR 0 x = p := by
  simp only [hyperbolicPolarPoint, lt_self_iff_false, false_and, dite_false]

theorem hyperbolicPolarPoint_mem (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.HyperbolicRadialAdmissible p r)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ 2 * R) (x : (T.linkComplex p).Space)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    T.hyperbolicPolarPoint p R hR r x ∈ T.cell σ ↔ x ∈ T.linkRegion p σ := by
  rw [T.hyperbolicPolarPoint_eq p R hR hr hrR x]
  exact ⟨T.support_subset_of_hyperbolicRadialSite_mem p _ hr x hσ hpσ,
    T.hyperbolicRadialSite_mem_of_support p _ x hσ hpσ⟩

theorem chart_hyperbolicPolarPoint (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.HyperbolicRadialAdmissible p r)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ 2 * R)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hx : x ∈ T.linkRegion p σ) :
    T.chart σ (T.hyperbolicPolarPoint p R hR r x) =
      conePoint .hyperbolic n (T.chart σ p) (T.hyperbolicAngularChart p σ x) r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [T.hyperbolicPolarPoint_zero, conePoint_zero]
  · rw [T.hyperbolicPolarPoint_eq p R hR hr hrR x]
    exact T.chart_hyperbolicRadialSite_in_coface p _ x hσ hpσ hx

theorem hyperbolicPolarPoint_reconstruct (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.HyperbolicRadialAdmissible p r)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x : P} (hxσ : x ∈ T.cell σ) (hx0 : 0 < T.radialDistance p x)
    (hxR : T.radialDistance p x < 2 * R) :
    ∃ u ∈ T.linkRegion p σ, T.hyperbolicPolarPoint p R hR (T.radialDistance p x) u = x := by
  have him := Set.mem_image_of_mem (T.chart σ) hxσ
  rw [T.image_cell σ hσ] at him
  have hne : T.chart σ x ≠ T.chart σ p := by
    intro he
    have hxD := T.radialDistance_eq p hσ hpσ hxσ
    rw [he, dist_self] at hxD
    linarith
  obtain ⟨u, hu, heu⟩ := T.exists_hyperbolicAngularChart_direction hσ hpσ him hne
  refine ⟨u, hu, ?_⟩
  apply T.chart_injectiveOn σ hσ
    ((T.hyperbolicPolarPoint_mem p R hR hx0 hxR.le u hσ hpσ).mpr hu) hxσ
  have h0 : 0 < dist (T.chart σ p) (T.chart σ x) := by
    rwa [T.radialDistance_eq p hσ hpσ hxσ] at hx0
  have hucone : T.hyperbolicAngularChart p σ u = coneDirection .hyperbolic n (T.chart σ p) (T.chart σ x)
      h0 (by intro h; cases h) := by
    apply GeodesicSphere.ext
    rw [heu, BrehmApprox.HyperbolicLink.frame, BrehmApprox.HyperbolicSpace.klein,
      NormedSpace.normalize_smul_of_pos
        (inv_pos.mpr (BrehmApprox.Hyperboloid.height_pos _))]
    change NormedSpace.normalize (BrehmApprox.HyperbolicSpace.radialVector
      (T.chart σ p) (T.chart σ x)) = _
    rw [NormedSpace.normalize, BrehmApprox.HyperbolicSpace.norm_radialVector]
    rfl
  rw [T.chart_hyperbolicPolarPoint p R hR hx0.le hxR.le u hσ hpσ hu, hucone,
    T.radialDistance_eq p hσ hpσ hxσ]
  exact conePoint_coneDirection .hyperbolic _ _ h0 (by intro h; cases h)

def hyperbolicPolarNetData (p : P) (R : ℝ) (hR0 : 0 < R)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.HyperbolicRadialAdmissible p r)
    (hstar : ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < 2 * R → x ∈ T.openStar p) :
    PolarNetData T p (T.hyperbolicLink p) where
  radius := R
  radius_pos := hR0
  region := fun _ hσ hpσ => T.hyperbolicAngularRegion hσ hpσ
  point := T.hyperbolicPolarPoint p R hR
  point_zero := T.hyperbolicPolarPoint_zero p R hR
  point_mem := fun _ hσ hpσ r hr hrR x => T.hyperbolicPolarPoint_mem p R hR hr hrR x hσ hpσ
  point_radius := by
    intro r hr hrR x
    rcases hr.eq_or_lt with rfl | hr
    · rw [T.hyperbolicPolarPoint_zero, T.radialDistance_self]
    · rw [T.hyperbolicPolarPoint_eq p R hR hr (by linarith) x,
        T.radialDistance_hyperbolicRadialSite p _ hr.le x]
  point_star := by
    intro r hr hrR x
    rcases hr.eq_or_lt with rfl | hr
    · rw [T.hyperbolicPolarPoint_zero]
      exact T.mem_openStar_self p
    · let hadm := hR r hr (by linarith)
      rw [T.hyperbolicPolarPoint_eq p R hR hr (by linarith) x]
      obtain ⟨hσ, hpσ, _, _⟩ := T.linkCoface_spec ((T.linkComplex p).support_mem x)
      apply hstar _ hσ hpσ _ (T.hyperbolicRadialSite_mem p hadm x)
      rw [← T.radialDistance_eq p hσ hpσ (T.hyperbolicRadialSite_mem p hadm x),
        T.radialDistance_hyperbolicRadialSite p hadm hr.le x]
      linarith
  reconstruct := fun _ hσ hpσ _ hx hx0 hxR => T.hyperbolicPolarPoint_reconstruct p R hR hσ hpσ hx hx0 hxR
  metric_modulus := by
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := exists_conePoint_metric_modulus .hyperbolic
      (⟨0⟩ : Model .hyperbolic (n + 1)) (2 * R) hε
    refine ⟨δ, hδ, ?_⟩
    intro σ hσ hpσ u hu v hv r hr s hs hrs huv
    change dist (T.chart σ (T.hyperbolicPolarPoint p R hR r u))
      (T.chart σ (T.hyperbolicPolarPoint p R hR s v)) < ε
    rw [T.chart_hyperbolicPolarPoint p R hR hr.1 hr.2 u hσ hpσ hu,
      T.chart_hyperbolicPolarPoint p R hR hs.1 hs.2 v hσ hpσ hv]
    change dist (conePoint .hyperbolic n (T.chart σ p) (T.hyperbolicAngularChart p σ u) r)
      (conePoint .hyperbolic n (T.chart σ p) (T.hyperbolicAngularChart p σ v) s) < ε
    rw [conePoint_dist_eq .hyperbolic (T.chart σ p) ⟨0⟩
      (T.hyperbolicAngularChart p σ u) (T.hyperbolicAngularChart p σ v)
      (T.hyperbolicAngularChart p σ u) (T.hyperbolicAngularChart p σ v) r s rfl]
    exact hd r hr s hs _ _ hrs huv
  strict_comparison := by
    intro σ hσ hpσ u hu v hv w hw r hr hrR s hs hsR hangle
    change dist (T.chart σ (T.hyperbolicPolarPoint p R hR r u))
        (T.chart σ (T.hyperbolicPolarPoint p R hR s v)) <
      dist (T.chart σ (T.hyperbolicPolarPoint p R hR r u))
        (T.chart σ (T.hyperbolicPolarPoint p R hR s w))
    rw [T.chart_hyperbolicPolarPoint p R hR hr.le hrR.le u hσ hpσ hu,
      T.chart_hyperbolicPolarPoint p R hR hs.le (by linarith) v hσ hpσ hv,
      T.chart_hyperbolicPolarPoint p R hR hs.le (by linarith) w hσ hpσ hw]
    let U := T.hyperbolicAngularChart p σ u
    let V := T.hyperbolicAngularChart p σ v
    let W := T.hyperbolicAngularChart p σ w
    have hcos : Real.cos (dist U W) < Real.cos (dist U V) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi dist_nonneg (GeodesicSphere.dist_le_pi _ _) hangle
    have h₁ := hyperbolic_cone_cosh_dist (T.chart σ p) U V r s
    have h₂ := hyperbolic_cone_cosh_dist (T.chart σ p) U W r s
    have hmul := mul_pos (mul_pos (Real.sinh_pos_iff.mpr hr) (Real.sinh_pos_iff.mpr hs))
      (sub_pos.mpr hcos)
    change dist (conePoint .hyperbolic n (T.chart σ p) U r) (conePoint .hyperbolic n (T.chart σ p) V s) <
      dist (conePoint .hyperbolic n (T.chart σ p) U r) (conePoint .hyperbolic n (T.chart σ p) W s)
    by_contra hn
    have hrev : Real.cosh (dist (conePoint .hyperbolic n (T.chart σ p) U r)
        (conePoint .hyperbolic n (T.chart σ p) W s)) ≤
      Real.cosh (dist (conePoint .hyperbolic n (T.chart σ p) U r)
        (conePoint .hyperbolic n (T.chart σ p) V s)) := by
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_of_nonneg dist_nonneg] using le_of_not_gt hn
    nlinarith

theorem exists_hyperbolicPolarNetData (p : P) :
    ∃ D : PolarNetData T p (T.hyperbolicLink p),
      ∀ σ ∈ T.simplices, p ∈ T.cell σ → ∀ x ∈ T.cell σ,
        dist (T.chart σ p) (T.chart σ x) < 2 * D.radius → x ∈ T.openStar p := by
  obtain ⟨ρ, hρ, hrad⟩ := T.exists_uniform_hyperbolic_link_radius p
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
  have hA : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.HyperbolicRadialAdmissible p r :=
    fun r hr hrR => hrad r hr (hrR.trans h2ρ)
  have hS : ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < 2 * R → x ∈ T.openStar p :=
    fun σ hσ hpσ x hx hdist => hstar σ hσ hpσ x hx (hdist.trans h2s)
  exact ⟨T.hyperbolicPolarNetData p R hR hA hS, hS⟩

end ArchivePLGeometry.FiniteChartedComplex
