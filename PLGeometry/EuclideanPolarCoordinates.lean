module

public import PLGeometry.EuclideanAngularRegion
public import PLGeometry.PolarNetData
public import PLGeometry.PolarMetricModulus

/-! # Complete local polar data for a finite Euclidean charted complex -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean (n + 1) P)

local instance euclideanPolarCoordinatesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def euclideanPolarPoint (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.EuclideanRadialAdmissible p r)
    (r : ℝ) (x : (T.linkComplex p).Space) : P := by
  classical
  exact if hr : 0 < r ∧ r ≤ 2 * R then T.euclideanRadialSite p (hR r hr.1 hr.2) x else p

theorem euclideanPolarPoint_eq (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.EuclideanRadialAdmissible p r)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ 2 * R) (x : (T.linkComplex p).Space) :
    T.euclideanPolarPoint p R hR r x = T.euclideanRadialSite p (hR r hr hrR) x := by
  simp only [euclideanPolarPoint, dite_eq_left (And.intro hr hrR)]

@[simp] theorem euclideanPolarPoint_zero (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.EuclideanRadialAdmissible p r)
    (x : (T.linkComplex p).Space) : T.euclideanPolarPoint p R hR 0 x = p := by
  simp only [euclideanPolarPoint, lt_self_iff_false, false_and, dite_false]

theorem euclideanPolarPoint_mem (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.EuclideanRadialAdmissible p r)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ 2 * R) (x : (T.linkComplex p).Space)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    T.euclideanPolarPoint p R hR r x ∈ T.cell σ ↔ x ∈ T.linkRegion p σ := by
  rw [T.euclideanPolarPoint_eq p R hR hr hrR x]
  exact ⟨T.support_subset_of_euclideanRadialSite_mem p _ hr x hσ hpσ,
    T.euclideanRadialSite_mem_of_support p _ x hσ hpσ⟩

theorem chart_euclideanPolarPoint (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.EuclideanRadialAdmissible p r)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ 2 * R)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hx : x ∈ T.linkRegion p σ) :
    T.chart σ (T.euclideanPolarPoint p R hR r x) =
      T.chart σ p + r • (T.euclideanAngularChart p σ x).val := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [T.euclideanPolarPoint_zero, zero_smul, add_zero]
  · rw [T.euclideanPolarPoint_eq p R hR hr hrR x]
    exact T.chart_euclideanRadialSite_in_coface p _ x hσ hpσ hx

theorem euclideanPolarPoint_reconstruct (p : P) (R : ℝ)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.EuclideanRadialAdmissible p r)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x : P} (hxσ : x ∈ T.cell σ) (hx0 : 0 < T.radialDistance p x)
    (hxR : T.radialDistance p x < 2 * R) :
    ∃ u ∈ T.linkRegion p σ, T.euclideanPolarPoint p R hR (T.radialDistance p x) u = x := by
  have him := Set.mem_image_of_mem (T.chart σ) hxσ
  rw [T.image_cell σ hσ] at him
  have hne : T.chart σ x ≠ T.chart σ p := by
    intro he
    have hxD := T.radialDistance_eq p hσ hpσ hxσ
    rw [he, dist_self] at hxD
    linarith
  obtain ⟨u, hu, heu⟩ := T.exists_euclideanAngularChart_direction hσ hpσ him hne
  refine ⟨u, hu, ?_⟩
  apply T.chart_injectiveOn σ hσ
    ((T.euclideanPolarPoint_mem p R hR hx0 hxR.le u hσ hpσ).mpr hu) hxσ
  rw [T.chart_euclideanPolarPoint p R hR hx0.le hxR.le u hσ hpσ hu, heu,
    T.radialDistance_eq p hσ hpσ hxσ, dist_eq_norm', NormedSpace.norm_smul_normalize]
  exact add_sub_cancel _ _

def euclideanPolarNetData (p : P) (R : ℝ) (hR0 : 0 < R)
    (hR : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.EuclideanRadialAdmissible p r)
    (hstar : ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < 2 * R → x ∈ T.openStar p) :
    PolarNetData T p (T.euclideanLink p) where
  radius := R
  radius_pos := hR0
  region := fun _ hσ hpσ => T.euclideanAngularRegion hσ hpσ
  point := T.euclideanPolarPoint p R hR
  point_zero := T.euclideanPolarPoint_zero p R hR
  point_mem := fun _ hσ hpσ r hr hrR x => T.euclideanPolarPoint_mem p R hR hr hrR x hσ hpσ
  point_radius := by
    intro r hr hrR x
    rcases hr.eq_or_lt with rfl | hr
    · rw [T.euclideanPolarPoint_zero, T.radialDistance_self]
    · rw [T.euclideanPolarPoint_eq p R hR hr (by linarith) x,
        T.radialDistance_euclideanRadialSite p _ hr.le x]
  point_star := by
    intro r hr hrR x
    rcases hr.eq_or_lt with rfl | hr
    · rw [T.euclideanPolarPoint_zero]
      exact T.mem_openStar_self p
    · let hadm := hR r hr (by linarith)
      rw [T.euclideanPolarPoint_eq p R hR hr (by linarith) x]
      obtain ⟨hσ, hpσ, _, _⟩ := T.linkCoface_spec ((T.linkComplex p).support_mem x)
      apply hstar _ hσ hpσ _ (T.euclideanRadialSite_mem p hadm x)
      rw [← T.radialDistance_eq p hσ hpσ (T.euclideanRadialSite_mem p hadm x),
        T.radialDistance_euclideanRadialSite p hadm hr.le x]
      linarith
  reconstruct := fun _ hσ hpσ _ hx hx0 hxR => T.euclideanPolarPoint_reconstruct p R hR hσ hpσ hx hx0 hxR
  metric_modulus := by
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := exists_conePoint_metric_modulus .euclidean
      (0 : Model .euclidean (n + 1)) (2 * R) hε
    refine ⟨δ, hδ, ?_⟩
    intro σ hσ hpσ u hu v hv r hr s hs hrs huv
    change dist (T.chart σ (T.euclideanPolarPoint p R hR r u))
      (T.chart σ (T.euclideanPolarPoint p R hR s v)) < ε
    rw [T.chart_euclideanPolarPoint p R hR hr.1 hr.2 u hσ hpσ hu,
      T.chart_euclideanPolarPoint p R hR hs.1 hs.2 v hσ hpσ hv]
    change dist (conePoint .euclidean n (T.chart σ p) (T.euclideanAngularChart p σ u) r)
      (conePoint .euclidean n (T.chart σ p) (T.euclideanAngularChart p σ v) s) < ε
    rw [conePoint_dist_eq .euclidean (T.chart σ p) 0
      (T.euclideanAngularChart p σ u) (T.euclideanAngularChart p σ v)
      (T.euclideanAngularChart p σ u) (T.euclideanAngularChart p σ v) r s rfl]
    exact hd r hr s hs _ _ hrs huv
  strict_comparison := by
    intro σ hσ hpσ u hu v hv w hw r hr hrR s hs hsR hangle
    change dist (T.chart σ (T.euclideanPolarPoint p R hR r u))
        (T.chart σ (T.euclideanPolarPoint p R hR s v)) <
      dist (T.chart σ (T.euclideanPolarPoint p R hR r u))
        (T.chart σ (T.euclideanPolarPoint p R hR s w))
    rw [T.chart_euclideanPolarPoint p R hR hr.le hrR.le u hσ hpσ hu,
      T.chart_euclideanPolarPoint p R hR hs.le (by linarith) v hσ hpσ hv,
      T.chart_euclideanPolarPoint p R hR hs.le (by linarith) w hσ hpσ hw]
    let U := T.euclideanAngularChart p σ u
    let V := T.euclideanAngularChart p σ v
    let W := T.euclideanAngularChart p σ w
    have hcos : Real.cos (dist U W) < Real.cos (dist U V) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi dist_nonneg (GeodesicSphere.dist_le_pi _ _) hangle
    have h₁ := euclidean_cone_dist_sq (T.chart σ p) U V r s
    have h₂ := euclidean_cone_dist_sq (T.chart σ p) U W r s
    have hmul := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hr) hs)
      (sub_pos.mpr hcos)
    change dist (conePoint .euclidean n (T.chart σ p) U r) (conePoint .euclidean n (T.chart σ p) V s) <
      dist (conePoint .euclidean n (T.chart σ p) U r) (conePoint .euclidean n (T.chart σ p) W s)
    nlinarith [dist_nonneg (x := conePoint .euclidean n (T.chart σ p) U r)
      (y := conePoint .euclidean n (T.chart σ p) V s),
      dist_nonneg (x := conePoint .euclidean n (T.chart σ p) U r)
      (y := conePoint .euclidean n (T.chart σ p) W s)]

theorem exists_euclideanPolarNetData (p : P) :
    ∃ D : PolarNetData T p (T.euclideanLink p),
      ∀ σ ∈ T.simplices, p ∈ T.cell σ → ∀ x ∈ T.cell σ,
        dist (T.chart σ p) (T.chart σ x) < 2 * D.radius → x ∈ T.openStar p := by
  obtain ⟨ρ, hρ, hrad⟩ := T.exists_uniform_euclidean_link_radius p
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
  have hA : ∀ r : ℝ, 0 < r → r ≤ 2 * R → T.EuclideanRadialAdmissible p r :=
    fun r hr hrR => hrad r hr (hrR.trans h2ρ)
  have hS : ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < 2 * R → x ∈ T.openStar p :=
    fun σ hσ hpσ x hx hdist => hstar σ hσ hpσ x hx (hdist.trans h2s)
  exact ⟨T.euclideanPolarNetData p R hR hA hS, hS⟩

end ArchivePLGeometry.FiniteChartedComplex
