module

public import BrehmApprox.SphericalProjection
public import BrehmApprox.SphericalGnomonic

/-!
# Quantitative gnomonic charts

On a spherical ball of radius tending to zero the actual central projection
and its inverse are bi-Lipschitz with constants tending to one. The proof uses
unit-vector identities and elementary trigonometric estimates only.
-/

@[expose] public section

noncomputable section

namespace GeodesicSphere

open BrehmApprox

variable {n : ℕ}

/-- On a small spherical cap the pole coordinate varies only to second order. -/
lemma abs_inner_pole_sub_le (p x y : GeodesicSphere n) {ρ : ℝ}
    (hx : dist p x ≤ ρ) (hy : dist p y ≤ ρ) :
    |inner ℝ p.val x.val - inner ℝ p.val y.val| ≤ ρ * ‖x.val - y.val‖ := by
  let a := inner ℝ (p.val - x.val) (x.val - y.val)
  let b := inner ℝ (p.val - y.val) (x.val - y.val)
  have hid : a + b = 2 * (inner ℝ p.val x.val - inner ℝ p.val y.val) := by
    dsimp [a, b]
    simp only [inner_sub_left, inner_sub_right,
      inner_self_eq_one_of_norm_eq_one x.norm_val,
      inner_self_eq_one_of_norm_eq_one y.norm_val]
    rw [real_inner_comm y.val x.val]
    ring
  have ha : |a| ≤ ρ * ‖x.val - y.val‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((chord_le_dist p x).trans hx) (norm_nonneg _))
  have hb : |b| ≤ ρ * ‖x.val - y.val‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((chord_le_dist p y).trans hy) (norm_nonneg _))
  have hsum := (abs_add_le a b).trans (add_le_add ha hb)
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsum
  linarith

/-- A concrete distortion bound for the central projection. Its value at zero
is one, and it is continuous near zero. -/
def gnomonicFactor (ρ : ℝ) : ℝ := (Real.cos ρ)⁻¹ + ρ / (Real.cos ρ) ^ 2

@[simp]
lemma gnomonicFactor_zero : gnomonicFactor 0 = 1 := by simp [gnomonicFactor]

lemma gnomonicFactor_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρπ : ρ < Real.pi / 2) :
    0 ≤ gnomonicFactor ρ := by
  have hc : 0 < Real.cos ρ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hρπ⟩
  exact add_nonneg (inv_nonneg.mpr hc.le) (div_nonneg hρ0 (sq_nonneg _))

lemma continuousAt_gnomonicFactor : ContinuousAt gnomonicFactor 0 := by
  unfold gnomonicFactor
  exact ((Real.continuous_cos.continuousAt.inv₀ (by simp)).add
    (continuousAt_id.div (Real.continuous_cos.continuousAt.pow 2) (by simp)))

/-- The chart is nearly short on a sufficiently small spherical ball. -/
theorem gnomonic_dist_le (p : GeodesicSphere n) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρπ : ρ < Real.pi / 2)
    (x y : openHemisphere p) (hx : dist p x.val ≤ ρ) (hy : dist p y.val ≤ ρ) :
    dist (gnomonic p x) (gnomonic p y) ≤ gnomonicFactor ρ * dist x.val y.val := by
  let a : ℝ := inner ℝ p.val x.val.val
  let b : ℝ := inner ℝ p.val y.val.val
  let c : ℝ := Real.cos ρ
  have ha0 : 0 < a := x.property
  have hb0 : 0 < b := y.property
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hρπ⟩
  have hca : c ≤ a := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (dist_nonneg : 0 ≤ dist p x.val) (by linarith [Real.pi_pos]) hx
    simpa only [cos_dist] using h
  have hcb : c ≤ b := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (dist_nonneg : 0 ≤ dist p y.val) (by linarith [Real.pi_pos]) hy
    simpa only [cos_dist] using h
  have hab : c ^ 2 ≤ a * b := by
    simpa only [pow_two] using mul_le_mul hca hcb hc0.le ha0.le
  have hinva : a⁻¹ ≤ c⁻¹ := (inv_le_inv₀ ha0 hc0).mpr hca
  have hinv : |a⁻¹ - b⁻¹| ≤ (ρ * ‖x.val.val - y.val.val‖) / c ^ 2 := by
    rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
    exact div_le_div₀ (mul_nonneg hρ0 (norm_nonneg _))
      (abs_inner_pole_sub_le p x.val y.val hx hy) (sq_pos_of_pos hc0) hab
  have heq : (gnomonic p x).val - (gnomonic p y).val =
      a⁻¹ • (x.val.val - y.val.val) + (a⁻¹ - b⁻¹) • y.val.val := by
    simp only [gnomonic_val, a, b, smul_sub, sub_smul]
    abel
  have hchord : dist (gnomonic p x) (gnomonic p y) ≤
      gnomonicFactor ρ * ‖x.val.val - y.val.val‖ := by
    rw [dist_eq_norm]
    change ‖(gnomonic p x).val - (gnomonic p y).val‖ ≤ _
    rw [heq]
    calc
      _ ≤ ‖a⁻¹ • (x.val.val - y.val.val)‖ + ‖(a⁻¹ - b⁻¹) • y.val.val‖ := norm_add_le _ _
      _ = a⁻¹ * ‖x.val.val - y.val.val‖ + |a⁻¹ - b⁻¹| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr ha0), y.val.norm_val, mul_one]
      _ ≤ c⁻¹ * ‖x.val.val - y.val.val‖ + (ρ * ‖x.val.val - y.val.val‖) / c ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hinva (norm_nonneg _)) hinv
      _ = gnomonicFactor ρ * ‖x.val.val - y.val.val‖ := by dsimp [gnomonicFactor, c]; ring
  exact hchord.trans (mul_le_mul_of_nonneg_left (chord_le_dist _ _)
    (gnomonicFactor_nonneg hρ0 hρπ))

lemma one_le_norm_pole_add_tangent (p : GeodesicSphere n) (z : tangentPlane p) :
    1 ≤ ‖p.val + z.val‖ := by
  have h := real_inner_le_norm p.val (p.val + z.val)
  rwa [inner_pole_add_tangent, p.norm_val, one_mul] at h

/-- Inverse central projection is nonexpansive for chord distances. -/
lemma gnomonicInverse_chord_le (p : GeodesicSphere n) (z w : tangentPlane p) :
    ‖(gnomonicInverse p z).val.val - (gnomonicInverse p w).val.val‖ ≤ dist z w := by
  rw [gnomonicInverse_val_val, gnomonicInverse_val_val]
  change ‖NormedSpace.normalize (p.val + z.val) -
    NormedSpace.normalize (p.val + w.val)‖ ≤ ‖z.val - w.val‖
  have h := norm_normalize_sub_normalize_le zero_lt_one
    (one_le_norm_pole_add_tangent p z) (one_le_norm_pole_add_tangent p w)
  simpa only [div_one, add_sub_add_left_eq_sub, dist_eq_norm] using h

/-- The inverse chart is nearly short when both image points lie in a small cap. -/
theorem gnomonicInverse_dist_le (p : GeodesicSphere n) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi / 2)
    (z w : tangentPlane p)
    (hz : dist p (gnomonicInverse p z).val ≤ ρ)
    (hw : dist p (gnomonicInverse p w).val ≤ ρ) :
    dist (gnomonicInverse p z).val (gnomonicInverse p w).val ≤
      (Real.sinc ρ)⁻¹ * dist z w := by
  have hdiam : dist (gnomonicInverse p z).val (gnomonicInverse p w).val ≤ 2 * ρ := by
    calc
      _ ≤ dist (gnomonicInverse p z).val p + dist p (gnomonicInverse p w).val := dist_triangle _ _ _
      _ ≤ ρ + ρ := add_le_add (by rwa [dist_comm]) hw
      _ = 2 * ρ := by ring
  have h := dist_le_diameter_factor_mul_chord (by positivity : 0 < 2 * ρ)
    (by linarith : 2 * ρ < Real.pi) hdiam
  have harg : 2 * ρ / 2 = ρ := by ring
  rw [harg] at h
  have hsinc : 0 < Real.sinc ρ := Real.sinc_pos (by rw [abs_of_pos hρ0]; linarith [Real.pi_pos])
  exact h.trans (mul_le_mul_of_nonneg_left (gnomonicInverse_chord_le p z w)
    (inv_nonneg.mpr hsinc.le))

/-- The same estimate, expressed on the original spherical points. -/
theorem dist_le_gnomonic_dist (p : GeodesicSphere n) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi / 2)
    (x y : openHemisphere p) (hx : dist p x.val ≤ ρ) (hy : dist p y.val ≤ ρ) :
    dist x.val y.val ≤ (Real.sinc ρ)⁻¹ * dist (gnomonic p x) (gnomonic p y) := by
  simpa only [gnomonicInverse_gnomonic] using
    gnomonicInverse_dist_le p hρ0 hρπ (gnomonic p x) (gnomonic p y)
      (by simpa only [gnomonicInverse_gnomonic] using hx)
      (by simpa only [gnomonicInverse_gnomonic] using hy)

lemma norm_pole_add_tangent_sq (p : GeodesicSphere n) (z : tangentPlane p) :
    ‖p.val + z.val‖ ^ 2 = 1 + ‖z‖ ^ 2 := by
  rw [norm_add_sq_real, p.norm_val, inner_tangentPlane]
  simp

lemma inner_pole_gnomonicInverse (p : GeodesicSphere n) (z : tangentPlane p) :
    inner ℝ p.val (gnomonicInverse p z).val.val = ‖p.val + z.val‖⁻¹ := by
  rw [gnomonicInverse_val_val, NormedSpace.normalize, inner_smul_right,
    inner_pole_add_tangent, mul_one]

/-- Decreasing tangent radius decreases spherical distance from the chart's pole. -/
lemma gnomonicInverse_dist_pole_mono (p : GeodesicSphere n)
    {z w : tangentPlane p} (hzw : ‖z‖ ≤ ‖w‖) :
    dist p (gnomonicInverse p z).val ≤ dist p (gnomonicInverse p w).val := by
  have hnorm : ‖p.val + z.val‖ ≤ ‖p.val + w.val‖ := by
    have hz := norm_pole_add_tangent_sq p z
    have hw := norm_pole_add_tangent_sq p w
    have hsq := pow_le_pow_left₀ (norm_nonneg z) hzw 2
    nlinarith [norm_nonneg (p.val + z.val), norm_nonneg (p.val + w.val)]
  rw [dist_eq_arccos_inner, dist_eq_arccos_inner,
    inner_pole_gnomonicInverse, inner_pole_gnomonicInverse]
  apply Real.arccos_le_arccos
  exact (inv_le_inv₀ (norm_pos_iff.mpr (pole_add_tangent_ne_zero p w))
    (norm_pos_iff.mpr (pole_add_tangent_ne_zero p z))).mpr hnorm

/-- A common local distortion bound for the two directions of the chart. -/
def gnomonicBiFactor (ρ : ℝ) : ℝ := max (gnomonicFactor ρ) (Real.sinc ρ)⁻¹

@[simp]
lemma gnomonicBiFactor_zero : gnomonicBiFactor 0 = 1 := by simp [gnomonicBiFactor]

lemma continuousAt_gnomonicBiFactor : ContinuousAt gnomonicBiFactor 0 :=
  continuousAt_gnomonicFactor.max
    (Real.continuous_sinc.continuousAt.inv₀ (by simp))

end GeodesicSphere
