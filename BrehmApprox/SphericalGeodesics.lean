module

public import BrehmApprox.SphericalFoldingGeometry
public import Mathlib.Tactic.Module

/-!
# Actual spherical geodesic segments

The circular formula in the tangent two-plane gives a constant-speed shortest
segment when the endpoints are not antipodal. Its exact distances and positive
spherical interpolation are proved, hence every genuine hemispherical cell
contains its metric segments. No geodesic-existence axiom is introduced.
-/

@[expose] public section

noncomputable section

namespace GeodesicSphere

variable {n : ℕ}

/-- A unit great circle through a specified pole and unit tangent direction. -/
def radialCircle (a : GeodesicSphere n) (u : tangentPlane a) (hu : ‖u‖ = 1)
    (t : ℝ) : GeodesicSphere n :=
  ⟨Real.cos t • a.val + Real.sin t • u.val, by
    have hsq := norm_add_sq_real (Real.cos t • a.val) (Real.sin t • u.val)
    have hu' : ‖u.val‖ = 1 := hu
    rw [norm_smul, norm_smul, a.norm_val, hu', mul_one, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      real_inner_smul_left, real_inner_smul_right, inner_tangentPlane] at hsq
    nlinarith [Real.cos_sq_add_sin_sq t, norm_nonneg (Real.cos t • a.val + Real.sin t • u.val)]⟩

@[simp] theorem radialCircle_val (a : GeodesicSphere n) (u : tangentPlane a)
    (hu : ‖u‖ = 1) (t : ℝ) :
    (radialCircle a u hu t).val = Real.cos t • a.val + Real.sin t • u.val := rfl

theorem inner_radialCircle (a : GeodesicSphere n) (u : tangentPlane a)
    (hu : ‖u‖ = 1) (s t : ℝ) :
    inner ℝ (radialCircle a u hu s).val (radialCircle a u hu t).val = Real.cos (s - t) := by
  have hu' : ‖u.val‖ = 1 := hu
  have hua : inner ℝ u.val a.val = 0 := by rw [real_inner_comm, inner_tangentPlane]
  simp only [radialCircle_val, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    inner_self_eq_one_of_norm_eq_one a.norm_val,
    inner_self_eq_one_of_norm_eq_one hu', inner_tangentPlane, hua,
    mul_zero, add_zero, zero_add, mul_one, Real.cos_sub]
  ring

/-- Great-circle distance equals parameter difference on arcs of length at
most `pi`. -/
theorem radialCircle_dist (a : GeodesicSphere n) (u : tangentPlane a)
    (hu : ‖u‖ = 1) (s t : ℝ) (hst : |s - t| ≤ Real.pi) :
    dist (radialCircle a u hu s) (radialCircle a u hu t) = |s - t| := by
  rw [dist_eq_arccos_inner, inner_radialCircle, ← Real.cos_abs (s - t)]
  exact Real.arccos_cos (abs_nonneg _) hst

/-- The short spherical segment. The formula is total in its real parameter;
its shortest-path identities are restricted to `[0,1]`. -/
def geodesic (a b : GeodesicSphere n) (hπ : dist a b < Real.pi) (t : ℝ) :
    GeodesicSphere n :=
  if h0 : 0 < dist a b then
    radialCircle a (radialDirection a b h0 hπ) (radialDirection_norm a b h0 hπ)
      (t * dist a b)
  else a

@[simp] theorem geodesic_self (a : GeodesicSphere n) (hπ : dist a a < Real.pi) (t : ℝ) :
    geodesic a a hπ t = a := by simp [geodesic]

@[simp] theorem geodesic_zero (a b : GeodesicSphere n) (hπ : dist a b < Real.pi) :
    geodesic a b hπ 0 = a := by
  by_cases h0 : 0 < dist a b
  · simp only [geodesic, dite_eq_left h0, zero_mul]
    apply GeodesicSphere.ext
    simp only [radialCircle_val, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
  · simp only [geodesic, dite_eq_right h0]

@[simp] theorem geodesic_one (a b : GeodesicSphere n) (hπ : dist a b < Real.pi) :
    geodesic a b hπ 1 = b := by
  by_cases h0 : 0 < dist a b
  · apply GeodesicSphere.ext
    simp only [geodesic, dite_eq_left h0, one_mul, radialCircle_val]
    exact (radial_decomposition a b h0 hπ).symm
  · have hab : a = b := dist_eq_zero.mp (le_antisymm (le_of_not_gt h0) dist_nonneg)
    subst b
    simp

/-- Exact metric speed on the complete short segment. -/
theorem geodesic_dist (a b : GeodesicSphere n) (hπ : dist a b < Real.pi)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (geodesic a b hπ s) (geodesic a b hπ t) = |s - t| * dist a b := by
  by_cases h0 : 0 < dist a b
  · simp only [geodesic, dite_eq_left h0]
    rw [radialCircle_dist]
    · rw [← sub_mul, abs_mul, abs_of_nonneg dist_nonneg]
    · rw [← sub_mul, abs_mul, abs_of_nonneg dist_nonneg]
      have habs : |s - t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
      exact (mul_le_of_le_one_left dist_nonneg habs).trans hπ.le
  · have hab : a = b := dist_eq_zero.mp (le_antisymm (le_of_not_gt h0) dist_nonneg)
    subst b
    simp

theorem geodesic_lipschitzOn (a b : GeodesicSphere n) (hπ : dist a b < Real.pi) :
    LipschitzOnWith ⟨dist a b, dist_nonneg⟩ (geodesic a b hπ) (Set.Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  change dist (geodesic a b hπ s) (geodesic a b hπ t) ≤ dist a b * dist s t
  rw [geodesic_dist a b hπ hs ht, Real.dist_eq]
  exact le_of_eq (mul_comm _ _)

/-- The positive spherical interpolation formula, obtained from the actual
unit-speed circle rather than postulated as a segment. -/
theorem val_geodesic (a b : GeodesicSphere n) (hab : a ≠ b)
    (hπ : dist a b < Real.pi) (t : ℝ) :
    (geodesic a b hπ t).val =
      (Real.sin ((1 - t) * dist a b) / Real.sin (dist a b)) • a.val +
      (Real.sin (t * dist a b) / Real.sin (dist a b)) • b.val := by
  have h0 : 0 < dist a b := dist_pos.mpr hab
  have hs : Real.sin (dist a b) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h0 hπ).ne'
  have ht : (1 - t) * dist a b = dist a b - t * dist a b := by ring
  have hc : Real.sin ((1 - t) * dist a b) / Real.sin (dist a b) =
      Real.cos (t * dist a b) - (Real.sin (t * dist a b) / Real.sin (dist a b)) *
        Real.cos (dist a b) := by
    rw [ht, Real.sin_sub]
    field_simp
  simp only [geodesic, dite_eq_left h0, radialCircle_val, radialDirection_val,
    radialVector, ← cos_dist, hc]
  simp only [smul_sub, smul_smul]
  simp only [div_eq_mul_inv]
  module

end GeodesicSphere

namespace BrehmApprox

open GeodesicSphere
open scoped BigOperators

variable {n : ℕ}

/-- Every genuine spherical cell contains the short metric segment between
any two of its nonantipodal points. -/
theorem geodesic_mem_sphericalCell {V : Finset (GeodesicSphere n)}
    {a b : GeodesicSphere n} (ha : a ∈ sphericalCell V) (hb : b ∈ sphericalCell V)
    (hπ : dist a b < Real.pi) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    geodesic a b hπ t ∈ sphericalCell V := by
  classical
  by_cases hab : a = b
  · subst b
    simpa only [geodesic_self] using ha
  · obtain ⟨w, hw, A, hA, hrepA⟩ := ha
    obtain ⟨z, hz, B, hB, hrepB⟩ := hb
    let c : ℝ := Real.sin ((1 - t) * dist a b) / Real.sin (dist a b)
    let d : ℝ := Real.sin (t * dist a b) / Real.sin (dist a b)
    have hs : 0 ≤ Real.sin (dist a b) :=
      (Real.sin_pos_of_pos_of_lt_pi (dist_pos.mpr hab) hπ).le
    have hct : 0 ≤ (1 - t) * dist a b := mul_nonneg (sub_nonneg.mpr ht1) dist_nonneg
    have hdt : 0 ≤ t * dist a b := mul_nonneg ht0 dist_nonneg
    have hcπ : (1 - t) * dist a b ≤ Real.pi := by
      have hh : (1 - t) * dist a b ≤ dist a b := by nlinarith [dist_nonneg (x := a) (y := b)]
      exact hh.trans hπ.le
    have hdπ : t * dist a b ≤ Real.pi := by
      have hh : t * dist a b ≤ dist a b := mul_le_of_le_one_left dist_nonneg ht1
      exact hh.trans hπ.le
    have hc : 0 ≤ c := div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hct hcπ) hs
    have hd : 0 ≤ d := div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hdt hdπ) hs
    refine ⟨fun v => c * (A⁻¹ * w v) + d * (B⁻¹ * z v), ?_, 1, zero_lt_one, ?_⟩
    · intro v hv
      exact add_nonneg (mul_nonneg hc (mul_nonneg (inv_nonneg.mpr hA.le) (hw v hv)))
        (mul_nonneg hd (mul_nonneg (inv_nonneg.mpr hB.le) (hz v hv)))
    · rw [one_smul, val_geodesic a b hab hπ]
      simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
        hrepA, hrepB]
      simp only [smul_smul, inv_mul_cancel₀ hA.ne', inv_mul_cancel₀ hB.ne', mul_one]
      rfl

end BrehmApprox
