module

public import BrehmApprox.Core
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Group.MinMax

/-!
# Euclidean radial flattening with a variable outer radius

For `0 ≤ α < 1` and `R ≥ 0`, the radial profile is zero up to `α R`,
linear with slope `1 / (1 - α)` between `α R` and `R`, and the identity
after `R`. The map acts in a real inner product space with its genuine
Euclidean norm. All estimates are proved without a geometric axiom.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

def radialProfile (α R t : ℝ) : ℝ :=
  min t (max 0 ((t - α * R) / (1 - α)))

lemma radialProfile_nonneg {α R t : ℝ} (ht : 0 ≤ t) :
    0 ≤ radialProfile α R t :=
  le_min ht (le_max_left _ _)

lemma radialProfile_le (α R t : ℝ) : radialProfile α R t ≤ t := min_le_left _ _

lemma radialProfile_inner {α R t : ℝ} (hα1 : α < 1) (ht : 0 ≤ t)
    (hin : t ≤ α * R) : radialProfile α R t = 0 := by
  have hq : (t - α * R) / (1 - α) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp only [radialProfile, max_eq_left hq, min_eq_right ht]

lemma radialProfile_outer {α R t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hout : R ≤ t) : radialProfile α R t = t := by
  have hβ : 0 < 1 - α := by linarith
  have hq : t ≤ (t - α * R) / (1 - α) := by
    apply (le_div_iff₀ hβ).2
    nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hout)]
  exact min_eq_left (hq.trans (le_max_right _ _))

lemma radialProfile_middle {α R t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hin : α * R ≤ t) (hout : t ≤ R) :
    radialProfile α R t = (t - α * R) / (1 - α) := by
  have hβ : 0 < 1 - α := by linarith
  have hq0 : 0 ≤ (t - α * R) / (1 - α) := div_nonneg (by linarith) hβ.le
  have hqt : (t - α * R) / (1 - α) ≤ t := by
    apply (div_le_iff₀ hβ).2
    nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hout)]
  simp only [radialProfile, max_eq_right hq0, min_eq_right hqt]

lemma radialProfile_zero {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hR : 0 ≤ R) :
    radialProfile α R 0 = 0 :=
  radialProfile_inner hα1 le_rfl (mul_nonneg hα0 hR)

lemma radialProfile_displacement {α R t : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hR : 0 ≤ R) (ht : 0 ≤ t) : t - radialProfile α R t ≤ α * R := by
  by_cases hin : t ≤ α * R
  · rw [radialProfile_inner hα1 ht hin]
    linarith
  · have hβ : 0 < 1 - α := by linarith
    have hn : 0 ≤ t - α * R := by linarith
    have hq : t - α * R ≤ (t - α * R) / (1 - α) := by
      apply (le_div_iff₀ hβ).2
      nlinarith [mul_nonneg hα0 hn]
    have hmin : t - α * R ≤ radialProfile α R t :=
      le_min (by nlinarith [mul_nonneg hα0 hR]) (hq.trans (le_max_right _ _))
    linarith

/-- The radial profile has the sharp Lipschitz bound `1 / (1 - α)`. -/
lemma radialProfile_lipschitz {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (R s t : ℝ) :
    |radialProfile α R s - radialProfile α R t| ≤ (1 / (1 - α)) * |s - t| := by
  have hβ : 0 < 1 - α := by linarith
  have hL : 1 ≤ 1 / (1 - α) := by
    apply (le_div_iff₀ hβ).2
    linarith
  have hlin : |(s - α * R) / (1 - α) - (t - α * R) / (1 - α)| =
      (1 / (1 - α)) * |s - t| := by
    have heq : (s - α * R) / (1 - α) - (t - α * R) / (1 - α) =
        (s - t) / (1 - α) := by ring
    rw [heq, abs_div, abs_of_pos hβ]
    ring
  have hmax : |max 0 ((s - α * R) / (1 - α)) -
      max 0 ((t - α * R) / (1 - α))| ≤ (1 / (1 - α)) * |s - t| := by
    calc
      _ ≤ |(s - α * R) / (1 - α) - (t - α * R) / (1 - α)| := by
        simpa only [max_comm] using abs_max_sub_max_le_abs
          ((s - α * R) / (1 - α)) ((t - α * R) / (1 - α)) 0
      _ = _ := hlin
  exact (abs_min_sub_min_le_max _ _ _ _).trans
    (max_le (by nlinarith [abs_nonneg (s - t)]) hmax)

/-- Dependence on the outer radius. This is the estimate needed when a
continuous cut-off radius varies along a face. -/
lemma radialProfile_parameter {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (R S t : ℝ) :
    |radialProfile α R t - radialProfile α S t| ≤ (α / (1 - α)) * |R - S| := by
  have hβ : 0 < 1 - α := by linarith
  have hlin : |(t - α * R) / (1 - α) - (t - α * S) / (1 - α)| =
      (α / (1 - α)) * |R - S| := by
    have heq : (t - α * R) / (1 - α) - (t - α * S) / (1 - α) =
        -(α / (1 - α)) * (R - S) := by ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg hα0 hβ.le)]
  have hmin : |radialProfile α R t - radialProfile α S t| ≤
      |max 0 ((t - α * R) / (1 - α)) - max 0 ((t - α * S) / (1 - α))| := by
    have habs : (0 : ℝ) ≤
        |max 0 ((t - α * R) / (1 - α)) - max 0 ((t - α * S) / (1 - α))| :=
      abs_nonneg _
    simpa only [radialProfile, sub_self, abs_zero, max_eq_right habs] using
      abs_min_sub_min_le_max t (max 0 ((t - α * R) / (1 - α)))
        t (max 0 ((t - α * S) / (1 - α)))
  calc
    _ ≤ _ := hmin
    _ ≤ |(t - α * R) / (1 - α) - (t - α * S) / (1 - α)| := by
      simpa only [max_comm] using abs_max_sub_max_le_abs
        ((t - α * R) / (1 - α)) ((t - α * S) / (1 - α)) 0
    _ = _ := hlin

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Radial flattening in the actual inner product norm. Division by zero is
harmless: the zero vector is sent to the zero vector. -/
def radialFlatten (α R : ℝ) (v : E) : E :=
  (radialProfile α R ‖v‖ / ‖v‖) • v

omit [InnerProductSpace ℝ E] in
lemma radial_coefficient_nonneg (α R : ℝ) (v : E) :
    0 ≤ radialProfile α R ‖v‖ / ‖v‖ :=
  div_nonneg (radialProfile_nonneg (norm_nonneg _)) (norm_nonneg _)

omit [InnerProductSpace ℝ E] in
lemma radial_coefficient_le_one (α R : ℝ) (v : E) :
    radialProfile α R ‖v‖ / ‖v‖ ≤ 1 := by
  by_cases hv : ‖v‖ = 0
  · simp only [hv, div_zero, zero_le_one]
  · exact (div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv))).2
      (radialProfile_le α R ‖v‖)

omit [InnerProductSpace ℝ E] in
lemma radial_coefficient_mul_norm {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hR : 0 ≤ R) (v : E) :
    (radialProfile α R ‖v‖ / ‖v‖) * ‖v‖ = radialProfile α R ‖v‖ := by
  by_cases hv : ‖v‖ = 0
  · simp only [hv, radialProfile_zero hα0 hα1 hR, div_zero, mul_zero]
  · exact div_mul_cancel₀ _ hv

lemma radialFlatten_norm {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hR : 0 ≤ R) (v : E) : ‖radialFlatten α R v‖ = radialProfile α R ‖v‖ := by
  rw [radialFlatten, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (radial_coefficient_nonneg α R v)]
  exact radial_coefficient_mul_norm hα0 hα1 hR v

lemma radialFlatten_inner {α R : ℝ} (hα1 : α < 1) {v : E}
    (hin : ‖v‖ ≤ α * R) : radialFlatten α R v = 0 := by
  simp only [radialFlatten, radialProfile_inner hα1 (norm_nonneg _) hin,
    zero_div, zero_smul]

lemma radialFlatten_outer {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {v : E}
    (hout : R ≤ ‖v‖) : radialFlatten α R v = v := by
  rw [radialFlatten, radialProfile_outer hα0 hα1 hout]
  by_cases hv : v = 0
  · simp [hv]
  · rw [div_self (norm_ne_zero_iff.mpr hv), one_smul]

lemma radialFlatten_displacement_eq {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hR : 0 ≤ R) (v : E) :
    dist (radialFlatten α R v) v = ‖v‖ - radialProfile α R ‖v‖ := by
  let c : ℝ := radialProfile α R ‖v‖ / ‖v‖
  have hc : c ≤ 1 := radial_coefficient_le_one α R v
  have hmul : c * ‖v‖ = radialProfile α R ‖v‖ :=
    radial_coefficient_mul_norm hα0 hα1 hR v
  calc
    dist (radialFlatten α R v) v = ‖c • v - (1 : ℝ) • v‖ := by
      simp only [radialFlatten, c, one_smul, dist_eq_norm]
    _ = |c - 1| * ‖v‖ := by rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    _ = (1 - c) * ‖v‖ := by rw [abs_of_nonpos (by linarith)]; ring
    _ = ‖v‖ - radialProfile α R ‖v‖ := by nlinarith

theorem radialFlatten_displacement {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hR : 0 ≤ R) (v : E) : dist (radialFlatten α R v) v ≤ α * R := by
  rw [radialFlatten_displacement_eq hα0 hα1 hR]
  exact radialProfile_displacement hα0 hα1 hR (norm_nonneg _)

/-- The Hilbert-space step: controlling radial distances and keeping radial
coefficients in `[0,1]` controls the entire Euclidean distance. -/
lemma radial_coefficients_lipschitz (v w : E) {a b L : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL : 1 ≤ L)
    (hrad : |a * ‖v‖ - b * ‖w‖| ≤ L * |‖v‖ - ‖w‖|) :
    dist (a • v) (b • w) ≤ L * dist v w := by
  have hgap : 0 ≤ ‖v‖ * ‖w‖ - inner ℝ v w := by
    linarith [real_inner_le_norm v w]
  have hab : a * b ≤ 1 := by
    simpa using mul_le_mul ha1 hb1 hb0 (show (0 : ℝ) ≤ 1 by norm_num)
  have habL : a * b ≤ L ^ 2 := by nlinarith
  have hangular : 2 * a * b * (‖v‖ * ‖w‖ - inner ℝ v w) ≤
      2 * L ^ 2 * (‖v‖ * ‖w‖ - inner ℝ v w) := by
    nlinarith [mul_le_mul_of_nonneg_right habL hgap]
  have hrad2 := pow_le_pow_left₀ (abs_nonneg _) hrad 2
  simp only [sq_abs, mul_pow] at hrad2
  have hfirst : ‖a • v - b • w‖ ^ 2 = (a * ‖v‖ - b * ‖w‖) ^ 2 +
      2 * a * b * (‖v‖ * ‖w‖ - inner ℝ v w) := by
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      real_inner_smul_left, inner_smul_right, mul_pow, sq_abs]
    ring
  have hbase : ‖v - w‖ ^ 2 = (‖v‖ - ‖w‖) ^ 2 +
      2 * (‖v‖ * ‖w‖ - inner ℝ v w) := by
    rw [norm_sub_sq_real]
    ring
  have htarget : (L * ‖v - w‖) ^ 2 = L ^ 2 * (‖v‖ - ‖w‖) ^ 2 +
      2 * L ^ 2 * (‖v‖ * ‖w‖ - inner ℝ v w) := by
    rw [mul_pow, hbase]
    ring
  have hsq : ‖a • v - b • w‖ ^ 2 ≤ (L * ‖v - w‖) ^ 2 := by
    rw [hfirst, htarget]
    exact add_le_add hrad2 hangular
  simp only [dist_eq_norm]
  have hright : 0 ≤ L * ‖v - w‖ := mul_nonneg (by linarith) (norm_nonneg _)
  nlinarith [norm_nonneg (a • v - b • w)]

/-- Sharp Lipschitz estimate for the radial collapse in a real inner product
space. -/
theorem radialFlatten_lipschitz {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hR : 0 ≤ R) (v w : E) :
    dist (radialFlatten α R v) (radialFlatten α R w) ≤
      (1 / (1 - α)) * dist v w := by
  have hβ : 0 < 1 - α := by linarith
  have hL : 1 ≤ 1 / (1 - α) := by
    apply (le_div_iff₀ hβ).2
    linarith
  apply radial_coefficients_lipschitz v w
    (radial_coefficient_nonneg α R v) (radial_coefficient_le_one α R v)
    (radial_coefficient_nonneg α R w) (radial_coefficient_le_one α R w) hL
  rw [radial_coefficient_mul_norm hα0 hα1 hR v,
    radial_coefficient_mul_norm hα0 hα1 hR w]
  exact radialProfile_lipschitz hα0 hα1 R ‖v‖ ‖w‖

/-- Uniform dependence on the cut-off radius, needed to taper a normal
collapse continuously near the boundary of a face. -/
theorem radialFlatten_parameter {α R S : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (v : E) :
    dist (radialFlatten α R v) (radialFlatten α S v) ≤
      (α / (1 - α)) * |R - S| := by
  by_cases hv : ‖v‖ = 0
  · have hv0 : v = 0 := norm_eq_zero.mp hv
    simp only [hv0, radialFlatten, smul_zero, dist_self]
    exact mul_nonneg (div_nonneg hα0 (by linarith)) (abs_nonneg _)
  · have heq : dist (radialFlatten α R v) (radialFlatten α S v) =
        |radialProfile α R ‖v‖ - radialProfile α S ‖v‖| := by
      rw [radialFlatten, radialFlatten, dist_eq_norm, ← sub_smul, norm_smul,
        Real.norm_eq_abs, ← sub_div, abs_div, abs_of_nonneg (norm_nonneg _)]
      exact div_mul_cancel₀ _ hv
    rw [heq]
    exact radialProfile_parameter hα0 hα1 R S ‖v‖

end InnerProduct
end BrehmApprox
