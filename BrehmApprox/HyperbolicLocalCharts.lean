module

public import BrehmApprox.HyperbolicProjectionShort

/-!
# Quantitative genuine Klein charts

Klein coordinates are globally nonexpanding from the hyperbolic metric to
the Euclidean metric.  On the Euclidean ball of radius `ρ < 1`, the inverse
chart has Lipschitz constant `1 / (1 - ρ^2)`.  Thus the distortion tends to
one on shrinking charts.  Every assertion concerns the concrete hyperboloid
metric, not a generic curvature interface.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox

lemma sinh_le_mul_cosh_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    Real.sinh r ≤ r * Real.cosh r := by
  have hderiv : ∀ s ∈ Set.Icc 0 r,
      HasDerivWithinAt Real.sinh (Real.cosh s) (Set.Icc 0 r) s :=
    fun s _ => (Real.hasDerivAt_sinh s).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico 0 r, ‖Real.cosh s‖ ≤ Real.cosh r := by
    intro s hs
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos s)]
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg hs.1, abs_of_nonneg hr] using hs.2.le
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound r ⟨hr, le_rfl⟩
  have hs := Real.sinh_nonneg_iff.mpr hr
  simpa only [Real.sinh_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hs, mul_comm] using h

lemma quadratic_le_two_cosh_sub_one {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 ≤ 2 * (Real.cosh r - 1) := by
  have hh := Real.cosh_two_mul (r / 2)
  rw [show 2 * (r / 2) = r by ring, Real.cosh_sq] at hh
  have hs := Real.self_le_sinh_iff.mpr (show 0 ≤ r / 2 by positivity)
  have hs0 := Real.sinh_nonneg_iff.mpr (show 0 ≤ r / 2 by positivity)
  nlinarith

namespace HyperbolicSpace

variable {n : ℕ}

lemma klein_denominator_sq {p : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ < 1) :
    (Real.sqrt (1 - ‖p‖ ^ 2)) ^ 2 = 1 - ‖p‖ ^ 2 := by
  rw [Real.sq_sqrt]
  nlinarith [norm_nonneg p]

lemma klein_cosh_identity {p q : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    2 * Real.sqrt (1 - ‖p‖ ^ 2) * Real.sqrt (1 - ‖q‖ ^ 2) *
        (Real.cosh (dist (fromKlein p) (fromKlein q)) - 1) =
      ‖p - q‖ ^ 2 + (Real.sqrt (1 - ‖p‖ ^ 2) - Real.sqrt (1 - ‖q‖ ^ 2)) ^ 2 := by
  have hc : Real.cosh (dist (fromKlein p) (fromKlein q)) *
      (Real.sqrt (1 - ‖p‖ ^ 2) * Real.sqrt (1 - ‖q‖ ^ 2)) = 1 - ⟪p, q⟫_ℝ := by
    rw [cosh_dist, coshDist_fromKlein hp hq]
    exact div_mul_cancel₀ _ (mul_ne_zero (klein_denominator_pos hp).ne'
      (klein_denominator_pos hq).ne')
  rw [norm_sub_sq_real]
  nlinarith [klein_denominator_sq hp, klein_denominator_sq hq]

theorem norm_sub_le_dist_fromKlein {p q : EuclideanSpace ℝ (Fin n)}
    (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    ‖p - q‖ ≤ dist (fromKlein p) (fromKlein q) := by
  let a := Real.sqrt (1 - ‖p‖ ^ 2)
  let b := Real.sqrt (1 - ‖q‖ ^ 2)
  let r := dist (fromKlein p) (fromKlein q)
  let c := Real.cosh r
  let D := ‖p - q‖
  have ha : 0 < a := klein_denominator_pos hp
  have hb : 0 < b := klein_denominator_pos hq
  have hr : 0 ≤ r := dist_nonneg
  have hc1 : 1 ≤ c := Real.one_le_cosh r
  have hc : c * (a * b) = 1 - ⟪p, q⟫_ℝ := by
    dsimp [c, r, a, b]
    rw [cosh_dist, coshDist_fromKlein hp hq]
    exact div_mul_cancel₀ _ (mul_ne_zero ha.ne' hb.ne')
  have hi : 2 * a * b * (c - 1) = D ^ 2 + (a - b) ^ 2 := klein_cosh_identity hp hq
  have hab : a * b * (c + 1) ≤ 2 := by
    have hn : 0 ≤ ‖p + q‖ ^ 2 := sq_nonneg _
    rw [norm_add_sq_real] at hn
    have ha2 : a ^ 2 = 1 - ‖p‖ ^ 2 := klein_denominator_sq hp
    have hb2 : b ^ 2 = 1 - ‖q‖ ^ 2 := klein_denominator_sq hq
    nlinarith [sq_nonneg (a - b)]
  have hD : D ^ 2 ≤ 2 * a * b * (c - 1) := by nlinarith [sq_nonneg (a - b)]
  have hsq : D ^ 2 * (c + 1) ≤ 4 * (c - 1) := by
    have h1 := mul_le_mul_of_nonneg_right hD (show 0 ≤ c + 1 by linarith)
    have h2 := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2 * (c - 1) by linarith)
    nlinarith
  let H := Real.cosh (r / 2)
  let S := Real.sinh (r / 2)
  have hH : 0 < H := Real.cosh_pos _
  have hS : 0 ≤ S := Real.sinh_nonneg_iff.mpr (by positivity)
  have hhalf : c = 2 * H ^ 2 - 1 := by
    have hh := Real.cosh_two_mul (r / 2)
    rw [show 2 * (r / 2) = r by ring] at hh
    have ht := Real.cosh_sq (r / 2)
    dsimp only [c, H]
    nlinarith
  have htrig : H ^ 2 = S ^ 2 + 1 := Real.cosh_sq _
  have hDS : D * H ≤ 2 * S := by
    have hD0 : 0 ≤ D := norm_nonneg _
    have hsq' : (D * H) ^ 2 ≤ (2 * S) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hD0 hH.le]
  have hsinh : S ≤ (r / 2) * H := sinh_le_mul_cosh_of_nonneg (by positivity)
  change D ≤ r
  exact le_of_mul_le_mul_right (by nlinarith : D * H ≤ r * H) hH

theorem klein_dist_le (x y : HyperbolicSpace n) :
    dist (klein x) (klein y) ≤ dist x y := by
  have h := norm_sub_le_dist_fromKlein (norm_klein_lt_one x) (norm_klein_lt_one y)
  simpa only [fromKlein_klein, dist_eq_norm] using h

theorem klein_lipschitz : LipschitzWith 1 (klein : HyperbolicSpace n → EuclideanSpace ℝ (Fin n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul] using klein_dist_le x y

theorem dist_fromKlein_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {p q : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ ≤ ρ) (hq : ‖q‖ ≤ ρ) :
    dist (fromKlein p) (fromKlein q) ≤ (1 - ρ ^ 2)⁻¹ * ‖p - q‖ := by
  have hp1 : ‖p‖ < 1 := hp.trans_lt hρ1
  have hq1 : ‖q‖ < 1 := hq.trans_lt hρ1
  let s := Real.sqrt (1 - ρ ^ 2)
  let a := Real.sqrt (1 - ‖p‖ ^ 2)
  let b := Real.sqrt (1 - ‖q‖ ^ 2)
  let D := ‖p - q‖
  let r := dist (fromKlein p) (fromKlein q)
  let c := Real.cosh r
  have hs2 : s ^ 2 = 1 - ρ ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    nlinarith
  have hs : 0 < s := by
    dsimp [s]
    apply Real.sqrt_pos.mpr
    nlinarith
  have ha : 0 < a := klein_denominator_pos hp1
  have hb : 0 < b := klein_denominator_pos hq1
  have ha2 : a ^ 2 = 1 - ‖p‖ ^ 2 := klein_denominator_sq hp1
  have hb2 : b ^ 2 = 1 - ‖q‖ ^ 2 := klein_denominator_sq hq1
  have hsa : s ≤ a := by nlinarith [norm_nonneg p]
  have hsb : s ≤ b := by nlinarith [norm_nonneg q]
  have habs : |a - b| * (a + b) ≤ 2 * ρ * D := by
    have hid : (a - b) * (a + b) = (‖q‖ - ‖p‖) * (‖q‖ + ‖p‖) := by
      nlinarith
    have habseq := congrArg abs hid
    rw [abs_mul, abs_of_pos (add_pos ha hb), abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg q) (norm_nonneg p))] at habseq
    have hn : |‖q‖ - ‖p‖| ≤ D := by
      simpa only [D, norm_sub_rev] using abs_norm_sub_norm_le q p
    have hmul := mul_le_mul_of_nonneg_right hn (add_nonneg (norm_nonneg q) (norm_nonneg p))
    have hD0 : 0 ≤ D := norm_nonneg _
    nlinarith
  have hdiff : s * |a - b| ≤ ρ * D := by
    have hab0 := abs_nonneg (a - b)
    have hmul := mul_le_mul_of_nonneg_left (show 2 * s ≤ a + b by linarith) hab0
    nlinarith
  have hdiffsq : s ^ 2 * (a - b) ^ 2 ≤ ρ ^ 2 * D ^ 2 := by
    have h0 : 0 ≤ s * |a - b| := mul_nonneg hs.le (abs_nonneg _)
    have h1 : 0 ≤ ρ * D := mul_nonneg hρ0 (norm_nonneg _)
    have hsq : (s * |a - b|) ^ 2 ≤ (ρ * D) ^ 2 := by nlinarith
    simpa only [mul_pow, sq_abs] using hsq
  have hi : 2 * a * b * (c - 1) = D ^ 2 + (a - b) ^ 2 := klein_cosh_identity hp1 hq1
  have hab : s ^ 2 ≤ a * b := by nlinarith [mul_nonneg (sub_nonneg.mpr hsa) (sub_nonneg.mpr hsb)]
  have hc : 0 ≤ c - 1 := sub_nonneg.mpr (Real.one_le_cosh r)
  have hmul := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2 * s ^ 2 * (c - 1) by positivity)
  have hsqbound : 2 * (s ^ 2) ^ 2 * (c - 1) ≤ D ^ 2 := by
    have hscaled : 2 * s ^ 2 * a * b * (c - 1) = s ^ 2 * (D ^ 2 + (a - b) ^ 2) := by
      nlinarith [congrArg (fun z : ℝ => s ^ 2 * z) hi]
    have hDs : (s ^ 2 + ρ ^ 2) * D ^ 2 = D ^ 2 := by rw [hs2]; ring
    nlinarith
  have hr : 0 ≤ r := dist_nonneg
  have hquad : r ^ 2 ≤ 2 * (c - 1) := quadratic_le_two_cosh_sub_one hr
  have hquadscaled := mul_le_mul_of_nonneg_left hquad (sq_nonneg (s ^ 2))
  have hfinal : r * s ^ 2 ≤ D := by
    have hr0 : 0 ≤ r * s ^ 2 := mul_nonneg hr (sq_nonneg s)
    have hD0 : 0 ≤ D := norm_nonneg _
    nlinarith
  rw [← hs2]
  change r ≤ (s ^ 2)⁻¹ * D
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ (sq_pos_of_pos hs)).mpr hfinal

end HyperbolicSpace
end BrehmApprox
