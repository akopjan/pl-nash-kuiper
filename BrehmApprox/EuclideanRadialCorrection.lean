module

public import BrehmApprox.FiniteContinuousSelection
public import BrehmApprox.EuclideanRigidity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Piecewise
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The metric part of the bounded Brehm correction

A bounded short map is corrected at the origin by radially extending its
norm-preserving locus. The construction is independent of polyhedral geometry.
It produces a global short homogeneous replacement, and pasting across the
displacement region preserves shortness.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Comparing two positive radial multiples detects angular contraction. -/
theorem radial_dist_le_of_scaled_dist_le
    {x y v w : E} {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hv : ‖v‖ = ‖x‖) (hw : ‖w‖ = ‖y‖)
    (hd : dist (t • v) (s • w) ≤ dist (t • x) (s • y)) :
    dist v w ≤ dist x y := by
  have hd2 := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist (t • v) (s • w)) hd 2
  simp only [dist_eq_norm, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht, abs_of_pos hs, real_inner_smul_left, inner_smul_right,
    hv, hw] at hd2
  have hp : 0 < t * s := mul_pos ht hs
  have hi : inner ℝ x y ≤ inner ℝ v w := by
    have hmul : 0 ≤ (t * s) * (inner ℝ v w - inner ℝ x y) := by
      nlinarith only [hd2]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hmul)
  have hsq : ‖v - w‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    simp only [norm_sub_sq_real, hv, hw]
    linarith
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [norm_nonneg (v - w), norm_nonneg (x - y)]

/-- A bounded short map not fixing the origin has a norm-preserving point on
every nonzero ray. The scale is strictly positive. -/
theorem exists_positive_radial_norm_match
    {ψ : E → E} (hψ : Short ψ) {R : ℝ} (hR : ∀ x, ‖ψ x‖ ≤ R)
    (hzero : ψ 0 ≠ 0) {x : E} (hx : x ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ‖ψ (t • x)‖ = ‖t • x‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg (ψ 0)).trans (hR 0)
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let T : ℝ := (R + 1) / ‖x‖
  have hT : 0 < T := div_pos (by linarith) hxnorm
  let q : ℝ → ℝ := fun t => ‖ψ (t • x)‖ - ‖t • x‖
  have hcont : Continuous q :=
    ((hψ.continuous.comp (continuous_id.smul continuous_const)).norm).sub
      (continuous_id.smul continuous_const).norm
  have hq0 : 0 < q 0 := by
    simpa [q] using norm_pos_iff.mpr hzero
  have hnormT : ‖T • x‖ = R + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]
    exact div_mul_cancel₀ (R + 1) hxnorm.ne'
  have hqT : q T ≤ 0 := by
    dsimp [q]
    rw [hnormT]
    linarith [hR (T • x)]
  obtain ⟨t, ht, heq⟩ :=
    intermediate_value_Icc' hT.le hcont.continuousOn (show 0 ∈ Icc (q T) (q 0) from ⟨hqT, hq0.le⟩)
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro he
    subst t
    linarith
  exact ⟨t, htpos, sub_eq_zero.mp heq⟩

/-- The radial extension of the norm-preserving locus of a bounded short map.
The final field records an actual boundary witness on every nonzero ray. -/
theorem exists_short_radial_replacement
    {ψ : E → E} (hψ : Short ψ) {R : ℝ} (hR : ∀ x, ‖ψ x‖ ≤ R)
    (hzero : ψ 0 ≠ 0) :
    ∃ H : E → E, Short H ∧ (∀ x, ‖H x‖ = ‖x‖) ∧
      (∀ x, ‖ψ x‖ = ‖x‖ → H x = ψ x) ∧
      ∀ x, x ≠ 0 → ∃ t : ℝ, 0 < t ∧
        ψ (t • x) = t • H x ∧ ‖t • x‖ ≤ R := by
  classical
  have hex : ∀ x : E, ∃ t : ℝ, 0 < t ∧
      (x ≠ 0 → ‖ψ (t • x)‖ = ‖t • x‖) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨1, zero_lt_one, fun hn => (hn hx).elim⟩
    · obtain ⟨t, ht, heq⟩ := exists_positive_radial_norm_match hψ hR hzero hx
      exact ⟨t, ht, fun _ => heq⟩
  choose t ht heq using hex
  let H : E → E := fun x => if x = 0 then 0 else (t x)⁻¹ • ψ (t x • x)
  have hH0 : H 0 = 0 := by simp [H]
  have hscale (x : E) (hx : x ≠ 0) : ψ (t x • x) = t x • H x := by
    simp only [H, ite_eq_right hx, smul_smul, mul_inv_cancel₀ (ht x).ne', one_smul]
  have hnorm (x : E) : ‖H x‖ = ‖x‖ := by
    by_cases hx : x = 0
    · subst x
      simp only [hH0]
    · simp only [H, ite_eq_right hx]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ht x)),
        heq x hx, norm_smul, Real.norm_eq_abs, abs_of_pos (ht x)]
      rw [← mul_assoc, inv_mul_cancel₀ (ht x).ne', one_mul]
  have hshort : Short H := by
    intro x y
    by_cases hx : x = 0
    · subst x
      simp only [hH0, dist_zero_left, hnorm, le_refl]
    by_cases hy : y = 0
    · subst y
      simp only [hH0, dist_zero_right, hnorm, le_refl]
    apply radial_dist_le_of_scaled_dist_le (ht x) (ht y) (hnorm x) (hnorm y)
    rw [← hscale x hx, ← hscale y hy]
    exact hψ _ _
  refine ⟨H, hshort, hnorm, ?_, ?_⟩
  · intro x hxmatch
    have hx : x ≠ 0 := by
      intro he
      subst x
      exact hzero (norm_eq_zero.mp (by simpa using hxmatch))
    apply dist_le_zero.mp
    have h := radial_dist_le_of_scaled_dist_le (ht x) zero_lt_one
      (hnorm x) hxmatch (by simpa only [one_smul, ← hscale x hx] using hψ (t x • x) x)
    simpa only [dist_self] using h
  · intro x hx
    exact ⟨t x, ht x, hscale x hx, (heq x hx).symm.trans_le (hR _)⟩

/-- Pasting the radial replacement into the displacement region is short. -/
theorem short_origin_correction
    {ψ H : E → E} (hψ : Short ψ) (hH : Short H)
    (hmatch : ∀ x, ‖ψ x‖ = ‖x‖ → H x = ψ x) :
    Short (fun x => if ‖x‖ < ‖ψ x‖ then H x else ψ x) := by
  classical
  let U : Set E := {x | ‖x‖ < ‖ψ x‖}
  have hcont : Continuous (U.piecewise H ψ) := by
    apply Continuous.piecewise ?_ hH.continuous hψ.continuous
    intro x hx
    exact hmatch x ((frontier_lt_subset_eq continuous_norm hψ.continuous.norm hx).symm)
  have hsel : ∀ x, ∃ i : Bool,
      U.piecewise H ψ x = (fun i : Bool => if i then H else ψ) i x := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨true, by simp [Set.piecewise, hx]⟩
    · exact ⟨false, by simp [Set.piecewise, hx]⟩
  have h := finite_selection_lipschitz_normed hcont
    (F := fun i : Bool => if i then H else ψ)
    (C := 1) (by intro i; cases i <;> simp only [Bool.false_eq_true,
      ite_false, ite_true]; exacts [short_iff_lipschitz.mp hψ, short_iff_lipschitz.mp hH]) hsel
  exact short_iff_lipschitz.mpr h

/-- The bounded Brehm correction fixes the origin, leaves all already-admissible
values unchanged, and preserves the bound on its image. -/
theorem exists_bounded_origin_correction
    {ψ : E → E} (hψ : Short ψ) {R : ℝ} (hR : ∀ x, ‖ψ x‖ ≤ R)
    (hzero : ψ 0 ≠ 0) :
    ∃ G H : E → E, Short G ∧ Short H ∧ G 0 = 0 ∧
      (∀ x, ‖G x‖ ≤ R) ∧ (∀ x, ‖H x‖ = ‖x‖) ∧
      (∀ x, G x = if ‖x‖ < ‖ψ x‖ then H x else ψ x) ∧
      (∀ x, ‖ψ x‖ ≤ ‖x‖ → G x = ψ x) ∧
      ∀ x, x ≠ 0 → ∃ t : ℝ, 0 < t ∧
        ψ (t • x) = t • H x ∧ ‖t • x‖ ≤ R := by
  obtain ⟨H, hH, hnorm, hmatch, hscale⟩ :=
    exists_short_radial_replacement hψ hR hzero
  let G : E → E := fun x => if ‖x‖ < ‖ψ x‖ then H x else ψ x
  have hG0 : G 0 = 0 := by
    have hH0 : H 0 = 0 := norm_eq_zero.mp (by simpa using hnorm 0)
    simp only [G, norm_zero, norm_pos_iff.mpr hzero, ite_true, hH0]
  refine ⟨G, H, short_origin_correction hψ hH hmatch, hH, hG0, ?_, hnorm,
    fun _ => rfl, ?_, hscale⟩
  · intro x
    dsimp [G]
    split_ifs with hx
    · rw [hnorm]
      exact hx.le.trans (hR x)
    · exact hR x
  · intro x hx
    simp [G, not_lt_of_ge hx]

/-- The linear motion obtained from an affine motion by reflecting its
translation vector. It agrees with the affine motion on the equal-norm locus. -/
def radialLinearMotion (r : E ≃ᵃⁱ[ℝ] E) : E ≃ₗᵢ[ℝ] E :=
  r.linearIsometryEquiv.trans (ℝ ∙ r 0)ᗮ.reflection

theorem radialLinearMotion_eq (r : E ≃ᵃⁱ[ℝ] E) {x : E}
    (hx : ‖r x‖ = ‖x‖) : radialLinearMotion r x = r x := by
  have hlin : r.linearIsometryEquiv x = r x - r 0 := by
    simpa only [vsub_eq_sub, sub_zero] using r.map_vsub x 0
  have hdiff : r.linearIsometryEquiv x - r x = -(r 0) := by
    rw [hlin]
    abel
  have hspan : (ℝ ∙ -(r 0)) = ℝ ∙ r 0 := by
    simpa only [neg_one_smul] using
      Submodule.span_singleton_smul_eq (R := ℝ) isUnit_neg_one (r 0)
  have heq := Submodule.reflection_sub (v := r.linearIsometryEquiv x) (w := r x)
    ((r.linearIsometryEquiv.norm_map x).trans hx.symm)
  simpa only [radialLinearMotion, LinearIsometryEquiv.trans_apply, hdiff, hspan] using heq

end BrehmApprox
