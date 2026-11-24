module

public import BrehmApprox.HyperbolicMixing

/-!
# Nonexpansion of the actual nearest projection onto a hyperbolic polytope

The proof is algebraic.  The variational inequalities at two nearest points
put the original points in opposite halfspaces perpendicular to the joining
geodesic.  A boost and Cauchy--Schwarz show that their distance is at least the
distance of the nearest points.  No face enumeration or CAT(0) axiom is used.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E]

lemma one_add_norm_mul_le_height_mul (x y : E) :
    1 + ‖x‖ * ‖y‖ ≤ height x * height y := by
  have hs : (height x * height y) ^ 2 - (1 + ‖x‖ * ‖y‖) ^ 2 =
      (‖x‖ - ‖y‖) ^ 2 := by
    rw [mul_pow, height_sq, height_sq]
    ring
  have h0 : 0 ≤ height x * height y := mul_nonneg (height_nonneg x) (height_nonneg y)
  have h1 : 0 ≤ 1 + ‖x‖ * ‖y‖ := by positivity
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

variable [InnerProductSpace ℝ E]

/-- Two opposite normal halfspace inequalities force separation by at least
the distance from the origin to `z`. -/
theorem normal_halfspaces_separated (x y z : E)
    (hx : height x * height z ≤ coshDist x z)
    (hy : coshDist y z * height z ≤ height y) :
    height z ≤ coshDist x y := by
  by_cases hz : z = 0
  · simpa only [hz, height, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one] using one_le_coshDist x y
  let R := ‖z‖
  let C := height z
  let A := height x
  let Y := height y
  let e : E := R⁻¹ • z
  let α : ℝ := ⟪x, e⟫_ℝ
  let β : ℝ := ⟪y, e⟫_ℝ
  let v : E := y - β • e
  have hR : 0 < R := norm_pos_iff.mpr hz
  have hC : 0 < C := height_pos z
  have hA : 0 < A := height_pos x
  have hY : 0 < Y := height_pos y
  have hCsq : C ^ 2 = 1 + R ^ 2 := height_sq z
  have hC1 : 1 ≤ C := by nlinarith [sq_nonneg R]
  have he : ‖e‖ = 1 := by
    dsimp [e, R]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), inv_mul_cancel₀ hR.ne']
  have hα : α ≤ 0 := by
    have hi : ⟪x, z⟫_ℝ ≤ 0 := by
      unfold coshDist at hx
      linarith
    dsimp [α, e]
    rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hR.le) hi
  have hβeq : R * β = ⟪y, z⟫_ℝ := by
    dsimp [β, e]
    rw [real_inner_smul_right]
    field_simp
  have hβ : R * Y ≤ C * β := by
    apply le_of_mul_le_mul_left (a := R) _ hR
    have hrel : C ^ 2 * Y = Y + R ^ 2 * Y := by rw [hCsq]; ring
    change (Y * C - ⟪y, z⟫_ℝ) * C ≤ Y at hy
    rw [← hβeq] at hy
    nlinarith
  have hβ0 : 0 ≤ β := by
    have hp := mul_pos hR hY
    nlinarith
  have hvnorm : ‖v‖ ^ 2 = ‖y‖ ^ 2 - β ^ 2 := by
    dsimp only [v]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, he, mul_one,
      real_inner_smul_right, sq_abs]
    change ‖y‖ ^ 2 - 2 * (β * β) + β ^ 2 = ‖y‖ ^ 2 - β ^ 2
    ring
  have hvheight : height v ^ 2 = Y ^ 2 - β ^ 2 := by
    rw [height_sq, hvnorm]
    dsimp only [Y]
    rw [height_sq]
    ring
  have hnormbound : C * height v ≤ Y := by
    have hsqβ : (R * Y) ^ 2 ≤ (C * β) ^ 2 := by
      nlinarith [mul_nonneg hR.le hY.le, mul_nonneg hC.le hβ0]
    have hrel : C ^ 2 * Y ^ 2 = Y ^ 2 + R ^ 2 * Y ^ 2 := by rw [hCsq]; ring
    have hsqv : (C * height v) ^ 2 ≤ Y ^ 2 := by
      rw [mul_pow, hvheight]
      nlinarith
    have hv0 := height_pos v
    nlinarith
  have hinner : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖v‖ := by
    have hv : ⟪x, y⟫_ℝ = ⟪x, v⟫_ℝ + β * α := by
      dsimp [v, α]
      rw [inner_sub_right, real_inner_smul_right]
      ring
    have hneg := mul_nonpos_of_nonneg_of_nonpos hβ0 hα
    have hc := real_inner_le_norm x v
    linarith
  have hreverse := one_add_norm_mul_le_height_mul x v
  have hreverseC := mul_le_mul_of_nonneg_left hreverse hC.le
  have hscale := mul_le_mul_of_nonneg_left hnormbound hA.le
  have hprod : 0 ≤ ‖x‖ * ‖v‖ := mul_nonneg (norm_nonneg x) (norm_nonneg v)
  have hrem : 0 ≤ (C - 1) * (‖x‖ * ‖v‖) :=
    mul_nonneg (sub_nonneg.mpr hC1) hprod
  change C ≤ A * Y - ⟪x, y⟫_ℝ
  change 1 + ‖x‖ * ‖v‖ ≤ A * height v at hreverse
  change C * (1 + ‖x‖ * ‖v‖) ≤ C * (A * height v) at hreverseC
  nlinarith

end BrehmApprox.Hyperboloid

namespace BrehmApprox

variable {n : ℕ}

/-- Two points satisfying the nearest-point right-angle inequalities are no
farther apart than the original two points. -/
theorem hyperbolic_dist_le_of_normal_inequalities (x y p q : HyperbolicSpace n)
    (hx : Real.cosh (dist x p) * Real.cosh (dist p q) ≤ Real.cosh (dist x q))
    (hy : Real.cosh (dist y q) * Real.cosh (dist q p) ≤ Real.cosh (dist y p)) :
    dist p q ≤ dist x y := by
  have h := Hyperboloid.normal_halfspaces_separated
    (Hyperboloid.boost p.point x.point) (Hyperboloid.boost p.point y.point)
    (Hyperboloid.boost p.point q.point) ?_ ?_
  · rw [Hyperboloid.height_boost, Hyperboloid.coshDist_boost, ← HyperbolicSpace.cosh_dist,
      ← HyperbolicSpace.cosh_dist] at h
    apply (HyperbolicSpace.dist_le_iff_coshDist_le p q x y).mpr
    simpa only [← HyperbolicSpace.cosh_dist] using h
  · rw [Hyperboloid.height_boost, Hyperboloid.height_boost, Hyperboloid.coshDist_boost,
      ← HyperbolicSpace.cosh_dist, ← HyperbolicSpace.cosh_dist, ← HyperbolicSpace.cosh_dist]
    simpa only [dist_comm p x] using hx
  · rw [Hyperboloid.coshDist_boost, Hyperboloid.height_boost, Hyperboloid.height_boost,
      ← HyperbolicSpace.cosh_dist, ← HyperbolicSpace.cosh_dist, ← HyperbolicSpace.cosh_dist]
    simpa only [dist_comm p q, dist_comm p y] using hy

/-- Nearest projection onto a genuine finite hyperbolic polytope is globally
short for the hyperbolic metric. -/
theorem hyperbolicCellProjection_short (V : Finset (HyperbolicSpace n)) (hV : V.Nonempty) :
    Short (hyperbolicCellProjection V hV) := by
  intro x y
  apply hyperbolic_dist_le_of_normal_inequalities x y
  · exact hyperbolicCell_nearest_cosh_inequality x
      (hyperbolicCellProjection_mem V hV x) (hyperbolicCellProjection_mem V hV y)
      (fun z hz => hyperbolicCellProjection_nearest V hV x hz)
  · exact hyperbolicCell_nearest_cosh_inequality y
      (hyperbolicCellProjection_mem V hV y) (hyperbolicCellProjection_mem V hV x)
      (fun z hz => hyperbolicCellProjection_nearest V hV y hz)

end BrehmApprox
