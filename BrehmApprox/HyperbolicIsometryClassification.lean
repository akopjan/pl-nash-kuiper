module

public import BrehmApprox.HyperbolicPogorelovMotions
public import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# Lorentz-linear lifts of hyperbolic isometries

An isometry fixing the origin preserves the height coordinate and all spatial
inner products. Its spatial action is therefore an orthogonal map. Composing
with a Lorentz boost gives a linear lift of every hyperbolic isometry.
-/

@[expose] public section
noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

private theorem height_zero : Hyperboloid.height (0 : EuclideanSpace ℝ (Fin n)) = 1 := by
  simp [Hyperboloid.height]

theorem height_eq_of_isometry_fix_zero
    (q : HyperbolicSpace n ≃ᵢ HyperbolicSpace n) (h0 : q ⟨0⟩ = ⟨0⟩)
    (x : HyperbolicSpace n) : Hyperboloid.height (q x).point = Hyperboloid.height x.point := by
  have h := congrArg Real.cosh (q.dist_eq x (⟨0⟩ : HyperbolicSpace n))
  rw [h0, cosh_dist, cosh_dist] at h
  change Hyperboloid.height (q x).point * Hyperboloid.height (0 : EuclideanSpace ℝ (Fin n)) -
    ⟪(q x).point, 0⟫_ℝ =
    Hyperboloid.height x.point * Hyperboloid.height (0 : EuclideanSpace ℝ (Fin n)) -
    ⟪x.point, 0⟫_ℝ at h
  simpa only [height_zero, mul_one, inner_zero_right, sub_zero] using h

theorem inner_eq_of_isometry_fix_zero
    (q : HyperbolicSpace n ≃ᵢ HyperbolicSpace n) (h0 : q ⟨0⟩ = ⟨0⟩)
    (x y : HyperbolicSpace n) : ⟪(q x).point, (q y).point⟫_ℝ = ⟪x.point, y.point⟫_ℝ := by
  have h := congrArg Real.cosh (q.dist_eq x y)
  rw [cosh_dist, cosh_dist, Hyperboloid.coshDist, Hyperboloid.coshDist,
    height_eq_of_isometry_fix_zero q h0 x, height_eq_of_isometry_fix_zero q h0 y] at h
  linarith

/-- The stabilizer of the origin acts orthogonally on spatial coordinates. -/
theorem exists_orthogonal_of_isometry_fix_zero
    (q : HyperbolicSpace n ≃ᵢ HyperbolicSpace n) (h0 : q ⟨0⟩ = ⟨0⟩) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : HyperbolicSpace n, (q x).point = U x.point := by
  let e : EuclideanSpace ℝ (Fin n) ≃ EuclideanSpace ℝ (Fin n) :=
    { toFun := fun x => (q ⟨x⟩).point
      invFun := fun x => (q.symm ⟨x⟩).point
      left_inv := fun x => congrArg HyperbolicSpace.point (q.symm_apply_apply ⟨x⟩)
      right_inv := fun x => congrArg HyperbolicSpace.point (q.apply_symm_apply ⟨x⟩) }
  have he : Isometry e := by
    apply Isometry.of_dist_eq
    intro x y
    have hxx := inner_eq_of_isometry_fix_zero q h0 (⟨x⟩ : HyperbolicSpace n) ⟨x⟩
    have hyy := inner_eq_of_isometry_fix_zero q h0 (⟨y⟩ : HyperbolicSpace n) ⟨y⟩
    have hxy := inner_eq_of_isometry_fix_zero q h0 (⟨x⟩ : HyperbolicSpace n) ⟨y⟩
    change ⟪e x, e x⟫_ℝ = ⟪x, x⟫_ℝ at hxx
    change ⟪e y, e y⟫_ℝ = ⟪y, y⟫_ℝ at hyy
    change ⟪e x, e y⟫_ℝ = ⟪x, y⟫_ℝ at hxy
    simp only [real_inner_self_eq_norm_sq] at hxx hyy
    have hh : ‖e x - e y‖ ^ 2 = ‖x - y‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, hxx, hyy, hxy]
    rw [dist_eq_norm, dist_eq_norm]
    nlinarith [norm_nonneg (e x - e y), norm_nonneg (x - y)]
  let r : EuclideanSpace ℝ (Fin n) ≃ᵢ EuclideanSpace ℝ (Fin n) :=
    { e with isometry_toFun := he }
  have hr0 : r 0 = 0 := congrArg HyperbolicSpace.point h0
  let U := r.toRealLinearIsometryEquivOfMapZero hr0
  exact ⟨U, fun x => rfl⟩

/-- Every hyperbolic isometry has an injective ambient Lorentz-linear lift. -/
theorem exists_injective_lorentz_linear_lift (r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n) :
    ∃ L : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)),
      Function.Injective L ∧ ∀ x, L (lift x) = lift (r x) := by
  let z := r (⟨0⟩ : HyperbolicSpace n)
  let q := r.trans (boostEquiv z.point)
  have h0 : q (⟨0⟩ : HyperbolicSpace n) = ⟨0⟩ := boostBy_self z
  obtain ⟨U, hU⟩ := exists_orthogonal_of_isometry_fix_zero q h0
  let L := (Hyperboloid.boostLinear (-z.point)).comp (Pogorelov.orthogonalLinear U)
  have hq (x : HyperbolicSpace n) : Pogorelov.orthogonalLinear U (lift x) = lift (q x) := by
    apply Prod.ext
    · exact (height_eq_of_isometry_fix_zero q h0 x).symm
    · exact (hU x).symm
  have hUinj : Function.Injective (Pogorelov.orthogonalLinear U) := by
    intro a b hab
    apply Prod.ext
    · have hh := congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.1) hab
      exact hh
    · apply U.injective
      have hh := congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.2) hab
      exact hh
  refine ⟨L, (Hyperboloid.boostLinearEquiv (-z.point)).injective.comp hUinj, fun x => ?_⟩
  change Hyperboloid.boostLinear (-z.point) (Pogorelov.orthogonalLinear U (lift x)) = _
  rw [hq, ← lift_boostBy]
  exact congrArg lift (boostBy_neg_inverse z.point (r x))

/-- The linear lift, with injectivity available in the stronger companion theorem. -/
theorem exists_lorentz_linear_lift (r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n) :
    ∃ L : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)),
      ∀ x, L (lift x) = lift (r x) := by
  obtain ⟨L, _, hL⟩ := exists_injective_lorentz_linear_lift r
  exact ⟨L, hL⟩

end BrehmApprox.HyperbolicSpace
