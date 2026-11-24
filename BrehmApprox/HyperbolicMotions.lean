module

public import BrehmApprox.HyperbolicProjection

/-!
# Explicit hyperbolic motions with Lorentz-linear lifts

The same boost used to prove the metric triangle inequality is now bundled as
a linear equivalence of Lorentz coordinates and an actual isometry equivalence
of hyperbolic space.  It sends any prescribed base point to the origin.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E]

lemma height_neg (z : E) : height (-z) = height z := by simp only [height, norm_neg]

variable [InnerProductSpace ℝ E]

/-- The full Lorentz-linear boost, acting on a time coordinate and spatial
coordinates. -/
def boostLinear (z : E) : (ℝ × E) →ₗ[ℝ] (ℝ × E) where
  toFun a := (height z * a.1 - ⟪z, a.2⟫_ℝ,
    a.2 + (⟪z, a.2⟫_ℝ / (height z + 1) - a.1) • z)
  map_add' a b := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
      ring
    · simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
      module
  map_smul' t a := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_right, smul_eq_mul,
        RingHom.id_apply]
      ring
    · simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_right, smul_eq_mul,
        RingHom.id_apply]
      module

lemma boostLinear_neg_inverse (z : E) (a : ℝ × E) : boostLinear (-z) (boostLinear z a) = a := by
  let k : ℝ := ⟪z, a.2⟫_ℝ / (height z + 1) - a.1
  let b : E := a.2 + k • z
  let T : ℝ := height z * a.1 - ⟪z, a.2⟫_ℝ
  have hz : ‖z‖ ^ 2 = height z ^ 2 - 1 := by linarith [height_sq z]
  have ht : height z * T + ⟪z, b⟫_ℝ = a.1 := by
    dsimp [T, b, k]
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hz]
    field_simp [height_add_one_ne_zero z]
    ring
  have hk : k + ⟪z, b⟫_ℝ / (height z + 1) + T = 0 := by
    dsimp [T, b, k]
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hz]
    field_simp [height_add_one_ne_zero z]
    ring
  apply Prod.ext
  · change height (-z) * T - ⟪-z, b⟫_ℝ = a.1
    simpa only [height_neg, inner_neg_left, sub_neg_eq_add] using ht
  · change b + (⟪-z, b⟫_ℝ / (height (-z) + 1) - T) • (-z) = a.2
    have hc : -(⟪-z, b⟫_ℝ / (height (-z) + 1) - T) = -k := by
      rw [height_neg, inner_neg_left, neg_div]
      linarith
    rw [smul_neg, ← neg_smul, hc]
    dsimp [b]
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]

def boostLinearEquiv (z : E) : (ℝ × E) ≃ₗ[ℝ] (ℝ × E) :=
  LinearEquiv.ofLinearMap (boostLinear z) (boostLinear (-z))
    (by
      apply LinearMap.ext
      intro a
      change boostLinear z (boostLinear (-z) a) = a
      simpa only [neg_neg] using boostLinear_neg_inverse (-z) a)
    (by
      apply LinearMap.ext
      intro a
      exact boostLinear_neg_inverse z a)

lemma height_boost (z x : E) : height (boost z x) = coshDist z x := by
  have hh := height_sq (boost z x)
  rw [boost_norm_sq] at hh
  have h0 := height_nonneg (boost z x)
  have hc := coshDist_pos z x
  nlinarith

lemma coshDist_boost (z x y : E) : coshDist (boost z x) (boost z y) = coshDist x y := by
  change height (boost z x) * height (boost z y) - ⟪boost z x, boost z y⟫_ℝ = _
  rw [height_boost, height_boost, boost_inner]
  ring

end BrehmApprox.Hyperboloid

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

def boostBy (z : EuclideanSpace ℝ (Fin n)) (x : HyperbolicSpace n) : HyperbolicSpace n :=
  ⟨Hyperboloid.boost z x.point⟩

lemma lift_boostBy (z : EuclideanSpace ℝ (Fin n)) (x : HyperbolicSpace n) :
    lift (boostBy z x) = Hyperboloid.boostLinear z (lift x) := by
  apply Prod.ext
  · exact Hyperboloid.height_boost z x.point
  · rfl

lemma boostBy_neg_inverse (z : EuclideanSpace ℝ (Fin n)) (x : HyperbolicSpace n) :
    boostBy (-z) (boostBy z x) = x := by
  apply HyperbolicSpace.ext
  have hh : lift (boostBy (-z) (boostBy z x)) = lift x := by
    rw [lift_boostBy, lift_boostBy, Hyperboloid.boostLinear_neg_inverse]
  exact congrArg Prod.snd hh

lemma isometry_boostBy (z : EuclideanSpace ℝ (Fin n)) : Isometry (boostBy z) := by
  apply Isometry.of_dist_eq
  intro x y
  change Real.arcosh (Hyperboloid.coshDist (Hyperboloid.boost z x.point)
    (Hyperboloid.boost z y.point)) = Real.arcosh (Hyperboloid.coshDist x.point y.point)
  rw [Hyperboloid.coshDist_boost]

/-- An actual isometry of hyperbolic space with its explicit Lorentz-linear lift. -/
def boostEquiv (z : EuclideanSpace ℝ (Fin n)) : HyperbolicSpace n ≃ᵢ HyperbolicSpace n where
  toFun := boostBy z
  invFun := boostBy (-z)
  left_inv := boostBy_neg_inverse z
  right_inv x := by simpa only [neg_neg] using boostBy_neg_inverse (-z) x
  isometry_toFun := isometry_boostBy z

lemma boostBy_self (x : HyperbolicSpace n) : boostBy x.point x = ⟨0⟩ := by
  apply HyperbolicSpace.ext
  apply norm_eq_zero.mp
  have hh := Hyperboloid.boost_norm_sq x.point x.point
  rw [Hyperboloid.coshDist_self] at hh
  change ‖Hyperboloid.boost x.point x.point‖ = 0
  nlinarith [norm_nonneg (Hyperboloid.boost x.point x.point)]

lemma boostLinear_lift_self (x : HyperbolicSpace n) :
    Hyperboloid.boostLinear x.point (lift x) = (1, 0) := by
  rw [← lift_boostBy, boostBy_self]
  simp only [lift, Hyperboloid.height, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_one]

end BrehmApprox.HyperbolicSpace
