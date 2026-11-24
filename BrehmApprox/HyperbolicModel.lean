module

public import Mathlib

/-!
# The genuine hyperboloid metric in every finite dimension

The spatial coordinates `x` represent the future unit Lorentz vector
`(sqrt (1 + ‖x‖²), x)`.  The distance is the intrinsic curvature `-1`
distance `arcosh (t(x) * t(y) - ⟪x,y⟫)`.

The triangle inequality is proved here from an explicit Lorentz boost and
Cauchy--Schwarz.  No geometric axiom, Brehm hypothesis, or `sorry` is used
to construct the model metric.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E]

/-- The positive time coordinate on the future unit hyperboloid. -/
def height (x : E) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2)

lemma height_nonneg (x : E) : 0 ≤ height x := Real.sqrt_nonneg _

lemma height_pos (x : E) : 0 < height x := by
  unfold height
  positivity

lemma height_sq (x : E) : height x ^ 2 = 1 + ‖x‖ ^ 2 := by
  unfold height
  rw [Real.sq_sqrt]
  positivity

lemma norm_lt_height (x : E) : ‖x‖ < height x := by
  have h := height_sq x
  have hp := height_nonneg x
  have hn := norm_nonneg x
  nlinarith

lemma height_add_one_ne_zero (x : E) : height x + 1 ≠ 0 := by
  have := height_pos x
  positivity

variable [InnerProductSpace ℝ E]

/-- The negative Lorentz pairing of two future unit vectors. -/
def coshDist (x y : E) : ℝ := height x * height y - ⟪x, y⟫_ℝ

lemma coshDist_comm (x y : E) : coshDist x y = coshDist y x := by
  simp only [coshDist, real_inner_comm x y, mul_comm]

lemma coshDist_self (x : E) : coshDist x x = 1 := by
  simp only [coshDist, real_inner_self_eq_norm_sq, ← pow_two]
  rw [height_sq]
  ring

lemma coshDist_pos (x y : E) : 0 < coshDist x y := by
  have hm : ‖x‖ * ‖y‖ < height x * height y := by
    calc
      ‖x‖ * ‖y‖ ≤ height x * ‖y‖ :=
        mul_le_mul_of_nonneg_right (norm_lt_height x).le (norm_nonneg y)
      _ < height x * height y := mul_lt_mul_of_pos_left (norm_lt_height y) (height_pos x)
  have hc := real_inner_le_norm x y
  unfold coshDist
  linarith

/-- The spatial part of the Lorentz boost sending `(height z, z)` to `(1,0)`. -/
def boost (z x : E) : E :=
  x + (⟪z, x⟫_ℝ / (height z + 1) - height x) • z

lemma boost_inner (z x y : E) :
    ⟪boost z x, boost z y⟫_ℝ = coshDist z x * coshDist z y - coshDist x y := by
  have hz : ‖z‖ ^ 2 = height z ^ 2 - 1 := by linarith [height_sq z]
  simp only [boost, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm z x, hz]
  unfold coshDist
  field_simp [height_add_one_ne_zero z]
  ring

lemma boost_norm_sq (z x : E) : ‖boost z x‖ ^ 2 = coshDist z x ^ 2 - 1 := by
  have h := boost_inner z x x
  rw [real_inner_self_eq_norm_sq, coshDist_self] at h
  simpa only [pow_two] using h

lemma one_le_coshDist (x y : E) : 1 ≤ coshDist x y := by
  have h := boost_norm_sq x y
  have hp := coshDist_pos x y
  nlinarith [sq_nonneg ‖boost x y‖]

lemma height_boost_identity (z x : E) :
    height x = height z * coshDist z x + ⟪z, boost z x⟫_ℝ := by
  have hz : ‖z‖ ^ 2 = height z ^ 2 - 1 := by linarith [height_sq z]
  simp only [boost, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hz]
  unfold coshDist
  field_simp [height_add_one_ne_zero z]
  ring

lemma eq_of_coshDist_eq_one {x y : E} (h : coshDist x y = 1) : x = y := by
  have hc : coshDist y x = 1 := by rwa [coshDist_comm]
  have hb : boost y x = 0 := by
    apply norm_eq_zero.mp
    have hs := boost_norm_sq y x
    rw [hc] at hs
    nlinarith [norm_nonneg (boost y x)]
  have ht : height x = height y := by
    have hi := height_boost_identity y x
    simpa [hc, hb] using hi
  have hi : ⟪y, x⟫_ℝ = height y ^ 2 - 1 := by
    unfold coshDist at hc
    rw [ht] at hc
    nlinarith
  have hk : ⟪y, x⟫_ℝ / (height y + 1) - height x = -1 := by
    rw [hi, ht]
    field_simp [height_add_one_ne_zero y]
    ring
  rw [boost, hk, neg_one_smul, ← sub_eq_add_neg] at hb
  exact sub_eq_zero.mp hb

lemma coshDist_eq_one_iff (x y : E) : coshDist x y = 1 ↔ x = y := by
  constructor
  · exact eq_of_coshDist_eq_one
  · rintro rfl
    exact coshDist_self x

/-- The hyperbolic distance, in spatial coordinates. -/
def distance (x y : E) : ℝ := Real.arcosh (coshDist x y)

lemma distance_nonneg (x y : E) : 0 ≤ distance x y :=
  Real.arcosh_nonneg (one_le_coshDist x y)

lemma distance_self (x : E) : distance x x = 0 := by
  simp [distance, coshDist_self]

lemma distance_comm (x y : E) : distance x y = distance y x := by
  simp only [distance, coshDist_comm x y]

lemma distance_eq_zero_iff (x y : E) : distance x y = 0 ↔ x = y := by
  rw [distance, Real.arcosh_eq_zero_iff (one_le_coshDist x y), coshDist_eq_one_iff]

lemma cosh_distance (x y : E) : Real.cosh (distance x y) = coshDist x y :=
  Real.cosh_arcosh (one_le_coshDist x y)

lemma boost_norm_eq_sinh (z x : E) : ‖boost z x‖ = Real.sinh (distance z x) := by
  rw [distance, Real.sinh_arcosh (one_le_coshDist z x), ← boost_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

lemma coshDist_triangle_bound (x y z : E) :
    coshDist x z ≤ Real.cosh (distance x y + distance y z) := by
  have hc := neg_le_of_abs_le (abs_real_inner_le_norm (boost y x) (boost y z))
  rw [boost_inner, boost_norm_eq_sinh, boost_norm_eq_sinh] at hc
  rw [Real.cosh_add, cosh_distance, cosh_distance]
  rw [coshDist_comm y x, distance_comm y x] at hc
  linarith

lemma distance_triangle (x y z : E) : distance x z ≤ distance x y + distance y z := by
  calc
    distance x z ≤ Real.arcosh (Real.cosh (distance x y + distance y z)) := by
      exact (Real.arcosh_le_arcosh (coshDist_pos x z) (Real.cosh_pos _)).2
        (coshDist_triangle_bound x y z)
    _ = distance x y + distance y z :=
      Real.arcosh_cosh (add_nonneg (distance_nonneg x y) (distance_nonneg y z))

end BrehmApprox.Hyperboloid

namespace BrehmApprox

/-- Hyperbolic `n`-space in spatial hyperboloid coordinates.  This wrapper
prevents the Euclidean metric on the coordinate vectors from being reused. -/
structure HyperbolicSpace (n : ℕ) where
  point : EuclideanSpace ℝ (Fin n)

namespace HyperbolicSpace

variable {n : ℕ}

instance : MetricSpace (HyperbolicSpace n) where
  dist x y := Hyperboloid.distance x.point y.point
  dist_self x := Hyperboloid.distance_self x.point
  dist_comm x y := Hyperboloid.distance_comm x.point y.point
  dist_triangle x y z := Hyperboloid.distance_triangle x.point y.point z.point
  eq_of_dist_eq_zero {x y} h := by
    have hp := (Hyperboloid.distance_eq_zero_iff _ _).mp h
    cases x
    cases y
    congr

theorem dist_eq (x y : HyperbolicSpace n) :
    dist x y = Real.arcosh
      (Real.sqrt (1 + ‖x.point‖ ^ 2) * Real.sqrt (1 + ‖y.point‖ ^ 2) -
        ⟪x.point, y.point⟫_ℝ) := rfl

end HyperbolicSpace
end BrehmApprox
