module

public import BrehmApprox.HyperbolicStrictification
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Genuine hyperbolic orthogonal projections

For a Euclidean linear subspace `K`, the associated totally geodesic
hyperbolic plane through the origin consists of points whose spatial
coordinate lies in `K`.  In Klein coordinates its hyperbolic orthogonal
projection is exactly the Euclidean orthogonal projection to `K`.

We prove its nonexpansion, nearest point property, exact Pythagorean formula,
and commutation for nested subspaces directly from the hyperbolic metric.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

/-- A genuine totally geodesic hyperbolic subspace through the origin. -/
def geodesicPlane (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set (HyperbolicSpace n) :=
  {x | x.point ∈ K}

lemma klein_mem_iff (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : HyperbolicSpace n) :
    klein x ∈ K ↔ x ∈ geodesicPlane K := by
  constructor
  · intro hx
    change x.point ∈ K
    have h := K.smul_mem (Hyperboloid.height x.point) hx
    simpa only [klein, smul_smul, mul_inv_cancel₀ (ne_of_gt (Hyperboloid.height_pos x.point)),
      one_smul] using h
  · intro hx
    exact K.smul_mem _ hx

lemma norm_projection_klein_lt_one (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : HyperbolicSpace n) : ‖K.starProjection (klein x)‖ < 1 :=
  (K.norm_starProjection_apply_le _).trans_lt (norm_klein_lt_one x)

/-- Hyperbolic normal projection to the totally geodesic plane through the
origin determined by `K`. -/
def geodesicProjection (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : HyperbolicSpace n) : HyperbolicSpace n :=
  fromKlein (K.starProjection (klein x))

lemma klein_geodesicProjection (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : HyperbolicSpace n) : klein (geodesicProjection K x) = K.starProjection (klein x) :=
  klein_fromKlein (norm_projection_klein_lt_one K x)

lemma geodesicProjection_mem (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : HyperbolicSpace n) : geodesicProjection K x ∈ geodesicPlane K := by
  apply (klein_mem_iff K _).mp
  rw [klein_geodesicProjection]
  exact K.starProjection_apply_mem _

lemma geodesicProjection_fix (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {x : HyperbolicSpace n} (hx : x ∈ geodesicPlane K) : geodesicProjection K x = x := by
  apply klein_injective
  rw [klein_geodesicProjection]
  exact K.starProjection_eq_self_iff.mpr ((klein_mem_iff K x).mpr hx)

lemma geodesicProjection_nested {J K : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (hJK : J ≤ K) (x : HyperbolicSpace n) :
    geodesicProjection J (geodesicProjection K x) = geodesicProjection J x := by
  apply klein_injective
  simp only [klein_geodesicProjection]
  have h := congrArg (fun P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
    P (klein x)) (Submodule.starProjection_comp_starProjection_of_le hJK)
  simpa only [ContinuousLinearMap.comp_apply] using h

lemma dist_le_iff_coshDist_le (x y z w : HyperbolicSpace n) :
    dist x y ≤ dist z w ↔
      Hyperboloid.coshDist x.point y.point ≤ Hyperboloid.coshDist z.point w.point := by
  rw [← cosh_dist, ← cosh_dist, Real.cosh_le_cosh,
    abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]

private lemma hypot_product_ge {a b r s A B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA2 : A ^ 2 = a ^ 2 + r ^ 2) (hB2 : B ^ 2 = b ^ 2 + s ^ 2) :
    a * b + r * s ≤ A * B := by
  have hl : 0 ≤ a * b + r * s := by positivity
  have hr' : 0 ≤ A * B := by positivity
  have heq : (A * B) ^ 2 - (a * b + r * s) ^ 2 = (a * s - b * r) ^ 2 := by
    rw [mul_pow, hA2, hB2]
    ring
  nlinarith [sq_nonneg (a * s - b * r)]

/-- Orthogonal projection to a hyperbolic totally geodesic plane is globally
distance nonincreasing. -/
theorem geodesicProjection_short (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Short (geodesicProjection K) := by
  intro x y
  apply (dist_le_iff_coshDist_le _ _ _ _).mpr
  let p := klein x
  let q := klein y
  let u := K.starProjection p
  let v := K.starProjection q
  let r := Kᗮ.starProjection p
  let s := Kᗮ.starProjection q
  let a := Real.sqrt (1 - ‖p‖ ^ 2)
  let b := Real.sqrt (1 - ‖q‖ ^ 2)
  let A := Real.sqrt (1 - ‖u‖ ^ 2)
  let B := Real.sqrt (1 - ‖v‖ ^ 2)
  let c := Hyperboloid.coshDist (geodesicProjection K x).point (geodesicProjection K y).point
  let d := Hyperboloid.coshDist x.point y.point
  have ha : 0 < a := klein_denominator_pos (norm_klein_lt_one x)
  have hb : 0 < b := klein_denominator_pos (norm_klein_lt_one y)
  have hA : 0 < A := klein_denominator_pos (norm_projection_klein_lt_one K x)
  have hB : 0 < B := klein_denominator_pos (norm_projection_klein_lt_one K y)
  have hap : a ^ 2 = 1 - ‖p‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_klein_lt_one x, norm_nonneg p])
  have hbq : b ^ 2 = 1 - ‖q‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_klein_lt_one y, norm_nonneg q])
  have hAu : A ^ 2 = 1 - ‖u‖ ^ 2 := Real.sq_sqrt
    (by nlinarith [norm_projection_klein_lt_one K x, norm_nonneg u])
  have hBv : B ^ 2 = 1 - ‖v‖ ^ 2 := Real.sq_sqrt
    (by nlinarith [norm_projection_klein_lt_one K y, norm_nonneg v])
  have hpn : ‖p‖ ^ 2 = ‖u‖ ^ 2 + ‖r‖ ^ 2 := K.norm_sq_eq_add_norm_sq_starProjection p
  have hqn : ‖q‖ ^ 2 = ‖v‖ ^ 2 + ‖s‖ ^ 2 := K.norm_sq_eq_add_norm_sq_starProjection q
  have hA2 : A ^ 2 = a ^ 2 + ‖r‖ ^ 2 := by linarith
  have hB2 : B ^ 2 = b ^ 2 + ‖s‖ ^ 2 := by linarith
  have hab := hypot_product_ge ha.le hb.le (norm_nonneg r) (norm_nonneg s) hA.le hB.le hA2 hB2
  have hc : 1 ≤ c := Hyperboloid.one_le_coshDist _ _
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hcp : A * B * c = 1 - ⟪u, v⟫_ℝ := by
    have hh := coshDist_eq_klein (geodesicProjection K x) (geodesicProjection K y)
    rw [klein_geodesicProjection, klein_geodesicProjection] at hh
    change c = (1 - ⟪u, v⟫_ℝ) / (A * B) at hh
    rw [hh]
    field_simp [ne_of_gt hA, ne_of_gt hB]
  have hdp : a * b * d = 1 - ⟪p, q⟫_ℝ := by
    have hh := coshDist_eq_klein x y
    change d = (1 - ⟪p, q⟫_ℝ) / (a * b) at hh
    rw [hh]
    field_simp [ne_of_gt ha, ne_of_gt hb]
  have hus : ⟪u, s⟫_ℝ = 0 :=
    (K.mem_orthogonal _).mp (Kᗮ.starProjection_apply_mem q) u (K.starProjection_apply_mem p)
  have hrv : ⟪r, v⟫_ℝ = 0 := by
    rw [real_inner_comm v r]
    exact (K.mem_orthogonal _).mp (Kᗮ.starProjection_apply_mem p) v (K.starProjection_apply_mem q)
  have hdot : ⟪p, q⟫_ℝ = ⟪u, v⟫_ℝ + ⟪r, s⟫_ℝ := by
    have hp : p = u + r := (K.starProjection_add_starProjection_orthogonal p).symm
    have hq : q = v + s := (K.starProjection_add_starProjection_orthogonal q).symm
    calc
      _ = ⟪u + r, v + s⟫_ℝ := congrArg₂ (inner ℝ) hp hq
      _ = _ := by simp only [inner_add_left, inner_add_right, hus, hrv, add_zero, zero_add]
  have hmult := mul_le_mul_of_nonneg_right hab hc0
  have hrs : 0 ≤ ‖r‖ * ‖s‖ := by positivity
  have hrsc : ‖r‖ * ‖s‖ ≤ ‖r‖ * ‖s‖ * c := by nlinarith
  have hcs := real_inner_le_norm r s
  have hfinal : a * b * c ≤ a * b * d := by nlinarith [hcp, hdp, hdot]
  exact le_of_mul_le_mul_left hfinal (mul_pos ha hb)

lemma coshDist_geodesicProjection_self (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : HyperbolicSpace n) :
    Hyperboloid.coshDist x.point (geodesicProjection K x).point =
      Real.sqrt (1 - ‖K.starProjection (klein x)‖ ^ 2) / Real.sqrt (1 - ‖klein x‖ ^ 2) := by
  rw [coshDist_eq_klein, klein_geodesicProjection]
  have hinner : ⟪klein x, K.starProjection (klein x)⟫_ℝ =
      ‖K.starProjection (klein x)‖ ^ 2 := by
    have hh := K.starProjection_inner_eq_zero (klein x) (K.starProjection (klein x))
      (K.starProjection_apply_mem _)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hh
    linarith
  rw [hinner]
  have hsq := Real.sq_sqrt (show 0 ≤ 1 - ‖K.starProjection (klein x)‖ ^ 2 by
    nlinarith [norm_projection_klein_lt_one K x, norm_nonneg (K.starProjection (klein x))])
  have ha := klein_denominator_pos (norm_klein_lt_one x)
  have hA := klein_denominator_pos (norm_projection_klein_lt_one K x)
  field_simp [ne_of_gt ha, ne_of_gt hA]
  nlinarith

/-- Hyperbolic Pythagoras, with one leg orthogonal to the whole plane. -/
theorem geodesicProjection_pythagoras (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : HyperbolicSpace n) {z : HyperbolicSpace n} (hz : z ∈ geodesicPlane K) :
    Real.cosh (dist x z) = Real.cosh (dist x (geodesicProjection K x)) *
      Real.cosh (dist (geodesicProjection K x) z) := by
  rw [cosh_dist, cosh_dist, cosh_dist, coshDist_geodesicProjection_self,
    coshDist_eq_klein, coshDist_eq_klein, klein_geodesicProjection]
  have hinner : ⟪klein x, klein z⟫_ℝ = ⟪K.starProjection (klein x), klein z⟫_ℝ := by
    have hh := K.starProjection_inner_eq_zero (klein x) (klein z) ((klein_mem_iff K z).mpr hz)
    rwa [inner_sub_left, sub_eq_zero] at hh
  rw [hinner]
  field_simp [ne_of_gt (klein_denominator_pos (norm_projection_klein_lt_one K x))]

theorem geodesicProjection_nearest (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : HyperbolicSpace n) {z : HyperbolicSpace n} (hz : z ∈ geodesicPlane K) :
    dist x (geodesicProjection K x) ≤ dist x z := by
  apply (dist_le_iff_coshDist_le _ _ _ _).mpr
  rw [← cosh_dist, ← cosh_dist, geodesicProjection_pythagoras K x hz]
  have h := Real.one_le_cosh (dist (geodesicProjection K x) z)
  have hp := Real.cosh_pos (dist x (geodesicProjection K x))
  nlinarith

theorem geodesicProjection_nearest_unique (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : HyperbolicSpace n) {z : HyperbolicSpace n} (hz : z ∈ geodesicPlane K)
    (hmin : dist x z ≤ dist x (geodesicProjection K x)) : z = geodesicProjection K x := by
  have heq : dist x z = dist x (geodesicProjection K x) :=
    le_antisymm hmin (geodesicProjection_nearest K x hz)
  have hp := geodesicProjection_pythagoras K x hz
  rw [heq] at hp
  have hpos := Real.cosh_pos (dist x (geodesicProjection K x))
  have hc : Real.cosh (dist (geodesicProjection K x) z) = 1 := by nlinarith
  rw [cosh_dist] at hc
  exact (HyperbolicSpace.ext (Hyperboloid.eq_of_coshDist_eq_one hc)).symm

end BrehmApprox.HyperbolicSpace
