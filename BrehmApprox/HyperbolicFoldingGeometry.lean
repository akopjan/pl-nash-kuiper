module

public import BrehmApprox.HyperbolicAffineProjection

/-!
# Actual hyperbolic radial geometry for finite initial folding

The angular Gram matrix and the directions of every barycentric base point
are computed in a canonical orthonormal frame obtained by a Lorentz boost.
The bisector angular base lies in an open hemisphere, and its linear span
does not contain its radial center.  These are geometric lemmas, not an
assumption of the still separate construction of an arbitrary polyhedral
complex's protected nets or angular complex.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

/-- The spatial radial vector in the canonical orthonormal frame at `a`. -/
def radialVector (a x : HyperbolicSpace n) : EuclideanSpace ℝ (Fin n) :=
  (boostBy a.point x).point

lemma norm_radialVector (a x : HyperbolicSpace n) :
    ‖radialVector a x‖ = Real.sinh (dist a x) :=
  Hyperboloid.boost_norm_eq_sinh a.point x.point

/-- The unit radial direction away from `a`; it is zero at the radial center. -/
def radialDirection (a x : HyperbolicSpace n) : EuclideanSpace ℝ (Fin n) :=
  (Real.sinh (dist a x))⁻¹ • radialVector a x

lemma radialDirection_norm (a x : HyperbolicSpace n) (h0 : 0 < dist a x) :
    ‖radialDirection a x‖ = 1 := by
  have hs := Real.sinh_pos_iff.mpr h0
  rw [radialDirection, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs), norm_radialVector, inv_mul_cancel₀ hs.ne']

lemma sinh_smul_radialDirection (a x : HyperbolicSpace n) :
    Real.sinh (dist a x) • radialDirection a x = radialVector a x := by
  by_cases hs : Real.sinh (dist a x) = 0
  · have hz : radialVector a x = 0 := by
      apply norm_eq_zero.mp
      rw [norm_radialVector, hs]
    rw [hs, zero_smul, hz]
  · rw [radialDirection, smul_smul, mul_inv_cancel₀ hs, one_smul]

lemma boosted_lift_radial_decomposition (a x : HyperbolicSpace n) :
    Hyperboloid.boostLinear a.point (lift x) =
      (Real.cosh (dist a x), Real.sinh (dist a x) • radialDirection a x) := by
  rw [← lift_boostBy, sinh_smul_radialDirection]
  apply Prod.ext
  · change Hyperboloid.height (Hyperboloid.boost a.point x.point) = _
    rw [Hyperboloid.height_boost]
    exact (cosh_dist a x).symm
  · rfl

theorem radial_cosine_law (a x y : HyperbolicSpace n) :
    Real.cosh (dist x y) = Real.cosh (dist a x) * Real.cosh (dist a y) -
      Real.sinh (dist a x) * Real.sinh (dist a y) *
        ⟪radialDirection a x, radialDirection a y⟫_ℝ := by
  have h := Hyperboloid.boost_inner a.point x.point y.point
  change ⟪radialVector a x, radialVector a y⟫_ℝ = _ at h
  rw [← sinh_smul_radialDirection a x, ← sinh_smul_radialDirection a y,
    real_inner_smul_left, real_inner_smul_right, ← cosh_dist, ← cosh_dist, ← cosh_dist] at h
  nlinarith

theorem radial_gram_formula (a x y : HyperbolicSpace n)
    (hx0 : 0 < dist a x) (hy0 : 0 < dist a y) :
    ⟪radialDirection a x, radialDirection a y⟫_ℝ =
      (Real.cosh (dist a x) * Real.cosh (dist a y) - Real.cosh (dist x y)) /
        (Real.sinh (dist a x) * Real.sinh (dist a y)) := by
  apply (eq_div_iff (mul_ne_zero (Real.sinh_pos_iff.mpr hx0).ne'
    (Real.sinh_pos_iff.mpr hy0).ne')).mpr
  nlinarith [radial_cosine_law a x y]

theorem radial_gram_eq_of_equal_radii (a b x y : HyperbolicSpace n)
    (hax : 0 < dist a x) (hay : 0 < dist a y)
    (hx : dist a x = dist b x) (hy : dist a y = dist b y) :
    ⟪radialDirection a x, radialDirection a y⟫_ℝ =
      ⟪radialDirection b x, radialDirection b y⟫_ℝ := by
  have hbx : 0 < dist b x := hx ▸ hax
  have hby : 0 < dist b y := hy ▸ hay
  rw [radial_gram_formula a x y hax hay, radial_gram_formula b x y hbx hby, hx, hy]

/-- Every point of a nontrivial bisector has direction strictly inside the
hemisphere centered on the direction to the second center. -/
theorem bisector_direction_in_open_hemisphere (a b x : HyperbolicSpace n)
    (hab : a ≠ b) (hax : a ≠ x) (hbis : dist a x = dist b x) :
    0 < ⟪radialDirection a b, radialDirection a x⟫_ℝ := by
  rw [radial_gram_formula a b x (dist_pos.mpr hab) (dist_pos.mpr hax), ← hbis]
  apply div_pos
  · have hc : 1 < Real.cosh (dist a b) :=
      Real.one_lt_cosh.mpr (ne_of_gt (dist_pos.mpr hab))
    have hx := Real.cosh_pos (dist a x)
    nlinarith
  · exact mul_pos (Real.sinh_pos_iff.mpr (dist_pos.mpr hab))
      (Real.sinh_pos_iff.mpr (dist_pos.mpr hax))

/-- The Lorentz pairing with a future unit point, with the positive time
convention, bundled as a real linear map. -/
def coshFunctional (a : HyperbolicSpace n) :
    (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ where
  toFun z := Hyperboloid.height a.point * z.1 - ⟪a.point, z.2⟫_ℝ
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
    ring
  map_smul' r z := by
    simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_right, smul_eq_mul,
      RingHom.id_apply]
    ring

lemma coshFunctional_lift (a x : HyperbolicSpace n) :
    coshFunctional a (lift x) = Real.cosh (dist a x) := (cosh_dist a x).symm

/-- A bisector base cannot have its radial center in the linear span of its
Lorentz vertices.  This is the nondegeneracy needed for angular projection. -/
theorem center_not_mem_span_bisector_vertices (a b : HyperbolicSpace n)
    (hab : a ≠ b) (V : Finset (HyperbolicSpace n))
    (hV : ∀ v ∈ V, dist a v = dist b v) :
    lift a ∉ Submodule.span ℝ (lift '' (V : Set (HyperbolicSpace n))) := by
  let L := coshFunctional a - coshFunctional b
  have hspan : Submodule.span ℝ (lift '' (V : Set (HyperbolicSpace n))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨v, hv, rfl⟩
    change coshFunctional a (lift v) - coshFunctional b (lift v) = 0
    rw [coshFunctional_lift, coshFunctional_lift, hV v hv, sub_self]
  intro ha
  have heq := hspan ha
  change coshFunctional a (lift a) - coshFunctional b (lift a) = 0 at heq
  rw [coshFunctional_lift, coshFunctional_lift, dist_self, Real.cosh_zero] at heq
  have hc := Real.one_lt_cosh.mpr (ne_of_gt (dist_pos.mpr hab.symm))
  linarith

/-- The whole barycentric base, including all interior points, has the same
weighted radial-vector formula in the frame at any center. -/
theorem radial_vector_barycentric (a x : HyperbolicSpace n)
    (V : Finset (HyperbolicSpace n)) (w : HyperbolicSpace n → ℝ) (c : ℝ)
    (hrep : ∑ v ∈ V, w v • lift v = c • lift x) :
    ∑ v ∈ V, w v • radialVector a v = c • radialVector a x := by
  have h := congrArg ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))).comp
    (Hyperboloid.boostLinear a.point)) hrep
  have hcoord (v : HyperbolicSpace n) :
      ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))).comp
        (Hyperboloid.boostLinear a.point)) (lift v) = radialVector a v := rfl
  simpa only [map_sum, map_smul, hcoord] using h

theorem radial_direction_barycentric (a x : HyperbolicSpace n)
    (V : Finset (HyperbolicSpace n)) (w : HyperbolicSpace n → ℝ) (c : ℝ)
    (hrep : ∑ v ∈ V, w v • lift v = c • lift x) :
    ∑ v ∈ V, (w v * Real.sinh (dist a v)) • radialDirection a v =
      (c * Real.sinh (dist a x)) • radialDirection a x := by
  simpa only [mul_smul, sinh_smul_radialDirection] using
    radial_vector_barycentric a x V w c hrep

theorem equal_radii_of_barycentric_bisector (a b x : HyperbolicSpace n)
    (V : Finset (HyperbolicSpace n)) (w : HyperbolicSpace n → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hrep : ∑ v ∈ V, w v • lift v = c • lift x)
    (hV : ∀ v ∈ V, dist a v = dist b v) : dist a x = dist b x := by
  apply Real.cosh_injOn (show dist a x ∈ Set.Ici 0 from dist_nonneg)
    (show dist b x ∈ Set.Ici 0 from dist_nonneg)
  have hs : ∑ v ∈ V, w v * Hyperboloid.coshDist a.point v.point =
      ∑ v ∈ V, w v * Hyperboloid.coshDist b.point v.point := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [← cosh_dist, ← cosh_dist, hV v hv]
  rw [hyperbolic_weighted_cosh hrep a, hyperbolic_weighted_cosh hrep b,
    ← cosh_dist, ← cosh_dist] at hs
  exact mul_left_cancel₀ hc hs

/-- Once the angular vertex isometry is chosen, it agrees with the radial
directions of every barycentric base point, not just its vertices. -/
theorem radial_direction_compatibility (a b x : HyperbolicSpace n)
    (V : Finset (HyperbolicSpace n)) (w : HyperbolicSpace n → ℝ) (c : ℝ)
    (hc : 0 < c) (hax : 0 < dist a x)
    (hrep : ∑ v ∈ V, w v • lift v = c • lift x)
    (hV : ∀ v ∈ V, dist a v = dist b v)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : ∀ v ∈ V, T (radialDirection a v) = radialDirection b v) :
    T (radialDirection a x) = radialDirection b x := by
  have hr := equal_radii_of_barycentric_bisector a b x V w c hc.ne' hrep hV
  have hleft := congrArg T (radial_direction_barycentric a x V w c hrep)
  simp only [map_sum, map_smul] at hleft
  have hsum : ∑ v ∈ V, (w v * Real.sinh (dist a v)) • T (radialDirection a v) =
      ∑ v ∈ V, (w v * Real.sinh (dist b v)) • radialDirection b v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [hV v hv, hT v hv]
  rw [hsum, radial_direction_barycentric b x V w c hrep, ← hr] at hleft
  exact (smul_right_injective (EuclideanSpace ℝ (Fin n))
    (mul_ne_zero hc.ne' (Real.sinh_pos_iff.mpr hax).ne'))
    hleft.symm

end BrehmApprox.HyperbolicSpace
