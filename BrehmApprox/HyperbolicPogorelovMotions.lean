module

public import BrehmApprox.HyperbolicPogorelov

/-!
# Euclidean motions under the Pogorelov graph transform

An affine Euclidean motion whose translation vector has norm less than two
corresponds to an explicit hyperbolic motion. Consequently a finite family of
Euclidean motions near the transformed graph gives a finite family of genuine
hyperbolic motions. All formulas are proved, without a Brehm hypothesis.
-/

@[expose] public section
noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox.Pogorelov

open Hyperboloid HyperbolicSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive denominator of the Cayley parametrization of a Lorentz boost. -/
def boostDenominator (b : E) : ℝ := 1 - ‖b‖ ^ 2 / 4

omit [InnerProductSpace ℝ E] in
lemma boostDenominator_pos {b : E} (hb : ‖b‖ < 2) : 0 < boostDenominator b := by
  dsimp [boostDenominator]
  nlinarith [norm_nonneg b]

/-- Spatial coordinate of the Lorentz boost corresponding to translation `b`. -/
def boostParameter (b : E) : E := (boostDenominator b)⁻¹ • b

lemma height_boostParameter {b : E} (hb : ‖b‖ < 2) :
    height (boostParameter b) = (1 + ‖b‖ ^ 2 / 4) / boostDenominator b := by
  have hd := boostDenominator_pos hb
  have hsq : (height (boostParameter b) * boostDenominator b) ^ 2 =
      (1 + ‖b‖ ^ 2 / 4) ^ 2 := by
    rw [mul_pow, height_sq]
    simp only [boostParameter, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hd.ne']
    dsimp [boostDenominator]
    ring
  have hnon : 0 ≤ height (boostParameter b) * boostDenominator b :=
    mul_nonneg (height_nonneg _) hd.le
  have hright : 0 ≤ 1 + ‖b‖ ^ 2 / 4 := by positivity
  apply (eq_div_iff hd.ne').mpr
  nlinarith

lemma height_boostParameter_add_one {b : E} (hb : ‖b‖ < 2) :
    height (boostParameter b) + 1 = 2 / boostDenominator b := by
  rw [height_boostParameter hb]
  field_simp [(boostDenominator_pos hb).ne']
  dsimp [boostDenominator]
  ring

lemma boostParameter_inner_quotient {b : E} (hb : ‖b‖ < 2) (w : E) :
    ⟪boostParameter b, w⟫_ℝ / (height (boostParameter b) + 1) = ⟪b, w⟫_ℝ / 2 := by
  rw [height_boostParameter_add_one hb]
  simp only [boostParameter, real_inner_smul_left]
  field_simp [(boostDenominator_pos hb).ne']

variable {n : ℕ}

/-- Hyperbolic motion corresponding to `u ↦ U u + b`. -/
def motion (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) : HyperbolicSpace n ≃ᵢ HyperbolicSpace n :=
  (orthogonalEquiv U).trans (boostEquiv (-boostParameter b))

lemma motion_point (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {b : EuclideanSpace ℝ (Fin n)} (hb : ‖b‖ < 2) (x : HyperbolicSpace n) :
    (motion U b x).point = U x.point +
      (⟪b, U x.point⟫_ℝ / 2 + height x.point) • boostParameter b := by
  change boost (-boostParameter b) (U x.point) = _
  rw [boost, height_neg, inner_neg_left, neg_div, smul_neg, ← neg_smul,
    boostParameter_inner_quotient hb]
  have hh : height (U x.point) = height x.point := by simp [height]
  rw [hh]
  congr 1
  congr 1
  ring

lemma motion_height (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (x : HyperbolicSpace n) :
    height (motion U b x).point = height (boostParameter b) * height x.point +
      ⟪boostParameter b, U x.point⟫_ℝ := by
  change height (boost (-boostParameter b) (U x.point)) = _
  rw [height_boost, coshDist, height_neg, inner_neg_left, sub_neg_eq_add]
  simp only [height, U.norm_map]

lemma motion_point_eq (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {b : EuclideanSpace ℝ (Fin n)} (hb : ‖b‖ < 2) (x : HyperbolicSpace n) :
    (motion U b x).point = U x.point +
      (scale x.point (motion U b x).point / 2) • b := by
  conv_lhs => rw [motion_point U hb x]
  have hs : scale x.point (motion U b x).point / 2 =
      (⟪b, U x.point⟫_ℝ / 2 + height x.point) / boostDenominator b := by
    unfold scale
    rw [motion_height, height_boostParameter hb]
    simp only [boostParameter, real_inner_smul_left]
    field_simp [(boostDenominator_pos hb).ne']
    dsimp [boostDenominator]
    ring
  rw [hs, boostParameter, smul_smul]
  congr 1

theorem graphRelated_motion
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {b : EuclideanSpace ℝ (Fin n)} (hb : ‖b‖ < 2) (x : HyperbolicSpace n) :
    GraphRelated (fun u => U u + b) x.point (motion U b x).point := by
  let c : ℝ := scale x.point (motion U b x).point
  change (2 / c) • (motion U b x).point = U ((2 / c) • x.point) + b
  rw [motion_point_eq U hb x]
  change (2 / c) • (U x.point + (c / 2) • b) = U ((2 / c) • x.point) + b
  rw [smul_add, smul_smul, map_smul]
  have hs : 2 / c * (c / 2) = 1 := by
    dsimp [c]
    field_simp [(scale_pos x.point (motion U b x).point).ne']
  rw [hs, one_smul]

/-- Hyperbolic motion corresponding to an affine Euclidean motion. -/
def affineMotion
    (r : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    HyperbolicSpace n ≃ᵢ HyperbolicSpace n := motion r.linearIsometryEquiv (r 0)

/-- The linear action of an orthogonal map on Lorentz coordinates. -/
def orthogonalLinear
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) :=
  (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))).prod
    (U.toLinearMap.comp (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))))

/-- The explicitly Lorentz-linear lift of `motion`. -/
def motionLinear
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) :
    (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) :=
  (boostLinear (-boostParameter b)).comp (orthogonalLinear U)

theorem lift_motion
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (x : HyperbolicSpace n) :
    HyperbolicSpace.lift (motion U b x) = motionLinear U b (HyperbolicSpace.lift x) := by
  change HyperbolicSpace.lift (boostBy (-boostParameter b) (orthogonalMap U x)) = _
  rw [lift_boostBy]
  apply congrArg (boostLinear (-boostParameter b))
  apply Prod.ext
  · exact height_orthogonalMap U x
  · rfl

theorem lift_affineMotion
    (r : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : HyperbolicSpace n) :
    HyperbolicSpace.lift (affineMotion r x) =
      motionLinear r.linearIsometryEquiv (r 0) (HyperbolicSpace.lift x) :=
  lift_motion r.linearIsometryEquiv (r 0) x

lemma affine_apply
    (r : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) : r u = r.linearIsometryEquiv u + r 0 := by
  simpa only [vadd_eq_add, add_zero] using r.map_vadd 0 u

theorem graphRelated_affineMotion
    (r : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    (hr : ‖r 0‖ < 2) (x : HyperbolicSpace n) :
    GraphRelated (fun u => r u) x.point (affineMotion r x).point := by
  change pairRight x.point (motion r.linearIsometryEquiv (r 0) x).point =
    r (pairLeft x.point (motion r.linearIsometryEquiv (r 0) x).point)
  rw [affine_apply r (pairLeft x.point (motion r.linearIsometryEquiv (r 0) x).point)]
  exact graphRelated_motion r.linearIsometryEquiv hr x

theorem translation_lt_two_of_graph
    (r : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    {x y : EuclideanSpace ℝ (Fin n)} (h : pairRight x y = r (pairLeft x y)) :
    ‖r 0‖ < 2 := by
  have hh := norm_pairLeft_add_norm_pairRight_lt_two x y
  rw [h] at hh
  have ht := dist_triangle (r 0) (r (pairLeft x y)) 0
  rw [r.isometry.dist_eq] at ht
  simp only [dist_zero_right, dist_zero_left] at ht
  exact lt_of_le_of_lt ht hh

theorem liftShort_eq_affineMotion
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LipschitzWith 1 F) (hzero : ‖F 0‖ < 2)
    (r : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : HyperbolicSpace n)
    (hr : F (pairLeft x.point (liftShort F hF hzero x).point) =
      r (pairLeft x.point (liftShort F hF hzero x).point)) :
    liftShort F hF hzero x = affineMotion r x := by
  have hgraph : GraphRelated (fun u => r u) x.point (liftShort F hF hzero x).point :=
    (graphRelated_liftShort F hF hzero x).trans hr
  have htrans := translation_lt_two_of_graph r hgraph
  apply HyperbolicSpace.ext
  exact graphRelated_unique r.isometry.lipschitzWith hgraph (graphRelated_affineMotion r htrans x)

/-- Finite affine motion selection on the radius-two ball transfers to finite
hyperbolic motion selection on the whole hyperbolic space. -/
theorem liftShort_finite_motion_selection
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LipschitzWith 1 F) (hzero : ‖F 0‖ < 2)
    (R : Finset (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)))
    (hR : ∀ u, ‖u‖ < 2 → ∃ r ∈ R, F u = r u) :
    ∃ M : Finset (HyperbolicSpace n ≃ᵢ HyperbolicSpace n),
      ∀ x, ∃ m ∈ M, liftShort F hF hzero x = m x := by
  classical
  refine ⟨R.image affineMotion, ?_⟩
  intro x
  let u := pairLeft x.point (liftShort F hF hzero x).point
  have hu : ‖u‖ < 2 := by
    have hh := norm_pairLeft_add_norm_pairRight_lt_two x.point (liftShort F hF hzero x).point
    dsimp [u]
    linarith [norm_nonneg (pairRight x.point (liftShort F hF hzero x).point)]
  obtain ⟨r, hrR, hr⟩ := hR u hu
  exact ⟨affineMotion r, Finset.mem_image.mpr ⟨r, hrR, rfl⟩,
    liftShort_eq_affineMotion F hF hzero r x hr⟩

end BrehmApprox.Pogorelov
