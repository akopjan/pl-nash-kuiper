module

public import BrehmApprox.HyperbolicTopology

/-!
# Coordinate continuity and properness of hyperbolic space

The coordinate map is proved continuous from an explicit Lorentz boost
estimate.  Closed metric balls are compact; hence the model is complete.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

namespace BrehmApprox

namespace Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma boost_inverse_coefficient (z x : E) :
    (⟪z, x⟫_ℝ / (height z + 1) - height x) +
      ⟪z, boost z x⟫_ℝ / (height z + 1) + coshDist z x = 0 := by
  have hz : ‖z‖ ^ 2 = height z ^ 2 - 1 := by linarith [height_sq z]
  simp only [boost, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hz]
  unfold coshDist
  field_simp [height_add_one_ne_zero z]
  ring

lemma sub_eq_boost (z x : E) :
    x - z = boost z x +
      (⟪z, boost z x⟫_ℝ / (height z + 1) + (coshDist z x - 1)) • z := by
  have hc := boost_inverse_coefficient z x
  change x - z = (x + (⟪z, x⟫_ℝ / (height z + 1) - height x) • z) +
    (⟪z, boost z x⟫_ℝ / (height z + 1) + (coshDist z x - 1)) • z
  rw [add_assoc, ← add_smul]
  have hcoef : (⟪z, x⟫_ℝ / (height z + 1) - height x) +
      (⟪z, boost z x⟫_ℝ / (height z + 1) + (coshDist z x - 1)) = -1 := by linarith
  rw [hcoef, neg_one_smul, sub_eq_add_neg]

lemma coordinate_distance_bound (z x : E) :
    ‖x - z‖ ≤ (1 + ‖z‖ ^ 2 / (height z + 1)) * Real.sinh (distance x z) +
      ‖z‖ * (Real.cosh (distance x z) - 1) := by
  have hden : 0 < height z + 1 := by have := height_pos z; positivity
  have hnonneg : 0 ≤ coshDist z x - 1 := sub_nonneg.mpr (one_le_coshDist z x)
  have hcoef : |⟪z, boost z x⟫_ℝ / (height z + 1) + (coshDist z x - 1)| ≤
      ‖z‖ * ‖boost z x‖ / (height z + 1) + (coshDist z x - 1) := by
    calc
      _ ≤ |⟪z, boost z x⟫_ℝ / (height z + 1)| + |coshDist z x - 1| := abs_add_le _ _
      _ = |⟪z, boost z x⟫_ℝ| / (height z + 1) + (coshDist z x - 1) := by
        rw [abs_div, abs_of_pos hden, abs_of_nonneg hnonneg]
      _ ≤ _ := by
        have hh := div_le_div_of_nonneg_right (abs_real_inner_le_norm z (boost z x)) hden.le
        linarith
  have hb : ‖x - z‖ ≤ (1 + ‖z‖ ^ 2 / (height z + 1)) * ‖boost z x‖ +
      ‖z‖ * (coshDist z x - 1) := by
    rw [sub_eq_boost]
    calc
      _ ≤ ‖boost z x‖ + ‖(⟪z, boost z x⟫_ℝ / (height z + 1) +
          (coshDist z x - 1)) • z‖ := norm_add_le _ _
      _ = ‖boost z x‖ + |⟪z, boost z x⟫_ℝ / (height z + 1) +
          (coshDist z x - 1)| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖boost z x‖ + (‖z‖ * ‖boost z x‖ / (height z + 1) +
          (coshDist z x - 1)) * ‖z‖ := by
        have hh := mul_le_mul_of_nonneg_right hcoef (norm_nonneg z)
        linarith
      _ = _ := by ring
  rw [boost_norm_eq_sinh, ← cosh_distance, distance_comm z x] at hb
  exact hb

lemma distance_zero_right (x : E) : distance x 0 = Real.arsinh ‖x‖ := by
  have hc : coshDist x 0 = Real.cosh (Real.arsinh ‖x‖) := by
    simp [coshDist, height, Real.cosh_arsinh]
  rw [distance, hc, Real.arcosh_cosh (Real.arsinh_nonneg_iff.mpr (norm_nonneg x))]

end Hyperboloid

namespace HyperbolicSpace

variable {n : ℕ}

lemma continuous_point : Continuous (point : HyperbolicSpace n → EuclideanSpace ℝ (Fin n)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hc : Continuous (fun x : HyperbolicSpace n =>
      (1 + ‖z.point‖ ^ 2 / (Hyperboloid.height z.point + 1)) * Real.sinh (dist x z) +
        ‖z.point‖ * (Real.cosh (dist x z) - 1)) := by fun_prop
  have ht := hc.continuousAt (x := z)
  change Filter.Tendsto _ (𝓝 z) (𝓝 _) at ht
  simp only [dist_self, Real.sinh_zero, mul_zero, Real.cosh_zero, sub_self, add_zero] at ht
  apply squeeze_zero (fun _ => dist_nonneg) ?_ ht
  intro x
  exact Hyperboloid.coordinate_distance_bound z.point x.point

lemma continuous_klein : Continuous (klein : HyperbolicSpace n → EuclideanSpace ℝ (Fin n)) := by
  unfold klein
  exact ((Hyperboloid.continuous_height.comp continuous_point).fun_inv₀
    (fun x => ne_of_gt (Hyperboloid.height_pos x.point))).fun_smul continuous_point

/-- The Klein coordinate bijection. -/
def kleinEquiv : HyperbolicSpace n ≃ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 where
  toFun x := ⟨klein x, by simpa using norm_klein_lt_one x⟩
  invFun p := fromKlein p.val
  left_inv x := fromKlein_klein x
  right_inv p := by
    apply Subtype.ext
    exact klein_fromKlein (by simpa only [Metric.mem_ball, dist_zero_right] using p.property)

/-- The Klein model is homeomorphic to the genuine hyperbolic metric model. -/
def kleinHomeomorph : HyperbolicSpace n ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  refine { toEquiv := kleinEquiv, continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact continuous_klein.subtype_mk _
  · exact continuousOn_fromKlein.comp_continuous continuous_subtype_val (fun p => p.property)

lemma dist_origin (x : HyperbolicSpace n) : dist x ⟨0⟩ = Real.arsinh ‖x.point‖ :=
  Hyperboloid.distance_zero_right x.point

lemma closedBall_origin_eq_image (R : ℝ) :
    Metric.closedBall (⟨0⟩ : HyperbolicSpace n) R =
      HyperbolicSpace.mk '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sinh R) := by
  ext x
  constructor
  · intro hx
    refine ⟨x.point, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_origin, ← Real.arsinh_sinh R, Real.arsinh_le_arsinh] at hx
    simpa using hx
  · rintro ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, dist_origin, ← Real.arsinh_sinh R, Real.arsinh_le_arsinh]
    simpa using hp

lemma isCompact_closedBall_origin (R : ℝ) :
    IsCompact (Metric.closedBall (⟨0⟩ : HyperbolicSpace n) R) := by
  rw [closedBall_origin_eq_image]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sinh R)).image continuous_mk

instance : ProperSpace (HyperbolicSpace n) :=
  ProperSpace.of_seq_closedBall (x := (⟨0⟩ : HyperbolicSpace n)) Filter.tendsto_id
    (Filter.Eventually.of_forall isCompact_closedBall_origin)

example : CompleteSpace (HyperbolicSpace n) := inferInstance

end HyperbolicSpace
end BrehmApprox
