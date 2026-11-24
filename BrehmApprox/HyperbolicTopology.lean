module

public import BrehmApprox.HyperbolicRigidity

/-!
# Topology and compact polyhedra in the hyperboloid model

This file connects the genuine hyperbolic metric to spatial and Klein
coordinates.  In particular, finite positive Lorentz hulls are compact.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

namespace BrehmApprox

namespace Hyperboloid

variable {E : Type*} [NormedAddCommGroup E]

lemma continuous_height : Continuous (height : E → ℝ) := by
  unfold height
  fun_prop

variable [InnerProductSpace ℝ E]

lemma continuous_coshDist : Continuous (fun p : E × E => coshDist p.1 p.2) := by
  unfold coshDist
  exact ((continuous_height.comp continuous_fst).mul
    (continuous_height.comp continuous_snd)).sub (continuous_fst.inner continuous_snd)

lemma continuous_distance : Continuous (fun p : E × E => distance p.1 p.2) := by
  exact Real.continuousOn_arcosh.comp_continuous continuous_coshDist
    (fun p => one_le_coshDist p.1 p.2)

end Hyperboloid

namespace HyperbolicSpace

variable {n : ℕ}

lemma continuous_mk : Continuous (HyperbolicSpace.mk :
    EuclideanSpace ℝ (Fin n) → HyperbolicSpace n) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have h := (Hyperboloid.continuous_distance.comp
    (continuous_id.prodMk (continuous_const : Continuous
      (fun _ : EuclideanSpace ℝ (Fin n) => x)))).continuousAt (x := x)
  change Filter.Tendsto (fun y => Hyperboloid.distance y x) (𝓝 x)
    (𝓝 (Hyperboloid.distance x x)) at h
  change Filter.Tendsto (fun y => Hyperboloid.distance y x) (𝓝 x) (𝓝 0)
  simpa only [Hyperboloid.distance_self] using h

/-- Klein coordinates in the open Euclidean unit ball. -/
def klein (x : HyperbolicSpace n) : EuclideanSpace ℝ (Fin n) :=
  (Hyperboloid.height x.point)⁻¹ • x.point

lemma norm_klein_lt_one (x : HyperbolicSpace n) : ‖klein x‖ < 1 := by
  rw [klein, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Hyperboloid.height_pos x.point))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (Hyperboloid.height_pos x.point)).mpr (Hyperboloid.norm_lt_height x.point)

/-- Inverse Klein coordinates; statements about this function use the open unit
ball, where the denominator is strictly positive. -/
def fromKlein (p : EuclideanSpace ℝ (Fin n)) : HyperbolicSpace n :=
  ⟨(Real.sqrt (1 - ‖p‖ ^ 2))⁻¹ • p⟩

lemma klein_denominator_pos {p : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ < 1) :
    0 < Real.sqrt (1 - ‖p‖ ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [norm_nonneg p]

lemma height_fromKlein {p : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ < 1) :
    Hyperboloid.height (fromKlein p).point = (Real.sqrt (1 - ‖p‖ ^ 2))⁻¹ := by
  let r : ℝ := Real.sqrt (1 - ‖p‖ ^ 2)
  have hr : 0 < r := klein_denominator_pos hp
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrsq : r ^ 2 = 1 - ‖p‖ ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt]
    nlinarith [norm_nonneg p]
  have hnorm : ‖(fromKlein p).point‖ ^ 2 = r⁻¹ ^ 2 * ‖p‖ ^ 2 := by
    simp only [fromKlein, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rfl
  have hs := Hyperboloid.height_sq (fromKlein p).point
  rw [hnorm] at hs
  have hs' : Hyperboloid.height (fromKlein p).point ^ 2 = r⁻¹ ^ 2 := by
    rw [hs]
    field_simp [hr0]
    nlinarith [hrsq]
  have hp' := Hyperboloid.height_nonneg (fromKlein p).point
  have hr' : 0 < r⁻¹ := inv_pos.mpr hr
  change Hyperboloid.height (fromKlein p).point = r⁻¹
  nlinarith

lemma klein_fromKlein {p : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ < 1) :
    klein (fromKlein p) = p := by
  rw [klein, height_fromKlein hp, inv_inv]
  change Real.sqrt (1 - ‖p‖ ^ 2) • ((Real.sqrt (1 - ‖p‖ ^ 2))⁻¹ • p) = p
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (klein_denominator_pos hp)), one_smul]

lemma fromKlein_klein (x : HyperbolicSpace n) : fromKlein (klein x) = x := by
  apply HyperbolicSpace.ext
  have hh : Hyperboloid.height (fromKlein (klein x)).point = Hyperboloid.height x.point := by
    have hk := klein_fromKlein (norm_klein_lt_one x)
    have ht := Hyperboloid.height_sq x.point
    have hpos := Hyperboloid.height_pos x.point
    rw [height_fromKlein (norm_klein_lt_one x)]
    have hnorm : ‖klein x‖ ^ 2 = ‖x.point‖ ^ 2 / Hyperboloid.height x.point ^ 2 := by
      simp only [klein, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp
    have heq : 1 - ‖klein x‖ ^ 2 = (Hyperboloid.height x.point)⁻¹ ^ 2 := by
      rw [hnorm]
      field_simp [ne_of_gt hpos]
      nlinarith [ht]
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_inv]
  have hk := klein_fromKlein (norm_klein_lt_one x)
  change (Hyperboloid.height (fromKlein (klein x)).point)⁻¹ •
      (fromKlein (klein x)).point = (Hyperboloid.height x.point)⁻¹ • x.point at hk
  rw [hh] at hk
  have hs := congrArg (fun v => Hyperboloid.height x.point • v) hk
  simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt (Hyperboloid.height_pos x.point)),
    one_smul] using hs

lemma continuousOn_fromKlein : ContinuousOn
    (fromKlein : EuclideanSpace ℝ (Fin n) → HyperbolicSpace n) (Metric.ball 0 1) := by
  apply continuous_mk.comp_continuousOn
  have hr : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) =>
      Real.sqrt (1 - ‖p‖ ^ 2)) (Metric.ball 0 1) := by fun_prop
  have hi := hr.fun_inv₀ (fun p hp => ne_of_gt (klein_denominator_pos (by simpa using hp)))
  exact hi.fun_smul continuous_id.continuousOn

lemma klein_injective : Function.Injective (klein : HyperbolicSpace n → _) := by
  intro x y h
  have hh := congrArg fromKlein h
  simpa only [fromKlein_klein] using hh

end HyperbolicSpace

variable {n : ℕ}

lemma hyperbolic_lift_sum_eq_iff {V : Finset (HyperbolicSpace n)}
    {w : HyperbolicSpace n → ℝ} {a : ℝ} {x : HyperbolicSpace n} :
    (∑ v ∈ V, w v • HyperbolicSpace.lift v = a • HyperbolicSpace.lift x) ↔
    (∑ v ∈ V, w v * Hyperboloid.height v.point = a * Hyperboloid.height x.point) ∧
    (∑ v ∈ V, w v • v.point = a • x.point) := by
  constructor
  · intro h
    constructor
    · have ht := congrArg (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))) h
      simpa only [map_sum, map_smul, LinearMap.fst_apply, HyperbolicSpace.lift,
        smul_eq_mul] using ht
    · have hp := congrArg (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) h
      simpa only [map_sum, map_smul, LinearMap.snd_apply, HyperbolicSpace.lift] using hp
  · rintro ⟨ht, hp⟩
    apply Prod.ext
    · change (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))
        (∑ v ∈ V, w v • HyperbolicSpace.lift v) =
        (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))) (a • HyperbolicSpace.lift x)
      simpa only [map_sum, map_smul, LinearMap.fst_apply, HyperbolicSpace.lift,
        smul_eq_mul] using ht
    · change (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n)))
        (∑ v ∈ V, w v • HyperbolicSpace.lift v) =
        (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) (a • HyperbolicSpace.lift x)
      simpa only [map_sum, map_smul, LinearMap.snd_apply, HyperbolicSpace.lift] using hp

lemma mem_hyperbolicCell_iff_klein_mem_convexHull (V : Finset (HyperbolicSpace n))
    (x : HyperbolicSpace n) :
    x ∈ hyperbolicCell V ↔ HyperbolicSpace.klein x ∈
      convexHull ℝ ((V.image HyperbolicSpace.klein : Finset (EuclideanSpace ℝ (Fin n))) : Set _) := by
  classical
  constructor
  · rintro ⟨w, hw, a, ha, hrep⟩
    obtain ⟨ht, hp⟩ := hyperbolic_lift_sum_eq_iff.mp hrep
    let b : HyperbolicSpace n → ℝ := fun v =>
      w v * Hyperboloid.height v.point / (a * Hyperboloid.height x.point)
    have hb : ∀ v ∈ V, 0 ≤ b v := by
      intro v hv
      exact div_nonneg (mul_nonneg (hw v hv) (Hyperboloid.height_nonneg v.point))
        (mul_pos ha (Hyperboloid.height_pos x.point)).le
    have hbs : ∑ v ∈ V, b v = 1 := by
      simp only [b, ← Finset.sum_div]
      rw [ht, div_self (ne_of_gt (mul_pos ha (Hyperboloid.height_pos x.point)))]
    have hbp : ∑ v ∈ V, b v • HyperbolicSpace.klein v = HyperbolicSpace.klein x := by
      calc
        _ = (a * Hyperboloid.height x.point)⁻¹ • (∑ v ∈ V, w v • v.point) := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro v hv
          rw [HyperbolicSpace.klein, smul_smul, smul_smul]
          congr 1
          dsimp [b]
          field_simp [ne_of_gt (Hyperboloid.height_pos v.point)]
        _ = HyperbolicSpace.klein x := by
          rw [hp, smul_smul, HyperbolicSpace.klein]
          congr 1
          field_simp [ne_of_gt ha, ne_of_gt (Hyperboloid.height_pos x.point)]
    have hm := V.centerMass_mem_convexHull
      (s := ((V.image HyperbolicSpace.klein : Finset (EuclideanSpace ℝ (Fin n))) : Set _))
      (z := HyperbolicSpace.klein) hb (by rw [hbs]; exact zero_lt_one)
      (fun v hv => (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, rfl⟩)))
    rw [Finset.centerMass_eq_of_sum_1 _ _ hbs, hbp] at hm
    exact hm
  · intro hx
    obtain ⟨b, hb, hbs, hbp⟩ := Finset.mem_convexHull'.mp hx
    have hinj : ∀ u ∈ V, ∀ v ∈ V, HyperbolicSpace.klein u = HyperbolicSpace.klein v → u = v :=
      fun _ _ _ _ h => HyperbolicSpace.klein_injective h
    rw [Finset.sum_image hinj] at hbs hbp
    refine ⟨fun v => b (HyperbolicSpace.klein v) / Hyperboloid.height v.point, ?_,
      (Hyperboloid.height x.point)⁻¹, inv_pos.mpr (Hyperboloid.height_pos x.point), ?_⟩
    · intro v hv
      exact div_nonneg (hb _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
        (Hyperboloid.height_nonneg v.point)
    · apply hyperbolic_lift_sum_eq_iff.mpr
      constructor
      · calc
          _ = ∑ v ∈ V, b (HyperbolicSpace.klein v) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact div_mul_cancel₀ _ (ne_of_gt (Hyperboloid.height_pos v.point))
          _ = 1 := hbs
          _ = _ := (inv_mul_cancel₀ (ne_of_gt (Hyperboloid.height_pos x.point))).symm
      · simpa only [HyperbolicSpace.klein, div_eq_mul_inv, mul_smul] using hbp

lemma hyperbolic_klein_hull_subset_ball (V : Finset (HyperbolicSpace n)) :
    convexHull ℝ ((V.image HyperbolicSpace.klein : Finset (EuclideanSpace ℝ (Fin n))) :
      Set (EuclideanSpace ℝ (Fin n))) ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  apply convexHull_min
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    simpa using HyperbolicSpace.norm_klein_lt_one v
  · exact convex_ball 0 1

lemma hyperbolicCell_eq_fromKlein_image (V : Finset (HyperbolicSpace n)) :
    hyperbolicCell V = HyperbolicSpace.fromKlein ''
      convexHull ℝ ((V.image HyperbolicSpace.klein : Finset (EuclideanSpace ℝ (Fin n))) : Set _) := by
  ext x
  constructor
  · intro hx
    exact ⟨HyperbolicSpace.klein x, (mem_hyperbolicCell_iff_klein_mem_convexHull V x).mp hx,
      HyperbolicSpace.fromKlein_klein x⟩
  · rintro ⟨p, hp, rfl⟩
    apply (mem_hyperbolicCell_iff_klein_mem_convexHull V _).mpr
    rwa [HyperbolicSpace.klein_fromKlein
      (by simpa using hyperbolic_klein_hull_subset_ball V hp)]

lemma isCompact_hyperbolicCell (V : Finset (HyperbolicSpace n)) : IsCompact (hyperbolicCell V) := by
  rw [hyperbolicCell_eq_fromKlein_image]
  exact ((V.image HyperbolicSpace.klein).finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
    (HyperbolicSpace.continuousOn_fromKlein.mono (hyperbolic_klein_hull_subset_ball V))

end BrehmApprox
