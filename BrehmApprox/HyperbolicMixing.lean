module

public import BrehmApprox.HyperbolicConvexProjection

/-!
# Positive Lorentz mixtures and the nearest-point variational inequality

For `t ≥ 0`, the normalized Lorentz vector `lift p + t • lift q` represents
a point of the geodesic segment from `p` to `q`.  Its membership in every
hyperbolic cell containing the endpoints and its exact distance formula are
proved algebraically.  Taking `t ↓ 0` proves the right-angle inequality for
the actual nearest projection, without a face or differential-geometric axiom.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace Topology
open Filter

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

def mixScale (p q : HyperbolicSpace n) (t : ℝ) : ℝ :=
  Real.sqrt (1 + 2 * t * Real.cosh (dist p q) + t ^ 2)

lemma mixScale_pos (p q : HyperbolicSpace n) {t : ℝ} (ht : 0 ≤ t) :
    0 < mixScale p q t := by
  unfold mixScale
  apply Real.sqrt_pos.mpr
  have hc := Real.cosh_pos (dist p q)
  nlinarith [mul_nonneg ht hc.le, sq_nonneg t]

lemma mixScale_sq (p q : HyperbolicSpace n) {t : ℝ} (ht : 0 ≤ t) :
    mixScale p q t ^ 2 = 1 + 2 * t * Real.cosh (dist p q) + t ^ 2 := by
  unfold mixScale
  rw [Real.sq_sqrt]
  have hc := Real.cosh_pos (dist p q)
  nlinarith [mul_nonneg ht hc.le, sq_nonneg t]

def positiveMix (p q : HyperbolicSpace n) (t : ℝ) : HyperbolicSpace n :=
  ⟨(mixScale p q t)⁻¹ • (p.point + t • q.point)⟩

lemma height_positiveMix (p q : HyperbolicSpace n) {t : ℝ} (ht : 0 ≤ t) :
    Hyperboloid.height (positiveMix p q t).point =
      (Hyperboloid.height p.point + t * Hyperboloid.height q.point) / mixScale p q t := by
  let D := mixScale p q t
  have hD : 0 < D := mixScale_pos p q ht
  have hsq : (Hyperboloid.height p.point + t * Hyperboloid.height q.point) ^ 2 =
      D ^ 2 + ‖p.point + t • q.point‖ ^ 2 := by
    dsimp only [D]
    rw [mixScale_sq p q ht, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht, real_inner_smul_right, cosh_dist]
    unfold Hyperboloid.coshDist
    nlinarith [Hyperboloid.height_sq p.point, Hyperboloid.height_sq q.point]
  have hm := Hyperboloid.height_sq (positiveMix p q t).point
  change Hyperboloid.height (positiveMix p q t).point ^ 2 =
    1 + ‖D⁻¹ • (p.point + t • q.point)‖ ^ 2 at hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)] at hm
  have hs : ((Hyperboloid.height p.point + t * Hyperboloid.height q.point) / D) ^ 2 =
      1 + (D⁻¹ * ‖p.point + t • q.point‖) ^ 2 := by
    field_simp
    nlinarith
  have hp : 0 < (Hyperboloid.height p.point + t * Hyperboloid.height q.point) / D := by
    apply div_pos _ hD
    have hp := Hyperboloid.height_pos p.point
    have hq := Hyperboloid.height_pos q.point
    nlinarith
  change Hyperboloid.height (positiveMix p q t).point =
    (Hyperboloid.height p.point + t * Hyperboloid.height q.point) / D
  nlinarith [Hyperboloid.height_nonneg (positiveMix p q t).point]

lemma lift_positiveMix (p q : HyperbolicSpace n) {t : ℝ} (ht : 0 ≤ t) :
    lift (positiveMix p q t) = (mixScale p q t)⁻¹ • (lift p + t • lift q) := by
  apply Prod.ext
  · change Hyperboloid.height (positiveMix p q t).point =
      (mixScale p q t)⁻¹ * (Hyperboloid.height p.point + t * Hyperboloid.height q.point)
    rw [height_positiveMix p q ht]
    ring
  · rfl

lemma scale_smul_lift_positiveMix (p q : HyperbolicSpace n) {t : ℝ} (ht : 0 ≤ t) :
    mixScale p q t • lift (positiveMix p q t) = lift p + t • lift q := by
  rw [lift_positiveMix p q ht, smul_smul, mul_inv_cancel₀ (mixScale_pos p q ht).ne', one_smul]

lemma cosh_dist_positiveMix (x p q : HyperbolicSpace n) {t : ℝ} (ht : 0 ≤ t) :
    Real.cosh (dist x (positiveMix p q t)) =
      (Real.cosh (dist x p) + t * Real.cosh (dist x q)) / mixScale p q t := by
  have h := congrArg (coshFunctional x) (scale_smul_lift_positiveMix p q ht)
  simp only [map_smul, map_add, coshFunctional_lift, smul_eq_mul] at h
  apply (eq_div_iff (mixScale_pos p q ht).ne').mpr
  nlinarith

end BrehmApprox.HyperbolicSpace

namespace BrehmApprox

variable {n : ℕ}

theorem positiveMix_mem_hyperbolicCell {V : Finset (HyperbolicSpace n)}
    {p q : HyperbolicSpace n} (hp : p ∈ hyperbolicCell V) (hq : q ∈ hyperbolicCell V)
    {t : ℝ} (ht : 0 ≤ t) : HyperbolicSpace.positiveMix p q t ∈ hyperbolicCell V := by
  classical
  obtain ⟨w, hw, a, ha, hrep⟩ := hp
  obtain ⟨z, hz, b, hb, hrep'⟩ := hq
  refine ⟨fun v => a⁻¹ * w v + t * (b⁻¹ * z v), ?_,
    HyperbolicSpace.mixScale p q t, HyperbolicSpace.mixScale_pos p q ht, ?_⟩
  · intro v hv
    exact add_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) (hw v hv))
      (mul_nonneg ht (mul_nonneg (inv_nonneg.mpr hb.le) (hz v hv)))
  · rw [HyperbolicSpace.scale_smul_lift_positiveMix p q ht]
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
      hrep, hrep']
    simp only [smul_smul, inv_mul_cancel₀ ha.ne', inv_mul_cancel₀ hb.ne', one_smul]

/-- The hyperbolic right-angle variational inequality for a true distance
minimizer in a cell.  The limiting argument is explicit and uses only positive
Lorentz mixtures remaining inside the same cell. -/
theorem hyperbolicCell_nearest_cosh_inequality {V : Finset (HyperbolicSpace n)}
    (x : HyperbolicSpace n) {p q : HyperbolicSpace n}
    (hp : p ∈ hyperbolicCell V) (hq : q ∈ hyperbolicCell V)
    (hmin : ∀ z ∈ hyperbolicCell V, dist x p ≤ dist x z) :
    Real.cosh (dist x p) * Real.cosh (dist p q) ≤ Real.cosh (dist x q) := by
  let A := Real.cosh (dist x p)
  let B := Real.cosh (dist x q)
  let C := Real.cosh (dist p q)
  have hA : 0 < A := Real.cosh_pos _
  have hB : 0 < B := Real.cosh_pos _
  have hbound (t : ℝ) (ht : 0 < t) :
      2 * A ^ 2 * C ≤ 2 * A * B + t * (B ^ 2 - A ^ 2) := by
    have hd := hmin (HyperbolicSpace.positiveMix p q t)
      (positiveMix_mem_hyperbolicCell hp hq ht.le)
    have hh : A ≤ Real.cosh (dist x (HyperbolicSpace.positiveMix p q t)) := by
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_of_nonneg dist_nonneg] using hd
    rw [HyperbolicSpace.cosh_dist_positiveMix x p q ht.le] at hh
    change A ≤ (A + t * B) / HyperbolicSpace.mixScale p q t at hh
    have hm := (le_div_iff₀ (HyperbolicSpace.mixScale_pos p q ht.le)).mp hh
    have hsq : A ^ 2 * (HyperbolicSpace.mixScale p q t) ^ 2 ≤ (A + t * B) ^ 2 := by
      have hleft : 0 ≤ A * HyperbolicSpace.mixScale p q t :=
        mul_nonneg hA.le (HyperbolicSpace.mixScale_pos p q ht.le).le
      nlinarith
    rw [HyperbolicSpace.mixScale_sq p q ht.le] at hsq
    change A ^ 2 * (1 + 2 * t * C + t ^ 2) ≤ (A + t * B) ^ 2 at hsq
    have hdiv : t * (2 * A ^ 2 * C) ≤ t * (2 * A * B + t * (B ^ 2 - A ^ 2)) := by
      nlinarith
    exact le_of_mul_le_mul_left hdiv ht
  have hlim : Tendsto (fun t : ℝ => 2 * A * B + t * (B ^ 2 - A ^ 2))
      (𝓝[>] 0) (𝓝 (2 * A * B)) := by
    have hc : ContinuousAt (fun t : ℝ => 2 * A * B + t * (B ^ 2 - A ^ 2)) 0 := by
      fun_prop
    simpa only [zero_mul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hle : 2 * A ^ 2 * C ≤ 2 * A * B :=
    ge_of_tendsto hlim (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hbound t ht)
  change A * C ≤ B
  nlinarith

end BrehmApprox
