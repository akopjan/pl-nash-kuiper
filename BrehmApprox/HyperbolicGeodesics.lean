module

public import BrehmApprox.HyperbolicFoldingGeometry

/-!
# Explicit geodesic segments in the genuine hyperbolic model

Lorentz boosts and the radial formula `(cosh t, sinh t • u)` provide actual
constant-speed geodesics. Their metric identities and containment in every
finite hyperbolic cell containing the endpoints are proved algebraically.
No length-space or geodesic axiom is added to the model.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

def radialLine (u : EuclideanSpace ℝ (Fin n)) (t : ℝ) : HyperbolicSpace n :=
  ⟨Real.sinh t • u⟩

lemma height_radialLine {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (t : ℝ) :
    Hyperboloid.height (radialLine u t).point = Real.cosh t := by
  have hs := Hyperboloid.height_sq (radialLine u t).point
  change Hyperboloid.height (radialLine u t).point ^ 2 = 1 + ‖Real.sinh t • u‖ ^ 2 at hs
  rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs] at hs
  nlinarith [Hyperboloid.height_nonneg (radialLine u t).point, Real.cosh_pos t, Real.cosh_sq t]

lemma lift_radialLine {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (t : ℝ) :
    lift (radialLine u t) = (Real.cosh t, Real.sinh t • u) := by
  apply Prod.ext
  · exact height_radialLine hu t
  · rfl

/-- The unit radial line is an isometric copy of the whole real line. -/
theorem radialLine_dist {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (s t : ℝ) :
    dist (radialLine u s) (radialLine u t) = |s - t| := by
  apply Real.cosh_injOn dist_nonneg (abs_nonneg _)
  rw [cosh_dist, Hyperboloid.coshDist, height_radialLine hu, height_radialLine hu,
    Real.cosh_abs, Real.cosh_sub]
  change Real.cosh s * Real.cosh t - ⟪Real.sinh s • u, Real.sinh t • u⟫_ℝ = _
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
  ring

theorem isometry_radialLine {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) :
    Isometry (radialLine u) := by
  apply Isometry.of_dist_eq
  intro s t
  simpa only [Real.dist_eq] using radialLine_dist hu s t

/-- Constant-speed geodesic, parametrized by `[0,1]`; the formula is total on
the real line and also covers coincident endpoints. -/
def geodesic (a b : HyperbolicSpace n) (t : ℝ) : HyperbolicSpace n :=
  boostBy (-a.point) (radialLine (radialDirection a b) (t * dist a b))

@[simp]
lemma geodesic_zero (a b : HyperbolicSpace n) : geodesic a b 0 = a := by
  have h := boostBy_neg_inverse a.point a
  rw [boostBy_self] at h
  simpa only [geodesic, zero_mul, radialLine, Real.sinh_zero, zero_smul] using h

@[simp]
lemma geodesic_one (a b : HyperbolicSpace n) : geodesic a b 1 = b := by
  have hrad : radialLine (radialDirection a b) (dist a b) = boostBy a.point b := by
    apply HyperbolicSpace.ext
    exact sinh_smul_radialDirection a b
  simpa only [geodesic, one_mul, hrad] using boostBy_neg_inverse a.point b

@[simp]
lemma geodesic_self (a : HyperbolicSpace n) (t : ℝ) : geodesic a a t = a := by
  have h := geodesic_zero a a
  simpa only [geodesic, dist_self, mul_zero] using h

/-- Exact distances along the segment, including the degenerate case. -/
theorem geodesic_dist (a b : HyperbolicSpace n) (s t : ℝ) :
    dist (geodesic a b s) (geodesic a b t) = |s - t| * dist a b := by
  by_cases hab : a = b
  · subst b
    simp
  · rw [geodesic, geodesic, (isometry_boostBy (-a.point)).dist_eq,
      radialLine_dist (radialDirection_norm a b (dist_pos.mpr hab)),
      ← sub_mul, abs_mul, abs_of_nonneg dist_nonneg]

theorem geodesic_lipschitz (a b : HyperbolicSpace n) :
    LipschitzWith ⟨dist a b, dist_nonneg⟩ (geodesic a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (geodesic a b s) (geodesic a b t) ≤ dist a b * dist s t
  rw [geodesic_dist, Real.dist_eq]
  exact le_of_eq (mul_comm _ _)

theorem continuous_geodesic (a b : HyperbolicSpace n) : Continuous (geodesic a b) :=
  (geodesic_lipschitz a b).continuous

def geodesicPath (a b : HyperbolicSpace n) : Path a b :=
  Path.ofLine (continuous_geodesic a b).continuousOn (geodesic_zero a b) (geodesic_one a b)

instance : PathConnectedSpace (HyperbolicSpace n) where
  nonempty := ⟨⟨0⟩⟩
  joined a b := ⟨geodesicPath a b⟩

/-- The usual positive Lorentz interpolation formula, proved from the actual
metric geodesic rather than postulated as a geodesic parametrization. -/
theorem lift_geodesic (a b : HyperbolicSpace n) (hab : a ≠ b) (t : ℝ) :
    lift (geodesic a b t) =
      (Real.sinh ((1 - t) * dist a b) / Real.sinh (dist a b)) • lift a +
      (Real.sinh (t * dist a b) / Real.sinh (dist a b)) • lift b := by
  have hd : 0 < dist a b := dist_pos.mpr hab
  have hs : Real.sinh (dist a b) ≠ 0 := (Real.sinh_pos_iff.mpr hd).ne'
  apply (Hyperboloid.boostLinearEquiv a.point).injective
  change Hyperboloid.boostLinear a.point (lift (geodesic a b t)) =
    Hyperboloid.boostLinear a.point _
  have hleft : Hyperboloid.boostLinear a.point (lift (geodesic a b t)) =
      lift (radialLine (radialDirection a b) (t * dist a b)) := by
    rw [geodesic, lift_boostBy]
    simpa only [neg_neg] using Hyperboloid.boostLinear_neg_inverse (-a.point)
      (lift (radialLine (radialDirection a b) (t * dist a b)))
  rw [hleft, map_add, map_smul, map_smul, boostLinear_lift_self,
    boosted_lift_radial_decomposition, lift_radialLine (radialDirection_norm a b hd)]
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one]
    have ht : (1 - t) * dist a b = dist a b - t * dist a b := by ring
    rw [ht, Real.sinh_sub]
    field_simp
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, smul_smul]
    congr 1
    exact (div_mul_cancel₀ _ hs).symm

/-- Equality in the triangle inequality places a point on the explicitly
constructed segment, with its uniquely determined distance parameter. -/
theorem eq_geodesic_of_dist_add (a b z : HyperbolicSpace n)
    (hab : a ≠ b) (hz : dist a z + dist z b = dist a b) :
    z = geodesic a b (dist a z / dist a b) := by
  have hD : 0 < dist a b := dist_pos.mpr hab
  by_cases haz : a = z
  · subst z
    simp
  · have hr : 0 < dist a z := dist_pos.mpr haz
    have hsD : Real.sinh (dist a b) ≠ 0 := (Real.sinh_pos_iff.mpr hD).ne'
    have hsr : Real.sinh (dist a z) ≠ 0 := (Real.sinh_pos_iff.mpr hr).ne'
    have hz' : dist z b = dist a b - dist a z := by linarith
    have hi : ⟪radialDirection a z, radialDirection a b⟫_ℝ = 1 := by
      rw [radial_gram_formula a z b hr hD, hz', Real.cosh_sub]
      field_simp
      ring
    have hdir : radialDirection a z = radialDirection a b := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      have hnorm := norm_sub_sq_real (radialDirection a z) (radialDirection a b)
      rw [radialDirection_norm a z hr, radialDirection_norm a b hD, hi] at hnorm
      nlinarith [norm_nonneg (radialDirection a z - radialDirection a b)]
    apply (boostEquiv a.point).injective
    change boostBy a.point z = boostBy a.point (geodesic a b (dist a z / dist a b))
    have hcancel (x : HyperbolicSpace n) : boostBy a.point (boostBy (-a.point) x) = x := by
      simpa only [neg_neg] using boostBy_neg_inverse (-a.point) x
    rw [geodesic, hcancel, div_mul_cancel₀ _ hD.ne']
    apply HyperbolicSpace.ext
    change radialVector a z = Real.sinh (dist a z) • radialDirection a b
    rw [← hdir, sinh_smul_radialDirection]

/-- A point is between two distinct endpoints precisely when it is on the
metric segment. This uses the true hyperbolic distance in both directions. -/
theorem dist_add_eq_iff_mem_geodesic (a b z : HyperbolicSpace n) (hab : a ≠ b) :
    dist a z + dist z b = dist a b ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1, z = geodesic a b t := by
  constructor
  · intro hz
    refine ⟨dist a z / dist a b, ⟨div_nonneg dist_nonneg dist_nonneg, ?_⟩,
      eq_geodesic_of_dist_add a b z hab hz⟩
    exact (div_le_one (dist_pos.mpr hab)).mpr (by linarith [dist_nonneg (x := z) (y := b)])
  · rintro ⟨t, ht, rfl⟩
    have hleft := geodesic_dist a b 0 t
    have hright := geodesic_dist a b t 1
    rw [geodesic_zero, zero_sub, abs_neg, abs_of_nonneg ht.1] at hleft
    rw [geodesic_one, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hright
    rw [hleft, hright]
    ring

end BrehmApprox.HyperbolicSpace

namespace BrehmApprox

open HyperbolicSpace

variable {n : ℕ}

/-- Every genuine hyperbolic finite cell contains the metric segment between
each pair of its points. The positive Lorentz weights are explicitly combined. -/
theorem geodesic_mem_hyperbolicCell {V : Finset (HyperbolicSpace n)}
    {a b : HyperbolicSpace n} (ha : a ∈ hyperbolicCell V) (hb : b ∈ hyperbolicCell V)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : geodesic a b t ∈ hyperbolicCell V := by
  classical
  by_cases hab : a = b
  · subst b
    simpa only [geodesic_self] using ha
  · obtain ⟨w, hw, A, hA, hrepA⟩ := ha
    obtain ⟨z, hz, B, hB, hrepB⟩ := hb
    let c : ℝ := Real.sinh ((1 - t) * dist a b) / Real.sinh (dist a b)
    let d : ℝ := Real.sinh (t * dist a b) / Real.sinh (dist a b)
    have hs : 0 ≤ Real.sinh (dist a b) := Real.sinh_nonneg_iff.mpr dist_nonneg
    have hc : 0 ≤ c := div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg (sub_nonneg.mpr ht1) dist_nonneg)) hs
    have hd : 0 ≤ d := div_nonneg
      (Real.sinh_nonneg_iff.mpr (mul_nonneg ht0 dist_nonneg)) hs
    refine ⟨fun v => c * (A⁻¹ * w v) + d * (B⁻¹ * z v), ?_, 1, zero_lt_one, ?_⟩
    · intro v hv
      exact add_nonneg (mul_nonneg hc (mul_nonneg (inv_nonneg.mpr hA.le) (hw v hv)))
        (mul_nonneg hd (mul_nonneg (inv_nonneg.mpr hB.le) (hz v hv)))
    · rw [one_smul, lift_geodesic a b hab]
      simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
        hrepA, hrepB]
      simp only [smul_smul, inv_mul_cancel₀ hA.ne', inv_mul_cancel₀ hB.ne', mul_one]
      rfl

theorem joinedIn_hyperbolicCell {V : Finset (HyperbolicSpace n)}
    {a b : HyperbolicSpace n} (ha : a ∈ hyperbolicCell V) (hb : b ∈ hyperbolicCell V) :
    JoinedIn (hyperbolicCell V) a b := by
  apply JoinedIn.ofLine (continuous_geodesic a b).continuousOn
    (geodesic_zero a b) (geodesic_one a b)
  rintro z ⟨t, ht, rfl⟩
  exact geodesic_mem_hyperbolicCell ha hb ht.1 ht.2

theorem isPathConnected_hyperbolicCell (V : Finset (HyperbolicSpace n))
    (hV : V.Nonempty) : IsPathConnected (hyperbolicCell V) := by
  rw [isPathConnected_iff]
  refine ⟨?_, fun _ ha _ hb => joinedIn_hyperbolicCell ha hb⟩
  obtain ⟨a, ha⟩ := hV
  exact ⟨a, mem_hyperbolicCell_of_mem ha⟩

end BrehmApprox
