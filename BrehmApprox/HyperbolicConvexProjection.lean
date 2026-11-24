module

public import BrehmApprox.HyperbolicFoldingGeometry

/-!
# Nearest points of actual compact hyperbolic polytopes

The Lorentz midpoint belongs to the positive hull of the endpoints.  Its exact
cosh-distance formula gives uniqueness of a distance minimizer on every
hyperbolic polytope.  Existence uses the already proved compactness of the
actual cells, and continuity follows from the positive gap on a compact set
away from the unique minimizer.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

def midpointScale (p q : HyperbolicSpace n) : ℝ :=
  Real.sqrt (2 + 2 * Real.cosh (dist p q))

lemma midpointScale_pos (p q : HyperbolicSpace n) : 0 < midpointScale p q := by
  unfold midpointScale
  apply Real.sqrt_pos.mpr
  have h := Real.cosh_pos (dist p q)
  linarith

lemma midpointScale_sq (p q : HyperbolicSpace n) :
    midpointScale p q ^ 2 = 2 + 2 * Real.cosh (dist p q) := by
  unfold midpointScale
  rw [Real.sq_sqrt]
  have h := Real.cosh_pos (dist p q)
  linarith

/-- The true midpoint of the short hyperbolic geodesic, in spatial coordinates. -/
def midpoint (p q : HyperbolicSpace n) : HyperbolicSpace n :=
  ⟨(midpointScale p q)⁻¹ • (p.point + q.point)⟩

lemma height_midpoint (p q : HyperbolicSpace n) :
    Hyperboloid.height (midpoint p q).point =
      (Hyperboloid.height p.point + Hyperboloid.height q.point) / midpointScale p q := by
  let D := midpointScale p q
  have hD : 0 < D := midpointScale_pos p q
  have hsq : (Hyperboloid.height p.point + Hyperboloid.height q.point) ^ 2 =
      D ^ 2 + ‖p.point + q.point‖ ^ 2 := by
    dsimp only [D]
    rw [midpointScale_sq, norm_add_sq_real, cosh_dist]
    unfold Hyperboloid.coshDist
    nlinarith [Hyperboloid.height_sq p.point, Hyperboloid.height_sq q.point]
  have hm := Hyperboloid.height_sq (midpoint p q).point
  change Hyperboloid.height (midpoint p q).point ^ 2 =
    1 + ‖D⁻¹ • (p.point + q.point)‖ ^ 2 at hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)] at hm
  have ht : ((Hyperboloid.height p.point + Hyperboloid.height q.point) / D) ^ 2 =
      1 + (D⁻¹ * ‖p.point + q.point‖) ^ 2 := by
    field_simp
    nlinarith
  have hp : 0 < (Hyperboloid.height p.point + Hyperboloid.height q.point) / D :=
    div_pos (add_pos (Hyperboloid.height_pos p.point) (Hyperboloid.height_pos q.point)) hD
  change Hyperboloid.height (midpoint p q).point =
    (Hyperboloid.height p.point + Hyperboloid.height q.point) / D
  nlinarith [Hyperboloid.height_nonneg (midpoint p q).point]

lemma lift_midpoint (p q : HyperbolicSpace n) :
    lift (midpoint p q) = (midpointScale p q)⁻¹ • (lift p + lift q) := by
  apply Prod.ext
  · change Hyperboloid.height (midpoint p q).point =
      (midpointScale p q)⁻¹ * (Hyperboloid.height p.point + Hyperboloid.height q.point)
    rw [height_midpoint]
    ring
  · rfl

lemma scale_smul_lift_midpoint (p q : HyperbolicSpace n) :
    midpointScale p q • lift (midpoint p q) = lift p + lift q := by
  rw [lift_midpoint, smul_smul, mul_inv_cancel₀ (midpointScale_pos p q).ne', one_smul]

lemma cosh_dist_midpoint (x p q : HyperbolicSpace n) :
    Real.cosh (dist x (midpoint p q)) =
      (Real.cosh (dist x p) + Real.cosh (dist x q)) / midpointScale p q := by
  have h := congrArg (coshFunctional x) (scale_smul_lift_midpoint p q)
  simp only [map_smul, map_add, coshFunctional_lift, smul_eq_mul] at h
  apply (eq_div_iff (midpointScale_pos p q).ne').mpr
  nlinarith

lemma midpointScale_gt_two {p q : HyperbolicSpace n} (hpq : p ≠ q) :
    2 < midpointScale p q := by
  have hc := Real.one_lt_cosh.mpr (ne_of_gt (dist_pos.mpr hpq))
  nlinarith [midpointScale_sq p q, midpointScale_pos p q]

end BrehmApprox.HyperbolicSpace

namespace BrehmApprox

variable {n : ℕ}

theorem midpoint_mem_hyperbolicCell {V : Finset (HyperbolicSpace n)}
    {p q : HyperbolicSpace n} (hp : p ∈ hyperbolicCell V) (hq : q ∈ hyperbolicCell V) :
    HyperbolicSpace.midpoint p q ∈ hyperbolicCell V := by
  classical
  obtain ⟨w, hw, a, ha, hrep⟩ := hp
  obtain ⟨z, hz, b, hb, hrep'⟩ := hq
  refine ⟨fun v => a⁻¹ * w v + b⁻¹ * z v, ?_,
    HyperbolicSpace.midpointScale p q, HyperbolicSpace.midpointScale_pos p q, ?_⟩
  · intro v hv
    exact add_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) (hw v hv))
      (mul_nonneg (inv_nonneg.mpr hb.le) (hz v hv))
  · rw [HyperbolicSpace.scale_smul_lift_midpoint]
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
      hrep, hrep']
    simp only [smul_smul, inv_mul_cancel₀ ha.ne', inv_mul_cancel₀ hb.ne', one_smul]

theorem hyperbolicCell_nearest_unique {V : Finset (HyperbolicSpace n)}
    (x : HyperbolicSpace n) {p q : HyperbolicSpace n}
    (hp : p ∈ hyperbolicCell V) (hq : q ∈ hyperbolicCell V)
    (hpmin : ∀ z ∈ hyperbolicCell V, dist x p ≤ dist x z)
    (hqmin : ∀ z ∈ hyperbolicCell V, dist x q ≤ dist x z) : p = q := by
  by_contra hpq
  have hdist : dist x p = dist x q := le_antisymm (hpmin q hq) (hqmin p hp)
  have hmid := hpmin (HyperbolicSpace.midpoint p q) (midpoint_mem_hyperbolicCell hp hq)
  have hcosh : Real.cosh (dist x p) ≤
      Real.cosh (dist x (HyperbolicSpace.midpoint p q)) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg] using hmid
  rw [HyperbolicSpace.cosh_dist_midpoint, ← hdist] at hcosh
  have hD := HyperbolicSpace.midpointScale_gt_two hpq
  have hc := Real.cosh_pos (dist x p)
  have hmul := (le_div_iff₀ (HyperbolicSpace.midpointScale_pos p q)).mp hcosh
  nlinarith

theorem exists_hyperbolicCell_nearest (V : Finset (HyperbolicSpace n))
    (hV : V.Nonempty) (x : HyperbolicSpace n) :
    ∃ p ∈ hyperbolicCell V, ∀ z ∈ hyperbolicCell V, dist x p ≤ dist x z := by
  have hne : (hyperbolicCell V).Nonempty := by
    obtain ⟨v, hv⟩ := hV
    exact ⟨v, mem_hyperbolicCell_of_mem hv⟩
  exact (isCompact_hyperbolicCell V).exists_isMinOn hne (continuous_const.dist continuous_id).continuousOn

/-- The actual, uniquely specified nearest point of a nonempty hyperbolic cell. -/
def hyperbolicCellProjection (V : Finset (HyperbolicSpace n)) (hV : V.Nonempty)
    (x : HyperbolicSpace n) : HyperbolicSpace n :=
  (exists_hyperbolicCell_nearest V hV x).choose

lemma hyperbolicCellProjection_mem (V : Finset (HyperbolicSpace n)) (hV : V.Nonempty)
    (x : HyperbolicSpace n) : hyperbolicCellProjection V hV x ∈ hyperbolicCell V :=
  (exists_hyperbolicCell_nearest V hV x).choose_spec.1

lemma hyperbolicCellProjection_nearest (V : Finset (HyperbolicSpace n)) (hV : V.Nonempty)
    (x : HyperbolicSpace n) {z : HyperbolicSpace n} (hz : z ∈ hyperbolicCell V) :
    dist x (hyperbolicCellProjection V hV x) ≤ dist x z :=
  (exists_hyperbolicCell_nearest V hV x).choose_spec.2 z hz

lemma hyperbolicCellProjection_unique (V : Finset (HyperbolicSpace n)) (hV : V.Nonempty)
    (x : HyperbolicSpace n) {z : HyperbolicSpace n} (hz : z ∈ hyperbolicCell V)
    (hmin : dist x z ≤ dist x (hyperbolicCellProjection V hV x)) :
    z = hyperbolicCellProjection V hV x := by
  apply hyperbolicCell_nearest_unique x hz (hyperbolicCellProjection_mem V hV x)
  · intro w hw
    exact hmin.trans (hyperbolicCellProjection_nearest V hV x hw)
  · intro w hw
    exact hyperbolicCellProjection_nearest V hV x hw

lemma hyperbolicCellProjection_fix (V : Finset (HyperbolicSpace n)) (hV : V.Nonempty)
    {x : HyperbolicSpace n} (hx : x ∈ hyperbolicCell V) :
    hyperbolicCellProjection V hV x = x := by
  apply Eq.symm
  apply hyperbolicCellProjection_unique V hV x hx
  simp only [dist_self, dist_nonneg]

/-- Continuity is proved from compactness and unique minimization, with no
regularity or nonexpansion assumption on the chosen map. -/
theorem continuous_hyperbolicCellProjection (V : Finset (HyperbolicSpace n)) (hV : V.Nonempty) :
    Continuous (hyperbolicCellProjection V hV) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let p := hyperbolicCellProjection V hV x
  let K : Set (HyperbolicSpace n) := hyperbolicCell V ∩ {z | ε ≤ dist z p}
  have hK : IsCompact K :=
    (isCompact_hyperbolicCell V).inter_right (isClosed_le continuous_const
      (continuous_id.dist continuous_const))
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne (continuous_const.dist continuous_id).continuousOn
    have hpz : dist x p < dist x z := by
      have hle := hyperbolicCellProjection_nearest V hV x hz.1
      apply lt_of_le_of_ne hle
      intro heq
      have hzp := hyperbolicCellProjection_unique V hV x hz.1 heq.symm.le
      have hε' := hz.2
      change ε ≤ dist z p at hε'
      change z = p at hzp
      rw [hzp, dist_self] at hε'
      exact (not_le_of_gt hε) hε'
    let δ := (dist x z - dist x p) / 3
    have hδ : 0 < δ := by dsimp [δ]; linarith
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    let q := hyperbolicCellProjection V hV y
    have hqC : q ∈ hyperbolicCell V := hyperbolicCellProjection_mem V hV y
    by_contra hbad
    have hqK : q ∈ K := ⟨hqC, le_of_not_gt hbad⟩
    have hminq : dist x z ≤ dist x q := hmin hqK
    have hqy : dist y q ≤ dist y p :=
      hyperbolicCellProjection_nearest V hV y (hyperbolicCellProjection_mem V hV x)
    have hxy : dist x y < δ := by simpa only [dist_comm] using hy
    have htri1 := dist_triangle x y q
    have htri2 := dist_triangle y x p
    rw [dist_comm y x] at htri2
    dsimp [δ] at hxy
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y _
    by_contra hbad
    apply hne
    exact ⟨hyperbolicCellProjection V hV y,
      hyperbolicCellProjection_mem V hV y, le_of_not_gt hbad⟩

end BrehmApprox
