module

public import BrehmApprox.HyperbolicRadialFolding
public import BrehmApprox.EuclideanRigidity

/-!
# The Pogorelov graph transform

Pairs of future unit hyperboloid points are transformed to pairs of Euclidean
points by dividing both spatial coordinates by the sum of their time
coordinates. The exact squared-distance identity converts shortness in either
direction. A continuous short Euclidean graph meeting the open diamond lifts
to a unique globally defined short hyperbolic graph.

No extension theorem or geometric axiom is used in this module.
-/

@[expose] public section
noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox.Pogorelov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Hyperboloid

/-- Sum of the two positive hyperboloid time coordinates. -/
def scale (x y : E) : ℝ := height x + height y

omit [InnerProductSpace ℝ E] in
lemma scale_pos (x y : E) : 0 < scale x y :=
  add_pos (height_pos x) (height_pos y)

/-- First Euclidean coordinate of a transformed hyperbolic pair. -/
def pairLeft (x y : E) : E := (2 / scale x y) • x

/-- Second Euclidean coordinate of a transformed hyperbolic pair. -/
def pairRight (x y : E) : E := (2 / scale x y) • y

theorem norm_pairLeft_add_norm_pairRight_lt_two (x y : E) :
    ‖pairLeft x y‖ + ‖pairRight x y‖ < 2 := by
  have hs := scale_pos x y
  have hc : 0 ≤ 2 / scale x y := (div_pos (by norm_num) hs).le
  rw [pairLeft, pairRight, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hc, ← mul_add]
  calc
    (2 / scale x y) * (‖x‖ + ‖y‖) < (2 / scale x y) * scale x y :=
      mul_lt_mul_of_pos_left (add_lt_add (norm_lt_height x) (norm_lt_height y))
        (div_pos (by norm_num) hs)
    _ = 2 := div_mul_cancel₀ _ hs.ne'

/-- The pair transform preserves the sign of the difference of squared
distances. This is the algebraic heart of the hyperbolic transfer. -/
theorem squared_dist_difference (x y x' y' : E) :
    dist (pairLeft x y) (pairLeft x' y') ^ 2 -
        dist (pairRight x y) (pairRight x' y') ^ 2 =
      8 * (coshDist x x' - coshDist y y') / (scale x y * scale x' y') := by
  have hx : ‖x‖ ^ 2 = height x ^ 2 - 1 := by linarith [height_sq x]
  have hy : ‖y‖ ^ 2 = height y ^ 2 - 1 := by linarith [height_sq y]
  have hx' : ‖x'‖ ^ 2 = height x' ^ 2 - 1 := by linarith [height_sq x']
  have hy' : ‖y'‖ ^ 2 = height y' ^ 2 - 1 := by linarith [height_sq y']
  simp only [pairLeft, pairRight, dist_eq_norm, norm_sub_sq_real, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  rw [hx, hy, hx', hy']
  unfold coshDist
  field_simp [(scale_pos x y).ne', (scale_pos x' y').ne']
  dsimp [scale]
  ring

theorem distance_le_iff_pair_dist (x y x' y' : E) :
    distance y y' ≤ distance x x' ↔
      dist (pairRight x y) (pairRight x' y') ≤
        dist (pairLeft x y) (pairLeft x' y') := by
  have hid := squared_dist_difference x y x' y'
  have hs : 0 < scale x y * scale x' y' := mul_pos (scale_pos x y) (scale_pos x' y')
  have heq : distance y y' ≤ distance x x' ↔ coshDist y y' ≤ coshDist x x' :=
    Real.arcosh_le_arcosh (coshDist_pos y y') (coshDist_pos x x')
  rw [heq]
  constructor
  · intro h
    have hn : 0 ≤ 8 * (coshDist x x' - coshDist y y') /
        (scale x y * scale x' y') := div_nonneg (by linarith) hs.le
    nlinarith [dist_nonneg (x := pairRight x y) (y := pairRight x' y'),
      dist_nonneg (x := pairLeft x y) (y := pairLeft x' y')]
  · intro h
    have hsq : 0 ≤ dist (pairLeft x y) (pairLeft x' y') ^ 2 -
        dist (pairRight x y) (pairRight x' y') ^ 2 := by
      nlinarith [dist_nonneg (x := pairRight x y) (y := pairRight x' y'),
        dist_nonneg (x := pairLeft x y) (y := pairLeft x' y')]
    rw [hid] at hsq
    have hn : 0 ≤ 8 * (coshDist x x' - coshDist y y') := by
      have hm := mul_nonneg hsq hs.le
      simpa only [div_mul_cancel₀ _ hs.ne'] using hm
    linarith

/-- The original hyperbolic pair lies on the transformed Euclidean graph. -/
def GraphRelated (F : E → E) (x y : E) : Prop :=
  pairRight x y = F (pairLeft x y)

omit [InnerProductSpace ℝ E] in
private lemma endpoint_identity (x : E) :
    4 - 4 * height x * (2 / (height x + 1)) +
      (2 / (height x + 1)) ^ 2 * ‖x‖ ^ 2 = 0 := by
  have hx : ‖x‖ ^ 2 = height x ^ 2 - 1 := by linarith [height_sq x]
  rw [hx]
  field_simp [height_add_one_ne_zero x]
  ring

/-- Every source point has a point on the lifted graph. Existence uses only
continuity and the strict inequality at the Euclidean origin. -/
theorem exists_graphRelated (F : E → E) (hF : Continuous F)
    (hzero : ‖F 0‖ < 2) (x : E) : ∃ y : E, GraphRelated F x y := by
  let b : ℝ := 2 / (height x + 1)
  have hb : 0 < b := div_pos (by norm_num) (by linarith [height_pos x])
  let q : ℝ → ℝ := fun s => ‖F (s • x)‖ ^ 2 -
    (4 - 4 * height x * s + s ^ 2 * ‖x‖ ^ 2)
  have hq : Continuous q := by
    dsimp [q]
    fun_prop
  have hq0 : q 0 < 0 := by
    dsimp [q]
    simp only [zero_smul, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
    nlinarith [norm_nonneg (F 0)]
  have hqb : 0 ≤ q b := by
    dsimp [q, b]
    rw [endpoint_identity]
    exact sub_nonneg.mpr (sq_nonneg _)
  obtain ⟨s, hs, hqs⟩ := intermediate_value_Icc hb.le hq.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (q 0) (q b) from ⟨hq0.le, hqb⟩)
  have hspos : 0 < s := by
    have hsne : s ≠ 0 := by
      intro h
      subst s
      linarith
    exact lt_of_le_of_ne hs.1 (Ne.symm hsne)
  have htime : 1 ≤ 2 / s - height x := by
    have hsb : s ≤ 2 / (height x + 1) := hs.2
    have ht := (le_div_iff₀ (show 0 < height x + 1 by linarith [height_pos x])).mp hsb
    have ht' : s * (height x + 1) ≤ 2 := ht
    have hh : height x + 1 ≤ 2 / s := (le_div_iff₀ hspos).mpr (by nlinarith)
    linarith
  let y : E := s⁻¹ • F (s • x)
  have hnorm : ‖y‖ ^ 2 = (2 / s - height x) ^ 2 - 1 := by
    have heq : ‖F (s • x)‖ ^ 2 = 4 - 4 * height x * s + s ^ 2 * ‖x‖ ^ 2 := by
      dsimp [q] at hqs
      linarith
    have hx : ‖x‖ ^ 2 = height x ^ 2 - 1 := by linarith [height_sq x]
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, heq, hx]
    field_simp [hspos.ne']
    ring
  have hheight : height y = 2 / s - height x := by
    have hh := height_sq y
    rw [hnorm] at hh
    have hpos := height_nonneg y
    nlinarith
  have hscale : 2 / scale x y = s := by
    unfold scale
    rw [hheight]
    field_simp [hspos.ne']
    ring
  refine ⟨y, ?_⟩
  unfold GraphRelated pairRight pairLeft
  rw [hscale]
  dsimp [y]
  rw [smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]

theorem graphRelated_unique {F : E → E} (hF : LipschitzWith 1 F)
    {x y z : E} (hy : GraphRelated F x y) (hz : GraphRelated F x z) : y = z := by
  have hd : dist (pairRight x y) (pairRight x z) ≤
      dist (pairLeft x y) (pairLeft x z) := by
    rw [hy, hz]
    simpa only [NNReal.coe_one, one_mul] using hF.dist_le_mul (pairLeft x y) (pairLeft x z)
  have hh := (distance_le_iff_pair_dist x y x z).mpr hd
  rw [distance_self] at hh
  exact (distance_eq_zero_iff y z).mp (le_antisymm hh (distance_nonneg y z))

variable {n : ℕ}

/-- The unique short hyperbolic graph obtained from a short Euclidean graph. -/
def liftShort (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LipschitzWith 1 F) (hzero : ‖F 0‖ < 2)
    (x : HyperbolicSpace n) : HyperbolicSpace n :=
  ⟨Classical.choose (exists_graphRelated F hF.continuous hzero x.point)⟩

theorem graphRelated_liftShort
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LipschitzWith 1 F) (hzero : ‖F 0‖ < 2) (x : HyperbolicSpace n) :
    GraphRelated F x.point (liftShort F hF hzero x).point :=
  Classical.choose_spec (exists_graphRelated F hF.continuous hzero x.point)

theorem liftShort_lipschitz
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LipschitzWith 1 F) (hzero : ‖F 0‖ < 2) :
    LipschitzWith 1 (liftShort F hF hzero) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  change distance (liftShort F hF hzero x).point (liftShort F hF hzero y).point ≤
    distance x.point y.point
  apply (distance_le_iff_pair_dist _ _ _ _).mpr
  rw [graphRelated_liftShort, graphRelated_liftShort]
  simpa only [NNReal.coe_one, one_mul] using hF.dist_le_mul
    (pairLeft x.point (liftShort F hF hzero x).point)
    (pairLeft y.point (liftShort F hF hzero y).point)

theorem liftShort_interpolates
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LipschitzWith 1 F) (hzero : ‖F 0‖ < 2) (x y : HyperbolicSpace n)
    (hxy : GraphRelated F x.point y.point) : liftShort F hF hzero x = y := by
  apply HyperbolicSpace.ext
  exact graphRelated_unique hF (graphRelated_liftShort F hF hzero x) hxy

end BrehmApprox.Pogorelov
