module

public import BrehmApprox.SphericalCells
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Strict contraction inside a hemisphere

Normalizing `x + t p` contracts spherical distances on the closed hemisphere
centered at `p`, for `0 < t < 1`.  The same map tends uniformly to the identity
as `t` tends to zero.  The estimate is derived from an exact normalization
identity and concavity of sine, without any unproved geometric assumptions.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact identity behind the sharp Lipschitz estimate for normalization. -/
lemma normalize_distance_identity (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖u - v‖ ^ 2 = (‖u‖ - ‖v‖) ^ 2 +
      ‖u‖ * ‖v‖ * ‖NormedSpace.normalize u - NormedSpace.normalize v‖ ^ 2 := by
  rw [norm_sub_sq_real u v,
    norm_sub_sq_real (NormedSpace.normalize u) (NormedSpace.normalize v),
    NormedSpace.norm_normalize hu, NormedSpace.norm_normalize hv]
  simp only [NormedSpace.normalize, real_inner_smul_left, inner_smul_right]
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hv]
  ring

/-- Normalization has Lipschitz factor `1 / R` for pairs of vectors whose norms
are at least the positive number `R`. -/
lemma norm_normalize_sub_normalize_le {u v : E} {R : ℝ}
    (hR : 0 < R) (hu : R ≤ ‖u‖) (hv : R ≤ ‖v‖) :
    ‖NormedSpace.normalize u - NormedSpace.normalize v‖ ≤ ‖u - v‖ / R := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp (hR.trans_le hu)
  have hv0 : v ≠ 0 := norm_pos_iff.mp (hR.trans_le hv)
  have hprod : R * R ≤ ‖u‖ * ‖v‖ := mul_le_mul hu hv hR.le (norm_nonneg _)
  have hprod' := mul_le_mul_of_nonneg_right hprod
    (sq_nonneg ‖NormedSpace.normalize u - NormedSpace.normalize v‖)
  have hid := normalize_distance_identity u v hu0 hv0
  have hsquare : (‖NormedSpace.normalize u - NormedSpace.normalize v‖ * R) ^ 2 ≤
      ‖u - v‖ ^ 2 := by nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  exact (le_div_iff₀ hR).mpr
    ((sq_le_sq₀ (mul_nonneg (norm_nonneg _) hR.le) (norm_nonneg _)).mp hsquare)

end BrehmApprox

namespace GeodesicSphere

variable {n : ℕ}

/-- Euclidean chord length and round distance on the unit sphere. -/
lemma chord_eq_two_mul_sin (x y : GeodesicSphere n) :
    ‖x.val - y.val‖ = 2 * Real.sin (dist x y / 2) := by
  have hd0 : 0 ≤ dist x y / 2 := by positivity
  have hdπ : dist x y / 2 ≤ Real.pi := by
    have h := dist_le_pi x y
    have hpi := Real.pi_pos
    linarith
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd0 hdπ
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hs0)).mp
  rw [norm_sub_sq_real, x.norm_val, y.norm_val, ← cos_dist]
  have hcos := Real.cos_two_mul_eq_one_sub (dist x y / 2)
  have htwo : 2 * (dist x y / 2) = dist x y := by ring
  rw [htwo] at hcos
  nlinarith

/-- Angular distance is at most `pi / 2` times chordal distance. -/
lemma dist_le_pi_div_two_mul_chord (x y : GeodesicSphere n) :
    dist x y ≤ (Real.pi / 2) * ‖x.val - y.val‖ := by
  have hd0 : 0 ≤ dist x y / 2 := by positivity
  have hdπ : dist x y / 2 ≤ Real.pi / 2 := by linarith [dist_le_pi x y]
  have hs := Real.mul_le_sin hd0 hdπ
  have hs' := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  rw [chord_eq_two_mul_sin]
  field_simp at hs'
  nlinarith

lemma mul_sin_le_sin_mul {K θ : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    K * Real.sin θ ≤ Real.sin (K * θ) := by
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ0, hθπ⟩
    (sub_nonneg.mpr hK1) hK0 (by ring)
  simpa [smul_eq_mul] using h

/-- A contraction of chord lengths with factor at most one contracts spherical
angles by the same factor. -/
lemma dist_le_mul_of_chord_le {x y u v : GeodesicSphere n} {K : ℝ}
    (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hchord : ‖u.val - v.val‖ ≤ K * ‖x.val - y.val‖) :
    dist u v ≤ K * dist x y := by
  have ha0 : 0 ≤ dist x y / 2 := by positivity
  have haπ : dist x y / 2 ≤ Real.pi / 2 := by linarith [dist_le_pi x y]
  have hb0 : 0 ≤ dist u v / 2 := by positivity
  have hbπ : dist u v / 2 ≤ Real.pi / 2 := by linarith [dist_le_pi u v]
  have hc0 : 0 ≤ K * (dist x y / 2) := mul_nonneg hK0 ha0
  have hcπ : K * (dist x y / 2) ≤ Real.pi / 2 :=
    (mul_le_of_le_one_left ha0 hK1).trans haπ
  have hs : Real.sin (dist u v / 2) ≤ K * Real.sin (dist x y / 2) := by
    rw [chord_eq_two_mul_sin, chord_eq_two_mul_sin] at hchord
    nlinarith
  have hs' : Real.sin (dist u v / 2) ≤ Real.sin (K * (dist x y / 2)) :=
    hs.trans (mul_sin_le_sin_mul hK0 hK1 ha0 (haπ.trans (by linarith [Real.pi_pos])))
  have hhalf : dist u v / 2 ≤ K * (dist x y / 2) :=
    (Real.strictMonoOn_sin.le_iff_le
      ⟨by linarith [Real.pi_pos], hbπ⟩ ⟨by linarith [Real.pi_pos], hcπ⟩).mp hs'
  nlinarith

/-- The closed hemisphere centered at a unit vector `p`. -/
def closedHemisphere (p : GeodesicSphere n) : Set (GeodesicSphere n) :=
  {x | 0 ≤ inner ℝ p.val x.val}

lemma shift_ne_zero (p x : GeodesicSphere n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    x.val + t • p.val ≠ 0 := by
  intro hz
  have hx : x.val = -(t • p.val) := eq_neg_iff_add_eq_zero.mpr hz
  have hn := congrArg norm hx
  rw [x.norm_val, norm_neg, norm_smul, p.norm_val, Real.norm_eq_abs,
    abs_of_nonneg ht0, mul_one] at hn
  linarith

/-- Shift towards a pole and normalize. -/
def tilt (p : GeodesicSphere n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x : GeodesicSphere n) : GeodesicSphere n :=
  normalizeVector (x.val + t • p.val) (shift_ne_zero p x ht0 ht1)

@[simp]
lemma tilt_val (p : GeodesicSphere n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x : GeodesicSphere n) :
    (tilt p t ht0 ht1 x).val = NormedSpace.normalize (x.val + t • p.val) := rfl

lemma continuous_tilt (p : GeodesicSphere n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Continuous (tilt p t ht0 ht1) :=
  continuous_normalizeVector (fun x : GeodesicSphere n => x.val + t • p.val)
    (continuous_val.add continuous_const) (fun x => shift_ne_zero p x ht0 ht1)

/-- Positive tilt takes even the boundary of a closed hemisphere into its interior. -/
lemma tilt_inner_pos (p x : GeodesicSphere n) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hx : x ∈ closedHemisphere p) :
    0 < inner ℝ p.val (tilt p t ht.le ht1 x).val := by
  rw [tilt_val, NormedSpace.normalize, inner_smul_right, inner_add_right,
    inner_smul_right, inner_self_eq_one_of_norm_eq_one p.norm_val, mul_one]
  apply mul_pos (inv_pos.mpr (norm_pos_iff.mpr (shift_ne_zero p x ht.le ht1)))
  exact add_pos_of_nonneg_of_pos hx ht

lemma norm_shift_sq (p x : GeodesicSphere n) (t : ℝ) :
    ‖x.val + t • p.val‖ ^ 2 = 1 + 2 * t * inner ℝ p.val x.val + t ^ 2 := by
  simp only [norm_add_sq_real, norm_smul, inner_smul_right, x.norm_val, p.norm_val,
    Real.norm_eq_abs, mul_one, sq_abs, real_inner_comm x.val p.val]
  ring

lemma sqrt_le_norm_shift (p x : GeodesicSphere n) {t : ℝ} (ht0 : 0 ≤ t)
    (hx : x ∈ closedHemisphere p) :
    Real.sqrt (1 + t ^ 2) ≤ ‖x.val + t • p.val‖ := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity), norm_shift_sq]
  have hprod := mul_nonneg ht0 hx
  nlinarith

/-- The contraction factor of `tilt` on a closed hemisphere. -/
def tiltFactor (t : ℝ) : NNReal :=
  ⟨(Real.sqrt (1 + t ^ 2))⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg _)⟩

lemma tiltFactor_lt_one {t : ℝ} (ht : 0 < t) : tiltFactor t < 1 := by
  have hsq : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hone : 1 < Real.sqrt (1 + t ^ 2) := by nlinarith [sq_pos_of_pos ht]
  change (Real.sqrt (1 + t ^ 2))⁻¹ < 1
  rw [inv_lt_one₀ hpos]
  exact hone

/-- The tilt is a strict contraction on the closed hemisphere. -/
theorem lipschitzOnWith_tilt (p : GeodesicSphere n) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    LipschitzOnWith (tiltFactor t) (tilt p t ht.le ht1) (closedHemisphere p) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  apply dist_le_mul_of_chord_le (tiltFactor t).property
    (show (tiltFactor t : ℝ) ≤ 1 from (tiltFactor_lt_one ht).le)
  have hnorm := BrehmApprox.norm_normalize_sub_normalize_le
    (Real.sqrt_pos.mpr (show 0 < 1 + t ^ 2 by positivity))
    (sqrt_le_norm_shift p x ht.le hx) (sqrt_le_norm_shift p y ht.le hy)
  simpa only [tilt_val, add_sub_add_right_eq_sub, tiltFactor, NNReal.coe_mk,
    div_eq_inv_mul] using hnorm

lemma one_sub_le_norm_shift (p x : GeodesicSphere n) {t : ℝ} (ht0 : 0 ≤ t) :
    1 - t ≤ ‖x.val + t • p.val‖ := by
  have h := norm_sub_le (x.val + t • p.val) (t • p.val)
  rw [add_sub_cancel_right, x.norm_val, norm_smul, p.norm_val,
    Real.norm_eq_abs, abs_of_nonneg ht0, mul_one] at h
  linarith

lemma tilt_chord_displacement_le (p x : GeodesicSphere n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖(tilt p t ht0 ht1 x).val - x.val‖ ≤ t / (1 - t) := by
  have h := BrehmApprox.norm_normalize_sub_normalize_le
    (sub_pos.mpr ht1) (one_sub_le_norm_shift p x ht0)
    (show 1 - t ≤ ‖x.val‖ by rw [x.norm_val]; linarith)
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val,
    add_sub_cancel_left, norm_smul, p.norm_val, Real.norm_eq_abs,
    abs_of_nonneg ht0, mul_one] at h
  exact h

lemma tilt_displacement_le (p x : GeodesicSphere n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hthalf : t ≤ 1 / 2) :
    dist (tilt p t ht0 ht1 x) x ≤ Real.pi * t := by
  have hchord := tilt_chord_displacement_le p x ht0 ht1
  have hfrac : t / (1 - t) ≤ 2 * t := by
    apply (div_le_iff₀ (sub_pos.mpr ht1)).mpr
    nlinarith
  have hdist := dist_le_pi_div_two_mul_chord (tilt p t ht0 ht1 x) x
  have hbound := mul_le_mul_of_nonneg_left (hchord.trans hfrac)
    (show 0 ≤ Real.pi / 2 by positivity)
  nlinarith

/-- The identity on a hemisphere admits arbitrarily close strict contraction
approximations. The approximating map is defined on the whole sphere, while its
Lipschitz estimate is asserted on the chosen hemisphere. -/
theorem hemisphere_strictification (p : GeodesicSphere n) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : GeodesicSphere n → GeodesicSphere n) (K : NNReal),
      K < 1 ∧ LipschitzOnWith K g (closedHemisphere p) ∧
      ∀ x, dist (g x) x < ε := by
  let t : ℝ := min (1 / 4) (ε / (2 * Real.pi))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have hthalf : t ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have ht1 : t < 1 := hthalf.trans_lt (by norm_num)
  refine ⟨tilt p t ht.le ht1, tiltFactor t, tiltFactor_lt_one ht,
    lipschitzOnWith_tilt p ht ht1, ?_⟩
  intro x
  have hsmall : t * (2 * Real.pi) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hclose : Real.pi * t < ε := by nlinarith
  exact (tilt_displacement_le p x ht.le ht1 hthalf).trans_lt hclose

/-- Every distance-nonincreasing map into a closed hemisphere can be uniformly
approximated by strict contractions, for an arbitrary metric source. -/
theorem strictify_lipschitz_with_hemispherical_range
    {X : Type*} [PseudoMetricSpace X] {f : X → GeodesicSphere n}
    (hf : LipschitzWith 1 f) (p : GeodesicSphere n)
    (himage : ∀ x, f x ∈ closedHemisphere p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : X → GeodesicSphere n) (K : NNReal),
      K < 1 ∧ LipschitzWith K g ∧ ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨T, K, hK, hT, hclose⟩ := hemisphere_strictification p hε
  refine ⟨T ∘ f, K, hK, LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x y
    calc
      dist (T (f x)) (T (f y)) ≤ K * dist (f x) (f y) :=
        hT.dist_le_mul (f x) (himage x) (f y) (himage y)
      _ ≤ K * dist x y := mul_le_mul_of_nonneg_left
        (by simpa using hf.dist_le_mul x y) K.property
  · intro x
    exact hclose (f x)

end GeodesicSphere
