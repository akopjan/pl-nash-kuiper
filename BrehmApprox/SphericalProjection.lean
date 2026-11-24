module

public import BrehmApprox.SphereContraction
public import BrehmApprox.ConvexProjection
public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Nearest projection to a spherical convex cone section

A closed convex Euclidean cone has a proved nonexpansive nearest projection.
After normalization this gives nearest projection on its spherical section
where the projected vector is nonzero.  The explicit spherical Lipschitz bound
on a tube around a small section tends to one with its diameter and tube radius.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Euclidean nearest projection to an actual closed convex cone. -/
def coneProjection (C : ProperCone ℝ E) (x : E) : E :=
  convexProjection (C : Set E) C.nonempty C.isClosed.isComplete C.convex x

lemma coneProjection_mem (C : ProperCone ℝ E) (x : E) : coneProjection C x ∈ C :=
  convexProjection_mem (C : Set E) C.nonempty C.isClosed.isComplete C.convex x

lemma coneProjection_variational (C : ProperCone ℝ E) (x : E) :
    ∀ y ∈ C, inner ℝ (x - coneProjection C x) (y - coneProjection C x) ≤ 0 :=
  convexProjection_variational (C : Set E) C.nonempty C.isClosed.isComplete C.convex x

lemma coneProjection_short (C : ProperCone ℝ E) : Short (coneProjection C) :=
  convexProjection_short (C : Set E) C.nonempty C.isClosed.isComplete C.convex

lemma coneProjection_fix (C : ProperCone ℝ E) {x : E} (hx : x ∈ C) :
    coneProjection C x = x :=
  convexProjection_fix (C : Set E) C.nonempty C.isClosed.isComplete C.convex hx

/-- The cone projection and its residual are orthogonal. -/
lemma coneProjection_orthogonal (C : ProperCone ℝ E) (x : E) :
    inner ℝ (x - coneProjection C x) (coneProjection C x) = 0 := by
  let p := coneProjection C x
  have hp : p ∈ C := coneProjection_mem C x
  have hzero := coneProjection_variational C x 0 C.toPointedCone.zero_mem
  have htwo := coneProjection_variational C x ((2 : ℝ) • p)
    (C.smul_mem hp (by norm_num : 0 ≤ (2 : ℝ)))
  have hsub : (2 : ℝ) • p - p = p := by rw [two_smul]; abel
  change inner ℝ (x - p) ((2 : ℝ) • p - p) ≤ 0 at htwo
  rw [hsub] at htwo
  change inner ℝ (x - p) (0 - p) ≤ 0 at hzero
  rw [zero_sub, inner_neg_right] at hzero
  exact le_antisymm htwo (neg_nonpos.mp hzero)

lemma coneProjection_polar (C : ProperCone ℝ E) (x : E) {v : E} (hv : v ∈ C) :
    inner ℝ (x - coneProjection C x) v ≤ 0 := by
  have h := coneProjection_variational C x v hv
  rwa [inner_sub_right, coneProjection_orthogonal, sub_zero] at h

lemma inner_coneProjection_self (C : ProperCone ℝ E) (x : E) :
    inner ℝ x (coneProjection C x) = ‖coneProjection C x‖ ^ 2 := by
  have h := coneProjection_orthogonal C x
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
  linarith

/-- Every unit vector of the cone has scalar product with `x` bounded by the
norm of the Euclidean cone projection. -/
lemma inner_le_norm_coneProjection (C : ProperCone ℝ E) (x : E)
    {v : E} (hv : v ∈ C) (hvnorm : ‖v‖ = 1) :
    inner ℝ x v ≤ ‖coneProjection C x‖ := by
  have hp := coneProjection_polar C x hv
  rw [inner_sub_left] at hp
  have hcs := real_inner_le_norm (coneProjection C x) v
  rw [hvnorm, mul_one] at hcs
  linarith

end BrehmApprox

namespace GeodesicSphere

open BrehmApprox

variable {n : ℕ}

/-- The round-sphere section of a closed convex Euclidean cone. -/
def coneSection (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1)))) : Set (GeodesicSphere n) :=
  {x | x.val ∈ C}

/-- Normalize the cone projection wherever it is nonzero; use the input point
elsewhere so that the function is defined on the whole sphere. -/
def sphericalConeProjection (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (x : GeodesicSphere n) : GeodesicSphere n := by
  classical
  exact if hx : coneProjection C x.val ≠ 0 then normalizeVector (coneProjection C x.val) hx else x

lemma sphericalConeProjection_val (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (x : GeodesicSphere n) (hx : coneProjection C x.val ≠ 0) :
    (sphericalConeProjection C x).val = NormedSpace.normalize (coneProjection C x.val) := by
  classical
  simp only [sphericalConeProjection, dite_eq_left hx, normalizeVector_val]

lemma sphericalConeProjection_mem (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (x : GeodesicSphere n) (hx : coneProjection C x.val ≠ 0) :
    sphericalConeProjection C x ∈ coneSection C := by
  change (sphericalConeProjection C x).val ∈ C
  rw [sphericalConeProjection_val C x hx, NormedSpace.normalize]
  exact C.smul_mem (coneProjection_mem C x.val) (inv_nonneg.mpr (norm_nonneg _))

lemma sphericalConeProjection_fix (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {x : GeodesicSphere n} (hx : x ∈ coneSection C) : sphericalConeProjection C x = x := by
  have hproj := coneProjection_fix C hx
  have hne : coneProjection C x.val ≠ 0 := by rw [hproj]; exact x.val_ne_zero
  apply GeodesicSphere.ext
  rw [sphericalConeProjection_val C x hne, hproj,
    NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val]

lemma inner_sphericalConeProjection (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (x : GeodesicSphere n) (hx : coneProjection C x.val ≠ 0) :
    inner ℝ x.val (sphericalConeProjection C x).val = ‖coneProjection C x.val‖ := by
  rw [sphericalConeProjection_val C x hx, NormedSpace.normalize, inner_smul_right,
    inner_coneProjection_self]
  field_simp [norm_ne_zero_iff.mpr hx]

/-- The normalized cone projection is a nearest point in its spherical section. -/
lemma sphericalConeProjection_nearest (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (x : GeodesicSphere n) (hx : coneProjection C x.val ≠ 0)
    {v : GeodesicSphere n} (hv : v ∈ coneSection C) :
    dist x (sphericalConeProjection C x) ≤ dist x v := by
  rw [dist_eq_arccos_inner, dist_eq_arccos_inner, inner_sphericalConeProjection C x hx]
  exact Real.arccos_le_arccos (inner_le_norm_coneProjection C x.val hv v.norm_val)

/-- A concrete closed spherical tube, written without distance-to-empty-set conventions. -/
def coneTube (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (r : ℝ) :
    Set (GeodesicSphere n) :=
  {x | ∃ v ∈ coneSection C, dist x v ≤ r}

lemma cos_le_norm_coneProjection (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {x : GeodesicSphere n} {r : ℝ} (hr : r ≤ Real.pi)
    (hx : x ∈ coneTube C r) : Real.cos r ≤ ‖coneProjection C x.val‖ := by
  obtain ⟨v, hv, hdist⟩ := hx
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (dist_nonneg : 0 ≤ dist x v) hr hdist
  rw [cos_dist] at hcos
  exact hcos.trans (inner_le_norm_coneProjection C x.val hv v.norm_val)

lemma coneProjection_ne_zero_on_tube (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {x : GeodesicSphere n} {r : ℝ} (hr0 : 0 ≤ r) (hr : r < Real.pi / 2)
    (hx : x ∈ coneTube C r) : coneProjection C x.val ≠ 0 := by
  have hcos : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hr⟩
  exact norm_pos_iff.mp (hcos.trans_le
    (cos_le_norm_coneProjection C (by linarith [Real.pi_pos]) hx))

/-- Chord length never exceeds angular distance. -/
lemma chord_le_dist (x y : GeodesicSphere n) : ‖x.val - y.val‖ ≤ dist x y := by
  rw [chord_eq_two_mul_sin]
  have h := Real.sin_le (show 0 ≤ dist x y / 2 by positivity)
  linarith

/-- The sharp arc-to-chord factor for pairs at distance at most `ℓ < pi`. -/
lemma dist_le_diameter_factor_mul_chord {x y : GeodesicSphere n} {ℓ : ℝ}
    (hℓ0 : 0 < ℓ) (hℓπ : ℓ < Real.pi) (hxy : dist x y ≤ ℓ) :
    dist x y ≤ (Real.sinc (ℓ / 2))⁻¹ * ‖x.val - y.val‖ := by
  have hd0 := dist_nonneg (x := x) (y := y)
  have hK0 : 0 ≤ dist x y / ℓ := div_nonneg hd0 hℓ0.le
  have hK1 : dist x y / ℓ ≤ 1 := (div_le_one hℓ0).mpr hxy
  have hθ0 : 0 ≤ ℓ / 2 := by positivity
  have hθπ : ℓ / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hs := mul_sin_le_sin_mul hK0 hK1 hθ0 hθπ
  have harg : dist x y / ℓ * (ℓ / 2) = dist x y / 2 := by field_simp
  rw [harg] at hs
  have hsin : 0 < Real.sin (ℓ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  rw [chord_eq_two_mul_sin, Real.sinc_of_ne_zero (by positivity)]
  field_simp
  have hs' := (mul_le_mul_of_nonneg_left hs hℓ0.le)
  field_simp at hs'
  nlinarith

/-- A continuous expression for the projection distortion, equal to
`ℓ / (2 * sin (ℓ / 2) * cos r)` for `0 < ℓ < pi`. -/
def sphericalProjectionFactor (ℓ r : ℝ) : ℝ := (Real.sinc (ℓ / 2) * Real.cos r)⁻¹

@[simp]
lemma sphericalProjectionFactor_zero : sphericalProjectionFactor 0 0 = 1 := by
  simp [sphericalProjectionFactor]

lemma sphericalProjectionFactor_pos {ℓ r : ℝ} (hℓ0 : 0 < ℓ) (hℓπ : ℓ < Real.pi)
    (hr0 : 0 ≤ r) (hrπ : r < Real.pi / 2) : 0 < sphericalProjectionFactor ℓ r := by
  apply inv_pos.mpr
  have hsinc : 0 < Real.sinc (ℓ / 2) := Real.sinc_pos (by
    rw [abs_of_pos (by positivity : 0 < ℓ / 2)]
    linarith [Real.pi_pos])
  exact mul_pos hsinc (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hrπ⟩)

/-- On a tube of radius `r < pi/2` about a cone section of diameter at most `ℓ`,
nearest projection has the explicit Lipschitz factor tending to one as
`(ℓ,r)` tends to `(0,0)`. -/
theorem sphericalConeProjection_lipschitz (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {ℓ r : ℝ} (hℓ0 : 0 < ℓ) (hℓπ : ℓ < Real.pi) (hr0 : 0 ≤ r) (hrπ : r < Real.pi / 2)
    (hdiam : ∀ v ∈ coneSection C, ∀ w ∈ coneSection C, dist v w ≤ ℓ)
    {x y : GeodesicSphere n} (hx : x ∈ coneTube C r) (hy : y ∈ coneTube C r) :
    dist (sphericalConeProjection C x) (sphericalConeProjection C y) ≤
      sphericalProjectionFactor ℓ r * dist x y := by
  have hcos : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hrπ⟩
  have hx0 := coneProjection_ne_zero_on_tube C hr0 hrπ hx
  have hy0 := coneProjection_ne_zero_on_tube C hr0 hrπ hy
  have hnorm := norm_normalize_sub_normalize_le hcos
    (cos_le_norm_coneProjection C (by linarith [Real.pi_pos]) hx)
    (cos_le_norm_coneProjection C (by linarith [Real.pi_pos]) hy)
  have hproj : ‖coneProjection C x.val - coneProjection C y.val‖ ≤ ‖x.val - y.val‖ :=
    coneProjection_short C x.val y.val
  have hchord : ‖(sphericalConeProjection C x).val - (sphericalConeProjection C y).val‖ ≤
      ‖x.val - y.val‖ / Real.cos r := by
    rw [sphericalConeProjection_val C x hx0, sphericalConeProjection_val C y hy0]
    exact hnorm.trans ((div_le_div_iff_of_pos_right hcos).mpr hproj)
  have hsinc : 0 < Real.sinc (ℓ / 2) := Real.sinc_pos (by
    rw [abs_of_pos (by positivity : 0 < ℓ / 2)]; linarith [Real.pi_pos])
  calc
    dist (sphericalConeProjection C x) (sphericalConeProjection C y)
      ≤ (Real.sinc (ℓ / 2))⁻¹ *
          ‖(sphericalConeProjection C x).val - (sphericalConeProjection C y).val‖ :=
        dist_le_diameter_factor_mul_chord hℓ0 hℓπ
          (hdiam _ (sphericalConeProjection_mem C x hx0) _ (sphericalConeProjection_mem C y hy0))
    _ ≤ (Real.sinc (ℓ / 2))⁻¹ * (‖x.val - y.val‖ / Real.cos r) :=
      mul_le_mul_of_nonneg_left hchord (inv_nonneg.mpr hsinc.le)
    _ ≤ (Real.sinc (ℓ / 2))⁻¹ * (dist x y / Real.cos r) :=
      mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hcos).mpr (chord_le_dist x y))
        (inv_nonneg.mpr hsinc.le)
    _ = sphericalProjectionFactor ℓ r * dist x y := by
      simp only [sphericalProjectionFactor, mul_inv_rev, div_eq_mul_inv]
      ring

/-- The distortion formula extends continuously to `(0,0)`, with value one. -/
theorem continuousAt_sphericalProjectionFactor :
    ContinuousAt (fun q : ℝ × ℝ => sphericalProjectionFactor q.1 q.2) (0, 0) := by
  unfold sphericalProjectionFactor
  apply ContinuousAt.inv₀
  · exact ((Real.continuous_sinc.comp (continuous_fst.div_const 2)).mul
      (Real.continuous_cos.comp continuous_snd)).continuousAt
  · simp

/-- Arbitrarily small cells and collars have projection distortion below any
prescribed constant greater than one. -/
theorem exists_sphericalProjectionFactor_lt {K : ℝ} (hK : 1 < K) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 2 ∧
      ∀ ℓ r : ℝ, 0 ≤ ℓ → ℓ ≤ δ → 0 ≤ r → r ≤ δ →
        sphericalProjectionFactor ℓ r < K := by
  obtain ⟨η, hη, hbound⟩ := Metric.continuousAt_iff.mp
    continuousAt_sphericalProjectionFactor (K - 1) (sub_pos.mpr hK)
  let δ : ℝ := min (η / 2) (Real.pi / 4)
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hδπ : δ < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  refine ⟨δ, hδ0, hδπ, ?_⟩
  intro ℓ r hℓ0 hℓδ hr0 hrδ
  have hd : dist (ℓ, r) (0, 0) < η := by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg hℓ0, abs_of_nonneg hr0]
    exact max_lt (hℓδ.trans_lt hδη) (hrδ.trans_lt hδη)
  have h := hbound hd
  simp only [sphericalProjectionFactor_zero, Real.dist_eq] at h
  have hu := (abs_lt.mp h).2
  linarith

/-- A strictly short map remains strictly short after composing with the
nearest projection of a sufficiently small spherical collar. -/
theorem exists_sphericalProjectionFactor_mul_lt_one {L : ℝ}
    (hL0 : 0 ≤ L) (hL1 : L < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 2 ∧
      ∀ ℓ r : ℝ, 0 ≤ ℓ → ℓ ≤ δ → 0 ≤ r → r ≤ δ →
        L * sphericalProjectionFactor ℓ r < 1 := by
  by_cases hL : L = 0
  · refine ⟨Real.pi / 4, by positivity, by linarith [Real.pi_pos], ?_⟩
    intro ℓ r _ _ _ _
    simp [hL]
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
  have hK : 1 < L⁻¹ := (one_lt_inv₀ hLpos).mpr hL1
  obtain ⟨δ, hδ0, hδπ, hδ⟩ := exists_sphericalProjectionFactor_lt hK
  refine ⟨δ, hδ0, hδπ, ?_⟩
  intro ℓ r hℓ0 hℓδ hr0 hrδ
  have h := mul_lt_mul_of_pos_left (hδ ℓ r hℓ0 hℓδ hr0 hrδ) hLpos
  simpa only [mul_inv_cancel₀ hL] using h

end GeodesicSphere
