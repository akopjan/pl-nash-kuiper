module

public import BrehmApprox.SphericalGnomonic
public import BrehmApprox.FiniteGramIsometry
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Concrete spherical radial geometry for the initial-folding argument

This file proves the tangent direction formula, its angular Gram matrix, and
the compatibility of all positive barycentric combinations. These are actual
round-sphere statements. The existence of protected nets and a finite angular
complex in an arbitrary intrinsic polyhedral space is not assumed or claimed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeodesicSphere

variable {n : ℕ}

/-- Tangential component of a unit vector at a chosen unit pole. -/
def radialVector (a x : GeodesicSphere n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  x.val - (inner ℝ a.val x.val) • a.val

lemma inner_radialVector (a x : GeodesicSphere n) : inner ℝ a.val (radialVector a x) = 0 := by
  rw [radialVector, inner_sub_right, inner_smul_right,
    inner_self_eq_one_of_norm_eq_one a.norm_val, mul_one, sub_self]

lemma norm_radialVector_sq (a x : GeodesicSphere n) :
    ‖radialVector a x‖ ^ 2 = 1 - (inner ℝ a.val x.val) ^ 2 := by
  rw [radialVector, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    x.norm_val, a.norm_val, mul_one, real_inner_smul_right,
    real_inner_comm x.val a.val]
  simp only [sq_abs]
  ring

/-- The tangential component has norm equal to the sine of the angular radius. -/
lemma norm_radialVector (a x : GeodesicSphere n) :
    ‖radialVector a x‖ = Real.sin (dist a x) := by
  have hsq := norm_radialVector_sq a x
  rw [← cos_dist] at hsq
  have htrig := Real.sin_sq_add_cos_sq (dist a x)
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi (dist_nonneg : 0 ≤ dist a x) (dist_le_pi a x)
  nlinarith [norm_nonneg (radialVector a x)]

/-- The actual unit tangent direction of a point distinct from the pole and
its antipode. -/
def radialDirection (a x : GeodesicSphere n) (_h0 : 0 < dist a x)
    (_hπ : dist a x < Real.pi) : tangentPlane a :=
  ⟨(Real.sin (dist a x))⁻¹ • radialVector a x, by
    change inner ℝ a.val ((Real.sin (dist a x))⁻¹ • radialVector a x) = 0
    rw [inner_smul_right, inner_radialVector, mul_zero]⟩

@[simp]
lemma radialDirection_val (a x : GeodesicSphere n) (h0 : 0 < dist a x)
    (hπ : dist a x < Real.pi) :
    (radialDirection a x h0 hπ).val = (Real.sin (dist a x))⁻¹ • radialVector a x := rfl

lemma radialDirection_norm (a x : GeodesicSphere n) (h0 : 0 < dist a x)
    (hπ : dist a x < Real.pi) : ‖radialDirection a x h0 hπ‖ = 1 := by
  change ‖(Real.sin (dist a x))⁻¹ • radialVector a x‖ = 1
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsin),
    norm_radialVector, inv_mul_cancel₀ hsin.ne']

lemma radialDirection_eq_normalize (a x : GeodesicSphere n) (h0 : 0 < dist a x)
    (hπ : dist a x < Real.pi) :
    (radialDirection a x h0 hπ).val = NormedSpace.normalize (radialVector a x) := by
  rw [NormedSpace.normalize, norm_radialVector, radialDirection_val]

/-- The actual polar decomposition of a round-sphere point. -/
lemma radial_decomposition (a x : GeodesicSphere n) (h0 : 0 < dist a x)
    (hπ : dist a x < Real.pi) :
    x.val = Real.cos (dist a x) • a.val +
      Real.sin (dist a x) • (radialDirection a x h0 hπ).val := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  rw [radialDirection_val, smul_smul, mul_inv_cancel₀ hsin.ne', one_smul,
    cos_dist, radialVector]
  abel

/-- The spherical cosine law in the tangent directions, with all objects
belonging to the concrete sphere model. -/
lemma radial_cosine_law (a x y : GeodesicSphere n)
    (hx0 : 0 < dist a x) (hxπ : dist a x < Real.pi)
    (hy0 : 0 < dist a y) (hyπ : dist a y < Real.pi) :
    Real.cos (dist x y) = Real.cos (dist a x) * Real.cos (dist a y) +
      Real.sin (dist a x) * Real.sin (dist a y) *
        inner ℝ (radialDirection a x hx0 hxπ) (radialDirection a y hy0 hyπ) := by
  rw [cos_dist]
  conv_lhs => rw [radial_decomposition a x hx0 hxπ, radial_decomposition a y hy0 hyπ]
  have hxorth : inner ℝ (radialDirection a x hx0 hxπ).val a.val = 0 := by
    rw [real_inner_comm, inner_tangentPlane]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
    inner_self_eq_one_of_norm_eq_one a.norm_val, inner_tangentPlane, hxorth, mul_zero,
    add_zero, zero_add, mul_one]
  change _ = _ + _ * inner ℝ (radialDirection a x hx0 hxπ).val
    (radialDirection a y hy0 hyπ).val
  ring

/-- The angular Gram matrix is determined solely by the two radii and the
edge lengths of the base. This is the center-independence used in folding. -/
theorem radial_gram_formula (a x y : GeodesicSphere n)
    (hx0 : 0 < dist a x) (hxπ : dist a x < Real.pi)
    (hy0 : 0 < dist a y) (hyπ : dist a y < Real.pi) :
    inner ℝ (radialDirection a x hx0 hxπ) (radialDirection a y hy0 hyπ) =
      (Real.cos (dist x y) - Real.cos (dist a x) * Real.cos (dist a y)) /
        (Real.sin (dist a x) * Real.sin (dist a y)) := by
  have hden : Real.sin (dist a x) * Real.sin (dist a y) ≠ 0 :=
    mul_ne_zero (Real.sin_pos_of_pos_of_lt_pi hx0 hxπ).ne'
      (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ).ne'
  apply (eq_div_iff hden).mpr
  nlinarith [radial_cosine_law a x y hx0 hxπ hy0 hyπ]

/-- Equality of the actual angular Gram entries at two nearest centers. -/
theorem radial_gram_eq_of_equal_radii (a b x y : GeodesicSphere n)
    (hax0 : 0 < dist a x) (haxπ : dist a x < Real.pi)
    (hay0 : 0 < dist a y) (hayπ : dist a y < Real.pi)
    (hbx0 : 0 < dist b x) (hbxπ : dist b x < Real.pi)
    (hby0 : 0 < dist b y) (hbyπ : dist b y < Real.pi)
    (hx : dist a x = dist b x) (hy : dist a y = dist b y) :
    inner ℝ (radialDirection a x hax0 haxπ) (radialDirection a y hay0 hayπ) =
      inner ℝ (radialDirection b x hbx0 hbxπ) (radialDirection b y hby0 hbyπ) := by
  rw [radial_gram_formula, radial_gram_formula, hx, hy]

/-- Every barycentric base point has the prescribed weighted angular vector.
The positive scale is the projective normalization of its spherical coordinates. -/
theorem radialDirection_positive_combination {ι : Type*} [Fintype ι]
    (a x : GeodesicSphere n) (v : ι → GeodesicSphere n) (t : ι → ℝ)
    (hx0 : 0 < dist a x) (hxπ : dist a x < Real.pi)
    (hv0 : ∀ i, 0 < dist a (v i)) (hvπ : ∀ i, dist a (v i) < Real.pi)
    {c : ℝ} (hc : 0 < c) (hrep : ∑ i, t i • (v i).val = c • x.val) :
    (radialDirection a x hx0 hxπ).val = NormedSpace.normalize
      (∑ i, (t i * Real.sin (dist a (v i))) • (radialDirection a (v i) (hv0 i) (hvπ i)).val) := by
  have hvec : (∑ i, t i • radialVector a (v i)) = c • radialVector a x := by
    have hinner := congrArg (fun z => inner ℝ a.val z) hrep
    simp only [inner_sum, inner_smul_right] at hinner
    simp only [radialVector, smul_sub, smul_smul, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hrep, hinner]
  have hsum : (∑ i, (t i * Real.sin (dist a (v i))) •
      (radialDirection a (v i) (hv0 i) (hvπ i)).val) = c • radialVector a x := by
    calc
      _ = ∑ i, t i • radialVector a (v i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [radialDirection_val, smul_smul]
        have hs := (Real.sin_pos_of_pos_of_lt_pi (hv0 i) (hvπ i)).ne'
        rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
      _ = _ := hvec
  rw [hsum, NormedSpace.normalize_smul_of_pos hc, radialDirection_eq_normalize]

/-- The same all-point compatibility formula inside the actual tangent space. -/
theorem radialDirection_positive_combination_tangent {ι : Type*} [Fintype ι]
    (a x : GeodesicSphere n) (v : ι → GeodesicSphere n) (t : ι → ℝ)
    (hx0 : 0 < dist a x) (hxπ : dist a x < Real.pi)
    (hv0 : ∀ i, 0 < dist a (v i)) (hvπ : ∀ i, dist a (v i) < Real.pi)
    {c : ℝ} (hc : 0 < c) (hrep : ∑ i, t i • (v i).val = c • x.val) :
    radialDirection a x hx0 hxπ = NormedSpace.normalize
      (∑ i, (t i * Real.sin (dist a (v i))) • radialDirection a (v i) (hv0 i) (hvπ i)) := by
  apply Subtype.ext
  have hs : (∑ i, (t i * Real.sin (dist a (v i))) •
      radialDirection a (v i) (hv0 i) (hvπ i) : tangentPlane a).val =
      ∑ i, (t i * Real.sin (dist a (v i))) • (radialDirection a (v i) (hv0 i) (hvπ i)).val := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  change (radialDirection a x hx0 hxπ).val =
    ‖(∑ i, (t i * Real.sin (dist a (v i))) •
      radialDirection a (v i) (hv0 i) (hvπ i) : tangentPlane a).val‖⁻¹ •
      (∑ i, (t i * Real.sin (dist a (v i))) •
      radialDirection a (v i) (hv0 i) (hvπ i) : tangentPlane a).val
  rw [hs]
  exact radialDirection_positive_combination a x v t hx0 hxπ hv0 hvπ hc hrep

lemma cos_dist_lt_one {a b : GeodesicSphere n} (hab : a ≠ b) :
    Real.cos (dist a b) < 1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
    (dist_le_pi a b) (dist_pos.mpr hab)
  simpa only [Real.cos_zero] using h

/-- A bisector's vertices span a hyperplane missing either of its distinct
centers. This gives the required nondegeneracy of the radial simplex. -/
theorem center_not_mem_span_of_equidistant {ι : Type*}
    (a b : GeodesicSphere n) (hab : a ≠ b) (v : ι → GeodesicSphere n)
    (heq : ∀ i, dist a (v i) = dist b (v i)) :
    a.val ∉ Submodule.span ℝ (Set.range (fun i => (v i).val)) := by
  have hspan : Submodule.span ℝ (Set.range (fun i => (v i).val)) ≤
      LinearMap.ker (innerₛₗ ℝ (a.val - b.val)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ (a.val - b.val) (v i).val = 0
    rw [inner_sub_left, ← cos_dist, ← cos_dist, heq i, sub_self]
  intro ha
  have hzero := hspan ha
  change inner ℝ (a.val - b.val) a.val = 0 at hzero
  rw [inner_sub_left, inner_self_eq_one_of_norm_eq_one a.norm_val,
    real_inner_comm a.val b.val, ← cos_dist] at hzero
  linarith [cos_dist_lt_one hab]

/-- Tangent unit directions of a nondegenerate spherical base remain
linearly independent if the center is outside the linear span of the base. -/
theorem radialDirection_linearIndependent {ι : Type*} [Fintype ι]
    (a : GeodesicSphere n) (v : ι → GeodesicSphere n)
    (hv0 : ∀ i, 0 < dist a (v i)) (hvπ : ∀ i, dist a (v i) < Real.pi)
    (hv : LinearIndependent ℝ (fun i => (v i).val))
    (ha : a.val ∉ Submodule.span ℝ (Set.range (fun i => (v i).val))) :
    LinearIndependent ℝ (fun i => radialDirection a (v i) (hv0 i) (hvπ i)) := by
  have hrad : LinearIndependent ℝ (fun i => radialVector a (v i)) :=
    BrehmApprox.linearIndependent_sub_smul_of_notMem_span
      (fun i => (v i).val) a.val (fun i => inner ℝ a.val (v i).val) hv ha
  rw [Fintype.linearIndependent_iff]
  intro t ht i
  have ht' := congrArg (fun z : tangentPlane a => z.val) ht
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
    radialDirection_val, smul_smul] at ht'
  have hi := Fintype.linearIndependent_iff.mp hrad
    (fun j => t j * (Real.sin (dist a (v j)))⁻¹) ht' i
  exact (mul_eq_zero.mp hi).resolve_right
    (inv_ne_zero (Real.sin_pos_of_pos_of_lt_pi (hv0 i) (hvπ i)).ne')

/-- All directions to a nearby bisector lie strictly on the same side of one
tangent hyperplane; this is the open-hemisphere property of the angular cell. -/
theorem bisector_radialDirection_positive (a b x : GeodesicSphere n)
    (hab : a ≠ b) (hx0 : 0 < dist a x) (hxhalf : dist a x < Real.pi / 2)
    (heq : dist a x = dist b x) :
    0 < inner ℝ (b.val - a.val)
      (radialDirection a x hx0 (by linarith [Real.pi_pos])).val := by
  have hxπ : dist a x < Real.pi := by linarith [Real.pi_pos]
  have hs : 0 < Real.sin (dist a x) := Real.sin_pos_of_pos_of_lt_pi hx0 hxπ
  have hc : 0 < inner ℝ a.val x.val := by
    rw [← cos_dist]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxhalf⟩
  have heqinner : inner ℝ b.val x.val = inner ℝ a.val x.val := by
    rw [← cos_dist, ← cos_dist, heq]
  have habinner : inner ℝ a.val b.val < 1 := by
    rw [← cos_dist]
    exact cos_dist_lt_one hab
  rw [radialDirection_val, inner_smul_right]
  apply mul_pos (inv_pos.mpr hs)
  rw [radialVector, inner_sub_right, inner_smul_right, inner_sub_left,
    inner_sub_left, inner_self_eq_one_of_norm_eq_one a.norm_val,
    real_inner_comm a.val b.val, heqinner]
  nlinarith

/-- The angular vertex set of a nearby spherical bisector lies in an actual
open hemisphere of the unit tangent sphere. -/
theorem bisector_radialDirections_hemispherical {ι : Type*} [Nonempty ι]
    (a b : GeodesicSphere n) (hab : a ≠ b) (v : ι → GeodesicSphere n)
    (hv0 : ∀ i, 0 < dist a (v i)) (hvhalf : ∀ i, dist a (v i) < Real.pi / 2)
    (heq : ∀ i, dist a (v i) = dist b (v i)) :
    ∃ p : tangentPlane a, ‖p‖ = 1 ∧ ∀ i,
      0 < inner ℝ p (radialDirection a (v i) (hv0 i) (by linarith [hvhalf i, Real.pi_pos])) := by
  classical
  let i : ι := Classical.arbitrary ι
  have hab0 : 0 < dist a b := dist_pos.mpr hab
  have habπ : dist a b < Real.pi := by
    have h := dist_triangle a (v i) b
    rw [dist_comm (v i) b, ← heq i] at h
    linarith [hvhalf i]
  refine ⟨radialDirection a b hab0 habπ, radialDirection_norm a b hab0 habπ, ?_⟩
  intro j
  have h := bisector_radialDirection_positive a b (v j) hab (hv0 j) (hvhalf j) (heq j)
  rw [inner_sub_left, inner_tangentPlane, sub_zero] at h
  change 0 < inner ℝ (radialDirection a b hab0 habπ).val
    (radialDirection a (v j) (hv0 j) (by linarith [hvhalf j, Real.pi_pos])).val
  rw [radialDirection_val, real_inner_smul_left]
  apply mul_pos (inv_pos.mpr (Real.sin_pos_of_pos_of_lt_pi hab0 habπ))
  rw [radialVector, inner_sub_left, real_inner_smul_left, inner_tangentPlane,
    mul_zero, sub_zero]
  exact h

/-- Equal nearest radii construct an actual linear isometry between the
angular spans; no abstract angular-complex interface is assumed here. -/
theorem exists_bisector_angular_isometry {ι : Type*} [Fintype ι]
    (a b : GeodesicSphere n) (hab : a ≠ b) (v : ι → GeodesicSphere n)
    (ha0 : ∀ i, 0 < dist a (v i)) (haπ : ∀ i, dist a (v i) < Real.pi)
    (hb0 : ∀ i, 0 < dist b (v i)) (hbπ : ∀ i, dist b (v i) < Real.pi)
    (hv : LinearIndependent ℝ (fun i => (v i).val))
    (heq : ∀ i, dist a (v i) = dist b (v i)) :
    ∃ f : Submodule.span ℝ (Set.range (fun i => radialDirection a (v i) (ha0 i) (haπ i)))
        ≃ₗᵢ[ℝ] Submodule.span ℝ (Set.range (fun i => radialDirection b (v i) (hb0 i) (hbπ i))),
      ∀ i, (f ⟨radialDirection a (v i) (ha0 i) (haπ i),
        Submodule.subset_span (Set.mem_range_self i)⟩).val =
          radialDirection b (v i) (hb0 i) (hbπ i) := by
  have hinda := radialDirection_linearIndependent a v ha0 haπ hv
    (center_not_mem_span_of_equidistant a b hab v heq)
  have hgram : ∀ i j,
      inner ℝ (radialDirection a (v i) (ha0 i) (haπ i)) (radialDirection a (v j) (ha0 j) (haπ j)) =
        inner ℝ (radialDirection b (v i) (hb0 i) (hbπ i)) (radialDirection b (v j) (hb0 j) (hbπ j)) := by
    intro i j
    exact radial_gram_eq_of_equal_radii a b (v i) (v j)
      (ha0 i) (haπ i) (ha0 j) (haπ j) (hb0 i) (hbπ i) (hb0 j) (hbπ j) (heq i) (heq j)
  obtain ⟨f, hf⟩ := BrehmApprox.exists_finite_gram_isometry _ _ hinda hgram
  refine ⟨f, ?_⟩
  intro i
  simpa only [Module.Basis.span_apply] using hf i

end GeodesicSphere
