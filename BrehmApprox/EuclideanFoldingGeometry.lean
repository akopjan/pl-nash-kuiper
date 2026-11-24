module

public import BrehmApprox.FiniteGramIsometry
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Tactic.Abel

/-!
# Actual Euclidean radial geometry for initial folding

The angular Gram matrix is determined by radii and base edge lengths.
Common bisector vertices give the same angular simplex at either center;
affine combinations of all base points, rather than vertices alone, are
compatible with the induced angular isometry. The bisector base is proved
hemispherical and nondegenerate. No protected-net or complex construction is
assumed in this file.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BrehmApprox.EuclideanFolding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual unit radial direction in a Euclidean inner-product space;
at the center it is zero. -/
def radialDirection (a x : E) : E := NormedSpace.normalize (x - a)

lemma radialDirection_norm (a x : E) (hax : a ≠ x) : ‖radialDirection a x‖ = 1 :=
  NormedSpace.norm_normalize (sub_ne_zero.mpr hax.symm)

lemma dist_smul_radialDirection (a x : E) :
    dist a x • radialDirection a x = x - a := by
  rw [dist_eq_norm', radialDirection, NormedSpace.norm_smul_normalize]

lemma radial_decomposition (a x : E) : x = a + dist a x • radialDirection a x := by
  rw [dist_smul_radialDirection]
  abel

/-- The Euclidean cosine law, including the zero-radius case. -/
theorem radial_cosine_law (a x y : E) :
    dist x y ^ 2 = dist a x ^ 2 + dist a y ^ 2 -
      2 * dist a x * dist a y * inner ℝ (radialDirection a x) (radialDirection a y) := by
  have h := norm_sub_sq_real (x - a) (y - a)
  rw [sub_sub_sub_cancel_right] at h
  have hi : inner ℝ (x - a) (y - a) =
      dist a x * dist a y * inner ℝ (radialDirection a x) (radialDirection a y) := by
    rw [← dist_smul_radialDirection a x, ← dist_smul_radialDirection a y,
      real_inner_smul_left, inner_smul_right]
    ring
  rw [hi, ← dist_eq_norm x y, ← dist_eq_norm' a x, ← dist_eq_norm' a y] at h
  nlinarith

/-- Every angular Gram entry depends only on radii and the corresponding
base edge length. -/
theorem radial_gram_formula (a x y : E)
    (hx : 0 < dist a x) (hy : 0 < dist a y) :
    inner ℝ (radialDirection a x) (radialDirection a y) =
      (dist a x ^ 2 + dist a y ^ 2 - dist x y ^ 2) / (2 * dist a x * dist a y) := by
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hx.ne') hy.ne')).mpr
  nlinarith [radial_cosine_law a x y]

theorem radial_gram_eq_of_equal_radii (a b x y : E)
    (hx : 0 < dist a x) (hy : 0 < dist a y)
    (hex : dist a x = dist b x) (hey : dist a y = dist b y) :
    inner ℝ (radialDirection a x) (radialDirection a y) =
      inner ℝ (radialDirection b x) (radialDirection b y) := by
  rw [radial_gram_formula a x y hx hy,
    radial_gram_formula b x y (hex ▸ hx) (hey ▸ hy), hex, hey]

omit [InnerProductSpace ℝ E] in
lemma bisector_radius_pos (a b x : E) (hab : a ≠ b) (hbis : dist a x = dist b x) :
    0 < dist a x := by
  have h := dist_triangle a x b
  rw [dist_comm x b, ← hbis] at h
  linarith [dist_pos.mpr hab]

/-- All radial directions of a nontrivial Euclidean bisector lie in the
open hemisphere centered on the direction towards the other center. -/
theorem bisector_direction_in_open_hemisphere (a b x : E)
    (hab : a ≠ b) (hbis : dist a x = dist b x) :
    0 < inner ℝ (radialDirection a b) (radialDirection a x) := by
  have hx := bisector_radius_pos a b x hab hbis
  have hab0 := dist_pos.mpr hab
  rw [radial_gram_formula a b x hab0 hx, ← hbis]
  apply div_pos
  · nlinarith [sq_pos_of_pos hab0]
  · exact mul_pos (mul_pos (by norm_num) hab0) hx

/-- An affine equation for the actual perpendicular bisector. -/
theorem bisector_inner (a b x : E) (hbis : dist a x = dist b x) :
    inner ℝ (b - a) (x - a) = ‖b - a‖ ^ 2 / 2 := by
  have h := norm_sub_sq_real (x - a) (b - a)
  rw [sub_sub_sub_cancel_right, real_inner_comm (b - a) (x - a)] at h
  have heq : ‖x - a‖ = ‖x - b‖ := by simpa only [dist_eq_norm'] using hbis
  rw [heq] at h
  linarith

theorem bisector_inner_iff (a b x : E) :
    dist a x = dist b x ↔ inner ℝ (b - a) (x - a) = ‖b - a‖ ^ 2 / 2 := by
  refine ⟨bisector_inner a b x, fun hi => ?_⟩
  have h := norm_sub_sq_real (x - a) (b - a)
  rw [sub_sub_sub_cancel_right, real_inner_comm (b - a) (x - a), hi] at h
  rw [dist_eq_norm', dist_eq_norm']
  nlinarith [norm_nonneg (x - a), norm_nonneg (x - b)]

/-- The affine span of a bisector base cannot contain its radial center. -/
theorem center_not_mem_affineSpan_bisector {ι : Type*} (a b : E) (v : ι → E)
    (hab : a ≠ b) (hbis : ∀ i, dist a (v i) = dist b (v i)) :
    a ∉ affineSpan ℝ (Set.range v) := by
  intro ha
  have h : inner ℝ (b - a) (a - a) = ‖b - a‖ ^ 2 / 2 := by
    refine affineSpan_induction (p := fun z : E =>
      inner ℝ (b - a) (z - a) = ‖b - a‖ ^ 2 / 2) ha ?_ ?_
    · rintro x ⟨i, rfl⟩
      exact bisector_inner a b (v i) (hbis i)
    · intro c u v w hu hv hw
      change inner ℝ (b - a) (c • (u - v) + w - a) = _
      have heq : c • (u - v) + w - a = c • ((u - a) - (v - a)) + (w - a) := by
        rw [sub_sub_sub_cancel_right]
        abel
      rw [heq, inner_add_right, inner_smul_right, inner_sub_right, hu, hv, hw]
      ring
  simp only [sub_self, inner_zero_right] at h
  have hn : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  nlinarith [sq_pos_of_pos hn]

section Finite

variable {ι : Type*} [Fintype ι]

/-- Affine barycentric coordinates give the exact radial-vector identity. -/
theorem radial_vector_barycentric (a x : E) (v : ι → E) (t : ι → ℝ)
    (ht : ∑ i, t i = 1) (hrep : ∑ i, t i • v i = x) :
    ∑ i, t i • (v i - a) = x - a := by
  simp only [smul_sub, Finset.sum_sub_distrib, hrep, ← Finset.sum_smul, ht, one_smul]

/-- The radial direction of every barycentric point is the normalized
combination with weights multiplied by the corresponding radii. -/
theorem radial_direction_barycentric (a x : E) (v : ι → E) (t : ι → ℝ)
    (ht : ∑ i, t i = 1) (hrep : ∑ i, t i • v i = x) :
    radialDirection a x = NormedSpace.normalize
      (∑ i, (t i * dist a (v i)) • radialDirection a (v i)) := by
  have hsum : (∑ i, (t i * dist a (v i)) • radialDirection a (v i)) = x - a := by
    simpa only [mul_smul, dist_smul_radialDirection] using
      radial_vector_barycentric a x v t ht hrep
  rw [hsum, radialDirection]

/-- Equality of distances to the centers holds on the whole affine base,
not only at the listed vertices. -/
theorem equal_radii_of_barycentric_bisector (a b x : E) (v : ι → E) (t : ι → ℝ)
    (ht : ∑ i, t i = 1) (hrep : ∑ i, t i • v i = x)
    (hbis : ∀ i, dist a (v i) = dist b (v i)) : dist a x = dist b x := by
  apply (bisector_inner_iff a b x).mpr
  have h := congrArg (fun z => inner ℝ (b - a) z)
    (radial_vector_barycentric a x v t ht hrep)
  simp only [inner_sum, inner_smul_right,
    fun i => bisector_inner a b (v i) (hbis i), ← Finset.sum_mul, ht, one_mul] at h
  exact h.symm

/-- Labelled vertex compatibility implies compatibility at every point of
the base, using the exact barycentric formula. -/
theorem radial_direction_compatibility (a b x : E) (v : ι → E) (t : ι → ℝ)
    (ht : ∑ i, t i = 1) (hrep : ∑ i, t i • v i = x)
    (hradii : ∀ i, dist a (v i) = dist b (v i))
    (f : E →ₗᵢ[ℝ] E) (hf : ∀ i, f (radialDirection a (v i)) = radialDirection b (v i)) :
    f (radialDirection a x) = radialDirection b x := by
  rw [radial_direction_barycentric a x v t ht hrep,
    linearIsometry_map_normalize]
  simp only [map_sum, map_smul, hf, hradii]
  exact (radial_direction_barycentric b x v t ht hrep).symm

/-- A linearly independent angular base is obtained from any affinely
independent Euclidean base contained in a nontrivial bisector. -/
theorem radialDirection_linearIndependent (a b : E) (v : ι → E)
    (hab : a ≠ b) (hbis : ∀ i, dist a (v i) = dist b (v i))
    (hv : AffineIndependent ℝ v) : LinearIndependent ℝ (radialDirection a ∘ v) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let t : ι → ℝ := fun j => c j / dist a (v j)
  have hrel : ∑ j, t j • (v j - a) = 0 := by
    simpa only [Function.comp_apply, radialDirection, NormedSpace.normalize,
      smul_smul, ← div_eq_mul_inv, ← dist_eq_norm'] using hc
  have hinner := congrArg (fun z => inner ℝ (b - a) z) hrel
  simp only [inner_sum, inner_smul_right, inner_zero_right,
    fun j => bisector_inner a b (v j) (hbis j), ← Finset.sum_mul] at hinner
  have hn : 0 < ‖b - a‖ ^ 2 / 2 :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm))) (by norm_num)
  have ht : ∑ j, t j = 0 := (mul_eq_zero.mp hinner).resolve_right hn.ne'
  have hsum : ∑ j, t j • v j = 0 := by
    simpa only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      ht, zero_smul, sub_zero] using hrel
  have hw : Finset.univ.weightedVSub v t = (0 : E) := by
    rw [Finset.weightedVSub_eq_linear_combination _ ht]
    exact hsum
  have hz := (affineIndependent_iff_of_fintype ℝ v).mp hv t ht hw i
  change c i / dist a (v i) = 0 at hz
  exact (div_eq_zero_iff.mp hz).resolve_right (bisector_radius_pos a b (v i) hab (hbis i)).ne'

/-- The actual angular spans at two centers of the same bisector base are
linearly isometric, with every labelled direction prescribed. -/
theorem exists_bisector_angular_isometry (a b : E) (v : ι → E)
    (hab : a ≠ b) (hbis : ∀ i, dist a (v i) = dist b (v i))
    (hv : AffineIndependent ℝ v) :
    ∃ f : Submodule.span ℝ (Set.range (radialDirection a ∘ v)) ≃ₗᵢ[ℝ]
        Submodule.span ℝ (Set.range (radialDirection b ∘ v)),
      ∀ i, (f ⟨radialDirection a (v i), Submodule.subset_span (Set.mem_range_self i)⟩).val =
        radialDirection b (v i) := by
  have hgram : ∀ i j, inner ℝ (radialDirection a (v i)) (radialDirection a (v j)) =
      inner ℝ (radialDirection b (v i)) (radialDirection b (v j)) := by
    intro i j
    exact radial_gram_eq_of_equal_radii a b (v i) (v j)
      (bisector_radius_pos a b (v i) hab (hbis i))
      (bisector_radius_pos a b (v j) hab (hbis j)) (hbis i) (hbis j)
  obtain ⟨f, hf⟩ := exists_finite_gram_isometry (radialDirection a ∘ v) (radialDirection b ∘ v)
    (radialDirection_linearIndependent a b v hab hbis hv) hgram
  refine ⟨f, fun i => ?_⟩
  simpa only [Module.Basis.span_apply, Function.comp_apply] using hf i

/-- In a finite-dimensional Euclidean space the angular span isometry
extends to an actual ambient orthogonal motion. Its translated motion fixes
every affine base point represented by the original vertices. -/
theorem exists_bisector_ambient_isometry [FiniteDimensional ℝ E]
    (a b : E) (v : ι → E) (hab : a ≠ b)
    (hbis : ∀ i, dist a (v i) = dist b (v i)) (hv : AffineIndependent ℝ v) :
    ∃ f : E ≃ₗᵢ[ℝ] E,
      (∀ i, f (radialDirection a (v i)) = radialDirection b (v i)) ∧
      ∀ (x : E) (t : ι → ℝ), ∑ i, t i = 1 → (∑ i, t i • v i) = x →
        b + f (x - a) = x := by
  have hgram : ∀ i j, inner ℝ (radialDirection a (v i)) (radialDirection a (v j)) =
      inner ℝ (radialDirection b (v i)) (radialDirection b (v j)) := by
    intro i j
    exact radial_gram_eq_of_equal_radii a b (v i) (v j)
      (bisector_radius_pos a b (v i) hab (hbis i))
      (bisector_radius_pos a b (v j) hab (hbis j)) (hbis i) (hbis j)
  obtain ⟨f, hf⟩ := exists_ambient_gram_isometry (radialDirection a ∘ v) (radialDirection b ∘ v)
    (radialDirection_linearIndependent a b v hab hbis hv) hgram
  refine ⟨f, hf, ?_⟩
  intro x t ht hrep
  have hdir := radial_direction_compatibility a b x v t ht hrep hbis f.toLinearIsometry hf
  have hr := equal_radii_of_barycentric_bisector a b x v t ht hrep hbis
  rw [← dist_smul_radialDirection a x, map_smul]
  change b + dist a x • f.toLinearIsometry (radialDirection a x) = x
  rw [hdir, hr, dist_smul_radialDirection]
  abel

end Finite

end BrehmApprox.EuclideanFolding
