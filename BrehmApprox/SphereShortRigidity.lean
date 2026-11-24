module

public import BrehmApprox.SphereContraction
public import BrehmApprox.SphereSurjectiveRigidity
public import BrehmApprox.FiniteGramIsometry

/-!
# An elementary dichotomy for short self-maps of the round sphere

For the standard antipodal frame `±eᵢ`, sum the image vectors. A nonzero sum
gives a pole of a closed hemisphere containing the whole image. If the sum is
zero, every shortness inequality against the frame is an equality. The images
of the positive frame form an orthonormal basis, and its coordinates determine
the map as an actual orthogonal motion.

Consequently a short map uniformly less than `pi/2` from the identity is an
isometry. No degree, surjectivity hypothesis, or Brehm axiom is needed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeodesicSphere

variable {n : ℕ}

/-- The positive half of the standard antipodal frame. -/
def coordinatePole (n : ℕ) (i : Fin (n + 1)) : GeodesicSphere n :=
  ⟨EuclideanSpace.single i 1, by simp⟩

@[simp]
lemma coordinatePole_val (i : Fin (n + 1)) :
    (coordinatePole n i).val = EuclideanSpace.single i 1 := rfl

/-- Shortness on the round sphere is exactly monotonicity of the corresponding
unit-vector inner products. Only the forward direction is needed here. -/
lemma inner_le_inner_of_short {g : GeodesicSphere n → GeodesicSphere n}
    (hg : BrehmApprox.Short g) (x y : GeodesicSphere n) :
    inner ℝ x.val y.val ≤ inner ℝ (g x).val (g y).val := by
  rw [← cos_dist, ← cos_dist]
  exact Real.cos_le_cos_of_nonneg_of_le_pi dist_nonneg (dist_le_pi x y) (hg x y)

/-- Sum of the images of the `2(n+1)` standard antipodal points. -/
def antipodalFrameSum (g : GeodesicSphere n → GeodesicSphere n) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  ∑ i, ((g (coordinatePole n i)).val + (g (antipode (coordinatePole n i))).val)

lemma inner_frame_pair_nonneg {g : GeodesicSphere n → GeodesicSphere n}
    (hg : BrehmApprox.Short g) (x : GeodesicSphere n) (i : Fin (n + 1)) :
    0 ≤ inner ℝ (g x).val (g (coordinatePole n i)).val +
      inner ℝ (g x).val (g (antipode (coordinatePole n i))).val := by
  have hpos := inner_le_inner_of_short hg x (coordinatePole n i)
  have hneg := inner_le_inner_of_short hg x (antipode (coordinatePole n i))
  change inner ℝ x.val (-(coordinatePole n i).val) ≤ _ at hneg
  rw [inner_neg_right] at hneg
  linarith

lemma inner_frameSum_nonneg {g : GeodesicSphere n → GeodesicSphere n}
    (hg : BrehmApprox.Short g) (x : GeodesicSphere n) :
    0 ≤ inner ℝ (g x).val (antipodalFrameSum g) := by
  rw [antipodalFrameSum, inner_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [inner_add_right]
  exact inner_frame_pair_nonneg hg x i

/-- Vanishing of the image-frame sum makes every coordinate shortness
inequality an equality. -/
lemma inner_coordinate_eq_of_frameSum_zero
    {g : GeodesicSphere n → GeodesicSphere n} (hg : BrehmApprox.Short g)
    (hsum : antipodalFrameSum g = 0) (x : GeodesicSphere n) (i : Fin (n + 1)) :
    inner ℝ (g x).val (g (coordinatePole n i)).val =
      inner ℝ x.val (coordinatePole n i).val := by
  have hz : ∑ j, (inner ℝ (g x).val (g (coordinatePole n j)).val +
      inner ℝ (g x).val (g (antipode (coordinatePole n j))).val) = 0 := by
    have h := congrArg (fun z => inner ℝ (g x).val z) hsum
    simpa only [antipodalFrameSum, inner_sum, inner_add_right, inner_zero_right] using h
  have hpair := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => inner_frame_pair_nonneg hg x j)).mp hz i (Finset.mem_univ i)
  have hpos := inner_le_inner_of_short hg x (coordinatePole n i)
  have hneg := inner_le_inner_of_short hg x (antipode (coordinatePole n i))
  change inner ℝ x.val (-(coordinatePole n i).val) ≤ _ at hneg
  rw [inner_neg_right] at hneg
  linarith

/-- The zero-sum case gives a genuine orthogonal motion on the entire sphere,
not merely an isometry of the finitely many frame points. -/
theorem exists_orthogonal_of_frameSum_zero
    {g : GeodesicSphere n → GeodesicSphere n} (hg : BrehmApprox.Short g)
    (hsum : antipodalFrameSum g = 0) :
    ∃ U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      g = mapEquiv U := by
  have hlin : LinearIndependent ℝ (fun i : Fin (n + 1) => (coordinatePole n i).val) := by
    simpa only [coordinatePole_val] using
      (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (n + 1))).linearIndependent
  have hgram : ∀ i j : Fin (n + 1),
      inner ℝ (coordinatePole n i).val (coordinatePole n j).val =
        inner ℝ (g (coordinatePole n i)).val (g (coordinatePole n j)).val := by
    intro i j
    exact (inner_coordinate_eq_of_frameSum_zero hg hsum (coordinatePole n i) j).symm
  obtain ⟨U, hU⟩ := BrehmApprox.exists_ambient_gram_isometry
    (fun i : Fin (n + 1) => (coordinatePole n i).val)
    (fun i => (g (coordinatePole n i)).val) hlin hgram
  refine ⟨U, ?_⟩
  funext x
  apply GeodesicSphere.ext
  change (g x).val = U x.val
  have hcoords : U.symm (g x).val = x.val := by
    apply PiLp.ext
    intro i
    have h := inner_coordinate_eq_of_frameSum_zero hg hsum x i
    rw [← hU i] at h
    have hu := U.inner_map_map (U.symm (g x).val) (coordinatePole n i).val
    rw [U.apply_symm_apply] at hu
    rw [hu] at h
    simpa only [coordinatePole_val, EuclideanSpace.inner_single_right,
      one_mul, conj_trivial] using h
  exact (U.apply_symm_apply (g x).val).symm.trans (congrArg U hcoords)

/-- Every short self-map of the round sphere is an orthogonal motion or has
its entire image in a closed hemisphere. -/
theorem orthogonal_or_hemispherical_of_short
    {g : GeodesicSphere n → GeodesicSphere n} (hg : BrehmApprox.Short g) :
    (∃ U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      g = mapEquiv U) ∨
    ∃ p : GeodesicSphere n, ∀ x, g x ∈ closedHemisphere p := by
  by_cases hsum : antipodalFrameSum g = 0
  · exact Or.inl (exists_orthogonal_of_frameSum_zero hg hsum)
  · right
    refine ⟨normalizeVector (antipodalFrameSum g) hsum, ?_⟩
    intro x
    change 0 ≤ inner ℝ (NormedSpace.normalize (antipodalFrameSum g)) (g x).val
    rw [NormedSpace.normalize, real_inner_smul_left, real_inner_comm]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inner_frameSum_nonneg hg x)

/-- Uniform distance less than `pi/2` from the identity rules out the
hemispherical alternative, without any use of degree theory. -/
theorem orthogonal_of_short_close_to_id
    {g : GeodesicSphere n → GeodesicSphere n} (hg : BrehmApprox.Short g)
    (hclose : ∀ x, dist (g x) x < Real.pi / 2) :
    ∃ U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      g = mapEquiv U := by
  rcases orthogonal_or_hemispherical_of_short hg with h | ⟨p, hp⟩
  · exact h
  · have hnonneg : 0 ≤ inner ℝ p.val (g (antipode p)).val := hp (antipode p)
    have hpos := (dist_lt_pi_div_two_iff (g (antipode p)) (antipode p)).mp
      (hclose (antipode p))
    change 0 < inner ℝ (g (antipode p)).val (-p.val) at hpos
    rw [inner_neg_right, real_inner_comm] at hpos
    linarith

theorem isometry_of_short_close_to_id
    {g : GeodesicSphere n → GeodesicSphere n} (hg : BrehmApprox.Short g)
    (hclose : ∀ x, dist (g x) x < Real.pi / 2) : Isometry g := by
  obtain ⟨U, rfl⟩ := orthogonal_of_short_close_to_id hg hclose
  exact (mapEquiv U).isometry

end GeodesicSphere
