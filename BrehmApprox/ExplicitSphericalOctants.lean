module

public import BrehmApprox.SphereShortRigidity
public import BrehmApprox.SphericalGeodesics

/-!
# Explicit geometric ingredients for the octant counterexample

This module constructs the real
equatorial inclusion S² → S³, the extra orthogonal direction, the shared edge,
and the short collapse associated to every equatorial anchor. The collapse
agrees with the identity across its attaching meridian and is constant on the
shared edge. It does not assert that the intrinsic metric on their union has
already been constructed.
-/

@[expose] public section
noncomputable section

namespace ExplicitSphericalOctants

open GeodesicSphere

def indexInclusion : Fin 3 ↪ Fin 4 := ⟨Fin.castSucc, Fin.castSucc_injective 3⟩

def linearInclusion : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  LinearIsometry.piLpExtendByZero 2 ℝ ℝ indexInclusion

def inclusion : GeodesicSphere 2 → GeodesicSphere 3 := GeodesicSphere.map linearInclusion

theorem isometry_inclusion : Isometry inclusion := GeodesicSphere.isometry_map linearInclusion

def north : GeodesicSphere 2 := coordinatePole 2 0
def extra : GeodesicSphere 3 := coordinatePole 3 3

lemma inclusion_val (x : GeodesicSphere 2) : (inclusion x).val = linearInclusion x.val := rfl

lemma inner_inclusion_extra (x : GeodesicSphere 2) :
    inner ℝ (inclusion x).val extra.val = 0 := by
  rw [inclusion_val]
  change inner ℝ (linearInclusion x.val) (EuclideanSpace.single (3 : Fin 4) 1) = 0
  rw [EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  apply LinearIsometry.piLpExtendByZero_apply_eq_zero
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

def edgeDirection : tangentPlane (inclusion north) :=
  ⟨extra.val, inner_inclusion_extra north⟩

lemma edgeDirection_norm : ‖edgeDirection‖ = 1 := extra.norm_val

/-- The actual common great-circle edge, parameterized by arc length. -/
def sharedEdge (t : ℝ) : GeodesicSphere 3 :=
  radialCircle (inclusion north) edgeDirection edgeDirection_norm t

theorem sharedEdge_dist {s t : ℝ} (hst : |s - t| ≤ Real.pi) :
    dist (sharedEdge s) (sharedEdge t) = |s - t| :=
  radialCircle_dist (inclusion north) edgeDirection edgeDirection_norm s t hst

@[simp] lemma sharedEdge_zero : sharedEdge 0 = inclusion north := by
  apply GeodesicSphere.ext
  simp only [sharedEdge, radialCircle_val, Real.cos_zero, Real.sin_zero,
    one_smul, zero_smul, add_zero]

@[simp] lemma sharedEdge_pi_div_two : sharedEdge (Real.pi / 2) = extra := by
  apply GeodesicSphere.ext
  simp only [sharedEdge, radialCircle_val, Real.cos_pi_div_two, Real.sin_pi_div_two,
    zero_smul, one_smul, zero_add, edgeDirection]

variable (a : GeodesicSphere 2) (ha : inner ℝ a.val north.val = 0)

def targetDirection : tangentPlane a := ⟨north.val, ha⟩

lemma targetDirection_norm : ‖targetDirection a ha‖ = 1 := north.norm_val

def meridian (t : ℝ) : GeodesicSphere 2 :=
  radialCircle a (targetDirection a ha) (targetDirection_norm a ha) t

@[simp] lemma meridian_zero : meridian a ha 0 = a := by
  apply GeodesicSphere.ext
  simp only [meridian, radialCircle_val, Real.cos_zero, Real.sin_zero,
    one_smul, zero_smul, add_zero]

@[simp] lemma meridian_pi_div_two : meridian a ha (Real.pi / 2) = north := by
  apply GeodesicSphere.ext
  simp only [meridian, radialCircle_val, Real.cos_pi_div_two, Real.sin_pi_div_two,
    zero_smul, one_smul, zero_add, targetDirection]

theorem meridian_dist {s t : ℝ} (hst : |s - t| ≤ Real.pi) :
    dist (meridian a ha s) (meridian a ha t) = |s - t| :=
  radialCircle_dist a (targetDirection a ha) (targetDirection_norm a ha) s t hst

/-- The concrete short map on the octant with anchor `a`. It is defined on
the whole ambient S³, so no extension of its cellwise definition is assumed. -/
def collapse (x : GeodesicSphere 3) : GeodesicSphere 2 :=
  meridian a ha (dist (inclusion a) x)

theorem collapse_short : LipschitzWith 1 (collapse a ha) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (meridian a ha (dist (inclusion a) x))
    (meridian a ha (dist (inclusion a) y)) ≤ (1 : ℝ) * dist x y
  rw [one_mul, meridian_dist]
  · simpa only [dist_comm] using abs_dist_sub_le x y (inclusion a)
  · have hx0 := dist_nonneg (x := inclusion a) (y := x)
    have hy0 := dist_nonneg (x := inclusion a) (y := y)
    have hxπ := dist_le_pi (inclusion a) x
    have hyπ := dist_le_pi (inclusion a) y
    exact abs_le.mpr ⟨by linarith, by linarith⟩

include ha in
/-- Along the common edge, every anchor has exactly distance `pi/2`. -/
theorem sharedEdge_anchor_distance (t : ℝ) :
    dist (inclusion a) (sharedEdge t) = Real.pi / 2 := by
  rw [dist_eq_arccos_inner]
  have horth : inner ℝ (inclusion a).val (inclusion north).val = 0 := by
    rw [inclusion_val, inclusion_val, linearInclusion.inner_map_map]
    exact ha
  change Real.arccos (inner ℝ (inclusion a).val
    (Real.cos t • (inclusion north).val + Real.sin t • extra.val)) = _
  rw [inner_add_right, inner_smul_right, inner_smul_right, horth,
    inner_inclusion_extra, mul_zero, mul_zero, add_zero, Real.arccos_zero]

/-- All the octant collapses agree on the entire shared edge. -/
theorem collapse_sharedEdge (t : ℝ) : collapse a ha (sharedEdge t) = north := by
  unfold collapse
  rw [sharedEdge_anchor_distance a ha, meridian_pi_div_two]

/-- On the attaching meridian the map agrees with the inverse equatorial
inclusion, exactly as required to glue it to the identity on the old sphere. -/
theorem collapse_attaching_meridian {t : ℝ} (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) :
    collapse a ha (inclusion (meridian a ha t)) = meridian a ha t := by
  have hd : dist (inclusion a) (inclusion (meridian a ha t)) = t := by
    rw [isometry_inclusion.dist_eq]
    have ht : |(0 : ℝ) - t| ≤ Real.pi := by
      simpa only [zero_sub, abs_neg, abs_of_nonneg ht0] using htπ
    have h := meridian_dist a ha ht
    simpa only [meridian_zero, zero_sub, abs_neg, abs_of_nonneg ht0] using h
  change meridian a ha (dist (inclusion a) (inclusion (meridian a ha t))) = _
  rw [hd]

def equatorDirection : tangentPlane (coordinatePole 2 1) :=
  ⟨(coordinatePole 2 2).val, by
    change inner ℝ (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) = 0
    simp [EuclideanSpace.inner_single_left]⟩

lemma equatorDirection_norm : ‖equatorDirection‖ = 1 := (coordinatePole 2 2).norm_val

def equatorCircle (t : ℝ) : GeodesicSphere 2 :=
  radialCircle (coordinatePole 2 1) equatorDirection equatorDirection_norm t

theorem equatorCircle_orthogonal (t : ℝ) :
    inner ℝ (equatorCircle t).val north.val = 0 := by
  simp only [equatorCircle, radialCircle_val, inner_add_left,
    real_inner_smul_left, equatorDirection, north, coordinatePole_val,
    EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply]
  norm_num

/-- The actual three equatorial anchors, at angles `0`, `2π/3`, `4π/3`. -/
def anchor (i : Fin 3) : GeodesicSphere 2 :=
  equatorCircle ((i : ℝ) * (2 * Real.pi / 3))

theorem anchor_orthogonal (i : Fin 3) : inner ℝ (anchor i).val north.val = 0 :=
  equatorCircle_orthogonal _

/-- Three real spherical octants in S³. -/
def octant (i : Fin 3) : Set (GeodesicSphere 3) := by
  classical
  exact BrehmApprox.sphericalCell {inclusion north, inclusion (anchor i), extra}

/-- The actual underlying subset of S³. Its subtype ambient metric is NOT the
intrinsic metric required by the counterexample; the latter remains to be
constructed from finite chains through the displayed cells. -/
def sourceSet : Set (GeodesicSphere 3) :=
  Set.range inclusion ∪ ⋃ i : Fin 3, octant i

def octantCollapse (i : Fin 3) : GeodesicSphere 3 → GeodesicSphere 2 :=
  collapse (anchor i) (anchor_orthogonal i)

theorem octantCollapse_short (i : Fin 3) : LipschitzWith 1 (octantCollapse i) :=
  collapse_short (anchor i) (anchor_orthogonal i)

theorem octantCollapse_sharedEdge (i : Fin 3) (t : ℝ) :
    octantCollapse i (sharedEdge t) = north :=
  collapse_sharedEdge (anchor i) (anchor_orthogonal i) t

theorem octantCollapse_attaching_meridian (i : Fin 3)
    {t : ℝ} (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) :
    octantCollapse i (inclusion (meridian (anchor i) (anchor_orthogonal i) t)) =
      meridian (anchor i) (anchor_orthogonal i) t :=
  collapse_attaching_meridian (anchor i) (anchor_orthogonal i) ht0 htπ

end ExplicitSphericalOctants
