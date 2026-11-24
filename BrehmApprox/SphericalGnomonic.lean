module

public import BrehmApprox.SphericalCells
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Tactic.Abel

/-!
# A genuine gnomonic chart on an open round hemisphere

The chart centered at a unit vector `p` takes `x` to `x / inner(p,x) - p`
in the tangent hyperplane `inner(p,z)=0`. Its inverse normalizes `p + z`.
-/

@[expose] public section

noncomputable section

namespace GeodesicSphere

variable {n : ℕ}

/-- The open hemisphere with pole `p`. -/
def openHemisphere (p : GeodesicSphere n) : Set (GeodesicSphere n) :=
  {x | 0 < inner ℝ p.val x.val}

lemma isOpen_openHemisphere (p : GeodesicSphere n) : IsOpen (openHemisphere p) :=
  isOpen_lt continuous_const (continuous_const.inner continuous_val)

/-- The Euclidean tangent vector space at the pole. -/
def tangentPlane (p : GeodesicSphere n) : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  LinearMap.ker (innerₛₗ ℝ p.val)

@[simp]
lemma inner_tangentPlane (p : GeodesicSphere n) (z : tangentPlane p) :
    inner ℝ p.val z.val = 0 := z.property

lemma inner_pole_add_tangent (p : GeodesicSphere n) (z : tangentPlane p) :
    inner ℝ p.val (p.val + z.val) = 1 := by
  rw [inner_add_right, inner_tangentPlane,
    inner_self_eq_one_of_norm_eq_one p.norm_val, add_zero]

lemma pole_add_tangent_ne_zero (p : GeodesicSphere n) (z : tangentPlane p) :
    p.val + z.val ≠ 0 := by
  intro hz
  have hp := inner_pole_add_tangent p z
  rw [hz, inner_zero_right] at hp
  norm_num at hp

/-- Central projection from a hemisphere to its tangent affine plane,
translated so that its pole corresponds to the origin. -/
def gnomonic (p : GeodesicSphere n) (x : openHemisphere p) : tangentPlane p :=
  ⟨(inner ℝ p.val x.val.val)⁻¹ • x.val.val - p.val, by
    change inner ℝ p.val ((inner ℝ p.val x.val.val)⁻¹ • x.val.val - p.val) = 0
    rw [inner_sub_right, inner_smul_right,
      inner_self_eq_one_of_norm_eq_one p.norm_val, inv_mul_cancel₀ (ne_of_gt x.property),
      sub_self]⟩

@[simp]
lemma gnomonic_val (p : GeodesicSphere n) (x : openHemisphere p) :
    (gnomonic p x).val = (inner ℝ p.val x.val.val)⁻¹ • x.val.val - p.val := rfl

lemma continuous_gnomonic (p : GeodesicSphere n) : Continuous (gnomonic p) := by
  have hv : Continuous (fun x : openHemisphere p => x.val.val) :=
    continuous_val.comp continuous_subtype_val
  have hd : Continuous (fun x : openHemisphere p => inner ℝ p.val x.val.val) :=
    continuous_const.inner hv
  exact (((hd.inv₀ (fun x => ne_of_gt x.property)).smul hv).sub continuous_const).subtype_mk _

/-- Inverse central projection, obtained by normalizing a point of the tangent
affine plane. -/
def gnomonicInverse (p : GeodesicSphere n) (z : tangentPlane p) : openHemisphere p :=
  ⟨normalizeVector (p.val + z.val) (pole_add_tangent_ne_zero p z), by
    change 0 < inner ℝ p.val (NormedSpace.normalize (p.val + z.val))
    rw [NormedSpace.normalize, inner_smul_right, inner_pole_add_tangent, mul_one]
    exact inv_pos.mpr (norm_pos_iff.mpr (pole_add_tangent_ne_zero p z))⟩

@[simp]
lemma gnomonicInverse_val_val (p : GeodesicSphere n) (z : tangentPlane p) :
    (gnomonicInverse p z).val.val = NormedSpace.normalize (p.val + z.val) := rfl

lemma continuous_gnomonicInverse (p : GeodesicSphere n) : Continuous (gnomonicInverse p) :=
  (continuous_normalizeVector (fun z : tangentPlane p => p.val + z.val)
    (continuous_const.add continuous_subtype_val) (pole_add_tangent_ne_zero p)).subtype_mk _

@[simp]
lemma gnomonicInverse_gnomonic (p : GeodesicSphere n) (x : openHemisphere p) :
    gnomonicInverse p (gnomonic p x) = x := by
  apply Subtype.ext
  apply GeodesicSphere.ext
  change NormedSpace.normalize
    (p.val + ((inner ℝ p.val x.val.val)⁻¹ • x.val.val - p.val)) = x.val.val
  have heq : p.val + ((inner ℝ p.val x.val.val)⁻¹ • x.val.val - p.val) =
      (inner ℝ p.val x.val.val)⁻¹ • x.val.val := by abel
  rw [heq, NormedSpace.normalize_smul_of_pos (inv_pos.mpr x.property),
    NormedSpace.normalize_eq_self_of_norm_eq_one x.val.norm_val]

@[simp]
lemma gnomonic_gnomonicInverse (p : GeodesicSphere n) (z : tangentPlane p) :
    gnomonic p (gnomonicInverse p z) = z := by
  apply Subtype.ext
  change (inner ℝ p.val (NormedSpace.normalize (p.val + z.val)))⁻¹ •
    NormedSpace.normalize (p.val + z.val) - p.val = z.val
  rw [NormedSpace.normalize, inner_smul_right, inner_pole_add_tangent,
    mul_one, inv_inv, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (pole_add_tangent_ne_zero p z)), one_smul]
  abel

/-- The gnomonic homeomorphism, with all maps and continuity proofs explicit. -/
def gnomonicHomeomorph (p : GeodesicSphere n) : openHemisphere p ≃ₜ tangentPlane p where
  toFun := gnomonic p
  invFun := gnomonicInverse p
  left_inv := gnomonicInverse_gnomonic p
  right_inv := gnomonic_gnomonicInverse p
  continuous_toFun := continuous_gnomonic p
  continuous_invFun := continuous_gnomonicInverse p

end GeodesicSphere
