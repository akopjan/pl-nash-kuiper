module

public import BrehmApprox.HyperbolicSimplexLink

/-! # Homeomorphisms between hyperbolic simplex slices and angular links -/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.HyperbolicLink

open HyperbolicSpace CrossPolytope

variable {n : ℕ}

def radiusSlice (V : Finset (HyperbolicSpace (n + 1))) (p : HyperbolicSpace (n + 1)) (r : ℝ) :
    Set (HyperbolicSpace (n + 1)) := {x | x ∈ hyperbolicCell V ∧ dist x p = r}

theorem radiusSlice_vector_ne_zero
    {V : Finset (HyperbolicSpace (n + 1))} {p : HyperbolicSpace (n + 1)} {r : ℝ}
    (hr : 0 < r) (x : radiusSlice V p r) : radialVector p x.val ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_radialVector, dist_comm, x.property.2]
  exact Real.sinh_pos_iff.mpr hr

def sliceDirection {V : Finset (HyperbolicSpace (n + 1))}
    {p : HyperbolicSpace (n + 1)} {r : ℝ} (x : radiusSlice V p r) : GeodesicSphere n :=
  sphereNormalize (radialVector p x.val)

theorem radialPoint_sliceDirection
    {V : Finset (HyperbolicSpace (n + 1))} {p : HyperbolicSpace (n + 1)} {r : ℝ}
    (hr : 0 < r) (x : radiusSlice V p r) : radialPoint p (sliceDirection x) r = x.val := by
  apply (boostEquiv p.point).injective
  change boostBy p.point (radialPoint p (sliceDirection x) r) = boostBy p.point x.val
  rw [boost_radialPoint]
  apply HyperbolicSpace.ext
  change Real.sinh r • (sphereNormalize (radialVector p x.val)).val = radialVector p x.val
  have hn : ‖radialVector p x.val‖ = Real.sinh r := by
    rw [norm_radialVector, dist_comm, x.property.2]
  rw [← hn]
  exact norm_smul_sphereNormalize (radiusSlice_vector_ne_zero hr x)

theorem direction_radialPoint (p : HyperbolicSpace (n + 1)) (u : GeodesicSphere n)
    {r : ℝ} (hr : 0 < r) : sphereNormalize (radialVector p (radialPoint p u r)) = u := by
  have hv : radialVector p (radialPoint p u r) = Real.sinh r • u.val := by
    rw [radialVector, boost_radialPoint]
    rfl
  rw [hv]
  exact sphereNormalize_pos_smul u (Real.sinh_pos_iff.mpr hr)

/-- Radial normalization is a homeomorphism on every sufficiently small positive slice. -/
def radialSliceHomeomorph
    (V : Finset (HyperbolicSpace (n + 1))) (p : HyperbolicSpace (n + 1))
    {r : ℝ} (hr : 0 < r) (W : Finset (GeodesicSphere n))
    (hmem : ∀ u : GeodesicSphere n,
      radialPoint p u r ∈ hyperbolicCell V ↔ u ∈ sphericalCell W) :
    radiusSlice V p r ≃ₜ sphericalCell W where
  toFun x := ⟨sliceDirection x, (hmem _).mp (by
    rw [radialPoint_sliceDirection hr x]
    exact x.property.1)⟩
  invFun u := ⟨radialPoint p u.val r, (hmem _).mpr u.property, radialPoint_dist p u.val hr.le⟩
  left_inv x := Subtype.ext (radialPoint_sliceDirection hr x)
  right_inv u := Subtype.ext (direction_radialPoint p u.val hr)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc := GeodesicSphere.continuous_normalizeVector
      (fun x : radiusSlice V p r => radialVector p x.val)
      ((continuous_point.comp (isometry_boostBy p.point).continuous).comp continuous_subtype_val)
      (radiusSlice_vector_ne_zero hr)
    convert hc using 1
    funext x
    simp only [sliceDirection, sphereNormalize, dite_eq_right (radiusSlice_vector_ne_zero hr x)]
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hval : Continuous (fun u : sphericalCell W => u.val.val) :=
      GeodesicSphere.continuous_val.comp continuous_subtype_val
    exact (isometry_boostBy (-p.point)).continuous.comp
      (continuous_mk.comp (hval.const_smul (Real.sinh r)))

@[simp] theorem radialSliceHomeomorph_apply
    (V : Finset (HyperbolicSpace (n + 1))) (p : HyperbolicSpace (n + 1))
    {r : ℝ} (hr : 0 < r) (W : Finset (GeodesicSphere n))
    (hmem : ∀ u : GeodesicSphere n,
      radialPoint p u r ∈ hyperbolicCell V ↔ u ∈ sphericalCell W)
    (x : radiusSlice V p r) :
    (radialSliceHomeomorph V p hr W hmem x).val = sliceDirection x := rfl

/-- The exact hyperbolic cosine law on a fixed-radius angular slice. -/
theorem cosh_dist_radialPoints (p : HyperbolicSpace (n + 1))
    (u v : GeodesicSphere n) (r : ℝ) :
    Real.cosh (dist (radialPoint p u r) (radialPoint p v r)) =
      (Real.cosh r) ^ 2 - (Real.sinh r) ^ 2 * inner ℝ u.val v.val := by
  rw [radialPoint, radialPoint, (isometry_boostBy (-p.point)).dist_eq,
    cosh_dist, Hyperboloid.coshDist, height_radialLine u.norm_val, height_radialLine v.norm_val]
  change Real.cosh r * Real.cosh r - inner ℝ (Real.sinh r • u.val) (Real.sinh r • v.val) = _
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

end BrehmApprox.HyperbolicLink
