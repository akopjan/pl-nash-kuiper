module

public import BrehmApprox.SphericalSimplexLink

/-!
# Radial charts on spherical simplex links

The fixed-radius slice of a spherical simplex is homeomorphic to the
spherical cell of its unit tangent directions.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.SphericalLink

open GeodesicSphere CrossPolytope

variable {n : ℕ}

local instance sphericalLinkChartDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem continuous_sphere_of_val {T : Type*} [TopologicalSpace T]
    {f : T → GeodesicSphere n} (hf : Continuous (fun x => (f x).val)) : Continuous f := by
  have hunit : Continuous (fun x => (⟨(f x).val, by simpa only [Metric.mem_sphere, dist_zero_right] using (f x).norm_val⟩ :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := hf.subtype_mk _
  exact (continuous_unitSphereEquiv n).comp hunit

def radiusSlice (V : Finset (GeodesicSphere n)) (p : GeodesicSphere n) (r : ℝ) :
    Set (GeodesicSphere n) := {x | x ∈ sphericalCell V ∧ dist x p = r}

theorem radiusSlice_tangent_ne_zero
    {V : Finset (GeodesicSphere n)} {p : GeodesicSphere n} {r : ℝ}
    (hr : 0 < r) (hrπ : r < Real.pi) (x : radiusSlice V p r) :
    tangentLinear p x.val.val ≠ 0 := by
  have hn : ‖tangentLinear p x.val.val‖ = Real.sin r := by
    change ‖radialVector p x.val‖ = Real.sin r
    rw [norm_radialVector, dist_comm, x.property.2]
  exact norm_pos_iff.mp ((Real.sin_pos_of_pos_of_lt_pi hr hrπ).trans_eq hn.symm)

def sliceDirection {V : Finset (GeodesicSphere n)} {p : GeodesicSphere n} {r : ℝ}
    (x : radiusSlice V p r) : GeodesicSphere n := sphereNormalize (tangentLinear p x.val.val)

theorem inner_sliceDirection
    {V : Finset (GeodesicSphere n)} {p : GeodesicSphere n} {r : ℝ}
    (hr : 0 < r) (hrπ : r < Real.pi) (x : radiusSlice V p r) :
    inner ℝ p.val (sliceDirection x).val = 0 := by
  rw [sliceDirection, sphereNormalize_val (radiusSlice_tangent_ne_zero hr hrπ x)]
  simp only [NormedSpace.normalize, inner_smul_right, inner_tangentLinear, mul_zero]

theorem radialPoint_sliceDirection
    {V : Finset (GeodesicSphere n)} {p : GeodesicSphere n} {r : ℝ}
    (hr : 0 < r) (hrπ : r < Real.pi) (x : radiusSlice V p r) :
    radialPoint p (sliceDirection x) (inner_sliceDirection hr hrπ x) r = x.val := by
  have hx : dist p x.val = r := (dist_comm _ _).trans x.property.2
  have hx0 : 0 < dist p x.val := hr.trans_eq hx.symm
  have hxπ : dist p x.val < Real.pi := hx.trans_lt hrπ
  have hd := radial_decomposition p x.val hx0 hxπ
  rw [radialDirection_eq_normalize] at hd
  apply GeodesicSphere.ext
  rw [radialPoint_val, sliceDirection,
    sphereNormalize_val (radiusSlice_tangent_ne_zero hr hrπ x)]
  simpa only [hx, tangentLinear_apply, radialVector] using hd.symm

/-- The radial chart of a spherical simplex at a fixed positive radius. -/
def radialSliceHomeomorph
    (V : Finset (GeodesicSphere n)) (p : GeodesicSphere n)
    {r : ℝ} (hr : 0 < r) (hrπ : r < Real.pi) (W : Finset (GeodesicSphere n))
    (hW : ∀ u ∈ sphericalCell W, inner ℝ p.val u.val = 0)
    (hmem : ∀ u : GeodesicSphere n, ∀ hu : inner ℝ p.val u.val = 0,
      radialPoint p u hu r ∈ sphericalCell V ↔ u ∈ sphericalCell W) :
    radiusSlice V p r ≃ₜ sphericalCell W where
  toFun x := ⟨sliceDirection x, (hmem _ (inner_sliceDirection hr hrπ x)).mp (by
    rw [radialPoint_sliceDirection hr hrπ x]
    exact x.property.1)⟩
  invFun u := ⟨radialPoint p u.val (hW u.val u.property) r,
    (hmem _ _).mpr u.property, radialPoint_dist_p _ _ _ hr.le hrπ.le⟩
  left_inv x := Subtype.ext (radialPoint_sliceDirection hr hrπ x)
  right_inv u := by
    apply Subtype.ext
    change sphereNormalize (tangentLinear p (radialPoint p u.val (hW u.val u.property) r).val) = u.val
    rw [tangentLinear_radialPoint]
    exact sphereNormalize_pos_smul u.val (Real.sin_pos_of_pos_of_lt_pi hr hrπ)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc := continuous_normalizeVector
      (fun x : radiusSlice V p r => tangentLinear p x.val.val)
      ((tangentLinear p).toContinuousLinearMap.continuous.comp
        (continuous_val.comp continuous_subtype_val)) (radiusSlice_tangent_ne_zero hr hrπ)
    convert hc using 1
    funext x
    simp only [sliceDirection, sphereNormalize,
      dite_eq_right (radiusSlice_tangent_ne_zero hr hrπ x)]
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_sphere_of_val
    change Continuous (fun u : sphericalCell W => Real.cos r • p.val + Real.sin r • u.val.val)
    have hval : Continuous (fun u : sphericalCell W => u.val.val) :=
      continuous_val.comp continuous_subtype_val
    exact continuous_const.add (hval.const_smul (Real.sin r))

@[simp]
theorem radialSliceHomeomorph_apply
    (V : Finset (GeodesicSphere n)) (p : GeodesicSphere n)
    {r : ℝ} (hr : 0 < r) (hrπ : r < Real.pi) (W : Finset (GeodesicSphere n))
    (hW : ∀ u ∈ sphericalCell W, inner ℝ p.val u.val = 0)
    (hmem : ∀ u : GeodesicSphere n, ∀ hu : inner ℝ p.val u.val = 0,
      radialPoint p u hu r ∈ sphericalCell V ↔ u ∈ sphericalCell W)
    (x : radiusSlice V p r) :
    (radialSliceHomeomorph V p hr hrπ W hW hmem x).val = sliceDirection x := rfl

end BrehmApprox.SphericalLink
