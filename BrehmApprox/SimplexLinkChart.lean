module

public import BrehmApprox.SimplexRadialLink

/-!
# Charts on small spherical slices of Euclidean simplices

Radial normalization gives an explicit homeomorphism from a fixed-radius
simplex slice to its spherical link.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.RadialLink

open GeodesicSphere CrossPolytope

variable {n : ℕ}

local instance linkChartDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def radiusSlice (V : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (p : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | x ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∧ dist x p = r}

theorem radiusSlice_sub_ne_zero
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    {p : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hr : 0 < r)
    (x : radiusSlice V p r) : x.val - p ≠ 0 := by
  have hn : ‖x.val - p‖ = r := by simpa only [dist_eq_norm] using x.property.2
  exact norm_pos_iff.mp (hr.trans_eq hn.symm)

theorem radiusSlice_radial_eq
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    {p : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hr : 0 < r)
    (x : radiusSlice V p r) : p + r • (sphereNormalize (x.val - p)).val = x.val := by
  have hn : ‖x.val - p‖ = r := by simpa only [dist_eq_norm] using x.property.2
  have hscale : r • (sphereNormalize (x.val - p)).val = x.val - p := by
    calc
      _ = ‖x.val - p‖ • (sphereNormalize (x.val - p)).val :=
        congrArg (fun t : ℝ => t • (sphereNormalize (x.val - p)).val) hn.symm
      _ = x.val - p := norm_smul_sphereNormalize (radiusSlice_sub_ne_zero hr x)
  rw [hscale]
  abel

/-- The radial chart on a fixed-radius slice. -/
def radialSliceHomeomorph
    (V : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (p : EuclideanSpace ℝ (Fin (n + 1))) {r : ℝ} (hr : 0 < r)
    (W : Finset (GeodesicSphere n))
    (hmem : ∀ u : GeodesicSphere n,
      p + r • u.val ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ↔
        u ∈ sphericalCell W) :
    radiusSlice V p r ≃ₜ sphericalCell W where
  toFun x := ⟨sphereNormalize (x.val - p), (hmem _).mp (by
    rw [radiusSlice_radial_eq hr x]
    exact x.property.1)⟩
  invFun u := ⟨p + r • u.val.val, (hmem u.val).mpr u.property, by
    rw [dist_eq_norm]
    have heq : p + r • u.val.val - p = r • u.val.val := by abel
    rw [heq, norm_smul, u.val.norm_val, mul_one, Real.norm_eq_abs, abs_of_pos hr]⟩
  left_inv x := Subtype.ext (radiusSlice_radial_eq hr x)
  right_inv u := by
    apply Subtype.ext
    change sphereNormalize (p + r • u.val.val - p) = u.val
    have heq : p + r • u.val.val - p = r • u.val.val := by abel
    rw [heq]
    exact sphereNormalize_pos_smul u.val hr
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc := continuous_normalizeVector
      (fun x : radiusSlice V p r => x.val - p)
      (continuous_subtype_val.sub continuous_const) (radiusSlice_sub_ne_zero hr)
    convert hc using 1
    funext x
    simp only [sphereNormalize, dite_eq_right (radiusSlice_sub_ne_zero hr x)]
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hval : Continuous (fun u : sphericalCell W => u.val.val) :=
      continuous_val.comp continuous_subtype_val
    exact continuous_const.add (hval.const_smul r)

@[simp]
theorem radialSliceHomeomorph_apply
    (V : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (p : EuclideanSpace ℝ (Fin (n + 1))) {r : ℝ} (hr : 0 < r)
    (W : Finset (GeodesicSphere n))
    (hmem : ∀ u : GeodesicSphere n,
      p + r • u.val ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ↔
        u ∈ sphericalCell W)
    (x : radiusSlice V p r) :
    (radialSliceHomeomorph V p hr W hmem x).val = sphereNormalize (x.val - p) := rfl

end BrehmApprox.RadialLink
