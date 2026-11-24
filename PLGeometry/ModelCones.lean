module

public import PLGeometry.Definitions
public import BrehmApprox.SphericalTangentDimension
public import BrehmApprox.SphericalGeodesics
public import BrehmApprox.HyperbolicSimplexLink
public import BrehmApprox.HyperbolicRadialFolding

/-!
# Radial cones in the three model geometries

The radius and the spherical distance between directions determine every
pairwise cone distance. This is the metric identity used to extend angular
piecewise isometries across the Voronoi cones.
-/

@[expose] public section
noncomputable section

open BrehmApprox
open scoped InnerProductSpace

namespace ArchivePLGeometry

variable {n : ℕ}

def sphericalConeDirection (o : GeodesicSphere (n + 1)) (u : GeodesicSphere n) :
    GeodesicSphere.tangentPlane o := (GeodesicSphere.tangentEuclideanEquiv o).symm u.val

@[simp] theorem sphericalConeDirection_norm (o : GeodesicSphere (n + 1)) (u : GeodesicSphere n) :
    ‖sphericalConeDirection o u‖ = 1 := by
  rw [sphericalConeDirection, (GeodesicSphere.tangentEuclideanEquiv o).symm.norm_map, u.norm_val]

theorem sphericalConeDirection_inner (o : GeodesicSphere (n + 1)) (u v : GeodesicSphere n) :
    ⟪(sphericalConeDirection o u).val, (sphericalConeDirection o v).val⟫_ℝ = ⟪u.val, v.val⟫_ℝ :=
  (GeodesicSphere.tangentEuclideanEquiv o).symm.inner_map_map u.val v.val

/-- The point at signed radius `r` in a unit angular direction at `o`. -/
def conePoint (κ : Geometry) (n : ℕ) (o : Model κ (n + 1))
    (u : GeodesicSphere n) (r : ℝ) : Model κ (n + 1) :=
  match κ with
  | .euclidean => o + r • u.val
  | .spherical => GeodesicSphere.radialCircle o (sphericalConeDirection o u)
      (sphericalConeDirection_norm o u) r
  | .hyperbolic => HyperbolicLink.radialPoint o u r

@[simp] theorem conePoint_zero (κ : Geometry) (o : Model κ (n + 1)) (u : GeodesicSphere n) :
    conePoint κ n o u 0 = o := by
  cases κ with
  | euclidean => simp only [conePoint, zero_smul, add_zero]
  | spherical =>
    apply GeodesicSphere.ext
    simp only [conePoint, GeodesicSphere.radialCircle_val, Real.cos_zero, Real.sin_zero,
      one_smul, zero_smul, add_zero]
  | hyperbolic =>
    apply dist_eq_zero.mp
    exact HyperbolicLink.radialPoint_dist o u le_rfl

theorem conePoint_dist_pole (κ : Geometry) (o : Model κ (n + 1)) (u : GeodesicSphere n)
    {r : ℝ} (hr : 0 ≤ r) (hrπ : κ = .spherical → r ≤ Real.pi) :
    dist (conePoint κ n o u r) o = r := by
  cases κ with
  | euclidean =>
    change dist (o + r • u.val) o = r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, u.norm_val, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hr]
  | spherical =>
    have hzero : GeodesicSphere.radialCircle o (sphericalConeDirection o u)
        (sphericalConeDirection_norm o u) 0 = o := conePoint_zero .spherical o u
    have h := GeodesicSphere.radialCircle_dist o (sphericalConeDirection o u)
      (sphericalConeDirection_norm o u) r 0
      (by simpa only [sub_zero, abs_of_nonneg hr] using hrπ rfl)
    rw [hzero, sub_zero, abs_of_nonneg hr] at h
    exact h
  | hyperbolic => exact HyperbolicLink.radialPoint_dist o u hr

theorem euclidean_cone_dist_sq (o : Model .euclidean (n + 1))
    (u v : GeodesicSphere n) (r s : ℝ) :
    dist (conePoint .euclidean n o u r) (conePoint .euclidean n o v s) ^ 2 =
      r ^ 2 + s ^ 2 - 2 * r * s * Real.cos (dist u v) := by
  change dist (o + r • u.val) (o + s • v.val) ^ 2 = _
  rw [dist_eq_norm, add_sub_add_left_eq_sub, norm_sub_sq_real,
    norm_smul, norm_smul, u.norm_val, v.norm_val, mul_one, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right, GeodesicSphere.cos_dist]
  ring

theorem spherical_cone_cos_dist (o : Model .spherical (n + 1))
    (u v : GeodesicSphere n) (r s : ℝ) :
    Real.cos (dist (conePoint .spherical n o u r) (conePoint .spherical n o v s)) =
      Real.cos r * Real.cos s + Real.sin r * Real.sin s * Real.cos (dist u v) := by
  rw [GeodesicSphere.cos_dist]
  change ⟪Real.cos r • o.val + Real.sin r • (sphericalConeDirection o u).val,
    Real.cos s • o.val + Real.sin s • (sphericalConeDirection o v).val⟫_ℝ = _
  have horth : ⟪(sphericalConeDirection o u).val, o.val⟫_ℝ = 0 := by
    rw [real_inner_comm, GeodesicSphere.inner_tangentPlane]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_self_eq_one_of_norm_eq_one o.norm_val, GeodesicSphere.inner_tangentPlane, horth,
    sphericalConeDirection_inner, GeodesicSphere.cos_dist]
  ring

theorem hyperbolic_cone_cosh_dist (o : Model .hyperbolic (n + 1))
    (u v : GeodesicSphere n) (r s : ℝ) :
    Real.cosh (dist (conePoint .hyperbolic n o u r) (conePoint .hyperbolic n o v s)) =
      Real.cosh r * Real.cosh s - Real.sinh r * Real.sinh s * Real.cos (dist u v) := by
  have h := (HyperbolicSpace.isometry_boostBy o.point).dist_eq
    (HyperbolicLink.radialPoint o u r) (HyperbolicLink.radialPoint o v s)
  rw [HyperbolicLink.boost_radialPoint, HyperbolicLink.boost_radialPoint] at h
  change Real.cosh (dist (HyperbolicLink.radialPoint o u r) (HyperbolicLink.radialPoint o v s)) = _
  rw [← h, HyperbolicSpace.cosh_dist, Hyperboloid.coshDist,
    HyperbolicSpace.height_radialLine u.norm_val, HyperbolicSpace.height_radialLine v.norm_val]
  change Real.cosh r * Real.cosh s - ⟪Real.sinh r • u.val, Real.sinh s • v.val⟫_ℝ = _
  rw [real_inner_smul_left, real_inner_smul_right, GeodesicSphere.cos_dist]
  ring

/-- Congruent angular pairs at the same radii give equal cone distances. -/
theorem conePoint_dist_eq (κ : Geometry) (o p : Model κ (n + 1))
    (u v u' v' : GeodesicSphere n) (r s : ℝ) (hangle : dist u v = dist u' v') :
    dist (conePoint κ n o u r) (conePoint κ n o v s) =
      dist (conePoint κ n p u' r) (conePoint κ n p v' s) := by
  cases κ with
  | euclidean =>
    have hsq : dist (conePoint .euclidean n o u r) (conePoint .euclidean n o v s) ^ 2 =
        dist (conePoint .euclidean n p u' r) (conePoint .euclidean n p v' s) ^ 2 := by
      rw [euclidean_cone_dist_sq, euclidean_cone_dist_sq, hangle]
    nlinarith [dist_nonneg (x := conePoint .euclidean n o u r) (y := conePoint .euclidean n o v s),
      dist_nonneg (x := conePoint .euclidean n p u' r) (y := conePoint .euclidean n p v' s)]
  | spherical =>
    rw [GeodesicSphere.dist_eq_arccos_inner, GeodesicSphere.dist_eq_arccos_inner,
      ← GeodesicSphere.cos_dist, ← GeodesicSphere.cos_dist,
      spherical_cone_cos_dist, spherical_cone_cos_dist, hangle]
  | hyperbolic =>
    apply Real.cosh_injOn dist_nonneg dist_nonneg
    rw [hyperbolic_cone_cosh_dist, hyperbolic_cone_cosh_dist, hangle]

end ArchivePLGeometry
