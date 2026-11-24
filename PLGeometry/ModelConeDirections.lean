module

public import PLGeometry.ModelCones
public import BrehmApprox.EuclideanFoldingGeometry
public import BrehmApprox.SphericalFoldingGeometry

/-! # Canonical directions and reconstruction in model polar coordinates -/

@[expose] public section
noncomputable section

open BrehmApprox
open scoped InnerProductSpace

namespace ArchivePLGeometry

variable {n : ℕ}

/-- The unit direction of a point viewed from a distinct pole. On the sphere,
the point must also be distinct from the antipode of the pole. -/
def coneDirection (κ : Geometry) (n : ℕ) (o x : Model κ (n + 1))
    (h0 : 0 < dist o x) (hπ : κ = .spherical → dist o x < Real.pi) :
    GeodesicSphere n :=
  match κ with
  | .euclidean => ⟨EuclideanFolding.radialDirection o x,
      EuclideanFolding.radialDirection_norm o x (dist_pos.mp h0)⟩
  | .spherical => ⟨GeodesicSphere.tangentEuclideanEquiv o
      (GeodesicSphere.radialDirection o x h0 (hπ rfl)), by
        rw [LinearIsometryEquiv.norm_map]
        exact GeodesicSphere.radialDirection_norm o x h0 (hπ rfl)⟩
  | .hyperbolic => ⟨HyperbolicSpace.radialDirection o x,
      HyperbolicSpace.radialDirection_norm o x h0⟩

@[simp] theorem coneDirection_euclidean_val
    (o x : Model .euclidean (n + 1)) (h0 : 0 < dist o x)
    (hπ : Geometry.euclidean = .spherical → dist o x < Real.pi) :
    (coneDirection .euclidean n o x h0 hπ).val = EuclideanFolding.radialDirection o x := rfl

@[simp] theorem coneDirection_spherical_val
    (o x : Model .spherical (n + 1)) (h0 : 0 < dist o x)
    (hπ : Geometry.spherical = .spherical → dist o x < Real.pi) :
    (coneDirection .spherical n o x h0 hπ).val =
      GeodesicSphere.tangentEuclideanEquiv o
        (GeodesicSphere.radialDirection o x h0 (hπ rfl)) := rfl

@[simp] theorem coneDirection_hyperbolic_val
    (o x : Model .hyperbolic (n + 1)) (h0 : 0 < dist o x)
    (hπ : Geometry.hyperbolic = .spherical → dist o x < Real.pi) :
    (coneDirection .hyperbolic n o x h0 hπ).val = HyperbolicSpace.radialDirection o x := rfl

/-- Radius and unit direction reconstruct the original model point. -/
theorem conePoint_coneDirection (κ : Geometry) (o x : Model κ (n + 1))
    (h0 : 0 < dist o x) (hπ : κ = .spherical → dist o x < Real.pi) :
    conePoint κ n o (coneDirection κ n o x h0 hπ) (dist o x) = x := by
  cases κ with
  | euclidean => exact (EuclideanFolding.radial_decomposition o x).symm
  | spherical =>
    apply GeodesicSphere.ext
    change Real.cos (dist o x) • o.val + Real.sin (dist o x) •
      ((GeodesicSphere.tangentEuclideanEquiv o).symm
        (GeodesicSphere.tangentEuclideanEquiv o
          (GeodesicSphere.radialDirection o x h0 (hπ rfl)))).val = x.val
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact (GeodesicSphere.radial_decomposition o x h0 (hπ rfl)).symm
  | hyperbolic =>
    apply (HyperbolicSpace.boostEquiv o.point).injective
    change HyperbolicSpace.boostBy o.point
      (HyperbolicLink.radialPoint o (coneDirection .hyperbolic n o x h0 hπ) (dist o x)) =
      HyperbolicSpace.boostBy o.point x
    rw [HyperbolicLink.boost_radialPoint]
    apply HyperbolicSpace.ext
    exact HyperbolicSpace.sinh_smul_radialDirection o x

/-- Polar metric comparison transfers an angular cell isometry to its cone. -/
theorem conePoint_dist_of_directions (κ : Geometry) (o p x y : Model κ (n + 1))
    (hx : 0 < dist o x) (hy : 0 < dist o y)
    (hxπ : κ = .spherical → dist o x < Real.pi)
    (hyπ : κ = .spherical → dist o y < Real.pi)
    (u v : GeodesicSphere n)
    (huv : dist u v = dist (coneDirection κ n o x hx hxπ) (coneDirection κ n o y hy hyπ)) :
    dist (conePoint κ n p u (dist o x)) (conePoint κ n p v (dist o y)) = dist x y := by
  have h := conePoint_dist_eq κ p o u v
    (coneDirection κ n o x hx hxπ) (coneDirection κ n o y hy hyπ)
    (dist o x) (dist o y) huv
  rwa [conePoint_coneDirection, conePoint_coneDirection] at h

end ArchivePLGeometry
