module

public import PLGeometry.EuclideanExtension
public import PLGeometry.SphericalExtension
public import PLGeometry.HyperbolicExtension

/-!
# The Brehm–Akopyan–Tarasov extension theorem

Finite short data in a simply connected model space of constant curvature
extend to a global short PL-isometry in the same dimension. Here PL-isometry
means isometry on the simplices of an actual compatible, locally finite
geodesic triangulation.
-/

@[expose] public section

namespace ArchivePLGeometry

/-- **Brehm–Akopyan–Tarasov.** Finite short data extend to a global PL-isometry
in the same dimension and geometry. The hyperbolic case is included. -/
theorem brehm_akopyan_tarasov (κ : Geometry) (n : ℕ)
    (A : Finset (Model κ n)) (f : Model κ n → Model κ n)
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ dist x y) :
    ∃ F : Model κ n → Model κ n,
      LipschitzWith 1 F ∧ PLIsometry κ n F ∧ ∀ x ∈ A, F x = f x := by
  cases κ with
  | euclidean => exact brehm_euclidean n A f hf
  | spherical => exact brehm_spherical n A f hf
  | hyperbolic => exact brehm_hyperbolic n A f hf

end ArchivePLGeometry
