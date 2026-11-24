module

public import PLGeometry.ProtectedNetInduction
public import PLGeometry.EuclideanPolarCoordinates
public import PLGeometry.SphericalPolarCoordinates
public import PLGeometry.HyperbolicPolarCoordinates

/-!
# Finite protected nets in the three constant-curvature geometries

Every finite charted complex admits arbitrarily fine finite nets whose
nearest sites respect every common face. The construction is intrinsic to
the finite cell atlas and does not assume a folding of the source.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]

theorem exists_spherical_protected_net
    (T : FiniteChartedComplex .spherical n P) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  apply spherical_protected_net_of_polar_coordinates
    (fun Q _ _ A p => A.exists_sphericalPolarNetData p) T hη

theorem exists_euclidean_protected_net
    (T : FiniteChartedComplex .euclidean n P) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  cases n with
  | zero => exact T.exists_protected_net_zero hη
  | succ n =>
    apply T.exists_protected_net_of_link_nets T.euclideanLinkData
      T.exists_euclideanPolarNetData (fun p ε hε => ?_) hη
    exact (T.euclideanLink p).exists_spherical_protected_net hε

theorem exists_hyperbolic_protected_net
    (T : FiniteChartedComplex .hyperbolic n P) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  cases n with
  | zero => exact T.exists_protected_net_zero hη
  | succ n =>
    apply T.exists_protected_net_of_link_nets T.hyperbolicLinkData
      T.exists_hyperbolicPolarNetData (fun p ε hε => ?_) hη
    exact (T.hyperbolicLink p).exists_spherical_protected_net hε

/-- Arbitrarily fine finite protected nets exist in every finite Euclidean,
spherical, or hyperbolic charted complex. -/
theorem exists_protected_net {κ : Geometry} (T : FiniteChartedComplex κ n P)
    {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  cases κ with
  | euclidean => exact T.exists_euclidean_protected_net hη
  | spherical => exact T.exists_spherical_protected_net hη
  | hyperbolic => exact T.exists_hyperbolic_protected_net hη

end ArchivePLGeometry.FiniteChartedComplex
