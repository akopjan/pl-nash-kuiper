module

public import BrehmApprox.HyperbolicGeodesics
public import BrehmApprox.FiniteGramIsometry

/-!
# Real hyperbolic motions extending angular folding pieces

Orthogonal maps of the spatial frame induce genuine hyperbolic isometries.
Together with Lorentz boosts they extend congruent labelled radial families,
and each angular linear-isometric folding piece extends to a hyperbolic
motion. These are the metric and linear-algebra steps in initial folding;
the finite protected-net and angular-complex construction is not assumed.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

def orthogonalMap (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : HyperbolicSpace n) : HyperbolicSpace n := ⟨U x.point⟩

lemma height_orthogonalMap (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : HyperbolicSpace n) : Hyperboloid.height (orthogonalMap U x).point =
      Hyperboloid.height x.point := by
  simp only [orthogonalMap, Hyperboloid.height, U.norm_map]

theorem isometry_orthogonalMap
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Isometry (orthogonalMap U) := by
  apply Isometry.of_dist_eq
  intro x y
  apply Real.cosh_injOn dist_nonneg dist_nonneg
  rw [cosh_dist, cosh_dist, Hyperboloid.coshDist, Hyperboloid.coshDist,
    height_orthogonalMap, height_orthogonalMap]
  change Hyperboloid.height x.point * Hyperboloid.height y.point -
    ⟪U x.point, U y.point⟫_ℝ = _
  rw [U.inner_map_map]

def orthogonalEquiv (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    HyperbolicSpace n ≃ᵢ HyperbolicSpace n where
  toFun := orthogonalMap U
  invFun := orthogonalMap U.symm
  left_inv x := by
    apply HyperbolicSpace.ext
    exact U.symm_apply_apply x.point
  right_inv x := by
    apply HyperbolicSpace.ext
    exact U.apply_symm_apply x.point
  isometry_toFun := isometry_orthogonalMap U

lemma orthogonalMap_zero
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    orthogonalMap U (⟨0⟩ : HyperbolicSpace n) = ⟨0⟩ := by
  apply HyperbolicSpace.ext
  exact map_zero U

/-- Change from the frame at `a` to the frame at `b`, with prescribed
orthogonal map of those Euclidean spatial frames. -/
def radialMotion (a b : HyperbolicSpace n)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    HyperbolicSpace n ≃ᵢ HyperbolicSpace n :=
  (boostEquiv a.point).trans ((orthogonalEquiv U).trans (boostEquiv b.point).symm)

lemma radialMotion_apply (a b x : HyperbolicSpace n)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    radialMotion a b U x = boostBy (-b.point) (orthogonalMap U (boostBy a.point x)) := rfl

lemma radialMotion_center (a b : HyperbolicSpace n)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    radialMotion a b U a = b := by
  rw [radialMotion_apply, boostBy_self, orthogonalMap_zero]
  have h := boostBy_neg_inverse b.point b
  rwa [boostBy_self] at h

lemma radialMotion_apply_of_vector (a b x y : HyperbolicSpace n)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hxy : U (radialVector a x) = radialVector b y) : radialMotion a b U x = y := by
  have hframe : orthogonalMap U (boostBy a.point x) = boostBy b.point y := by
    apply HyperbolicSpace.ext
    exact hxy
  rw [radialMotion_apply, hframe, boostBy_neg_inverse]

lemma inner_radialVector (a x y : HyperbolicSpace n) :
    ⟪radialVector a x, radialVector a y⟫_ℝ =
      Real.cosh (dist a x) * Real.cosh (dist a y) - Real.cosh (dist x y) := by
  have h := Hyperboloid.boost_inner a.point x.point y.point
  simpa only [radialVector, boostBy, ← cosh_dist] using h

/-- A congruent labelled independent radial family extends to an actual
ambient hyperbolic motion. The second family's independence is derived. -/
theorem exists_radial_congruence {ι : Type*} [Fintype ι]
    (a b : HyperbolicSpace n) (v w : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => radialVector a (v i)))
    (hr : ∀ i, dist a (v i) = dist b (w i))
    (hd : ∀ i j, dist (v i) (v j) = dist (w i) (w j)) :
    ∃ e : HyperbolicSpace n ≃ᵢ HyperbolicSpace n,
      e a = b ∧ ∀ i, e (v i) = w i := by
  have hgram : ∀ i j, ⟪radialVector a (v i), radialVector a (v j)⟫_ℝ =
      ⟪radialVector b (w i), radialVector b (w j)⟫_ℝ := by
    intro i j
    rw [inner_radialVector, inner_radialVector, hr i, hr j, hd i j]
  obtain ⟨U, hU⟩ := BrehmApprox.exists_ambient_gram_isometry
    (fun i => radialVector a (v i)) (fun i => radialVector b (w i)) hv hgram
  exact ⟨radialMotion a b U, radialMotion_center a b U,
    fun i => radialMotion_apply_of_vector a b (v i) (w i) U (hU i)⟩

/-- The explicit radial formula used when all centers are folded to the
origin. The angular function is total so its arbitrary value at zero causes
no problem at the center, where the radial scalar vanishes. -/
def radialFold (a : HyperbolicSpace n)
    (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : HyperbolicSpace n) : HyperbolicSpace n :=
  ⟨Real.sinh (dist a x) • ψ (radialDirection a x)⟩

lemma radialFold_eq_motion (a x : HyperbolicSpace n)
    (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hψ : ψ (radialDirection a x) = U (radialDirection a x)) :
    radialFold a ψ x = orthogonalMap U (boostBy a.point x) := by
  apply HyperbolicSpace.ext
  change Real.sinh (dist a x) • ψ (radialDirection a x) = U (radialVector a x)
  rw [hψ, ← map_smul, sinh_smul_radialDirection]

/-- Every angular orthogonal piece becomes a genuine hyperbolic isometric
piece under the radial folding formula. -/
theorem radialFold_isometryOn_piece (a : HyperbolicSpace n)
    (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (A : Set (HyperbolicSpace n))
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hψ : ∀ x ∈ A, ψ (radialDirection a x) = U (radialDirection a x)) :
    ∃ e : HyperbolicSpace n ≃ᵢ HyperbolicSpace n, ∀ x ∈ A, radialFold a ψ x = e x := by
  refine ⟨(boostEquiv a.point).trans (orthogonalEquiv U), ?_⟩
  intro x hx
  exact radialFold_eq_motion a x ψ U (hψ x hx)

end BrehmApprox.HyperbolicSpace
