module

public import BrehmApprox.SphericalFoldingGeometry
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The dimension of a spherical tangent space

The tangent hyperplane to the round n-sphere is isometric to Euclidean
n-space. Its unit directions therefore form the round (n-1)-sphere.
-/

@[expose] public section
noncomputable section

open scoped InnerProductSpace

namespace GeodesicSphere

variable {n : ℕ}

theorem tangentPlane_eq_orthogonal (p : GeodesicSphere n) :
    tangentPlane p = (ℝ ∙ p.val)ᗮ := by
  ext v
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rfl

/-- An orthonormal coordinate system on the actual tangent hyperplane. -/
def tangentEuclideanEquiv (p : GeodesicSphere n) :
    tangentPlane p ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  exact (LinearIsometryEquiv.ofEq _ _ (tangentPlane_eq_orthogonal p)).trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton n p.val_ne_zero).repr

@[simp] theorem tangentEuclideanEquiv_inner (p : GeodesicSphere n) (u v : tangentPlane p) :
    ⟪tangentEuclideanEquiv p u, tangentEuclideanEquiv p v⟫_ℝ = ⟪u.val, v.val⟫_ℝ :=
  (tangentEuclideanEquiv p).inner_map_map u v

/-- Compress a unit ambient vector orthogonal to the pole to one lower sphere. -/
def compressTangent (p u : GeodesicSphere (n + 1)) (hu : ⟪p.val, u.val⟫_ℝ = 0) :
    GeodesicSphere n :=
  ⟨tangentEuclideanEquiv p ⟨u.val, hu⟩, by
    rw [(tangentEuclideanEquiv p).norm_map]
    exact u.norm_val⟩

@[simp] theorem compressTangent_inner (p u v : GeodesicSphere (n + 1))
    (hu : ⟪p.val, u.val⟫_ℝ = 0) (hv : ⟪p.val, v.val⟫_ℝ = 0) :
    ⟪(compressTangent p u hu).val, (compressTangent p v hv).val⟫_ℝ = ⟪u.val, v.val⟫_ℝ :=
  tangentEuclideanEquiv_inner p ⟨u.val, hu⟩ ⟨v.val, hv⟩

theorem compressTangent_dist (p u v : GeodesicSphere (n + 1))
    (hu : ⟪p.val, u.val⟫_ℝ = 0) (hv : ⟪p.val, v.val⟫_ℝ = 0) :
    dist (compressTangent p u hu) (compressTangent p v hv) = dist u v := by
  change InnerProductGeometry.angle (tangentEuclideanEquiv p ⟨u.val, hu⟩)
      (tangentEuclideanEquiv p ⟨v.val, hv⟩) = InnerProductGeometry.angle u.val v.val
  exact ((tangentEuclideanEquiv p).toLinearIsometry.angle_map
    (⟨u.val, hu⟩ : tangentPlane p) (⟨v.val, hv⟩ : tangentPlane p)).trans
    ((tangentPlane p).subtypeₗᵢ.angle_map (⟨u.val, hu⟩ : tangentPlane p)
      (⟨v.val, hv⟩ : tangentPlane p)).symm

theorem compressTangent_independent {ι : Type*} (p : GeodesicSphere (n + 1))
    (u : ι → GeodesicSphere (n + 1)) (hu : ∀ i, ⟪p.val, (u i).val⟫_ℝ = 0)
    (hi : LinearIndependent ℝ (fun i => (u i).val)) :
    LinearIndependent ℝ (fun i => (compressTangent p (u i) (hu i)).val) := by
  let v : ι → tangentPlane p := fun i => ⟨(u i).val, hu i⟩
  have hv : LinearIndependent ℝ v := LinearIndependent.of_comp (tangentPlane p).subtype hi
  exact hv.map' (tangentEuclideanEquiv p).toLinearMap
    (LinearMap.ker_eq_bot.mpr (tangentEuclideanEquiv p).injective)

end GeodesicSphere
