module

public import PLGeometry.BarycentricRealization
public import BrehmApprox.PolytopeVertices

/-! # Standard barycentric cells are finite polytopes with extreme faces -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.Barycentric

variable {ι : Type*} [Fintype ι]

local instance barycentricPolytopesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance barycentricPolytopesFunctionEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem weightsOn_eq_convexHull (σ : Finset ι) :
    weightsOn σ = convexHull ℝ (σ.image (fun i => Pi.single i (1 : ℝ)) : Set (ι → ℝ)) := by
  let p : ι → (ι → ℝ) := fun i => Pi.single i 1
  change weightsOn σ = convexHull ℝ (σ.image p : Set (ι → ℝ))
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hid : Pulling.barycenter p = id := by
    funext w j
    simp [p, Pulling.barycenter, Finset.sum_apply, Pi.single_apply]
  rw [Pulling.convexHull_eq_barycenter_image, hid, Set.image_id]
  rfl

theorem weightsOn_polytope (σ : Finset ι) : IsFinitePolytope (weightsOn σ) :=
  ⟨σ.image (fun i => Pi.single i (1 : ℝ)), weightsOn_eq_convexHull σ⟩

theorem weightsOn_inter_extreme (σ τ : Finset ι) :
    _root_.IsExtreme ℝ (weightsOn σ) (weightsOn σ ∩ weightsOn τ) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ⟨hx.1, ?_⟩⟩
  intro i hi
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have he' := congrFun he i
  change a * x i + b * y i = z i at he'
  rw [hz.2.2 i hi] at he'
  have hx0 := hx.1.1 i
  have hy0 := hy.1.1 i
  have hby := mul_nonneg hb.le hy0
  have hax : a * x i = 0 := by nlinarith
  exact (mul_eq_zero.mp hax).resolve_left ha.ne'

end ArchivePLGeometry.Barycentric
