module

public import PLGeometry.ModelProjectiveGeometry

/-! # Independence of the barycentric coordinates of independent model points -/

@[expose] public section
noncomputable section

open BrehmApprox

namespace ArchivePLGeometry.ModelBarycentric

variable {ι J : Type*} [Fintype ι] [Fintype J] {κ : Geometry} {n : ℕ}

theorem affineIndependent_of_independent (v : ι → Model κ n)
    (u : J → Model κ n) (w : J → Weights ι)
    (hw : ∀ j, Represents κ n v (w j).val (u j))
    (hu : Independent κ n u) : AffineIndependent ℝ (fun j => (w j).val) := by
  cases κ with
  | euclidean =>
    let L := Fintype.linearCombination ℝ v
    apply AffineIndependent.of_comp L.toAffineMap
    have he : L.toAffineMap ∘ (fun j => (w j).val) = u := by
      funext j
      exact hw j
    rw [he]
    exact hu
  | spherical =>
    let L := Fintype.linearCombination ℝ (fun i => (v i).val)
    choose c hc hrep using hw
    let a : J → ℝˣ := fun j => Units.mk0 (c j) (hc j).ne'
    have hi := hu.units_smul a
    have he : L ∘ (fun j => (w j).val) = a • (fun j => (u j).val) := by
      funext j
      exact hrep j
    have him : LinearIndependent ℝ (L ∘ (fun j => (w j).val)) := he ▸ hi
    exact (LinearIndependent.of_comp L him).affineIndependent
  | hyperbolic =>
    let L := Fintype.linearCombination ℝ (fun i => HyperbolicSpace.lift (v i))
    choose c hc hrep using hw
    let a : J → ℝˣ := fun j => Units.mk0 (c j) (hc j).ne'
    have hi := hu.units_smul a
    have he : L ∘ (fun j => (w j).val) = a • (fun j => HyperbolicSpace.lift (u j)) := by
      funext j
      exact hrep j
    have him : LinearIndependent ℝ (L ∘ (fun j => (w j).val)) := he ▸ hi
    exact (LinearIndependent.of_comp L him).affineIndependent

end ArchivePLGeometry.ModelBarycentric
