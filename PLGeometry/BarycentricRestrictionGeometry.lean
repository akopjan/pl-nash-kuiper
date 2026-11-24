module

public import PLGeometry.ChartedBarycentricLinear
public import PLGeometry.BarycentricRealization

/-! # Linear restriction of standard barycentric coordinates -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.Barycentric

variable {ι J : Type*} [Fintype ι]

local instance barycentricRestrictionGeometryDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def restrictionLinear (σ : Finset ι) : (ι → ℝ) →ₗ[ℝ] (σ → ℝ) where
  toFun w i := w i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extensionLinear (σ : Finset ι) : (σ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun w i := if hi : i ∈ σ then w ⟨i, hi⟩ else 0
  map_add' x y := by ext i; by_cases hi : i ∈ σ <;> simp [hi]
  map_smul' c x := by ext i; by_cases hi : i ∈ σ <;> simp [hi]

theorem extension_restriction (σ : Finset ι) (w : weightsOn σ) :
    extensionLinear σ (restrict σ w).val = w.val := by
  funext i
  by_cases hi : i ∈ σ
  · simp only [extensionLinear, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left hi, restrict]
  · simp only [extensionLinear, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_right hi,
      w.property.2 i hi]

theorem restrict_mem_convexHull_iff (σ : Finset ι) (w : J → weightsOn σ) (x : weightsOn σ) :
    (restrict σ x).val ∈ convexHull ℝ (Set.range (fun j => (restrict σ (w j)).val)) ↔
      x.val ∈ convexHull ℝ (Set.range (fun j => (w j).val)) := by
  constructor
  · intro hx
    have h := linear_maps_convexHull_range (extensionLinear σ)
      (fun j => (restrict σ (w j)).val) hx
    simpa only [extension_restriction] using h
  · intro hx
    exact linear_maps_convexHull_range (restrictionLinear σ) (fun j => (w j).val) hx

theorem affineIndependent_restrict_iff (σ : Finset ι) (w : J → weightsOn σ) :
    AffineIndependent ℝ (fun j => (restrict σ (w j)).val) ↔
      AffineIndependent ℝ (fun j => (w j).val) := by
  constructor
  · intro h
    exact AffineIndependent.of_comp (restrictionLinear σ).toAffineMap h
  · intro h
    apply AffineIndependent.of_comp (extensionLinear σ).toAffineMap
    change AffineIndependent ℝ (fun j => extensionLinear σ (restrict σ (w j)).val)
    simpa only [extension_restriction] using h

end ArchivePLGeometry.Barycentric
