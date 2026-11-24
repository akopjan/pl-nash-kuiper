module

public import PLGeometry.BarycentricSupport
public import BrehmApprox.BarycentricReweighting

/-! # Positive reweighting of a finite simplicial realization -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.Barycentric.Complex

universe u
variable {ι : Type u} [Fintype ι] (K : Barycentric.Complex ι)

local instance complexReweightingDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def reweight (a : ι → ℝ) (ha : ∀ i, 0 < a i) (x : K.Space) : K.Space := by
  let w : BarycentricReweighting.Weights ι := ⟨x.val, K.weight_nonneg x, K.weight_sum x⟩
  let y := BarycentricReweighting.reweight a ha w
  refine ⟨y.val, Set.mem_iUnion₂.mpr ⟨K.support x, K.support_mem x, y.property, ?_⟩⟩
  intro i hi
  exact (BarycentricReweighting.reweight_eq_zero_iff a ha w i).mpr
    (K.weight_eq_zero_of_not_mem_support x hi)

@[simp] theorem reweight_val (a : ι → ℝ) (ha : ∀ i, 0 < a i) (x : K.Space) (i : ι) :
    (K.reweight a ha x).val i = a i * x.val i / BarycentricReweighting.total a x.val := rfl

theorem continuous_reweight (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Continuous (K.reweight a ha) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp ((BarycentricReweighting.continuous_reweight a ha).comp
    (continuous_subtype_val.subtype_mk (fun x => ⟨K.weight_nonneg x, K.weight_sum x⟩)))

theorem inverse_reweight (a : ι → ℝ) (ha : ∀ i, 0 < a i) (x : K.Space) :
    K.reweight (fun i => (a i)⁻¹) (fun i => inv_pos.mpr (ha i)) (K.reweight a ha x) = x := by
  apply Subtype.ext
  exact congrArg (fun w : BarycentricReweighting.Weights ι => w.val)
    (BarycentricReweighting.inverse_reweight a ha
    ⟨x.val, K.weight_nonneg x, K.weight_sum x⟩)

def reweightHomeomorph (a : ι → ℝ) (ha : ∀ i, 0 < a i) : K.Space ≃ₜ K.Space where
  toFun := K.reweight a ha
  invFun := K.reweight (fun i => (a i)⁻¹) (fun i => inv_pos.mpr (ha i))
  left_inv := K.inverse_reweight a ha
  right_inv x := by
    have h := K.inverse_reweight (fun i => (a i)⁻¹) (fun i => inv_pos.mpr (ha i)) x
    simpa only [inv_inv] using h
  continuous_toFun := K.continuous_reweight a ha
  continuous_invFun := K.continuous_reweight _ _

theorem reweight_mem_weightsOn_iff (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (x : K.Space) (σ : Finset ι) :
    (K.reweight a ha x).val ∈ Barycentric.weightsOn σ ↔ x.val ∈ Barycentric.weightsOn σ := by
  constructor
  · intro hx
    refine ⟨⟨K.weight_nonneg x, K.weight_sum x⟩, ?_⟩
    intro i hi
    exact (BarycentricReweighting.reweight_eq_zero_iff a ha
      ⟨x.val, K.weight_nonneg x, K.weight_sum x⟩ i).mp (hx.2 i hi)
  · intro hx
    refine ⟨⟨K.weight_nonneg (K.reweight a ha x), K.weight_sum (K.reweight a ha x)⟩, ?_⟩
    intro i hi
    exact (BarycentricReweighting.reweight_eq_zero_iff a ha
      ⟨x.val, K.weight_nonneg x, K.weight_sum x⟩ i).mpr (hx.2 i hi)

end ArchivePLGeometry.Barycentric.Complex
