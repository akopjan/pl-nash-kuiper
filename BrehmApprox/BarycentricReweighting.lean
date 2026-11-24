module

public import BrehmApprox.EuclideanBarycentricSimplex

/-! # Positive reweighting of a standard simplex -/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace BrehmApprox.BarycentricReweighting

variable {ι : Type*} [Fintype ι]

local instance barycentricReweightingDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

abbrev Weights (ι : Type*) [Fintype ι] := Pulling.simplexWeights ι

def total (a : ι → ℝ) (w : ι → ℝ) : ℝ := ∑ i, a i * w i

theorem total_pos (a : ι → ℝ) (ha : ∀ i, 0 < a i) (w : Weights ι) : 0 < total a w.val := by
  have hs : (0 : ℝ) < ∑ i, w.val i := by rw [w.property.2]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => w.property.1 i)).mp hs
  exact Finset.sum_pos' (fun j _ => mul_nonneg (ha j).le (w.property.1 j))
    ⟨i, Finset.mem_univ i, mul_pos (ha i) hi⟩

def reweight (a : ι → ℝ) (ha : ∀ i, 0 < a i) (w : Weights ι) : Weights ι :=
  ⟨fun i => a i * w.val i / total a w.val,
    ⟨fun i => div_nonneg (mul_nonneg (ha i).le (w.property.1 i)) (total_pos a ha w).le,
      by rw [← Finset.sum_div]; exact div_self (total_pos a ha w).ne'⟩⟩

@[simp] theorem reweight_apply (a : ι → ℝ) (ha : ∀ i, 0 < a i) (w : Weights ι) (i : ι) :
    (reweight a ha w).val i = a i * w.val i / total a w.val := rfl

theorem continuous_reweight (a : ι → ℝ) (ha : ∀ i, 0 < a i) : Continuous (reweight a ha) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have ht : Continuous (fun w : Weights ι => total a w.val) := by
    unfold total
    exact continuous_finsetSum _ (fun i _ =>
      continuous_const.mul ((continuous_apply i).comp continuous_subtype_val))
  exact (continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)).div ht
    (fun w => (total_pos a ha w).ne')

theorem inverse_total (a : ι → ℝ) (ha : ∀ i, 0 < a i) (w : Weights ι) :
    total (fun i => (a i)⁻¹) (reweight a ha w).val = (total a w.val)⁻¹ := by
  unfold total
  simp only [reweight_apply]
  calc
    (∑ i, (a i)⁻¹ * (a i * w.val i / ∑ j, a j * w.val j)) =
        (∑ i, w.val i) / ∑ j, a j * w.val j := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(ha i).ne']
    _ = (∑ j, a j * w.val j)⁻¹ := by rw [w.property.2, one_div]

theorem inverse_reweight (a : ι → ℝ) (ha : ∀ i, 0 < a i) (w : Weights ι) :
    reweight (fun i => (a i)⁻¹) (fun i => inv_pos.mpr (ha i)) (reweight a ha w) = w := by
  apply Subtype.ext
  funext i
  rw [reweight_apply, inverse_total, reweight_apply]
  field_simp [(ha i).ne', (total_pos a ha w).ne']

def homeomorph (a : ι → ℝ) (ha : ∀ i, 0 < a i) : Weights ι ≃ₜ Weights ι where
  toFun := reweight a ha
  invFun := reweight (fun i => (a i)⁻¹) (fun i => inv_pos.mpr (ha i))
  left_inv := inverse_reweight a ha
  right_inv w := by
    have h := inverse_reweight (fun i => (a i)⁻¹) (fun i => inv_pos.mpr (ha i)) w
    simpa only [inv_inv] using h
  continuous_toFun := continuous_reweight a ha
  continuous_invFun := continuous_reweight _ _

@[simp] theorem homeomorph_apply (a : ι → ℝ) (ha : ∀ i, 0 < a i) (w : Weights ι) :
    homeomorph a ha w = reweight a ha w := rfl

theorem reweight_eq_zero_iff (a : ι → ℝ) (ha : ∀ i, 0 < a i) (w : Weights ι) (i : ι) :
    (reweight a ha w).val i = 0 ↔ w.val i = 0 := by
  rw [reweight_apply, div_eq_zero_iff]
  simp only [(ha i).ne', (total_pos a ha w).ne', or_false, mul_eq_zero, false_or]

end BrehmApprox.BarycentricReweighting
