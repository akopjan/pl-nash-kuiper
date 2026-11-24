module

public import BrehmApprox.PositiveBarycentricGeometry

/-! # Transitivity of finite positive projective hulls -/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

variable {X V : Type*} [AddCommGroup V] [Module ℝ V]

local instance positiveHullTransitivityDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def positiveRayHull (lift : X → V) (A : Finset X) : Set X :=
  {x | ∃ w : X → ℝ, (∀ v ∈ A, 0 ≤ w v) ∧ ∃ c : ℝ, 0 < c ∧
    ∑ v ∈ A, w v • lift v = c • lift x}

theorem positiveRayHull_transitive (lift : X → V) (A B : Finset X)
    (hAB : (A : Set X) ⊆ positiveRayHull lift B) :
    positiveRayHull lift A ⊆ positiveRayHull lift B := by
  choose w hw c hc hrep using fun a : A => hAB a.property
  intro x hx
  obtain ⟨b, hb, d, hd, hbx⟩ := hx
  let a : X → ℝ := fun v => ∑ z : A, (b z.val / c z) * w z v
  refine ⟨a, ?_, d, hd, ?_⟩
  · intro v hv
    exact Finset.sum_nonneg (fun z _ =>
      mul_nonneg (div_nonneg (hb z.val z.property) (hc z).le) (hw z v hv))
  · calc
      ∑ v ∈ B, a v • lift v = ∑ z : A, (b z.val / c z) • ∑ v ∈ B, w z v • lift v := by
        simp only [a, Finset.sum_smul, Finset.smul_sum, smul_smul]
        exact Finset.sum_comm
      _ = ∑ z : A, b z.val • lift z.val := by
        apply Finset.sum_congr rfl
        intro z _
        rw [hrep z, smul_smul, div_mul_cancel₀ _ (hc z).ne']
      _ = ∑ z ∈ A, b z • lift z := Finset.sum_coe_sort A (fun z => b z • lift z)
      _ = d • lift x := hbx

end BrehmApprox
