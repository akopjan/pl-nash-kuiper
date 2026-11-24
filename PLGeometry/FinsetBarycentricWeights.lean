module

public import PLGeometry.ModelBarycentricNaturality

/-! # Extending barycentric weights from a face by zero -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.ModelBarycentric

variable {P : Type*}

local instance finsetBarycentricWeightsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def extendWeights {σ τ : Finset P} (hτσ : τ ⊆ σ) (w : Weights τ) : Weights σ :=
  ⟨fun v => if hv : v.val ∈ τ then w.val ⟨v.val, hv⟩ else 0,
    ⟨by
      intro v
      dsimp only
      split_ifs with hv
      · exact w.property.1 ⟨v.val, hv⟩
      · exact le_refl 0,
    by
      let a : P → ℝ := fun v => if hv : v ∈ τ then w.val ⟨v, hv⟩ else 0
      change (∑ v : σ, a v.val) = 1
      rw [Finset.sum_coe_sort]
      calc
        ∑ v ∈ σ, a v = ∑ v ∈ τ, a v :=
          (Finset.sum_subset hτσ (fun v _ hv => by simp only [a, dite_eq_right hv])).symm
        _ = ∑ v : τ, w.val v := by
          rw [← Finset.sum_coe_sort]
          apply Finset.sum_congr rfl
          intro v _
          simp only [a, dite_eq_left v.property]
        _ = 1 := w.property.2⟩⟩

theorem sum_extendWeights {σ τ : Finset P} (hτσ : τ ⊆ σ) (w : Weights τ)
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (v : P → E) :
    (∑ p : σ, (extendWeights hτσ w).val p • v p.val) = ∑ p : τ, w.val p • v p.val := by
  let a : P → ℝ := fun p => if hp : p ∈ τ then w.val ⟨p, hp⟩ else 0
  change (∑ p : σ, a p.val • v p.val) = _
  calc
    (∑ p : σ, a p.val • v p.val) = ∑ p ∈ σ, a p • v p :=
      Finset.sum_coe_sort σ (fun p => a p • v p)
    _ = ∑ p ∈ τ, a p • v p :=
      (Finset.sum_subset hτσ (fun p _ hp => by simp only [a, dite_eq_right hp, zero_smul])).symm
    _ = ∑ p : τ, w.val p • v p.val := by
      rw [← Finset.sum_coe_sort τ (fun p => a p • v p)]
      apply Finset.sum_congr rfl
      intro p _
      simp only [a, dite_eq_left p.property]

theorem represents_extend {κ : Geometry} {n : ℕ} {σ τ : Finset P}
    (hτσ : τ ⊆ σ) (w : Weights τ) (v : P → Model κ n) (x : Model κ n)
    (h : Represents κ n (fun p : τ => v p.val) w.val x) :
    Represents κ n (fun p : σ => v p.val) (extendWeights hτσ w).val x := by
  cases κ with
  | euclidean =>
    change (∑ p : σ, (extendWeights hτσ w).val p • v p.val) = x
    rw [sum_extendWeights]
    exact h
  | spherical =>
    obtain ⟨c, hc, he⟩ := h
    refine ⟨c, hc, ?_⟩
    change (∑ p : σ, (extendWeights hτσ w).val p • (v p.val).val) = c • x.val
    rw [sum_extendWeights hτσ w (fun p => (v p).val)]
    exact he
  | hyperbolic =>
    obtain ⟨c, hc, he⟩ := h
    refine ⟨c, hc, ?_⟩
    change (∑ p : σ, (extendWeights hτσ w).val p • HyperbolicSpace.lift (v p.val)) = c • HyperbolicSpace.lift x
    rw [sum_extendWeights hτσ w (fun p => HyperbolicSpace.lift (v p))]
    exact he

end ArchivePLGeometry.ModelBarycentric
