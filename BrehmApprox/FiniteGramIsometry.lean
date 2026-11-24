module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.Linarith

/-!
# Actual isometries determined by finite Gram matrices

Equal Gram matrices give equal norms of all linear combinations, preserve
linear independence, and induce the unique linear isometric equivalence of
the spans matching the labelled independent vectors. This provides the
non-combinatorial gluing step for angular simplices in the folding argument.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BrehmApprox

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Projecting an independent family along a vector outside its span keeps
the family independent. The projection coefficients may be arbitrary. -/
lemma linearIndependent_sub_smul_of_notMem_span (v : ι → E) (a : E) (c : ι → ℝ)
    (hv : LinearIndependent ℝ v) (ha : a ∉ Submodule.span ℝ (Set.range v)) :
    LinearIndependent ℝ (fun i => v i - c i • a) := by
  rw [Fintype.linearIndependent_iff]
  intro t ht i
  have hvec : (∑ j, t j • v j) = (∑ j, t j * c j) • a := by
    simpa only [smul_sub, smul_smul, Finset.sum_sub_distrib,
      ← Finset.sum_smul, sub_eq_zero] using ht
  have hmem : (∑ j, t j * c j) • a ∈ Submodule.span ℝ (Set.range v) := by
    rw [← hvec]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  have hc : (∑ j, t j * c j) = 0 := by
    by_contra hne
    apply ha
    have h := (Submodule.span ℝ (Set.range v)).smul_mem (∑ j, t j * c j)⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using h
  rw [hc, zero_smul] at hvec
  exact Fintype.linearIndependent_iff.mp hv t hvec i

lemma norm_sum_eq_of_gram_eq (v : ι → E) (w : ι → F)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) (c : ι → ℝ) :
    ‖∑ i, c i • v i‖ = ‖∑ i, c i • w i‖ := by
  have hinner : inner ℝ (∑ i, c i • v i) (∑ i, c i • v i) =
      inner ℝ (∑ i, c i • w i) (∑ i, c i • w i) := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right, hgram]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (∑ i, c i • v i), norm_nonneg (∑ i, c i • w i)]

lemma linearIndependent_of_gram_eq (v : ι → E) (w : ι → F)
    (hv : LinearIndependent ℝ v)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) :
    LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hnorm := norm_sum_eq_of_gram_eq v w hgram c
  rw [hc, norm_zero] at hnorm
  exact Fintype.linearIndependent_iff.mp hv c (norm_eq_zero.mp hnorm) i

/-- The uniquely labelled Gram isometry of the two actual linear spans. -/
def finiteGramIsometry (v : ι → E) (w : ι → F)
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) :
    Submodule.span ℝ (Set.range v) ≃ₗᵢ[ℝ] Submodule.span ℝ (Set.range w) := by
  let bv := Module.Basis.span hv
  let bw := Module.Basis.span hw
  let e := bv.equiv bw (Equiv.refl ι)
  refine e.isometryOfInner ?_
  intro x y
  have hb (i : ι) : e (bv i) = bw i := by simp only [e, Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [← bv.sum_repr x, ← bv.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, inner_smul_right, hb]
  simp only [bv, bw, Submodule.coe_inner, Module.Basis.coe_span_apply, hgram]

@[simp]
lemma finiteGramIsometry_basis (v : ι → E) (w : ι → F)
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) (i : ι) :
    finiteGramIsometry v w hv hw hgram (Module.Basis.span hv i) = Module.Basis.span hw i := by
  change (Module.Basis.span hv).equiv (Module.Basis.span hw) (Equiv.refl ι)
    (Module.Basis.span hv i) = Module.Basis.span hw i
  simp only [Module.Basis.equiv_apply, Equiv.refl_apply]

lemma finiteGramIsometry_unique (v : ι → E) (w : ι → F)
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j))
    (f : Submodule.span ℝ (Set.range v) ≃ₗᵢ[ℝ] Submodule.span ℝ (Set.range w))
    (hf : ∀ i, f (Module.Basis.span hv i) = Module.Basis.span hw i) :
    f = finiteGramIsometry v w hv hw hgram := by
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply (Module.Basis.span hv).ext'
  intro i
  exact (hf i).trans (finiteGramIsometry_basis v w hv hw hgram i).symm

lemma linearIsometry_map_normalize (f : E →ₗᵢ[ℝ] F) (x : E) :
    f (NormedSpace.normalize x) = NormedSpace.normalize (f x) := by
  simp only [NormedSpace.normalize, map_smul, f.norm_map]

/-- Matching the labelled vertices also matches every normalized linear
combination, not just the vertices. -/
lemma finiteGramIsometry_normalizedCombination (v : ι → E) (w : ι → F)
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) (c : ι → ℝ) :
    finiteGramIsometry v w hv hw hgram
        (NormedSpace.normalize (∑ i, c i • Module.Basis.span hv i)) =
      NormedSpace.normalize (∑ i, c i • Module.Basis.span hw i) := by
  have hs : finiteGramIsometry v w hv hw hgram (∑ i, c i • Module.Basis.span hv i) =
      ∑ i, c i • Module.Basis.span hw i := by
    simp only [map_sum, map_smul, finiteGramIsometry_basis]
  have hn := (finiteGramIsometry v w hv hw hgram).norm_map
    (∑ i, c i • Module.Basis.span hv i)
  rw [hs] at hn
  simp only [NormedSpace.normalize, map_smul, hs, hn]

/-- Existence with no assumption of linear independence on the second family:
it follows from equality of Gram matrices. -/
theorem exists_finite_gram_isometry (v : ι → E) (w : ι → F)
    (hv : LinearIndependent ℝ v)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) :
    ∃ f : Submodule.span ℝ (Set.range v) ≃ₗᵢ[ℝ] Submodule.span ℝ (Set.range w),
      ∀ i, (f (Module.Basis.span hv i)).val = w i := by
  let hw := linearIndependent_of_gram_eq v w hv hgram
  refine ⟨finiteGramIsometry v w hv hw hgram, ?_⟩
  intro i
  rw [finiteGramIsometry_basis, Module.Basis.coe_span_apply]

/-- In finite dimension the labelled Gram isometry extends to a genuine
orthogonal motion of the whole ambient space. This is the final geometric
extension used on each radial folding piece. -/
theorem exists_ambient_gram_isometry [FiniteDimensional ℝ E]
    (v w : ι → E) (hv : LinearIndependent ℝ v)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (w i) (w j)) :
    ∃ f : E ≃ₗᵢ[ℝ] E, ∀ i, f (v i) = w i := by
  let hw := linearIndependent_of_gram_eq v w hv hgram
  let e := finiteGramIsometry v w hv hw hgram
  let l : Submodule.span ℝ (Set.range v) →ₗᵢ[ℝ] E :=
    (Submodule.span ℝ (Set.range w)).subtypeₗᵢ.comp e.toLinearIsometry
  let f : E ≃ₗᵢ[ℝ] E := l.extend.toLinearIsometryEquiv rfl
  refine ⟨f, ?_⟩
  intro i
  calc
    f (v i) = l.extend (v i) := rfl
    _ = l (Module.Basis.span hv i) := by
      rw [← Module.Basis.coe_span_apply hv i]
      exact l.extend_apply _
    _ = w i := by
      change (e (Module.Basis.span hv i)).val = w i
      rw [finiteGramIsometry_basis, Module.Basis.coe_span_apply]

end BrehmApprox
