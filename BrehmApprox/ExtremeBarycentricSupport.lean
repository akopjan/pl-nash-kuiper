module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

/-!
# Barycentric support on a face

A convex combination belonging to an extreme subset can use positive
coefficients only at points of that subset. This gives the face compatibility
of canonical pulling triangulations.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

theorem IsExtreme.mem_of_positive_weight
    {C D : Set E} (hCD : _root_.IsExtreme ℝ C D) (hC : Convex ℝ C)
    (v : ι → E) (w : ι → ℝ)
    (hv : ∀ i, v i ∈ C) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hmean : (∑ i, w i • v i) ∈ D) (i : ι) (hi : 0 < w i) : v i ∈ D := by
  classical
  have hile : w i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  have hrest : ∑ j ∈ Finset.univ.erase i, w j = 1 - w i := by
    have h := Finset.sum_erase_add (Finset.univ : Finset ι) w (Finset.mem_univ i)
    rw [hsum] at h
    linarith
  by_cases hi1 : w i = 1
  · have hz (j : ι) (hji : j ≠ i) : w j = 0 := by
      have hjle : w j ≤ ∑ k ∈ Finset.univ.erase i, w k :=
        Finset.single_le_sum (fun k _ => hw k) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      rw [hrest, hi1] at hjle
      linarith [hw j]
    have hmeanEq : (∑ j, w j • v j) = v i := by
      rw [Finset.sum_eq_single i]
      · rw [hi1, one_smul]
      · intro j _ hji
        rw [hz j hji, zero_smul]
      · simp
    rwa [hmeanEq] at hmean
  · have hrestpos : 0 < 1 - w i := sub_pos.mpr (lt_of_le_of_ne hile hi1)
    let y : E := ∑ j ∈ Finset.univ.erase i, (w j / (1 - w i)) • v j
    have hy : y ∈ C := by
      apply hC.sum_mem
      · intro j _
        exact div_nonneg (hw j) hrestpos.le
      · rw [← Finset.sum_div, hrest, div_self hrestpos.ne']
      · intro j _
        exact hv j
    have hdecomp : w i • v i + (1 - w i) • y = ∑ j, w j • v j := by
      dsimp [y]
      rw [Finset.smul_sum]
      simp only [smul_smul]
      have hcoeff (j : ι) : (1 - w i) * (w j / (1 - w i)) = w j := by
        field_simp
      simp_rw [hcoeff]
      exact Finset.add_sum_erase (Finset.univ : Finset ι) (fun j => w j • v j)
        (Finset.mem_univ i)
    exact hCD.left_mem_of_mem_openSegment (hv i) hy hmean
      ⟨w i, 1 - w i, hi, hrestpos, by ring, hdecomp⟩

end BrehmApprox
