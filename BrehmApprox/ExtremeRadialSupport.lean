module

public import BrehmApprox.ExtremeBarycentricSupport

/-!
# Positive radial combinations and faces

A ray from a point of a convex face cannot reenter that face after leaving
it. Consequently, a positive radial combination in the face uses only
vertices of the face, even when its coefficient at the radial center is
not known to be nonnegative.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem IsExtreme.radial_mem
    {C D : Set E} (hCD : _root_.IsExtreme ℝ C D) (hD : Convex ℝ D)
    {p y : E} (hp : p ∈ D) (hy : y ∈ C) {t : ℝ} (ht : 0 < t)
    (hq : p + t • (y - p) ∈ D) : y ∈ D := by
  by_cases ht1 : t < 1
  · apply hCD.right_mem_of_mem_openSegment (hCD.subset hp) hy hq
    refine ⟨1 - t, t, sub_pos.mpr ht1, ht, by ring, ?_⟩
    rw [sub_smul, one_smul, smul_sub]
    abel
  · have ht1' : 1 ≤ t := le_of_not_gt ht1
    have hi0 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
    have hi1 : t⁻¹ ≤ 1 := (inv_le_one₀ ht).mpr ht1'
    have hc := hD hp hq (sub_nonneg.mpr hi1) hi0
      (show (1 - t⁻¹) + t⁻¹ = 1 by ring)
    have he : (1 - t⁻¹) • p + t⁻¹ • (p + t • (y - p)) = y := by
      rw [sub_smul, one_smul, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    rwa [he] at hc

theorem IsExtreme.mem_of_positive_radial_weight
    {ι : Type*} [Fintype ι] {C D : Set E}
    (hCD : _root_.IsExtreme ℝ C D) (hC : Convex ℝ C) (hD : Convex ℝ D)
    {p : E} (hp : p ∈ D) (v : ι → E) (w : ι → ℝ)
    (hv : ∀ i, v i ∈ C) (hw : ∀ i, 0 ≤ w i)
    (hs : 0 < ∑ i, w i) {t : ℝ} (ht : 0 < t)
    (hq : p + t • (∑ i, w i • (v i - p)) ∈ D)
    (i : ι) (hi : 0 < w i) : v i ∈ D := by
  let s : ℝ := ∑ i, w i
  let y : E := ∑ i, (w i / s) • v i
  have hsum : ∑ i, w i / s = 1 := by
    rw [← Finset.sum_div]
    exact div_self hs.ne'
  have hy : y ∈ C := hC.sum_mem
    (fun j _ => div_nonneg (hw j) hs.le) hsum (fun j _ => hv j)
  have hscale : s • y = ∑ i, w i • v i := by
    rw [show y = ∑ i, (w i / s) • v i from rfl, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, mul_div_cancel₀ _ hs.ne']
  have hvec : ∑ i, w i • (v i - p) = s • (y - p) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, s, hscale]
  have hq' : p + (t * s) • (y - p) ∈ D := by
    rw [hvec, smul_smul] at hq
    exact hq
  have hyD := IsExtreme.radial_mem hCD hD hp hy (mul_pos ht hs) hq'
  exact IsExtreme.mem_of_positive_weight hCD hC v (fun j => w j / s) hv
    (fun j => div_nonneg (hw j) hs.le) hsum hyD i (div_pos hi hs)

end BrehmApprox
