module

public import BrehmApprox.SimplexFaces
public import Mathlib.Analysis.Convex.Extreme

/-! # Every vertex subface of a simplex is an extreme face -/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isExtreme_convexHull_vertex_subset {V W : Finset E}
    (hV : AffineIndependent ℝ ((↑) : V → E)) (hWV : W ⊆ V) :
    _root_.IsExtreme ℝ (convexHull ℝ (V : Set E)) (convexHull ℝ (W : Set E)) := by
  classical
  refine ⟨convexHull_mono (Finset.coe_subset.mpr hWV), ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  obtain ⟨u, hu0, hu1, hux⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨v, hv0, hv1, hvy⟩ := Finset.mem_convexHull'.mp hy
  obtain ⟨w, hw0, hw1, hwz⟩ := Finset.mem_convexHull'.mp hz
  let w' : E → ℝ := fun p => if p ∈ W then w p else 0
  have hwsum : (∑ p ∈ V, w' p) = 1 := by
    calc
      _ = ∑ p ∈ W, w' p := (Finset.sum_subset hWV (fun p _ hp => by simp [w', hp])).symm
      _ = ∑ p ∈ W, w p := Finset.sum_congr rfl (fun p hp => by simp [w', hp])
      _ = 1 := hw1
  have hwmean : (∑ p ∈ V, w' p • p) = a • x + b • y := by
    calc
      _ = ∑ p ∈ W, w' p • p :=
        (Finset.sum_subset hWV (fun p _ hp => by simp [w', hp])).symm
      _ = ∑ p ∈ W, w p • p := Finset.sum_congr rfl (fun p hp => by simp [w', hp])
      _ = _ := hwz
  have husum : (∑ p ∈ V, (a * u p + b * v p)) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu1, hv1,
      mul_one, mul_one, hab]
  have humean : (∑ p ∈ V, (a * u p + b * v p) • p) = a • x + b • y := by
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hux, hvy]
  have heq := hV.eq_of_sum_eq_sum_subtype (husum.trans hwsum.symm) (humean.trans hwmean.symm)
  have hu_zero : ∀ p ∈ V, p ∉ W → u p = 0 := by
    intro p hp hpW
    have h := heq p hp
    simp only [w', ite_eq_right hpW] at h
    have hu := hu0 p hp
    have hv := mul_nonneg hb.le (hv0 p hp)
    nlinarith
  apply Finset.mem_convexHull'.mpr
  refine ⟨u, fun p hp => hu0 p (hWV hp), ?_, ?_⟩
  · exact (Finset.sum_subset hWV (fun p hp hpW => hu_zero p hp hpW)).trans hu1
  · exact (Finset.sum_subset hWV (fun p hp hpW => by
      rw [hu_zero p hp hpW, zero_smul])).trans hux

end BrehmApprox
