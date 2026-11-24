module

public import BrehmApprox.ExtremeBarycentricSupport

/-! # Restricting a finite convex hull to an extreme face -/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance extremeHullRestrictionDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem convexHull_inter_extreme (V : Finset E) {C D : Set E}
    (hC : Convex ℝ C) (hD : Convex ℝ D) (hCD : _root_.IsExtreme ℝ C D)
    (hV : (V : Set E) ⊆ C) :
    convexHull ℝ (V : Set E) ∩ D =
      convexHull ℝ (V.filter (fun v => v ∈ D) : Set E) := by
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    obtain ⟨w, hw, hs, he⟩ := Finset.mem_convexHull'.mp hx
    have hwzero (v : E) (hv : v ∈ V) (hvD : v ∉ D) : w v = 0 := by
      apply le_antisymm _ (hw v hv)
      by_contra h
      have hpos : 0 < w v := lt_of_not_ge h
      have hsum : (∑ j : V, w j.val) = 1 := by
        simpa only [Finset.sum_coe_sort] using hs
      have hmean : (∑ j : V, w j.val • j.val) ∈ D := by
        rw [Finset.sum_coe_sort V (fun j : E => w j • j), he]
        exact hxD
      exact hvD (IsExtreme.mem_of_positive_weight hCD hC (fun j : V => j.val)
        (fun j => w j.val) (fun j => hV j.property) (fun j => hw j.val j.property)
        hsum hmean ⟨v, hv⟩ hpos)
    let W := V.filter (fun v => v ∈ D)
    have hWV : W ⊆ V := Finset.filter_subset _ _
    have hz (v : E) (hv : v ∈ V) (hvW : v ∉ W) : w v = 0 :=
      hwzero v hv (fun h => hvW (Finset.mem_filter.mpr ⟨hv, h⟩))
    exact Finset.mem_convexHull'.mpr ⟨w, fun v hv => hw v (hWV hv),
      (Finset.sum_subset hWV hz).trans hs,
      (Finset.sum_subset hWV (fun v hv hn => by rw [hz v hv hn, zero_smul])).trans he⟩
  · intro hx
    refine ⟨convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hx, ?_⟩
    exact convexHull_min (fun v hv => (Finset.mem_filter.mp hv).2) hD hx

end BrehmApprox
