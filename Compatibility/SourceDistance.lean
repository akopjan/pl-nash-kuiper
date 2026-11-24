module

public import Compatibility.Original

/-! Universal properties of the original extended cell-chain distance. -/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PLGeometry

namespace Polyhedron

variable {κ : Geometry} {d m : ℕ} (K : Polyhedron κ d m)

theorem segmentEDist_le_chart (σ : Finset (E m)) (hσ : σ ∈ K.K.faces)
    (x y : ↥K.K.space) (hx : x.val ∈ cell σ) (hy : y.val ∈ cell σ) :
    segmentEDist K x y ≤ ENNReal.ofReal
      (modelDist κ d ((K.simplex σ hσ).toModel x.val) ((K.simplex σ hσ).toModel y.val)) := by
  exact iInf_le_of_le σ (iInf_le_of_le hσ (iInf_le_of_le hx (iInf_le _ hy)))

theorem intrinsicEDist_le_sum (N : ℕ) (p : ℕ → ↥K.K.space) :
    intrinsicEDist K (p 0) (p N) ≤ ∑ i ∈ Finset.range N, segmentEDist K (p i) (p (i + 1)) := by
  exact iInf_le_of_le N (iInf_le_of_le p (iInf_le _ ⟨rfl, rfl⟩))

theorem intrinsicEDist_self (x : ↥K.K.space) : intrinsicEDist K x x = 0 := by
  apply le_antisymm _ bot_le
  simpa using K.intrinsicEDist_le_sum 0 (fun _ => x)

theorem intrinsicEDist_le_segment (x y : ↥K.K.space) :
    intrinsicEDist K x y ≤ segmentEDist K x y := by
  let p : ℕ → ↥K.K.space := fun i => if i = 0 then x else y
  simpa [p] using K.intrinsicEDist_le_sum 1 p

theorem intrinsicEDist_le_chart (σ : Finset (E m)) (hσ : σ ∈ K.K.faces)
    (x y : ↥K.K.space) (hx : x.val ∈ cell σ) (hy : y.val ∈ cell σ) :
    intrinsicEDist K x y ≤ ENNReal.ofReal
      (modelDist κ d ((K.simplex σ hσ).toModel x.val) ((K.simplex σ hσ).toModel y.val)) :=
  (K.intrinsicEDist_le_segment x y).trans (K.segmentEDist_le_chart σ hσ x y hx hy)

/-- Any extended pseudodistance bounded by the chart distances is bounded
by the intrinsic chain distance. Symmetry is not needed for this implication. -/
theorem le_intrinsicEDist (D : ↥K.K.space → ↥K.K.space → ENNReal)
    (hself : ∀ x, D x x = 0)
    (htriangle : ∀ x y z, D x z ≤ D x y + D y z)
    (hchart : ∀ σ (hσ : σ ∈ K.K.faces) (x y : ↥K.K.space),
      x.val ∈ cell σ → y.val ∈ cell σ →
      D x y ≤ ENNReal.ofReal
        (modelDist κ d ((K.simplex σ hσ).toModel x.val) ((K.simplex σ hσ).toModel y.val)))
    (x y : ↥K.K.space) : D x y ≤ intrinsicEDist K x y := by
  have hseg : ∀ a b, D a b ≤ segmentEDist K a b := by
    intro a b
    apply le_iInf
    intro σ
    apply le_iInf
    intro hσ
    apply le_iInf
    intro ha
    apply le_iInf
    intro hb
    exact hchart σ hσ a b ha hb
  have hpath (N : ℕ) (p : ℕ → ↥K.K.space) :
      D (p 0) (p N) ≤ ∑ i ∈ Finset.range N, segmentEDist K (p i) (p (i + 1)) := by
    induction N with
    | zero => simp only [hself, Finset.range_zero, Finset.sum_empty, le_refl]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      exact (htriangle _ _ _).trans (add_le_add ih (hseg _ _))
  apply le_iInf
  intro N
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  simpa only [hp.1, hp.2] using hpath N p

theorem edist_le_intrinsicEDist_of_cellwise
    {Y : Type*} [PseudoEMetricSpace Y] (F : ↥K.K.space → Y)
    (hchart : ∀ σ (hσ : σ ∈ K.K.faces) (x y : ↥K.K.space),
      x.val ∈ cell σ → y.val ∈ cell σ →
      edist (F x) (F y) ≤ ENNReal.ofReal
        (modelDist κ d ((K.simplex σ hσ).toModel x.val) ((K.simplex σ hσ).toModel y.val)))
    (x y : ↥K.K.space) : edist (F x) (F y) ≤ intrinsicEDist K x y :=
  K.le_intrinsicEDist (fun x y => edist (F x) (F y))
    (fun _ => edist_self _) (fun _ _ _ => edist_triangle _ _ _) hchart x y

end Polyhedron
end PLGeometry
