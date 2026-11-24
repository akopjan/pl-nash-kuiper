module

public import BrehmApprox.GluedApproximation

/-!
# Cell-chain characterization of the intrinsic metric

This is an explicit metric property, not an approximation assumption.
It is the polygonal-chain description of the intrinsic metric when the listed
polyhedral cells are isometric to their model cells. The theorem proves that
cellwise Lipschitz estimates then give the same global estimate.
-/

@[expose] public section

namespace BrehmApprox

universe u v w
variable {P : Type u} [MetricSpace P] {Y : Type v} [MetricSpace Y]

/-- Distances can be approximated by finite chains whose consecutive points
belong to a common cell. -/
def ChainGenerated {ι : Type w} (cell : ι → Set P) : Prop :=
  ∀ x y : P, ∀ ε : ℝ, 0 < ε →
    ∃ n : ℕ, ∃ z : ℕ → P,
      z 0 = x ∧ z n = y ∧
      (∀ j < n, ∃ i, z j ∈ cell i ∧ z (j + 1) ∈ cell i) ∧
      (∑ j ∈ Finset.range n, dist (z j) (z (j + 1))) < dist x y + ε

theorem lipschitz_of_cellwise {ι : Type w} {cell : ι → Set P}
    (hintrinsic : ChainGenerated cell) {f : P → Y} {L : ℝ} (hL : 0 ≤ L)
    (hlocal : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i,
      dist (f x) (f y) ≤ L * dist x y) :
    ∀ x y, dist (f x) (f y) ≤ L * dist x y := by
  intro x y
  by_contra hnot
  have hgap : 0 < dist (f x) (f y) - L * dist x y := by linarith
  let ε : ℝ := (dist (f x) (f y) - L * dist x y) / (L + 1)
  have hε : 0 < ε := div_pos hgap (by linarith)
  obtain ⟨n, z, hz0, hzn, hcells, hcost⟩ := hintrinsic x y ε hε
  have hbound : dist (f x) (f y) ≤
      L * ∑ j ∈ Finset.range n, dist (z j) (z (j + 1)) := by
    rw [← hz0, ← hzn]
    calc
      dist (f (z 0)) (f (z n)) ≤
          ∑ j ∈ Finset.range n, dist (f (z j)) (f (z (j + 1))) :=
        dist_le_range_sum_dist (fun j => f (z j)) n
      _ ≤ ∑ j ∈ Finset.range n, L * dist (z j) (z (j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨i, hji, hnext⟩ := hcells j (Finset.mem_range.mp hj)
        exact hlocal i (z j) hji (z (j + 1)) hnext
      _ = L * ∑ j ∈ Finset.range n, dist (z j) (z (j + 1)) :=
        (Finset.mul_sum _ _ _).symm
  have hscaled := mul_le_mul_of_nonneg_left hcost.le hL
  have heq : (L + 1) * ε = dist (f x) (f y) - L * dist x y := by
    dsimp [ε]
    field_simp
  nlinarith

theorem lipschitzWith_of_cellwise {ι : Type w} {cell : ι → Set P}
    (hintrinsic : ChainGenerated cell) {f : P → Y} {L : NNReal}
    (hlocal : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i,
      dist (f x) (f y) ≤ L * dist x y) : LipschitzWith L f :=
  LipschitzWith.of_dist_le_mul (lipschitz_of_cellwise hintrinsic L.coe_nonneg hlocal)

namespace FoldedSource

variable {X : Type v} [MetricSpace X] {Good : (X → X) → Prop}
variable {M : PolytopeModel X Good} {N : ℕ} {L : ℝ}
variable {D : ReferenceAtlas M N L} (S : FoldedSource D P)

/-- The glued approximation is globally short for an intrinsic source.
The conclusion follows from the actual cellwise restrictions of the global
short Brehm maps, and the cell-chain metric condition above. -/
theorem approximate_short
    (hintrinsic : ChainGenerated S.cell)
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : P → X) (href : ∀ i, ∀ x ∈ S.cell i, D.reference i (S.fold x) = f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → X, LipschitzWith 1 g ∧ PolyhedralPiecewiseIsometry M S.fold g ∧
      ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨H, hH, hcompat⟩ := D.approximate hB hL0 hL1 hε
  obtain ⟨g, hg⟩ := S.glue hcompat
  refine ⟨g, ?_, S.piecewise_of_glued (fun i => (hH i).2.1) hg, ?_⟩
  · apply lipschitzWith_of_cellwise hintrinsic
    intro i x hx y hy
    simp only [NNReal.coe_one, one_mul]
    rw [hg i x hx, hg i y hy]
    exact ((hH i).1 (S.fold x) (S.fold y)).trans_eq (S.isometry_cell i x hx y hy)
  · intro x
    obtain ⟨i, hxi⟩ := S.cover x
    rw [hg i x hxi, ← href i x hxi]
    exact (hH i).2.2 _ (S.fold_mem_core hxi)

end FoldedSource
end BrehmApprox
