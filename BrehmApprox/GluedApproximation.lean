module

public import BrehmApprox.ReferenceAtlas

/-!
# The final gluing on a folded polyhedral source

This file proves that the compatible model maps really assemble to one map
on a source, with a finite cover by actual isometric polyhedral pieces.

The initial folding and the compatible local reference atlas are INPUTS.
Their existence for every intrinsic finite polyhedral complex is not claimed
here. Keeping those inputs explicit is essential: this is not yet the full
unconditional Akopyan theorem.
-/

@[expose] public section

namespace BrehmApprox

universe u v
variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good}
variable {N : ℕ} {L : ℝ}

/-- A source already equipped with a finite initial folding. Each listed cell
is isometric, under that folding, to the corresponding genuine model polytope.
The family includes common faces, possibly the empty face. -/
structure FoldedSource (D : ReferenceAtlas M N L) (P : Type v) [MetricSpace P] where
  cell : Fin N → Set P
  cover : ∀ x : P, ∃ i, x ∈ cell i
  fold : P → X
  image_cell : ∀ i, fold '' cell i = D.core i
  isometry_cell : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i,
    dist (fold x) (fold y) = dist x y
  cell_mono : ∀ i j, D.faceLE i j → cell i ⊆ cell j
  intersection : ∀ i j, cell i ∩ cell j ⊆ cell (D.meet i j)

/-- A finite cover by isometric model-polyhedral pieces, with the source
charts supplied by the initial folding. This states the actual pieces and
distance equalities; it is not an abstract `Good` label for the conclusion. -/
def PolyhedralPiecewiseIsometry (M : PolytopeModel X Good) (q : P → X) (f : P → X) : Prop :=
  ∃ S : Finset (Set P), (∀ x : P, ∃ B ∈ S, x ∈ B) ∧
    ∀ B ∈ S, M.Polytope (q '' B) ∧
      ∀ x ∈ B, ∀ y ∈ B,
        dist (q x) (q y) = dist x y ∧ dist (f x) (f y) = dist x y

namespace FoldedSource

variable {D : ReferenceAtlas M N L} (S : FoldedSource D P)

lemma fold_mem_core {i : Fin N} {x : P} (hx : x ∈ S.cell i) : S.fold x ∈ D.core i := by
  rw [← S.image_cell i]
  exact Set.mem_image_of_mem S.fold hx

/-- Compatible ambient maps determine a single map on the actual source. -/
theorem glue {H : Fin N → X → X}
    (hcompat : ∀ i j, D.faceLE i j → ∀ x ∈ D.core i, H j x = H i x) :
    ∃ f : P → X, ∀ i, ∀ x ∈ S.cell i, f x = H i (S.fold x) := by
  classical
  let f : P → X := fun x => H (S.cover x).choose (S.fold x)
  refine ⟨f, ?_⟩
  intro i x hx
  let j : Fin N := (S.cover x).choose
  have hxj : x ∈ S.cell j := (S.cover x).choose_spec
  have hxm : x ∈ S.cell (D.meet j i) := S.intersection j i ⟨hxj, hx⟩
  change H j (S.fold x) = H i (S.fold x)
  exact (hcompat (D.meet j i) j (D.meet_le_left j i) _ (S.fold_mem_core hxm)).trans
    (hcompat (D.meet j i) i (D.meet_le_right j i) _ (S.fold_mem_core hxm)).symm

/-- Finite geometric piece data pull back through the actual isometric
source charts. No triangulation, regularity or isometry is asserted merely
because an arbitrary predicate was named `PL`. -/
theorem piecewise_of_glued {H : Fin N → X → X} {f : P → X}
    (hGood : ∀ i, Good (H i))
    (hf : ∀ i, ∀ x ∈ S.cell i, f x = H i (S.fold x)) :
    PolyhedralPiecewiseIsometry M S.fold f := by
  classical
  have hp := fun i => M.pieces (D.core i) (H i) (D.polytope_core i) (hGood i)
  choose C hC hpieces using hp
  let piece : Fin N → Set X → Set P := fun i B => S.cell i ∩ S.fold ⁻¹' B
  let T : Finset (Set P) := Finset.univ.biUnion fun i => (C i).image (piece i)
  refine ⟨T, ?_, ?_⟩
  · intro x
    obtain ⟨i, hxi⟩ := S.cover x
    have hqx := S.fold_mem_core hxi
    rw [hC i] at hqx
    obtain ⟨B, hB, hqxB⟩ := Set.mem_iUnion₂.mp hqx
    refine ⟨piece i B, ?_, hxi, hqxB⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨B, hB, rfl⟩⟩
  · intro A hA
    obtain ⟨i, _, hAi⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hAi
    have hBcore : B ⊆ D.core i := by
      intro y hy
      rw [hC i]
      exact Set.mem_iUnion₂.mpr ⟨B, hB, hy⟩
    have himage : S.fold '' piece i B = B := by
      apply Set.Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact hx.2
      · intro y hy
        have hycore := hBcore hy
        rw [← S.image_cell i] at hycore
        obtain ⟨x, hx, rfl⟩ := hycore
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [himage]
      exact (hpieces i B hB).1
    · intro x hx y hy
      have hq := S.isometry_cell i x hx.1 y hy.1
      refine ⟨hq, ?_⟩
      rw [hf i x hx.1, hf i y hy.1]
      exact ((hpieces i B hB).2 _ hx.2 _ hy.2).trans hq

/-- Full final gluing and approximation once the initial folding and its
compatible local reference maps have actually been constructed. -/
theorem approximate
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : P → X)
    (href : ∀ i, ∀ x ∈ S.cell i, D.reference i (S.fold x) = f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → X, PolyhedralPiecewiseIsometry M S.fold g ∧
      ∀ x : P, dist (g x) (f x) < ε := by
  obtain ⟨H, hH, hcompat⟩ := D.approximate hB hL0 hL1 hε
  obtain ⟨g, hg⟩ := S.glue hcompat
  refine ⟨g, S.piecewise_of_glued (fun i => (hH i).2.1) hg, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := S.cover x
  rw [hg i x hxi, ← href i x hxi]
  exact (hH i).2.2 _ (S.fold_mem_core hxi)

/-- The preliminary perturbation and the final Brehm approximation consume
separate error budgets. This last triangle inequality is also checked. -/
theorem approximate_original
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f f₀ : P → X)
    (href : ∀ i, ∀ x ∈ S.cell i, D.reference i (S.fold x) = f₀ x)
    {ε : ℝ} (hε : 0 < ε) (hclose : ∀ x, dist (f₀ x) (f x) < ε / 2) :
    ∃ g : P → X, PolyhedralPiecewiseIsometry M S.fold g ∧
      ∀ x : P, dist (g x) (f x) < ε := by
  obtain ⟨g, hg, hgf⟩ := S.approximate hB hL0 hL1 f₀ href (half_pos hε)
  refine ⟨g, hg, ?_⟩
  intro x
  have ht := dist_triangle (g x) (f₀ x) (f x)
  have h₁ := hgf x
  have h₂ := hclose x
  linarith

end FoldedSource
end BrehmApprox
