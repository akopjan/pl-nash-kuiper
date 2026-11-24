module

public import BrehmApprox.ChainRemetricization
public import Mathlib.Data.List.FinRange

/-!
# Removing repeated cells from intrinsic chains

If a finite chain visits a cell twice, the intervening part can be replaced
by one edge in that cell. The triangle inequality ensures that the cost does
not increase. Hence every chain has a competitor using each cell at most once.
-/

@[expose] public section

namespace BrehmApprox.CellChain

variable {P : Type*} [MetricSpace P] {ι : Type*} {cell : ι → Set P}
variable {x y z : P}

/-- The ordered list of cells traversed by a chain. -/
def cells : {x y : P} → CellChain cell x y → List ι
  | _, _, .nil _ => []
  | _, _, .cons i _ _ a => i :: a.cells

@[simp] theorem cells_nil (x : P) : (CellChain.nil (cell := cell) x).cells = [] := rfl

@[simp] theorem cells_cons (i : ι) (hx : x ∈ cell i) (hy : y ∈ cell i)
    (a : CellChain cell y z) : (CellChain.cons i hx hy a).cells = i :: a.cells := rfl

/-- Split a chain with no repeated cell just after its visit to a given cell. -/
theorem split_at_cell (a : CellChain cell x y) (ha : a.cells.Nodup)
    {i : ι} (hi : i ∈ a.cells) :
    ∃ z : P, ∃ p : CellChain cell x z, ∃ q : CellChain cell z y,
      z ∈ cell i ∧ a.cost id = p.cost id + q.cost id ∧
      q.cells.Nodup ∧ i ∉ q.cells := by
  induction a with
  | nil => simp only [cells, List.not_mem_nil] at hi
  | @cons x v y j hx hv a ih =>
    have hnodup := List.nodup_cons.mp ha
    rcases List.mem_cons.mp hi with hij | hi
    · subst j
      exact ⟨v, single i hx hv, a, hv, by simp, hnodup.2, hnodup.1⟩
    · obtain ⟨z, p, q, hzi, hcost, hq, hnot⟩ := ih hnodup.2 hi
      refine ⟨z, (single j hx hv).append p, q, hzi, ?_, hq, hnot⟩
      simp only [cost_cons, cost_append, cost_single, hcost, add_assoc]

/-- Every intrinsic chain has a no-longer competitor that uses each cell at
most once. No convexity or geodesic assumption is needed for the pruning. -/
theorem exists_nodup_cells (a : CellChain cell x y) :
    ∃ b : CellChain cell x y, b.cells.Nodup ∧ b.cost id ≤ a.cost id := by
  classical
  induction a with
  | nil x => exact ⟨.nil x, List.nodup_nil, le_rfl⟩
  | @cons x v y i hx hv a ih =>
    obtain ⟨b, hb, hcost⟩ := ih
    by_cases hi : i ∈ b.cells
    · obtain ⟨z, p, q, hzi, hbdecomp, hq, hnot⟩ := split_at_cell b hb hi
      refine ⟨.cons i hx hzi q, List.nodup_cons.mpr ⟨hnot, hq⟩, ?_⟩
      have hpdist : dist v z ≤ p.cost id := p.dist_le_cost id
      have hdist : dist x z ≤ dist x v + p.cost id :=
        (dist_triangle x v z).trans (add_le_add le_rfl hpdist)
      simp only [cost_cons, id_eq]
      calc
        dist x z + q.cost id ≤ (dist x v + p.cost id) + q.cost id :=
          add_le_add hdist le_rfl
        _ = dist x v + b.cost id := by rw [hbdecomp, add_assoc]
        _ ≤ dist x v + a.cost id := add_le_add le_rfl hcost
    · exact ⟨.cons i hx hv b, List.nodup_cons.mpr ⟨hi, hb⟩,
        add_le_add le_rfl hcost⟩

end BrehmApprox.CellChain
