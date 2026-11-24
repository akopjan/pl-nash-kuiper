module

public import BrehmApprox.IntrinsicChains
public meta import Lean.Elab.Tactic.Omega

/-!
# Remetricizing an intrinsic cell complex through a common chart

The new distance is the infimum of actual finite cell-chain lengths in the
chart.  Its metric axioms and its exact restriction to each cell are proved;
no existence or metric-compatibility assumption is hidden in the definition.
-/

@[expose] public section

namespace BrehmApprox

universe u v w

/-- A finite chain, every edge of which lies in one specified source cell. -/
inductive CellChain {P : Type u} {ι : Type w} (cell : ι → Set P) : P → P → Type (max u w)
  | nil (x : P) : CellChain cell x x
  | cons {x y z : P} (i : ι) (hx : x ∈ cell i) (hy : y ∈ cell i)
      (tail : CellChain cell y z) : CellChain cell x z

namespace CellChain

variable {P : Type u} {ι : Type w} {cell : ι → Set P}
variable {E : Type v} [MetricSpace E] (q : P → E)
variable {x y z : P}

def cost : {x y : P} → CellChain cell x y → ℝ
  | _, _, .nil _ => 0
  | x, _, .cons (y := y) _ _ _ tail => dist (q x) (q y) + cost tail

@[simp] theorem cost_nil (x : P) : cost q (.nil (cell := cell) x) = 0 := rfl
@[simp] theorem cost_cons (i : ι) (hx : x ∈ cell i) (hy : y ∈ cell i)
    (tail : CellChain cell y z) :
    cost q (.cons i hx hy tail) = dist (q x) (q y) + cost q tail := rfl

omit [MetricSpace E] q in
def append : {x y z : P} → CellChain cell x y → CellChain cell y z → CellChain cell x z
  | _, _, _, .nil _, b => b
  | _, _, _, .cons i hx hy a, b => .cons i hx hy (append a b)

@[simp] theorem cost_append (a : CellChain cell x y) (b : CellChain cell y z) :
    cost q (a.append b) = cost q a + cost q b := by
  induction a with
  | nil => simp [append]
  | cons i hx hy a ih => simp [append, ih, add_assoc]

omit [MetricSpace E] q in
def single (i : ι) (hx : x ∈ cell i) (hy : y ∈ cell i) : CellChain cell x y :=
  .cons i hx hy (.nil y)

@[simp] theorem cost_single (i : ι) (hx : x ∈ cell i) (hy : y ∈ cell i) :
    cost q (single i hx hy) = dist (q x) (q y) := by simp [single]

omit [MetricSpace E] q in
def reverse : {x y : P} → CellChain cell x y → CellChain cell y x
  | _, _, .nil x => .nil x
  | _, _, .cons i hx hy a => (reverse a).append (single i hy hx)

@[simp] theorem cost_reverse (a : CellChain cell x y) : cost q a.reverse = cost q a := by
  induction a with
  | nil => rfl
  | cons i hx hy a ih => simp [reverse, ih, dist_comm, add_comm]

theorem cost_nonneg (a : CellChain cell x y) : 0 ≤ cost q a := by
  induction a with
  | nil => simp
  | cons i hx hy a ih => exact add_nonneg dist_nonneg ih

theorem dist_le_cost (a : CellChain cell x y) : dist (q x) (q y) ≤ cost q a := by
  induction a with
  | nil => simp
  | cons i hx hy a ih => exact (dist_triangle _ _ _).trans (add_le_add_right ih _)

omit [MetricSpace E] q in
noncomputable def ofSequence : (n : ℕ) → (z : ℕ → P) →
    (∀ j < n, ∃ i, z j ∈ cell i ∧ z (j + 1) ∈ cell i) →
    CellChain cell (z 0) (z n)
  | 0, z, _ => .nil (z 0)
  | n + 1, z, hc =>
    (ofSequence n z (fun j hj => hc j (Nat.lt_trans hj (Nat.lt_succ_self n)))).append
      (single (hc n (Nat.lt_succ_self n)).choose
        (hc n (Nat.lt_succ_self n)).choose_spec.1
        (hc n (Nat.lt_succ_self n)).choose_spec.2)

@[simp] theorem cost_ofSequence (n : ℕ) (z : ℕ → P)
    (hc : ∀ j < n, ∃ i, z j ∈ cell i ∧ z (j + 1) ∈ cell i) :
    cost q (ofSequence n z hc) =
      ∑ j ∈ Finset.range n, dist (q (z j)) (q (z (j + 1))) := by
  induction n with
  | zero => simp [ofSequence]
  | succ n ih => simp [ofSequence, ih, Finset.sum_range_succ]


/-- Every inductive cell chain has the finite-sequence form used by the
intrinsic metric definition. -/
theorem exists_sequence (a : CellChain cell x y) :
    ∃ n : ℕ, ∃ z : ℕ → P,
      z 0 = x ∧ z n = y ∧
      (∀ j < n, ∃ i, z j ∈ cell i ∧ z (j + 1) ∈ cell i) ∧
      (∑ j ∈ Finset.range n, dist (q (z j)) (q (z (j + 1)))) = a.cost q := by
  induction a with
  | nil x => exact ⟨0, fun _ => x, rfl, rfl, by simp, by simp⟩
  | @cons x y t i hx hy a ih =>
    obtain ⟨n, z, h0, hn, hc, hs⟩ := ih
    let w : ℕ → P := fun j => match j with | 0 => x | k + 1 => z k
    refine ⟨n + 1, w, rfl, hn, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => exact ⟨i, hx, by simpa [w, h0] using hy⟩
      | succ k => exact hc k (by omega)
    · rw [Finset.sum_range_succ']
      simp [w, h0, hs, cost, add_comm]

variable [MetricSpace P]

theorem old_dist_le_cost (a : CellChain cell x y) {B : ℝ}
    (hinv : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist a b ≤ B * dist (q a) (q b)) :
    dist x y ≤ B * cost q a := by
  induction a with
  | nil => simp
  | cons i hx hy a ih =>
    calc
      dist _ _ ≤ dist _ _ + dist _ _ := dist_triangle _ _ _
      _ ≤ B * dist (q _) (q _) + B * cost q a := add_le_add (hinv i _ hx _ hy) ih
      _ = B * cost q (.cons i hx hy a) := by simp [mul_add]

end CellChain

/-- Distances formed from chart lengths of finite cell chains. -/
noncomputable def chartChainDist {P : Type u} {ι : Type w} {E : Type v} [MetricSpace E]
    (cell : ι → Set P) (q : P → E) (x y : P) : ℝ :=
  sInf {r : ℝ | ∃ a : CellChain cell x y, a.cost q = r}

namespace ChartChainDist

variable {P : Type u} [MetricSpace P] {ι : Type w} {cell : ι → Set P}
variable {E : Type v} [MetricSpace E] {q : P → E}
variable (hc : ChainGenerated cell)

include hc in
theorem chain_exists (x y : P) : Nonempty (CellChain cell x y) := by
  obtain ⟨n, z, h0, hn, hcell, _⟩ := hc x y 1 (by norm_num)
  rw [← h0, ← hn]
  exact ⟨CellChain.ofSequence n z hcell⟩

include hc in
theorem costs_nonempty (x y : P) :
    ({r : ℝ | ∃ a : CellChain cell x y, a.cost q = r} : Set ℝ).Nonempty := by
  obtain ⟨a⟩ := chain_exists hc x y
  exact ⟨a.cost q, a, rfl⟩

omit [MetricSpace P] in
theorem costs_bddBelow (x y : P) :
    BddBelow ({r : ℝ | ∃ a : CellChain cell x y, a.cost q = r} : Set ℝ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, rfl⟩
  exact a.cost_nonneg q

include hc in
theorem nonneg (x y : P) : 0 ≤ chartChainDist cell q x y := by
  apply le_csInf (costs_nonempty hc x y)
  rintro r ⟨a, rfl⟩
  exact a.cost_nonneg q

omit [MetricSpace P] in
theorem le_cost {x y : P} (a : CellChain cell x y) :
    chartChainDist cell q x y ≤ a.cost q :=
  csInf_le (costs_bddBelow x y) ⟨a, rfl⟩

include hc in
theorem approx (x y : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : CellChain cell x y, a.cost q < chartChainDist cell q x y + ε := by
  obtain ⟨r, ⟨a, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (costs_nonempty hc (q := q) x y)
    (lt_add_of_pos_right (chartChainDist cell q x y) hε)
  exact ⟨a, hr⟩

include hc in
theorem self (x : P) : chartChainDist cell q x x = 0 :=
  le_antisymm (by simpa using le_cost (q := q) (.nil x)) (nonneg hc x x)

include hc in
theorem comm (x y : P) : chartChainDist cell q x y = chartChainDist cell q y x := by
  apply le_antisymm
  · apply le_csInf (costs_nonempty hc y x)
    rintro r ⟨a, rfl⟩
    simpa using le_cost (q := q) a.reverse
  · apply le_csInf (costs_nonempty hc x y)
    rintro r ⟨a, rfl⟩
    simpa using le_cost (q := q) a.reverse

include hc in
theorem triangle (x y z : P) :
    chartChainDist cell q x z ≤ chartChainDist cell q x y + chartChainDist cell q y z := by
  by_contra hnot
  have hgap : 0 < chartChainDist cell q x z -
      (chartChainDist cell q x y + chartChainDist cell q y z) := by linarith
  obtain ⟨a, ha⟩ := approx hc (q := q) x y (show 0 <
    (chartChainDist cell q x z - (chartChainDist cell q x y + chartChainDist cell q y z)) / 3 by linarith)
  obtain ⟨b, hb⟩ := approx hc (q := q) y z (show 0 <
    (chartChainDist cell q x z - (chartChainDist cell q x y + chartChainDist cell q y z)) / 3 by linarith)
  have hh := le_cost (q := q) (a.append b)
  rw [CellChain.cost_append] at hh
  linarith

include hc in
theorem chord_le (x y : P) : dist (q x) (q y) ≤ chartChainDist cell q x y := by
  apply le_csInf (costs_nonempty hc x y)
  rintro r ⟨a, rfl⟩
  exact a.dist_le_cost q

include hc in
theorem on_cell (i : ι) {x y : P} (hx : x ∈ cell i) (hy : y ∈ cell i) :
    chartChainDist cell q x y = dist (q x) (q y) := by
  apply le_antisymm
  · simpa using le_cost (q := q) (CellChain.single i hx hy)
  · exact chord_le hc x y

include hc in
theorem lower_bound {B : ℝ} (hB : 0 < B)
    (hinv : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist a b ≤ B * dist (q a) (q b))
    (x y : P) : dist x y ≤ B * chartChainDist cell q x y := by
  have h : dist x y / B ≤ chartChainDist cell q x y := by
    apply le_csInf (costs_nonempty hc x y)
    rintro r ⟨a, rfl⟩
    exact (div_le_iff₀ hB).mpr (by simpa [mul_comm] using a.old_dist_le_cost q hinv)
  simpa [mul_comm] using (div_le_iff₀ hB).mp h

include hc in
theorem upper_bound {A : ℝ} (hA : 0 ≤ A)
    (hchart : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist (q a) (q b) ≤ A * dist a b)
    (x y : P) : chartChainDist cell q x y ≤ A * dist x y := by
  by_contra hnot
  have hgap : 0 < chartChainDist cell q x y - A * dist x y := by linarith
  let ε : ℝ := (chartChainDist cell q x y - A * dist x y) / (A + 1)
  have hε : 0 < ε := div_pos hgap (by linarith)
  obtain ⟨n, z, h0, hn, hcells, hcost⟩ := hc x y ε hε
  have hcq : chartChainDist cell q x y ≤
      ∑ j ∈ Finset.range n, dist (q (z j)) (q (z (j + 1))) := by
    rw [← h0, ← hn]
    simpa using le_cost (q := q) (CellChain.ofSequence n z hcells)
  have hsum : (∑ j ∈ Finset.range n, dist (q (z j)) (q (z (j + 1)))) ≤
      A * ∑ j ∈ Finset.range n, dist (z j) (z (j + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨i, hi, hj'⟩ := hcells j (Finset.mem_range.mp hj)
    exact hchart i _ hi _ hj'
  have heq : (A + 1) * ε = chartChainDist cell q x y - A * dist x y := by
    dsimp [ε]
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hcost.le hA
  nlinarith


include hc in
/-- The common-chart chain distance has the same open sets as the old metric. -/
theorem isOpen_iff {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hchart : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist (q a) (q b) ≤ A * dist a b)
    (hinv : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist a b ≤ B * dist (q a) (q b))
    (s : Set P) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0,
      ∀ y, chartChainDist cell q x y < ε → y ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, he⟩ := hs x hx
    refine ⟨ε / B, div_pos hε hB, ?_⟩
    intro y hy
    apply he
    rw [Metric.mem_ball, dist_comm]
    have hl := lower_bound hc hB hinv x y
    have hm := (lt_div_iff₀ hB).mp hy
    nlinarith
  · intro hs x hx
    obtain ⟨ε, hε, he⟩ := hs x hx
    refine ⟨ε / (A + 1), div_pos hε (by linarith), ?_⟩
    intro y hy
    apply he
    have hu := upper_bound hc hA hchart x y
    have hd : dist x y < ε / (A + 1) := by simpa [Metric.mem_ball, dist_comm] using hy
    have hm := (lt_div_iff₀ (show 0 < A + 1 by linarith)).mp hd
    have hd0 := dist_nonneg (x := x) (y := y)
    nlinarith

/-- An actual metric structure, with exactly the pre-existing topology. -/
@[instance_reducible]
noncomputable def metricSpace {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hchart : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist (q a) (q b) ≤ A * dist a b)
    (hinv : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist a b ≤ B * dist (q a) (q b)) :
    MetricSpace P :=
  MetricSpace.ofDistTopology (chartChainDist cell q) (self hc) (comm hc) (triangle hc)
    (isOpen_iff hc hA hB hchart hinv) (by
      intro x y hxy
      apply eq_of_dist_eq_zero
      have h := lower_bound hc hB hinv x y
      rw [hxy, mul_zero] at h
      exact le_antisymm h dist_nonneg)

/-- The newly constructed metric is itself generated by the same source cells. -/
theorem intrinsic {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hchart : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist (q a) (q b) ≤ A * dist a b)
    (hinv : ∀ i, ∀ a ∈ cell i, ∀ b ∈ cell i, dist a b ≤ B * dist (q a) (q b)) :
    @ChainGenerated P (metricSpace hc hA hB hchart hinv) ι cell := by
  intro x y ε hε
  obtain ⟨a, ha⟩ := approx hc (q := q) x y hε
  obtain ⟨n, z, h0, hn, hcells, hcost⟩ := a.exists_sequence q
  refine ⟨n, z, h0, hn, hcells, ?_⟩
  change (∑ j ∈ Finset.range n, chartChainDist cell q (z j) (z (j + 1))) <
    chartChainDist cell q x y + ε
  have heq : (∑ j ∈ Finset.range n, chartChainDist cell q (z j) (z (j + 1))) = a.cost q := by
    rw [← hcost]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨i, hi, hj'⟩ := hcells j (Finset.mem_range.mp hj)
    exact on_cell hc i hi hj'
  rwa [heq]

end ChartChainDist
end BrehmApprox
