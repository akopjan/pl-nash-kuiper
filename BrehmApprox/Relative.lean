module

public import BrehmApprox.Core

/-!
# Relative approximation from finite Brehm interpolation

The net is chosen only outside a fixed collar of the prescribed set. This
avoids the circular requirement that a net finer than its own separation from
the prescribed set should exist. The argument is purely metric, and applies to
any model space for which finite Brehm interpolation and finite determination
have been supplied.
-/

@[expose] public section

namespace BrehmApprox

universe u
variable {X : Type u} [MetricSpace X]

/-- A compact metric set has a finite internal net with strict mesh. The empty
set is allowed. -/
lemma compact_finite_net {K : Set X} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ N : Finset X, (N : Set X) ⊆ K ∧
      ∀ x ∈ K, ∃ p ∈ N, dist x p < η := by
  classical
  obtain ⟨N, hNK, hN, hcover⟩ := hK.finite_cover_balls hη
  refine ⟨hN.toFinset, by simpa using hNK, ?_⟩
  intro x hx
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcover hx)
  exact ⟨p, by simpa using hp, hxp⟩

/-- Finite Brehm interpolation gives uniform approximation on every compact
subset of the model space, while interpolating any additional finite set.
Unlike the relative collar lemma, this elementary consequence needs no strict
contraction. -/
theorem compact_model_approximation
    {Good : (X → X) → Prop} (hB : FiniteExtension Good)
    {W : Set X} (hW : IsCompact W) (V : Finset X) {u : X → X}
    (hu : ShortOn u (W ∪ (V : Set X))) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : X → X, Short H ∧ Good H ∧
      (∀ v ∈ V, H v = u v) ∧
      ∀ x ∈ W, dist (H x) (u x) < ε := by
  classical
  obtain ⟨N, hNW, hnet⟩ := compact_finite_net hW (show 0 < ε / 2 by linarith)
  have hmem : ∀ x ∈ N ∪ V, x ∈ W ∪ (V : Set X) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxN | hxV
    · exact Set.mem_union_left _ (hNW hxN)
    · exact Set.mem_union_right _ hxV
  have hshort : ShortOn u ((N ∪ V : Finset X) : Set X) :=
    fun x hx y hy => hu x (hmem x hx) y (hmem y hy)
  obtain ⟨H, hH, hGood, hHu⟩ := hB (N ∪ V) u hshort
  refine ⟨H, hH, hGood, (fun v hv => hHu v (Finset.mem_union_right N hv)), ?_⟩
  intro x hx
  obtain ⟨p, hp, hxp⟩ := hnet x hx
  have hpW := hNW hp
  calc
    dist (H x) (u x) ≤ dist (H x) (H p) + dist (u p) (u x) := by
      simpa [hHu p (Finset.mem_union_left V hp)] using dist_triangle (H x) (H p) (u x)
    _ ≤ dist x p + dist p x :=
      add_le_add (hH x p) (hu p (Set.mem_union_left _ hpW) x (Set.mem_union_left _ hx))
    _ = 2 * dist x p := by rw [dist_comm p x]; ring
    _ < ε := by linarith

/-- The compact part of `W` at distance at least `r` from every point of `A`.
This definition is also correct when `A` is empty, unlike a convention-dependent
real-valued distance to the empty set. -/
def Away (A W : Set X) (r : ℝ) : Set X :=
  {x | x ∈ W ∧ ∀ a ∈ A, r ≤ dist x a}

lemma isCompact_away {A W : Set X} (hW : IsCompact W) (r : ℝ) :
    IsCompact (Away A W r) := by
  have hclosed : IsClosed {x : X | ∀ a ∈ A, r ≤ dist x a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_id.dist continuous_const)
  exact hW.inter_right hclosed

/-- Relative approximation with explicit collar radius and mesh. All
geometric inputs are visible: `FiniteExtension Good` and finite determination
of the prescribed map. No extension theorem for arbitrary polyhedral sources
is used. The reference map need be contracting only on `A ∪ W`. -/
theorem relative_approximation
    {Good : (X → X) → Prop} (hB : FiniteExtension Good)
    {A W : Set X} (hW : IsCompact W) {g u : X → X}
    (hdet : DeterminedOn A g) (hg : ShortOn g A)
    {L δ r η : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hu : ∀ x ∈ A ∪ W, ∀ y ∈ A ∪ W,
      dist (u x) (u y) ≤ L * dist x y)
    (herr : ∀ a ∈ A, dist (g a) (u a) ≤ δ)
    (hr : 0 < r) (hδr : δ ≤ (1 - L) * r) (hη : 0 < η) :
    ∃ H : X → X, Short H ∧ Good H ∧
      (∀ a ∈ A, H a = g a) ∧
      ∀ x ∈ W, dist (H x) (u x) <
        max (δ + (1 + L) * r) ((1 + L) * η) := by
  classical
  obtain ⟨V, hVA, hVdet⟩ := hdet
  obtain ⟨N, hNK, hnet⟩ := compact_finite_net (isCompact_away hW r) hη
  have hNnotA : ∀ p ∈ N, p ∉ A := by
    intro p hp hpA
    have h := (hNK hp).2 p hpA
    simp only [dist_self] at h
    linarith
  let f : X → X := fun x => if x ∈ A then g x else u x
  have hmem : ∀ x ∈ V ∪ N, x ∈ A ∪ W := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxV | hxN
    · exact Set.mem_union_left _ (hVA hxV)
    · exact Set.mem_union_right _ (hNK hxN).1
  have hN_of_notA : ∀ x ∈ V ∪ N, x ∉ A → x ∈ N := by
    intro x hx hxA
    rcases Finset.mem_union.mp hx with hxV | hxN
    · exact False.elim (hxA (hVA hxV))
    · exact hxN
  have hmixed : ∀ a ∈ A, ∀ p ∈ N, dist (g a) (u p) ≤ dist a p := by
    intro a ha p hp
    have hsep : r ≤ dist a p := by simpa [dist_comm] using (hNK hp).2 a ha
    have hmargin : (1 - L) * r ≤ (1 - L) * dist a p :=
      mul_le_mul_of_nonneg_left hsep (by linarith)
    calc
      dist (g a) (u p) ≤ dist (g a) (u a) + dist (u a) (u p) :=
        dist_triangle _ _ _
      _ ≤ δ + L * dist a p :=
        add_le_add (herr a ha)
          (hu a (Set.mem_union_left _ ha) p (Set.mem_union_right _ (hNK hp).1))
      _ ≤ dist a p := by nlinarith
  have hf : ShortOn f ((V ∪ N : Finset X) : Set X) := by
    intro x hx y hy
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · simpa [f, hxA, hyA] using hg x hxA y hyA
    · simpa [f, hxA, hyA] using hmixed x hxA y (hN_of_notA y hy hyA)
    · simpa [f, hxA, hyA, dist_comm] using hmixed y hyA x (hN_of_notA x hx hxA)
    · have hL : L * dist x y ≤ dist x y := by
        nlinarith [dist_nonneg (x := x) (y := y)]
      simpa [f, hxA, hyA] using (hu x (hmem x hx) y (hmem y hy)).trans hL
  obtain ⟨H, hH, hGood, hHf⟩ := hB (V ∪ N) f hf
  have hHg : ∀ a ∈ A, H a = g a := by
    apply hVdet H hH
    intro v hv
    simpa [f, hVA hv] using hHf v (Finset.mem_union_left N hv)
  have hHu : ∀ p ∈ N, H p = u p := by
    intro p hp
    simpa [f, hNnotA p hp] using hHf p (Finset.mem_union_right V hp)
  refine ⟨H, hH, hGood, hHg, ?_⟩
  intro x hxW
  by_cases hxK : x ∈ Away A W r
  · obtain ⟨p, hp, hxp⟩ := hnet x hxK
    have hpW := (hNK hp).1
    calc
      dist (H x) (u x) ≤ dist (H x) (H p) + dist (u p) (u x) := by
        simpa [hHu p hp] using dist_triangle (H x) (H p) (u x)
      _ ≤ dist x p + L * dist x p := by
        exact add_le_add (hH x p)
          (by simpa [dist_comm] using
            hu p (Set.mem_union_right _ hpW) x (Set.mem_union_right _ hxW))
      _ = (1 + L) * dist x p := by ring
      _ < (1 + L) * η := mul_lt_mul_of_pos_left hxp (by linarith)
      _ ≤ max (δ + (1 + L) * r) ((1 + L) * η) := le_max_right _ _
  · have hnear : ∃ a ∈ A, dist x a < r := by
      have : ¬ ∀ a ∈ A, r ≤ dist x a := by
        intro h
        exact hxK ⟨hxW, h⟩
      push Not at this
      exact this
    obtain ⟨a, ha, hxa⟩ := hnear
    calc
      dist (H x) (u x) ≤ dist (H x) (H a) +
          (dist (g a) (u a) + dist (u a) (u x)) := by
        rw [hHg a ha]
        exact (dist_triangle (H x) (g a) (u x)).trans
          (add_le_add le_rfl (dist_triangle (g a) (u a) (u x)))
      _ ≤ dist x a + (δ + L * dist x a) := by
        exact add_le_add (hH x a) (add_le_add (herr a ha)
          (by simpa [dist_comm] using
            hu a (Set.mem_union_left _ ha) x (Set.mem_union_right _ hxW)))
      _ = δ + (1 + L) * dist x a := by ring
      _ < δ + (1 + L) * r := by
        have hmul : (1 + L) * dist x a < (1 + L) * r :=
          mul_lt_mul_of_pos_left hxa (by linarith)
        linarith
      _ ≤ max (δ + (1 + L) * r) ((1 + L) * η) := le_max_left _ _

/-- A convenient version in which the loss is explicitly linear in the old
error. `ρ` is an arbitrary positive new error budget. -/
theorem relative_approximation_linear
    {Good : (X → X) → Prop} (hB : FiniteExtension Good)
    {A W : Set X} (hW : IsCompact W) {g u : X → X}
    (hdet : DeterminedOn A g) (hg : ShortOn g A)
    {L δ ρ : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hu : ∀ x ∈ A ∪ W, ∀ y ∈ A ∪ W,
      dist (u x) (u y) ≤ L * dist x y)
    (hδ0 : 0 ≤ δ) (herr : ∀ a ∈ A, dist (g a) (u a) ≤ δ)
    (hρ : 0 < ρ) :
    ∃ H : X → X, Short H ∧ Good H ∧
      (∀ a ∈ A, H a = g a) ∧
      ∀ x ∈ W, dist (H x) (u x) < 2 * δ / (1 - L) + ρ := by
  have hm : 0 < 1 - L := by linarith
  have hp : 0 < 1 + L := by linarith
  have hm0 : 1 - L ≠ 0 := ne_of_gt hm
  have hp0 : 1 + L ≠ 0 := ne_of_gt hp
  let r : ℝ := δ / (1 - L) + ρ / (1 + L)
  let η : ℝ := ρ / (1 + L)
  have hr : 0 < r := by dsimp [r]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hδr : δ ≤ (1 - L) * r := by
    have heq : (1 - L) * r = δ + (1 - L) * (ρ / (1 + L)) := by
      dsimp [r]
      field_simp
    rw [heq]
    exact le_add_of_nonneg_right (by positivity)
  obtain ⟨H, hH, hGood, hHg, herror⟩ :=
    relative_approximation hB hW hdet hg hL0 hL1 hu herr hr hδr hη
  refine ⟨H, hH, hGood, hHg, ?_⟩
  have hnear : δ + (1 + L) * r = 2 * δ / (1 - L) + ρ := by
    dsimp [r]
    field_simp
    ring
  have hfar : (1 + L) * η = ρ := by
    dsimp [η]
    field_simp
  have hbound : ρ ≤ 2 * δ / (1 - L) + ρ :=
    le_add_of_nonneg_left (by positivity)
  intro x hx
  simpa only [hnear, hfar, max_eq_left hbound] using herror x hx

end BrehmApprox
