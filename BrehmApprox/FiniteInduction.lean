module

public import BrehmApprox.Relative
public import BrehmApprox.MetricGluing
public meta import Lean.Elab.Tactic.Omega

/-!
# The complete finite induction after geometric preparation

`PreparedSystem` records actual ambient neighborhoods, reference maps and a
geometric overlap condition.  It does NOT contain any approximating maps or
an approximation theorem.  This module proves the induction from those data.

This theorem is deliberately separate from the assertion that every finite
polyhedral space admits such preparation.  Folding, flattening and construction
of the neighborhoods must be proved to obtain that assertion; they are not
silently assumed as additional axioms here.
-/

@[expose] public section

namespace BrehmApprox

universe u
variable {X : Type u} [MetricSpace X]

/-- Geometric data prepared before choosing any approximation errors.
The finite face index is ordered so that a proper subface has smaller index.
The `near_meet` field is a condition on the neighborhoods alone. -/
structure PreparedSystem (X : Type u) [MetricSpace X] (N : ℕ)
    (Good : (X → X) → Prop) (L a : ℝ) where
  faceLE : Fin N → Fin N → Prop
  le_refl : ∀ i, faceLE i i
  le_trans : ∀ i j k, faceLE i j → faceLE j k → faceLE i k
  index_strict : ∀ i j, faceLE i j → i ≠ j → i.val < j.val
  W : Fin N → Set X
  compact_W : ∀ i, IsCompact (W i)
  reference : Fin N → X → X
  reference_agree : ∀ i j, faceLE i j → ∀ x ∈ W i,
    reference i x = reference j x
  reference_short : ∀ i x y,
    (∃ j, faceLE j i ∧ x ∈ W j) →
    (∃ j, faceLE j i ∧ y ∈ W j) →
    dist (reference i x) (reference i y) ≤ L * dist x y
  determined : ∀ i H, Good H → DeterminedOn (W i) H
  near_meet : ∀ i j k, faceLE j i → faceLE k i →
    ¬ faceLE j k → ¬ faceLE k j →
    ∃ l, faceLE l j ∧ faceLE l k ∧
      ∀ x ∈ W j, ∀ y ∈ W k, dist x y < a → x ∈ W l ∧ y ∈ W l

namespace PreparedSystem

variable {N : ℕ} {Good : (X → X) → Prop} {L a : ℝ}
variable (D : PreparedSystem X N Good L a)

lemma index_le {i j : Fin N} (h : D.faceLE i j) : i.val ≤ j.val := by
  by_cases hij : i = j
  · subst j; exact le_rfl
  · exact (D.index_strict i j h hij).le

/-- The invariant maintained after the first `k` faces have been treated. -/
def Prefix (δ : ℕ → ℝ) (k : ℕ) (H : Fin N → X → X) : Prop :=
  (∀ i, i.val < k → Short (H i) ∧ Good (H i) ∧
    ∀ x ∈ D.W i, dist (H i x) (D.reference i x) < δ (i.val + 1)) ∧
  (∀ i j, i.val < k → j.val < k → D.faceLE i j →
    ∀ x ∈ D.W i, H j x = H i x)

/-- One induction step, including existence, well-defined gluing, shortness,
finite determination, application of Brehm, and exact preservation of all old
neighborhoods. -/
theorem prefix_step
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1) (ha : 0 < a)
    {δ ρ : ℕ → ℝ} (hmono : Monotone δ)
    {k : ℕ} (hk : k < N) (hδ : 0 ≤ δ k) (hρ : 0 < ρ k)
    (hsmall : 2 * δ k ≤ (1 - L) * a)
    (hstep : 2 * δ k / (1 - L) + ρ k ≤ δ (k + 1))
    {H : Fin N → X → X} (hH : D.Prefix δ k H) :
    ∃ H' : Fin N → X → X, D.Prefix δ (k + 1) H' := by
  classical
  let i : Fin N := ⟨k, hk⟩
  let I : Finset (Fin N) := Finset.univ.filter fun j => D.faceLE j i ∧ j ≠ i
  let A : Set X := ⋃ j ∈ I, D.W j
  have hI (j : Fin N) : j ∈ I ↔ D.faceLE j i ∧ j ≠ i := by simp [I]
  have hold (j : Fin N) (hj : j ∈ I) : j.val < k :=
    D.index_strict j i ((hI j).mp hj).1 ((hI j).mp hj).2
  have hquality (j : Fin N) (hj : j ∈ I) := hH.1 j (hold j hj)
  have hpair : ∀ j ∈ I, ∀ l ∈ I, ∀ x ∈ D.W j ∩ D.W l, H j x = H l x := by
    intro j hj l hl x hx
    by_cases hjl : D.faceLE j l
    · exact (hH.2 j l (hold j hj) (hold l hl) hjl x hx.1).symm
    by_cases hlj : D.faceLE l j
    · exact hH.2 l j (hold l hl) (hold j hj) hlj x hx.2
    obtain ⟨m, hmj, hml, hm⟩ :=
      D.near_meet i j l ((hI j).mp hj).1 ((hI l).mp hl).1 hjl hlj
    have hmold : m.val < k := lt_of_le_of_lt (D.index_le hmj) (hold j hj)
    have hxm := (hm x hx.1 x hx.2 (by simpa using ha)).1
    exact (hH.2 m j hmold (hold j hj) hmj x hxm).trans
      (hH.2 m l hmold (hold l hl) hml x hxm).symm
  obtain ⟨g, hg, hdet⟩ := exists_glued_determined_map I D.W H hpair
    (fun j hj => D.determined j (H j) (hquality j hj).2.1)
  have hloc : ∀ x ∈ A, ∀ y ∈ A, dist x y < a → dist (g x) (g y) ≤ dist x y := by
    intro x hx y hy hxy
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨l, hl, hyl⟩ := Set.mem_iUnion₂.mp hy
    rw [hg j hj x hxj, hg l hl y hyl]
    by_cases hjl : D.faceLE j l
    · rw [← hH.2 j l (hold j hj) (hold l hl) hjl x hxj]
      exact (hquality l hl).1 x y
    by_cases hlj : D.faceLE l j
    · rw [← hH.2 l j (hold l hl) (hold j hj) hlj y hyl]
      exact (hquality j hj).1 x y
    obtain ⟨m, hmj, hml, hm⟩ :=
      D.near_meet i j l ((hI j).mp hj).1 ((hI l).mp hl).1 hjl hlj
    have hmold : m.val < k := lt_of_le_of_lt (D.index_le hmj) (hold j hj)
    obtain ⟨hxm, hym⟩ := hm x hxj y hyl hxy
    rw [hH.2 m j hmold (hold j hj) hmj x hxm,
      hH.2 m l hmold (hold l hl) hml y hym]
    exact (hH.1 m hmold).1 x y
  have hu : ∀ x ∈ A ∪ D.W i, ∀ y ∈ A ∪ D.W i,
      dist (D.reference i x) (D.reference i y) ≤ L * dist x y := by
    have hex (x : X) (hx : x ∈ A ∪ D.W i) :
        ∃ j, D.faceLE j i ∧ x ∈ D.W j := by
      rcases hx with hx | hx
      · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
        exact ⟨j, ((hI j).mp hj).1, hxj⟩
      · exact ⟨i, D.le_refl i, hx⟩
    intro x hx y hy
    exact D.reference_short i x y (hex x hx) (hex y hy)
  have herr : ∀ x ∈ A, dist (g x) (D.reference i x) ≤ δ k := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    rw [hg j hj x hxj, ← D.reference_agree j i ((hI j).mp hj).1 x hxj]
    exact ((hquality j hj).2.2 x hxj).le.trans (hmono (Nat.succ_le_of_lt (hold j hj)))
  have hgshort : ShortOn g A :=
    shortOn_of_local_uniform_approximation hL1 hloc
      (fun x hx y hy => hu x (Set.mem_union_left _ hx) y (Set.mem_union_left _ hy))
      herr hsmall
  obtain ⟨F, hFshort, hFgood, hFg, hFerr⟩ :=
    relative_approximation_linear hB (D.compact_W i) hdet hgshort
      hL0 hL1 hu hδ herr hρ
  let H' : Fin N → X → X := Function.update H i F
  have hnew : H' i = F := Function.update_self i F H
  have hother (j : Fin N) (hj : j ≠ i) : H' j = H j :=
    Function.update_of_ne hj F H
  refine ⟨H', ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst j
      rw [hnew]
      refine ⟨hFshort, hFgood, ?_⟩
      intro x hx
      exact (hFerr x hx).trans_le hstep
    · have hjold : j.val < k := by
        have hne : j.val ≠ k := by
          intro h
          exact hji (Fin.ext h)
        omega
      rw [hother j hji]
      exact hH.1 j hjold
  · intro j l hj hl hjl x hx
    by_cases hji : j = i
    · subst j
      have hil : l = i := by
        apply Fin.ext
        have hki : k ≤ l.val := D.index_le hjl
        dsimp [i] at hki ⊢
        omega
      subst l
      rfl
    by_cases hli : l = i
    · subst l
      have hjI : j ∈ I := (hI j).mpr ⟨hjl, hji⟩
      rw [hnew, hother j hji, hFg x (Set.mem_iUnion₂.mpr ⟨j, hjI, hx⟩)]
      exact hg j hjI x hx
    · have hjold : j.val < k := by
        have hne : j.val ≠ k := by intro h; exact hji (Fin.ext h)
        omega
      have hlold : l.val < k := by
        have hne : l.val ≠ k := by intro h; exact hli (Fin.ext h)
        omega
      rw [hother j hji, hother l hli]
      exact hH.2 j l hjold hlold hjl x hx

/-- Every finite prepared system has compatible approximations. The budgets
are chosen only after the geometric overlap scale `a` has been fixed. -/
theorem compatible_approximations
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1) (ha : 0 < a)
    (δ ρ : ℕ → ℝ) (hmono : Monotone δ)
    (hδ : ∀ k < N, 0 ≤ δ k) (hρ : ∀ k < N, 0 < ρ k)
    (hsmall : ∀ k < N, 2 * δ k ≤ (1 - L) * a)
    (hstep : ∀ k < N, 2 * δ k / (1 - L) + ρ k ≤ δ (k + 1)) :
    ∃ H : Fin N → X → X,
      (∀ i, Short (H i) ∧ Good (H i) ∧
        ∀ x ∈ D.W i, dist (H i x) (D.reference i x) < δ (i.val + 1)) ∧
      (∀ i j, D.faceLE i j → ∀ x ∈ D.W i, H j x = H i x) := by
  have hprefix : ∀ k, k ≤ N → ∃ H, D.Prefix δ k H := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨D.reference, ?_, ?_⟩
        · intro i hi; omega
        · intro i j hi; omega
    | succ k ih =>
        intro hkN
        have hk : k < N := hkN
        obtain ⟨H, hH⟩ := ih (Nat.le_of_lt hk)
        exact D.prefix_step hB hL0 hL1 ha hmono hk
          (hδ k hk) (hρ k hk) (hsmall k hk) (hstep k hk) hH
  obtain ⟨H, hH⟩ := hprefix N le_rfl
  exact ⟨H, fun i => hH.1 i i.isLt,
    fun i j hij => hH.2 i j i.isLt j.isLt hij⟩

/-- Quantitative budgets always exist. Thus a prepared system admits an
arbitrarily accurate compatible family, without any remaining numerical
choice or circular dependency between mesh and separation. -/
theorem compatible_approximations_uniform
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1) (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Fin N → X → X,
      (∀ i, Short (H i) ∧ Good (H i) ∧
        ∀ x ∈ D.W i, dist (H i x) (D.reference i x) < ε) ∧
      (∀ i j, D.faceLE i j → ∀ x ∈ D.W i, H j x = H i x) := by
  let C : ℝ := 2 / (1 - L) + 1
  let b : ℝ := min ε ((1 - L) * a)
  let τ : ℝ := b / (4 * C ^ N)
  let δ : ℕ → ℝ := fun k => C ^ k * τ
  let ρ : ℕ → ℝ := fun k => δ k / 2
  have hmargin : 0 < 1 - L := by linarith
  have hC1 : 1 ≤ C := by
    have hq : 0 < 2 / (1 - L) := div_pos (by norm_num) hmargin
    dsimp [C]
    linarith
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hb : 0 < b := lt_min hε (mul_pos hmargin ha)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hmono : Monotone δ := by
    intro k l hkl
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 hkl) hτ.le
  have hN : δ N = b / 4 := by
    have hpow : C ^ N ≠ 0 := ne_of_gt (pow_pos hC N)
    dsimp [δ, τ]
    field_simp
  have hsmall : ∀ k < N, 2 * δ k ≤ (1 - L) * a := by
    intro k hk
    have hle := hmono (Nat.le_of_lt hk)
    rw [hN] at hle
    have hbmargin : b ≤ (1 - L) * a := min_le_right _ _
    nlinarith
  have hstep : ∀ k < N, 2 * δ k / (1 - L) + ρ k ≤ δ (k + 1) := by
    intro k _
    have hnext : δ (k + 1) = C * δ k := by dsimp [δ]; rw [pow_succ]; ring
    have hmul : C * δ k = 2 * δ k / (1 - L) + δ k := by dsimp [C]; ring
    rw [hnext, hmul]
    dsimp [ρ]
    have := hδ k
    linarith
  obtain ⟨H, hH, hagree⟩ := D.compatible_approximations hB hL0 hL1 ha δ ρ hmono
    (fun k _ => (hδ k).le) (fun k _ => by dsimp [ρ]; positivity) hsmall hstep
  refine ⟨H, ?_, hagree⟩
  intro i
  refine ⟨(hH i).1, (hH i).2.1, ?_⟩
  intro x hx
  have hle := hmono (Nat.succ_le_of_lt i.isLt)
  rw [hN] at hle
  change δ (i.val + 1) ≤ b / 4 at hle
  have hbε : b ≤ ε := min_le_left _ _
  have hε' : δ (i.val + 1) < ε := by nlinarith
  exact ((hH i).2.2 x hx).trans hε'

end PreparedSystem
end BrehmApprox
