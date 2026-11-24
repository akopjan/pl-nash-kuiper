module

public import BrehmApprox.CollarGeometry

/-!
# Choosing all collars before approximation starts

This is a finite compact-neighborhood construction. The cores intersect along
their common face whenever they belong to a common simplex. An admissible
neighborhood basis (proved separately for model-space polyhedra) produces
compact neighborhoods whose intersections lie inside earlier collars.

No approximating maps occur in the data or in the construction.
-/

@[expose] public section

namespace BrehmApprox

universe u
variable {X : Type u} [MetricSpace X]

/-- A sorted finite family of compact face images, together with arbitrarily
small admissible compact neighborhoods. `allowed` supplies any extra open
constraints, such as equality of the reference maps. -/
structure CoreNeighborhoodData (X : Type u) [MetricSpace X] (N : ℕ)
    (Admissible : Set X → Prop) where
  faceLE : Fin N → Fin N → Prop
  le_refl : ∀ i, faceLE i i
  index_strict : ∀ i j, faceLE i j → i ≠ j → i.val < j.val
  meet : Fin N → Fin N → Fin N
  meet_comm : ∀ i j, meet i j = meet j i
  meet_le_left : ∀ i j, faceLE (meet i j) i
  meet_le_right : ∀ i j, faceLE (meet i j) j
  core : Fin N → Set X
  compact_core : ∀ i, IsCompact (core i)
  core_inter : ∀ i j k, faceLE j i → faceLE k i →
    core j ∩ core k = core (meet j k)
  allowed : Fin N → Set X
  open_allowed : ∀ i, IsOpen (allowed i)
  core_allowed : ∀ i, core i ⊆ allowed i
  basis : ∀ i U, IsOpen U → core i ⊆ U →
    ∃ W : Set X, Admissible W ∧ IsCompact W ∧ core i ⊆ interior W ∧ W ⊆ U

namespace CoreNeighborhoodData

variable {N : ℕ} {Admissible : Set X → Prop}
variable (D : CoreNeighborhoodData X N Admissible)

/-- The only pairs for which an intersection buffer is required. -/
def Relevant (i j : Fin N) : Prop :=
  (∃ k, D.faceLE i k ∧ D.faceLE j k) ∧ ¬ D.faceLE i j ∧ ¬ D.faceLE j i

lemma Relevant.symm {i j : Fin N} (h : D.Relevant i j) : D.Relevant j i := by
  obtain ⟨⟨k, hik, hjk⟩, hij, hji⟩ := h
  exact ⟨⟨k, hjk, hik⟩, hji, hij⟩

lemma relevant_meet_lt_left {i j : Fin N} (h : D.Relevant i j) :
    (D.meet i j).val < i.val := by
  apply D.index_strict _ _ (D.meet_le_left i j)
  intro heq
  have hij := D.meet_le_right i j
  rw [heq] at hij
  exact h.2.1 hij

lemma relevant_inter {i j : Fin N} (h : D.Relevant i j) :
    D.core i ∩ D.core j = D.core (D.meet i j) := by
  obtain ⟨k, hik, hjk⟩ := h.1
  exact D.core_inter k i j hik hjk

def Prefix (k : ℕ) (W : Fin N → Set X) : Prop :=
  (∀ i, i.val < k → Admissible (W i) ∧ IsCompact (W i) ∧
    D.core i ⊆ interior (W i) ∧ W i ⊆ D.allowed i) ∧
  (∀ i j, i.val < k → j.val < k → D.Relevant i j →
    W i ∩ W j ⊆ interior (W (D.meet i j))) ∧
  (∀ i j, i.val < k → k ≤ j.val → D.Relevant i j →
    W i ∩ D.core j ⊆ interior (W (D.meet i j)))

theorem prefix_step {k : ℕ} (hk : k < N) {W : Fin N → Set X}
    (hW : D.Prefix k W) : ∃ W', D.Prefix (k + 1) W' := by
  classical
  let i : Fin N := ⟨k, hk⟩
  let T : Fin N → Set X := fun j => if j.val < k then W j else D.core j
  let B : Fin N → Set X := fun j =>
    if D.Relevant i j then (T j \ interior (W (D.meet i j)))ᶜ else Set.univ
  let U : Set X := D.allowed i ∩ ⋂ j, B j
  have hT (j : Fin N) : IsCompact (T j) := by
    by_cases hj : j.val < k
    · simpa [T, hj] using (hW.1 j hj).2.1
    · simpa [T, hj] using D.compact_core j
  have hB (j : Fin N) : IsOpen (B j) := by
    by_cases hij : D.Relevant i j
    · simpa [B, hij] using ((hT j).diff isOpen_interior).isClosed.isOpen_compl
    · simp [B, hij]
  have hU : IsOpen U := (D.open_allowed i).inter (isOpen_iInter_of_finite hB)
  have hcoreU : D.core i ⊆ U := by
    intro x hx
    refine ⟨D.core_allowed i hx, Set.mem_iInter.mpr ?_⟩
    intro j
    by_cases hij : D.Relevant i j
    · simp only [B, ite_eq_left hij, Set.mem_compl_iff, Set.mem_sdiff]
      intro hxT
      apply hxT.2
      by_cases hj : j.val < k
      · have hxWj : x ∈ W j := by simpa [T, hj] using hxT.1
        have h := hW.2.2 j i hj (by simp [i]) hij.symm ⟨hxWj, hx⟩
        simpa only [D.meet_comm j i] using h
      · have hxKj : x ∈ D.core j := by simpa [T, hj] using hxT.1
        have hmold : (D.meet i j).val < k := D.relevant_meet_lt_left hij
        exact (hW.1 (D.meet i j) hmold).2.2.1
          (by rw [← D.relevant_inter hij]; exact ⟨hx, hxKj⟩)
    · simp [B, hij]
  obtain ⟨V, hVad, hVcomp, hKV, hVU⟩ := D.basis i U hU hcoreU
  let W' : Fin N → Set X := Function.update W i V
  have hnew : W' i = V := Function.update_self i V W
  have hother (j : Fin N) (hj : j ≠ i) : W' j = W j :=
    Function.update_of_ne hj V W
  have hmeetold {j l : Fin N} (hjl : D.Relevant j l) (hj : j.val ≤ k) :
      D.meet j l ≠ i := by
    intro heq
    have hm := D.relevant_meet_lt_left hjl
    rw [heq] at hm
    dsimp [i] at hm
    omega
  have hVconstraint (j : Fin N) (hij : D.Relevant i j) :
      V ∩ T j ⊆ interior (W (D.meet i j)) := by
    intro x hx
    have hb := Set.mem_iInter.mp (hVU hx.1).2 j
    simp only [B, ite_eq_left hij, Set.mem_compl_iff, Set.mem_sdiff] at hb
    by_contra hnot
    exact hb ⟨hx.2, hnot⟩
  refine ⟨W', ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst j
      rw [hnew]
      exact ⟨hVad, hVcomp, hKV, fun x hx => (hVU hx).1⟩
    · have hjold : j.val < k := by
        have hne : j.val ≠ k := by intro h; exact hji (Fin.ext h)
        omega
      rw [hother j hji]
      exact hW.1 j hjold
  · intro j l hj hl hjl
    rw [hother (D.meet j l) (hmeetold hjl (by omega))]
    by_cases hji : j = i
    · subst j
      have hli : l ≠ i := by
        intro h; subst l; exact hjl.2.1 (D.le_refl i)
      have hlold : l.val < k := by
        have hne : l.val ≠ k := by intro h; exact hli (Fin.ext h)
        omega
      rw [hnew, hother l hli]
      simpa [T, hlold] using hVconstraint l hjl
    by_cases hli : l = i
    · subst l
      have hjold : j.val < k := by
        have hne : j.val ≠ k := by intro h; exact hji (Fin.ext h)
        omega
      rw [hother j hji, hnew, Set.inter_comm, D.meet_comm j i]
      simpa [T, hjold] using hVconstraint j hjl.symm
    · have hjold : j.val < k := by
        have hne : j.val ≠ k := by intro h; exact hji (Fin.ext h)
        omega
      have hlold : l.val < k := by
        have hne : l.val ≠ k := by intro h; exact hli (Fin.ext h)
        omega
      rw [hother j hji, hother l hli]
      exact hW.2.1 j l hjold hlold hjl
  · intro j l hj hl hjl
    rw [hother (D.meet j l) (hmeetold hjl (by omega))]
    by_cases hji : j = i
    · subst j
      have hlnew : ¬ l.val < k := by omega
      rw [hnew]
      simpa [T, hlnew] using hVconstraint l hjl
    · have hjold : j.val < k := by
        have hne : j.val ≠ k := by intro h; exact hji (Fin.ext h)
        omega
      rw [hother j hji]
      exact hW.2.2 j l hjold (by omega) hjl

/-- All admissible compact collars exist simultaneously, with genuine
interior overlap buffers. This construction precedes all error choices. -/
theorem exists_collars :
    ∃ W : Fin N → Set X,
      (∀ i, Admissible (W i) ∧ IsCompact (W i) ∧
        D.core i ⊆ interior (W i) ∧ W i ⊆ D.allowed i) ∧
      (∀ i j, D.Relevant i j → W i ∩ W j ⊆ interior (W (D.meet i j))) := by
  have hpref : ∀ k, k ≤ N → ∃ W, D.Prefix k W := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨D.core, ?_, ?_, ?_⟩
        · intro i hi; omega
        · intro i j hi; omega
        · intro i j hi; omega
    | succ k ih =>
        intro hkN
        have hk : k < N := hkN
        obtain ⟨W, hW⟩ := ih (Nat.le_of_lt hk)
        exact D.prefix_step hk hW
  obtain ⟨W, hW⟩ := hpref N le_rfl
  exact ⟨W, fun i => hW.1 i i.isLt, fun i j hij => hW.2.1 i j i.isLt j.isLt hij⟩

end CoreNeighborhoodData
end BrehmApprox
