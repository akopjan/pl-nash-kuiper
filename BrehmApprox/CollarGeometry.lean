module

public import BrehmApprox.FiniteInduction

/-!
# Obtaining the shortness scale from compact collar geometry

The positive separation used in the approximation induction is *proved* from
compactness and interior overlap inclusions. It is fixed before numerical
approximation errors or finite nets are chosen.

The construction of such collars from the faces of an arbitrary polyhedral
space remains a separate geometric task. This file does not put that
construction into an axiom.
-/

@[expose] public section

namespace BrehmApprox

universe u
variable {X : Type u} [MetricSpace X]

/-- Compact polyhedral collar data with an explicit intersection buffer.
The determination field is supplied by the proved model-space rigidity
theorems when the sets are actual finite polyhedra. -/
structure CollarData (X : Type u) [MetricSpace X] (N : ℕ)
    (Good : (X → X) → Prop) (L : ℝ) where
  faceLE : Fin N → Fin N → Prop
  le_refl : ∀ i, faceLE i i
  le_trans : ∀ i j k, faceLE i j → faceLE j k → faceLE i k
  index_strict : ∀ i j, faceLE i j → i ≠ j → i.val < j.val
  meet : Fin N → Fin N → Fin N
  meet_le_left : ∀ i j, faceLE (meet i j) i
  meet_le_right : ∀ i j, faceLE (meet i j) j
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
  interior_overlap : ∀ i j k, faceLE j i → faceLE k i →
    ¬ faceLE j k → ¬ faceLE k j →
    W j ∩ W k ⊆ interior (W (meet j k))

namespace CollarData

variable {N : ℕ} {Good : (X → X) → Prop} {L : ℝ}
variable (D : CollarData X N Good L)

/-- The whole collar system has a positive common scale. -/
theorem exists_uniform_scale :
    ∃ a : ℝ, 0 < a ∧ ∀ i j k, D.faceLE j i → D.faceLE k i →
      ¬ D.faceLE j k → ¬ D.faceLE k j →
      ∀ x ∈ D.W j, ∀ y ∈ D.W k, dist x y < a →
        x ∈ D.W (D.meet j k) ∧ y ∈ D.W (D.meet j k) := by
  classical
  let relevant : Fin N → Fin N → Prop := fun j k =>
    ∃ i, D.faceLE j i ∧ D.faceLE k i ∧ ¬ D.faceLE j k ∧ ¬ D.faceLE k j
  let U : Fin N → Fin N → Set X := fun j k =>
    if relevant j k then interior (D.W (D.meet j k)) else Set.univ
  have hU (j k : Fin N) : IsOpen (U j k) := by
    by_cases h : relevant j k <;> simp [U, h]
  have hinter (j k : Fin N) : D.W j ∩ D.W k ⊆ U j k := by
    by_cases h : relevant j k
    · obtain ⟨i, hji, hki, hjk, hkj⟩ := h
      simpa [U, show relevant j k from ⟨i, hji, hki, hjk, hkj⟩] using
        D.interior_overlap i j k hji hki hjk hkj
    · simp [U, h]
  obtain ⟨a, ha, hnear⟩ := compact_family_near_intersection Finset.univ D.W U
    (fun i _ => D.compact_W i) (fun i _ j _ => hU i j) (fun i _ j _ => hinter i j)
  refine ⟨a, ha, ?_⟩
  intro i j k hji hki hjk hkj x hx y hy hxy
  have hrel : relevant j k := ⟨i, hji, hki, hjk, hkj⟩
  have h := hnear j (Finset.mem_univ _) k (Finset.mem_univ _) x hx y hy hxy
  simp only [U, ite_eq_left hrel] at h
  exact ⟨interior_subset h.1, interior_subset h.2⟩

/-- The finite induction with the separation scale eliminated from the input.
All hypotheses are geometric collar data, strictness of the reference maps,
and the model-space finite Brehm principle. -/
theorem compatible_approximations
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Fin N → X → X,
      (∀ i, Short (H i) ∧ Good (H i) ∧
        ∀ x ∈ D.W i, dist (H i x) (D.reference i x) < ε) ∧
      (∀ i j, D.faceLE i j → ∀ x ∈ D.W i, H j x = H i x) := by
  obtain ⟨a, ha, hnear⟩ := D.exists_uniform_scale
  let P : PreparedSystem X N Good L a := {
    faceLE := D.faceLE
    le_refl := D.le_refl
    le_trans := D.le_trans
    index_strict := D.index_strict
    W := D.W
    compact_W := D.compact_W
    reference := D.reference
    reference_agree := D.reference_agree
    reference_short := D.reference_short
    determined := D.determined
    near_meet := fun i j k hji hki hjk hkj =>
      ⟨D.meet j k, D.meet_le_left j k, D.meet_le_right j k,
        hnear i j k hji hki hjk hkj⟩ }
  exact P.compatible_approximations_uniform hB hL0 hL1 ha hε

end CollarData
end BrehmApprox
