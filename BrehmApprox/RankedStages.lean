module

public import BrehmApprox.SourceStages
public import BrehmApprox.SourceFiniteFlattening

/-!+# A bounded number of simultaneous face stages

Faces of equal rank are handled simultaneously. The total Lipschitz estimate
depends on the number of ranks, not on the number of faces; this removes the
circular dependence between a small curved chart radius and a fine subdivision.
The local projection factorization is proved for this actual ranked composition.
-/

@[expose] public section

noncomputable section

open scoped Topology
open Filter

namespace BrehmApprox

universe u

variable {N K : ℕ}

def rankMembers (rank : Fin N → Fin K) (k : Fin K) : Finset (Fin N) :=
  Finset.univ.filter fun i => rank i = k

lemma mem_rankMembers (rank : Fin N → Fin K) (k : Fin K) (i : Fin N) :
    i ∈ rankMembers rank k ↔ rank i = k := by simp [rankMembers]

variable {X : Type u}

def rankStage (rank : Fin N → Fin K) (Q : Fin N → X → X) (k : Fin K) : X → X :=
  disjointStage (rankMembers rank k) Q

def rankComposition (rank : Fin N → Fin K) (Q : Fin N → X → X) : X → X :=
  composeSteps (rankStage rank Q) (descendingFaces K)

lemma descendingFaces_length (K : ℕ) : (descendingFaces K).length = K := by
  simp only [descendingFaces, Finset.length_sort, Finset.card_univ, Fintype.card_fin]

lemma rankStage_mapsTo (rank : Fin N → Fin K) (Q : Fin N → X → X) {A : Set X}
    (hQ : ∀ i, Set.MapsTo (Q i) A A) (k : Fin K) : Set.MapsTo (rankStage rank Q k) A A :=
  disjointStage_mapsTo _ Q (fun i _ => hQ i)

lemma rankComposition_mapsTo (rank : Fin N → Fin K) (Q : Fin N → X → X) {A : Set X}
    (hQ : ∀ i, Set.MapsTo (Q i) A A) : Set.MapsTo (rankComposition rank Q) A A :=
  composeSteps_mapsTo _ _ (fun k _ => rankStage_mapsTo rank Q hQ k)

section Metric

variable [MetricSpace X]

/-- With `K` ranks, the exponent is `2*K` even if the source has arbitrarily
many small simplices. -/
theorem rankComposition_lipschitz (rank : Fin N → Fin K) (Q : Fin N → X → X)
    (hdis : ∀ k, DisjointActivity (rankMembers rank k) Q)
    (hstable : ∀ k, StableActivity (rankMembers rank k) Q)
    {C : NNReal} (hC : 1 ≤ C) (hQ : ∀ i, LipschitzWith C (Q i)) :
    LipschitzWith (C ^ (2 * K)) (rankComposition rank Q) := by
  have hs (k : Fin K) : LipschitzWith (C * C) (rankStage rank Q k) :=
    disjointStage_lipschitz _ Q (hdis k) (hstable k) hC (fun i _ => hQ i)
  have h := composeSteps_lipschitz (rankStage rank Q) (descendingFaces K)
    (fun _ => C * C) (fun k _ => hs k)
  have heq : ((descendingFaces K).map (fun _ => C * C)).prod = C ^ (2 * K) := by
    rw [List.map_const', List.prod_replicate, descendingFaces_length]
    rw [← pow_two, ← pow_mul]
  rw [heq] at h
  exact h

/-- The displacement cost is one copy per rank, not one per face. -/
theorem rankComposition_displacement (rank : Fin N → Fin K) (Q : Fin N → X → X)
    {δ : ℝ} (hδ : 0 ≤ δ) (hQ : ∀ i x, dist (Q i x) x ≤ δ) :
    ∀ x, dist (rankComposition rank Q x) x ≤ (K : ℝ) * δ := by
  intro x
  have h := composeSteps_displacement (rankStage rank Q) (descendingFaces K) (fun _ => δ)
    (fun k _ => disjointStage_displacement _ Q hδ (fun i _ => hQ i)) x
  rw [List.map_const', List.sum_replicate, descendingFaces_length, nsmul_eq_mul] at h
  exact h

end Metric

section Topology

variable [TopologicalSpace X]

/-- The local face factorization survives dimension stages. Earlier ranks
need only fix the selected point and preserve the selected projection locally;
other maps in the selected rank are locally the identity. -/
theorem rankComposition_local_factors (rank : Fin N → Fin K) (Q : Fin N → X → X)
    (e : Fin N) (p : X) (π : X → X)
    (hπ : ContinuousAt π p) (hπp : π p = p)
    (hππ : (fun x => π (π x)) =ᶠ[𝓝 p] π)
    (hstage : ∀ k, ContinuousAt (rankStage rank Q k) p)
    (hfix : ∀ i, rank e < rank i → Q i p = p)
    (hproj : ∀ i, rank e < rank i → (fun x => π (Q i x)) =ᶠ[𝓝 p] π)
    (hother : ∀ i, rank i = rank e → i ≠ e → Q i =ᶠ[𝓝 p] id)
    (he : Q e =ᶠ[𝓝 p] π) :
    rankComposition rank Q =ᶠ[𝓝 p] (fun x => rankComposition rank Q (π x)) := by
  obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp (mem_descendingFaces (rank e))
  have horder : List.Pairwise (fun i j : Fin K => j < i) (descendingFaces K) :=
    (Finset.sortedGT_sort Finset.univ).pairwise
  rw [hsplit] at horder
  have hbefore : ∀ k ∈ before, rank e < k := fun k hk =>
    (List.pairwise_append.mp horder).2.2 k hk (rank e) (by simp)
  change composeSteps (rankStage rank Q) (descendingFaces K) =ᶠ[𝓝 p]
    (fun x => composeSteps (rankStage rank Q) (descendingFaces K) (π x))
  rw [hsplit]
  apply composeSteps_local_collapse (rankStage rank Q) before after (rank e) p π hπ hπp hππ
    (fun k _ => hstage k)
  · intro k hk
    apply disjointStage_eq_of_fixed
    intro i hi
    apply hfix i
    rw [(mem_rankMembers rank k i).mp hi]
    exact hbefore k hk
  · intro k hk
    apply disjointStage_eventually_preserves_projection
    intro i hi
    apply hproj i
    rw [(mem_rankMembers rank k i).mp hi]
    exact hbefore k hk
  · apply disjointStage_local_collapse _ Q
      ((mem_rankMembers rank (rank e) e).mpr rfl)
    · intro i hi hie
      exact hother i ((mem_rankMembers rank (rank e) i).mp hi) hie
    · exact he

end Topology

end BrehmApprox
