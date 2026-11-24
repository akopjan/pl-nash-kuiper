module

public import BrehmApprox.Core
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Finite composition of face collapses

The execution order is the list order: its first map is applied first. Products
of Lipschitz constants and sums of uniform displacements are proved directly.
The local projection theorem explains why, after one factor has collapsed a
neighborhood, all later factors preserve the resulting equality.
-/

@[expose] public section

open scoped Topology NNReal
open Filter

namespace BrehmApprox

universe u v w

variable {X : Type u} {ι : Type v}

/-- Execute a finite list of maps in the displayed order. -/
def composeSteps (Q : ι → X → X) : List ι → X → X
  | [], x => x
  | i :: is, x => composeSteps Q is (Q i x)

lemma composeSteps_append (Q : ι → X → X) (is js : List ι) (x : X) :
    composeSteps Q (is ++ js) x = composeSteps Q js (composeSteps Q is x) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, composeSteps, ih]

lemma composeSteps_fix (Q : ι → X → X) (is : List ι) (p : X)
    (hfix : ∀ i ∈ is, Q i p = p) : composeSteps Q is p = p := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [composeSteps, hfix i (by simp)]
      exact ih (fun j hj => hfix j (by simp [hj]))

lemma composeSteps_mapsTo (Q : ι → X → X) (is : List ι) {A : Set X}
    (hQ : ∀ i ∈ is, Set.MapsTo (Q i) A A) : Set.MapsTo (composeSteps Q is) A A := by
  induction is with
  | nil => exact fun _ hx => hx
  | cons i is ih =>
      intro x hx
      exact ih (fun j hj => hQ j (by simp [hj])) (hQ i (by simp) hx)

section Topology

variable [TopologicalSpace X]

lemma composeSteps_continuous (Q : ι → X → X) (is : List ι)
    (hQ : ∀ i ∈ is, Continuous (Q i)) : Continuous (composeSteps Q is) := by
  induction is with
  | nil => exact continuous_id
  | cons i is ih =>
      exact (ih (fun j hj => hQ j (by simp [hj]))).comp (hQ i (by simp))

lemma composeSteps_continuousAt (Q : ι → X → X) (is : List ι) (p : X)
    (hQ : ∀ i ∈ is, ContinuousAt (Q i) p)
    (hfix : ∀ i ∈ is, Q i p = p) : ContinuousAt (composeSteps Q is) p := by
  induction is with
  | nil => exact continuousAt_id
  | cons i is ih =>
      have htail := ih (fun j hj => hQ j (by simp [hj]))
        (fun j hj => hfix j (by simp [hj]))
      have htail' : ContinuousAt (composeSteps Q is) (Q i p) := by
        simpa only [hfix i (by simp)] using htail
      exact htail'.comp (hQ i (by simp))

/-- Local preservation of a projection is stable under a finite composition
of maps continuous at, and fixing, the selected point. -/
lemma composeSteps_preserves_projection (Q : ι → X → X) (is : List ι)
    (p : X) (π : X → X)
    (hQ : ∀ i ∈ is, ContinuousAt (Q i) p)
    (hfix : ∀ i ∈ is, Q i p = p)
    (hproj : ∀ i ∈ is, (fun x => π (Q i x)) =ᶠ[𝓝 p] π) :
    (fun x => π (composeSteps Q is x)) =ᶠ[𝓝 p] π := by
  induction is with
  | nil => exact Filter.EventuallyEq.rfl
  | cons i is ih =>
      have htail := ih (fun j hj => hQ j (by simp [hj]))
        (fun j hj => hfix j (by simp [hj])) (fun j hj => hproj j (by simp [hj]))
      have hQi : Tendsto (Q i) (𝓝 p) (𝓝 p) := by
        simpa only [hfix i (by simp)] using (hQ i (by simp)).tendsto
      exact (htail.comp_tendsto hQi).trans (hproj i (by simp))

/-- Fixing the projection range locally is also stable under a finite
composition; this statement does not even require continuity. -/
lemma composeSteps_fixes_projection_range (Q : ι → X → X) (is : List ι)
    (p : X) (π : X → X)
    (hfix : ∀ i ∈ is, (fun x => Q i (π x)) =ᶠ[𝓝 p] π) :
    (fun x => composeSteps Q is (π x)) =ᶠ[𝓝 p] π := by
  induction is with
  | nil => exact Filter.EventuallyEq.rfl
  | cons i is ih =>
      have htail := ih (fun j hj => hfix j (by simp [hj]))
      filter_upwards [hfix i (by simp), htail] with x hi hx
      simpa only [composeSteps, hi] using hx

lemma collapse_after_prefix_eventuallyEq {p : X} {π B Q : X → X}
    (hB : ContinuousAt B p) (hBp : B p = p)
    (hproj : (fun x => π (B x)) =ᶠ[𝓝 p] π) (hQ : Q =ᶠ[𝓝 p] π) :
    (fun x => Q (B x)) =ᶠ[𝓝 p] π := by
  have hBt : Tendsto B (𝓝 p) (𝓝 p) := by simpa only [hBp] using hB.tendsto
  exact (hQ.comp_tendsto hBt).trans hproj

/-- Once a factor collapses to a projection near `p`, arbitrary later maps
preserve equality along its fibers. No continuity of the later map is needed. -/
theorem collapse_composition_factors {Y : Type w} {p : X} {π B Q : X → X}
    (C : X → Y) (hπ : ContinuousAt π p) (hπp : π p = p)
    (hππ : (fun x => π (π x)) =ᶠ[𝓝 p] π)
    (hB : ContinuousAt B p) (hBp : B p = p)
    (hproj : (fun x => π (B x)) =ᶠ[𝓝 p] π) (hQ : Q =ᶠ[𝓝 p] π) :
    (fun x => C (Q (B x))) =ᶠ[𝓝 p] (fun x => C (Q (B (π x)))) := by
  have hQB := collapse_after_prefix_eventuallyEq hB hBp hproj hQ
  have hCπ : (fun x => C (Q (B x))) =ᶠ[𝓝 p] (fun x => C (π x)) := hQB.fun_comp C
  have hπt : Tendsto π (𝓝 p) (𝓝 p) := by simpa only [hπp] using hπ.tendsto
  have hpull := hCπ.comp_tendsto hπt
  have hid := hππ.fun_comp C
  exact hCπ.trans (hpull.trans hid).symm

/-- The local normal-flattening conclusion for a finite ordered family. The
factors before the selected collapse need only fix `p` and preserve its
projection locally; the factors after it are unrestricted. -/
theorem composeSteps_local_collapse (Q : ι → X → X)
    (before after : List ι) (k : ι) (p : X) (π : X → X)
    (hπ : ContinuousAt π p) (hπp : π p = p)
    (hππ : (fun x => π (π x)) =ᶠ[𝓝 p] π)
    (hQ : ∀ i ∈ before, ContinuousAt (Q i) p)
    (hfix : ∀ i ∈ before, Q i p = p)
    (hproj : ∀ i ∈ before, (fun x => π (Q i x)) =ᶠ[𝓝 p] π)
    (hk : Q k =ᶠ[𝓝 p] π) :
    composeSteps Q (before ++ k :: after) =ᶠ[𝓝 p]
      (fun x => composeSteps Q (before ++ k :: after) (π x)) := by
  have h := collapse_composition_factors (composeSteps Q after) hπ hπp hππ
    (composeSteps_continuousAt Q before p hQ hfix) (composeSteps_fix Q before p hfix)
    (composeSteps_preserves_projection Q before p π hQ hfix hproj) hk
  change (fun x => composeSteps Q (before ++ k :: after) x) =ᶠ[𝓝 p] _
  simpa only [composeSteps_append, composeSteps] using h

end Topology

section Metric

variable [MetricSpace X]

theorem composeSteps_lipschitz (Q : ι → X → X) (is : List ι) (L : ι → ℝ≥0)
    (hQ : ∀ i ∈ is, LipschitzWith (L i) (Q i)) :
    LipschitzWith (is.map L).prod (composeSteps Q is) := by
  induction is with
  | nil =>
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [composeSteps, List.map_nil, List.prod_nil, NNReal.coe_one, one_mul, le_refl]
  | cons i is ih =>
      have htail := ih (fun j hj => hQ j (by simp [hj]))
      rw [List.map_cons, List.prod_cons, mul_comm]
      exact htail.comp (hQ i (by simp))

/-- Uniform displacement errors add, without multiplying by intermediate
Lipschitz constants. -/
theorem composeSteps_displacement (Q : ι → X → X) (is : List ι) (e : ι → ℝ)
    (hQ : ∀ i ∈ is, ∀ x, dist (Q i x) x ≤ e i) :
    ∀ x, dist (composeSteps Q is x) x ≤ (is.map e).sum := by
  induction is with
  | nil => intro x; simp only [composeSteps, dist_self, List.map_nil, List.sum_nil, le_refl]
  | cons i is ih =>
      intro x
      have htail := ih (fun j hj => hQ j (by simp [hj])) (Q i x)
      calc
        dist (composeSteps Q (i :: is) x) x ≤
            dist (composeSteps Q is (Q i x)) (Q i x) + dist (Q i x) x := dist_triangle _ _ _
        _ ≤ (is.map e).sum + e i := add_le_add htail (hQ i (by simp) x)
        _ = ((i :: is).map e).sum := by simp only [List.map_cons, List.sum_cons]; ring

end Metric

/-- One common sufficiently small positive collapse parameter controls the
whole finite Lipschitz product and displacement sum. Thus parameter selection
does not require any implicit diagonal argument. -/
theorem exists_small_common_flattening_parameter (is : List ι) (c M : ι → ℝ)
    {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      (is.map (fun i => (1 + α * c i) / (1 - α))).prod < 1 + b ∧
      α * (is.map M).sum < ε := by
  have hfactor (i : ι) : ContinuousAt (fun α : ℝ => (1 + α * c i) / (1 - α)) 0 :=
    (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).div
      (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hprod : ContinuousAt
      (fun α : ℝ => (is.map (fun i => (1 + α * c i) / (1 - α))).prod) 0 := by
    induction is with
    | nil => simpa only [List.map_nil, List.prod_nil] using (continuousAt_const (y := (1 : ℝ)))
    | cons i is ih =>
        convert (hfactor i).mul ih using 1
        funext α
        simp only [List.map_cons, List.prod_cons, Pi.mul_apply]
  have hprod0 : (is.map (fun i => (1 + (0 : ℝ) * c i) / (1 - 0))).prod = 1 := by simp
  have hprodEv : ∀ᶠ α : ℝ in 𝓝 0,
      (is.map (fun i => (1 + α * c i) / (1 - α))).prod < 1 + b :=
    hprod.eventually (gt_mem_nhds (by change (is.map (fun i => (1 + (0 : ℝ) * c i) / (1 - 0))).prod < 1 + b; rw [hprod0]; linarith))
  have hsum : ContinuousAt (fun α : ℝ => α * (is.map M).sum) 0 :=
    continuousAt_id.mul continuousAt_const
  have hsumEv : ∀ᶠ α : ℝ in 𝓝 0, α * (is.map M).sum < ε :=
    hsum.eventually (gt_mem_nhds (by simpa using hε))
  have hltEv : ∀ᶠ α : ℝ in 𝓝 0, α < 1 := gt_mem_nhds zero_lt_one
  have hAll : ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α ∧ α < 1 ∧
      (is.map (fun i => (1 + α * c i) / (1 - α))).prod < 1 + b ∧
      α * (is.map M).sum < ε := by
    filter_upwards [self_mem_nhdsWithin,
      hltEv.filter_mono nhdsWithin_le_nhds,
      hprodEv.filter_mono nhdsWithin_le_nhds,
      hsumEv.filter_mono nhdsWithin_le_nhds] with α hpos hlt hprod hsum
    exact ⟨hpos, hlt, hprod, hsum⟩
  exact hAll.exists

end BrehmApprox
