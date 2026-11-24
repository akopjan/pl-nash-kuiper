module

public import BrehmApprox.SourceFlattening
public import BrehmApprox.FiniteFlatteningComposition
public import Mathlib.Data.Finset.Sort

/-!+# Descending composition of actual source face collapses

For a minimal face, every earlier containing-face collapse preserves its
retraction, and every earlier incomparable-face collapse is locally the identity.
The selected factor collapses a neighborhood. The full finite source composition
therefore factors locally through that face retraction.
-/

@[expose] public section

noncomputable section

open scoped Topology
open Filter

namespace BrehmApprox

def descendingFaces (N : ℕ) : List (Fin N) := Finset.univ.sort (· ≥ ·)

lemma mem_descendingFaces {N : ℕ} (i : Fin N) : i ∈ descendingFaces N := by
  simp only [descendingFaces, Finset.mem_sort, Finset.mem_univ]

lemma descendingFaces_pairwise {X : Type*} [MetricSpace X] {Good : (X → X) → Prop}
    {M : PolytopeModel X Good} {N : ℕ} {L : ℝ} (D : ReferenceAtlas M N L) :
    List.Pairwise (fun i j => ¬ D.faceLE i j) (descendingFaces N) := by
  have horder : List.Pairwise (fun i j : Fin N => j < i) (descendingFaces N) :=
    (Finset.sortedGT_sort Finset.univ).pairwise
  apply horder.imp
  intro i j hij hface
  have hne : i ≠ j := ne_of_gt hij
  have hidx := D.index_strict i j hface hne
  exact Nat.lt_asymm (show j.val < i.val from hij) hidx

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : Type v} [MetricSpace P]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

theorem compose_source_cutoffs_flat_at
    (hintrinsic : ChainGenerated S.cell) (before after : List (Fin N)) (e : Fin N)
    (F : Fin N → AffineSubspace ℝ E)
    [∀ i, Nonempty (F i)] [∀ i, (F i).direction.HasOrthogonalProjection]
    (Bad : Fin N → Set E) (b : Fin N → ℝ) {c α : ℝ} (Q : Fin N → P → P)
    (hQ : ∀ i, S.FaceMapRealization i (cutoffAffineFlatten (F i) (Bad i) (b i) c α) (Q i))
    (hcont : ∀ i, Continuous (Q i))
    (hcoreF : ∀ i, D.core i ⊆ F i)
    (hbad : ∀ i, (F i : Set E) \ D.core i ⊆ Bad i)
    (hcross : ∀ k i j, D.faceLE k i → D.faceLE j i → ¬ D.faceLE k j → D.core j ⊆ Bad k)
    (hb : ∀ i, 0 ≤ b i) (hbe : 0 < b e)
    (hc0 : 0 < c) (hc1 : c < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hne : (D.core e).Nonempty) (hconvex : Convex ℝ (D.core e)) (hBad : IsClosed (Bad e))
    (hbefore : ∀ k ∈ before, ¬ D.faceLE k e)
    {p : P} (hp : p ∈ S.cell e) (hpBad : S.fold p ∉ Bad e)
    (hmin : ∀ i, p ∈ S.cell i → D.faceLE e i) :
    composeSteps Q (before ++ e :: after) =ᶠ[𝓝 p]
      (fun x => composeSteps Q (before ++ e :: after)
        (S.retractFromCore e (S.convexCoreProjection e hne hconvex) x)) := by
  let r := S.convexCoreProjection e hne hconvex
  let π := S.retractFromCore e r
  have hrfix : ∀ z ∈ D.core e, (r z : E) = z := fun z hz =>
    S.convexCoreProjection_fix e hne hconvex hz
  have hπcont : ContinuousAt π p :=
    (S.retractFromCore_lipschitz e r hintrinsic
      (S.convexCoreProjection_short e hne hconvex)).continuous.continuousAt
  have hπp : π p = p := S.retractFromCore_fix e r hrfix hp
  have hππ : (fun x => π (π x)) =ᶠ[𝓝 p] π :=
    Filter.Eventually.of_forall (S.retractFromCore_idempotent e r hrfix)
  have hfix : ∀ k ∈ before, Q k p = p := fun k hk =>
    (hQ k).nonincident e (hbefore k hk) p hp
  have hproj : ∀ k ∈ before, (fun x => π (Q k x)) =ᶠ[𝓝 p] π := by
    intro k hk
    by_cases hek : D.faceLE e k
    · apply Filter.Eventually.of_forall
      intro x
      exact S.cutoff_face_preserves_retraction k e hne hconvex (F k)
        ((D.core_mono e k hek).trans (hcoreF k)) (Bad k) (b k) c α (hQ k) x
    · have hid := S.cutoff_face_locally_identity_at_incomparable hintrinsic e k hek
        (hbefore k hk) (F k) (Bad k) (hbad k) (hcross k) (hb k) hc0.le hc1
        hα0.le hα1 (hQ k) hp hmin
      filter_upwards [hid] with x hx
      simpa only [id_eq] using congrArg π hx
  have he := S.cutoff_face_locally_collapses hintrinsic e hne hconvex (F e)
    (hcoreF e) (Bad e) hBad (hbad e) hbe hc0 hα0 hα1 (hQ e) hp hpBad hmin
  exact composeSteps_local_collapse Q before after e p π hπcont hπp hππ
    (fun k _ => (hcont k).continuousAt) hfix hproj he

/-- Every face occurs in the canonical descending order, so the preceding
local theorem applies simultaneously at every minimal-face point. -/
theorem descending_source_cutoffs_flat_at
    (hintrinsic : ChainGenerated S.cell) (e : Fin N)
    (F : Fin N → AffineSubspace ℝ E)
    [∀ i, Nonempty (F i)] [∀ i, (F i).direction.HasOrthogonalProjection]
    (Bad : Fin N → Set E) (b : Fin N → ℝ) {c α : ℝ} (Q : Fin N → P → P)
    (hQ : ∀ i, S.FaceMapRealization i (cutoffAffineFlatten (F i) (Bad i) (b i) c α) (Q i))
    (hcont : ∀ i, Continuous (Q i))
    (hcoreF : ∀ i, D.core i ⊆ F i)
    (hbad : ∀ i, (F i : Set E) \ D.core i ⊆ Bad i)
    (hcross : ∀ k i j, D.faceLE k i → D.faceLE j i → ¬ D.faceLE k j → D.core j ⊆ Bad k)
    (hb : ∀ i, 0 ≤ b i) (hbe : 0 < b e)
    (hc0 : 0 < c) (hc1 : c < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hne : (D.core e).Nonempty) (hconvex : Convex ℝ (D.core e)) (hBad : IsClosed (Bad e))
    {p : P} (hp : p ∈ S.cell e) (hpBad : S.fold p ∉ Bad e)
    (hmin : ∀ i, p ∈ S.cell i → D.faceLE e i) :
    composeSteps Q (descendingFaces N) =ᶠ[𝓝 p]
      (fun x => composeSteps Q (descendingFaces N)
        (S.retractFromCore e (S.convexCoreProjection e hne hconvex) x)) := by
  obtain ⟨before, after, hsplit⟩ := List.mem_iff_append.mp (mem_descendingFaces e)
  have horder := descendingFaces_pairwise D
  rw [hsplit] at horder ⊢
  have hcrossOrder := (List.pairwise_append.mp horder).2.2
  apply S.compose_source_cutoffs_flat_at hintrinsic before after e F Bad b Q hQ hcont
    hcoreF hbad hcross hb hbe hc0 hc1 hα0 hα1 hne hconvex hBad
  · intro k hk
    exact hcrossOrder k hk e (by simp)
  · exact hp
  · exact hpBad
  · exact hmin

end FoldedSource
end BrehmApprox
