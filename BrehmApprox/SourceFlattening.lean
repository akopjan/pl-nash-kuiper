module

public import BrehmApprox.FaceLifting
public import BrehmApprox.CellProjections
public import BrehmApprox.FoldedGeometry

/-!+# Local flattening statements on the actual folded source

The maps constructed by `FaceLifting` act on source cells. This module proves
their local collapse, local identity at incomparable minimal faces, and exact
preservation of lower-face retractions. These are the actual hypotheses needed
by the finite composition theorem on the source itself.
-/

@[expose] public section

noncomputable section

open scoped Topology
open Filter

namespace BrehmApprox

universe u v

section Metric

variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

/-- The exact relation between an ambient face map and its already constructed
source lift. This records formulas, not an existence or preparation axiom. -/
structure FaceMapRealization (e : Fin N) (A : X → X) (Q : P → P) : Prop where
  preserves : ∀ i, Set.MapsTo Q (S.cell i) (S.cell i)
  incident : ∀ i, D.faceLE e i → ∀ x ∈ S.cell i, S.fold (Q x) = A (S.fold x)
  nonincident : ∀ i, ¬ D.faceLE e i → ∀ x ∈ S.cell i, Q x = x

lemma finite_cell_avoidance (J : Fin N → Prop) {p : P}
    (hp : ∀ i, J i → p ∉ S.cell i) :
    ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, ∀ i, J i → x ∉ S.cell i := by
  classical
  let U : Set P := ⋂ i, if J i then (S.cell i)ᶜ else Set.univ
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact (S.closed_cell i).isOpen_compl
    · exact isOpen_univ
  refine ⟨U, hU, ?_, ?_⟩
  · apply Set.mem_iInter.mpr
    intro i
    by_cases hi : J i
    · simpa only [ite_eq_left hi, Set.mem_compl_iff] using hp i hi
    · simp only [ite_eq_right hi, Set.mem_univ]
  · intro x hx i hi
    have hxi := Set.mem_iInter.mp hx i
    simpa only [ite_eq_left hi, Set.mem_compl_iff] using hxi

/-- A point whose minimal face is `e` has a neighborhood meeting only cells
which contain `e`. Finiteness and actual closed source cells suffice. -/
lemma open_star_of_minimal_face (e : Fin N) {p : P}
    (hmin : ∀ i, p ∈ S.cell i → D.faceLE e i) :
    ∃ U : Set P, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, ∀ i, x ∈ S.cell i → D.faceLE e i := by
  obtain ⟨U, hU, hpU, havoid⟩ := S.finite_cell_avoidance (fun i => ¬ D.faceLE e i)
    (fun i hi hpi => hi (hmin i hpi))
  refine ⟨U, hU, hpU, ?_⟩
  intro x hx i hxi
  by_contra hnot
  exact havoid x hx i hnot hxi

lemma FaceMapRealization.fix_of_model_fix {e : Fin N} {A : X → X} {Q : P → P}
    (hQ : S.FaceMapRealization e A Q) {x : P} (hA : A (S.fold x) = S.fold x) : Q x = x := by
  obtain ⟨i, hx⟩ := S.cover x
  by_cases hi : D.faceLE e i
  · apply S.fold_injective_cell i (hQ.preserves i hx) hx
    rw [hQ.incident i hi x hx, hA]
  · exact hQ.nonincident i hi x hx

lemma FaceMapRealization.preserves_retraction {e : Fin N} {A : X → X} {Q : P → P}
    (hQ : S.FaceMapRealization e A Q) (k : Fin N) (r : X → D.core k)
    (hcomm : ∀ z, (r (A z) : X) = (r z : X)) (x : P) :
    S.retractFromCore k r (Q x) = S.retractFromCore k r x := by
  apply S.fold_injective_cell k (S.retractFromCore_mem k r _) (S.retractFromCore_mem k r _)
  rw [S.fold_retractFromCore, S.fold_retractFromCore]
  obtain ⟨i, hx⟩ := S.cover x
  by_cases hi : D.faceLE e i
  · rw [hQ.incident i hi x hx]
    exact hcomm (S.fold x)
  · rw [hQ.nonincident i hi x hx]

lemma FaceMapRealization.locally_identity_of_model {e : Fin N} {A : X → X} {Q : P → P}
    (hQ : S.FaceMapRealization e A Q) (hintrinsic : ChainGenerated S.cell) {p : P}
    (hA : A =ᶠ[𝓝 (S.fold p)] id) : Q =ᶠ[𝓝 p] id := by
  have hq : Tendsto S.fold (𝓝 p) (𝓝 (S.fold p)) :=
    (S.fold_lipschitz hintrinsic).continuous.continuousAt.tendsto
  filter_upwards [hA.comp_tendsto hq] with x hx
  exact hQ.fix_of_model_fix S hx

lemma FaceMapRealization.locally_identity_outside_incident {e : Fin N}
    {A : X → X} {Q : P → P} (hQ : S.FaceMapRealization e A Q) {p : P}
    (hp : ∀ i, D.faceLE e i → p ∉ S.cell i) : Q =ᶠ[𝓝 p] id := by
  obtain ⟨U, hU, hpU, havoid⟩ := S.finite_cell_avoidance (D.faceLE e) hp
  filter_upwards [hU.mem_nhds hpU] with x hx
  obtain ⟨i, hxi⟩ := S.cover x
  exact hQ.nonincident i (fun hi => havoid x hx i hi hxi) x hxi

end FoldedSource
end Metric

section Affine

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : Type v} [MetricSpace P]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

theorem exists_cutoff_face_realization
    (hintrinsic : ChainGenerated S.cell) (e : Fin N)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (Bad : Set E) (hbad : (F : Set E) \ D.core e ⊆ Bad)
    (hconvex : ∀ i, Convex ℝ (D.core i))
    (hcross : ∀ i j, D.faceLE e i → D.faceLE j i → ¬ D.faceLE e j → D.core j ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ Q : P → P, S.FaceMapRealization e (cutoffAffineFlatten F Bad b c α) Q ∧
      (∀ x y, dist (Q x) (Q y) ≤ ((1 + α * c) / (1 - α)) * dist x y) ∧
      ∀ x, dist (Q x) x ≤ α * (c * b) := by
  obtain ⟨Q, hLip, hpres, hinc, hnon, hdisp⟩ :=
    S.exists_cutoff_face_lift hintrinsic e F Bad hbad hconvex hcross hb hc0 hc1 hα0 hα1
  exact ⟨Q, ⟨hpres, hinc, hnon⟩, hLip, hdisp⟩

/-- A lifted normal collapse along a larger affine face preserves the actual
source retraction onto each convex lower face, globally on the source. -/
theorem cutoff_face_preserves_retraction
    (e k : Fin N) (hne : (D.core k).Nonempty) (hconvex : Convex ℝ (D.core k))
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (hcoreF : D.core k ⊆ F) (Bad : Set E) (b c α : ℝ) {Q : P → P}
    (hQ : S.FaceMapRealization e (cutoffAffineFlatten F Bad b c α) Q) (x : P) :
    S.retractFromCore k (S.convexCoreProjection k hne hconvex) (Q x) =
      S.retractFromCore k (S.convexCoreProjection k hne hconvex) x := by
  apply hQ.preserves_retraction S k _
  intro z
  exact convexProjection_affineNormalFlatten (D.core k) hne
    (M.compact _ (D.polytope_core k)).isComplete hconvex F hcoreF α
    (distanceCutoff Bad b c) z

/-- At a minimal-face point, the lifted map really collapses a whole source
neighborhood to the actual closed-face retraction. -/
theorem cutoff_face_locally_collapses
    (hintrinsic : ChainGenerated S.cell) (e : Fin N)
    (hne : (D.core e).Nonempty) (hconvex : Convex ℝ (D.core e))
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (hcoreF : D.core e ⊆ F) (Bad : Set E) (hBad : IsClosed Bad)
    (hbad : (F : Set E) \ D.core e ⊆ Bad)
    {b c α : ℝ} (hb : 0 < b) (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1)
    {Q : P → P} (hQ : S.FaceMapRealization e (cutoffAffineFlatten F Bad b c α) Q)
    {p : P} (hp : p ∈ S.cell e) (hpBad : S.fold p ∉ Bad)
    (hmin : ∀ i, p ∈ S.cell i → D.faceLE e i) :
    Q =ᶠ[𝓝 p] S.retractFromCore e (S.convexCoreProjection e hne hconvex) := by
  let r := S.convexCoreProjection e hne hconvex
  obtain ⟨U, hU, hpU, hstar⟩ := S.open_star_of_minimal_face e hmin
  have hpF : S.fold p ∈ F := hcoreF (S.fold_mem_core hp)
  obtain ⟨V, hV, hpV, hcollapse⟩ := cutoffAffineFlatten_local_collapse F Bad hBad
    hb hc hα0 hα1 hpF hpBad
  have hq : Tendsto S.fold (𝓝 p) (𝓝 (S.fold p)) :=
    (S.fold_lipschitz hintrinsic).continuous.continuousAt.tendsto
  have hPcont : ContinuousAt (affineProjection F) (S.fold p) :=
    (affineProjection_short F).continuous.continuousAt
  have hP : Tendsto (affineProjection F) (𝓝 (S.fold p)) (𝓝 (S.fold p)) := by
    simpa only [affineProjection_fix F hpF] using hPcont.tendsto
  have hgood : ∀ᶠ z in 𝓝 (S.fold p), affineProjection F z ∉ Bad :=
    hP.eventually (hBad.isOpen_compl.mem_nhds hpBad)
  have hVpull : ∀ᶠ x in 𝓝 p, S.fold x ∈ V := hq.eventually (hV.mem_nhds hpV)
  have hgoodpull : ∀ᶠ x in 𝓝 p, affineProjection F (S.fold x) ∉ Bad := hq.eventually hgood
  filter_upwards [hU.mem_nhds hpU, hVpull, hgoodpull] with x hxU hxV hxgood
  obtain ⟨i, hxi⟩ := S.cover x
  have hei : D.faceLE e i := hstar x hxU i hxi
  have hPcore : affineProjection F (S.fold x) ∈ D.core e := by
    by_contra hnot
    exact hxgood (hbad ⟨affineProjection_mem F (S.fold x), hnot⟩)
  have hrx : (r (S.fold x) : E) = affineProjection F (S.fold x) := by
    calc
      _ = convexProjection (D.core e) hne (M.compact _ (D.polytope_core e)).isComplete
          hconvex (affineProjection F (S.fold x)) :=
        (convexProjection_after_affine_projection (D.core e) hne
          (M.compact _ (D.polytope_core e)).isComplete hconvex F hcoreF (S.fold x)).symm
      _ = _ := convexProjection_fix _ _ _ _ hPcore
  apply S.fold_injective_cell i (hQ.preserves i hxi)
    (S.cell_mono e i hei (S.retractFromCore_mem e r x))
  rw [hQ.incident i hei x hxi, hcollapse _ hxV, S.fold_retractFromCore]
  exact hrx.symm

/-- Incomparable faces do not interfere near a point of a minimal source
face. The proof separates genuinely cofacial cells from unrelated folded
sheets, which may have arbitrary overlapping model images. -/
theorem cutoff_face_locally_identity_at_incomparable
    (hintrinsic : ChainGenerated S.cell) (e k : Fin N)
    (hek : ¬ D.faceLE e k) (hke : ¬ D.faceLE k e)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (Bad : Set E) (hbad : (F : Set E) \ D.core k ⊆ Bad)
    (hcross : ∀ i j, D.faceLE k i → D.faceLE j i → ¬ D.faceLE k j → D.core j ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    {Q : P → P} (hQ : S.FaceMapRealization k (cutoffAffineFlatten F Bad b c α) Q)
    {p : P} (hp : p ∈ S.cell e)
    (hmin : ∀ i, p ∈ S.cell i → D.faceLE e i) : Q =ᶠ[𝓝 p] id := by
  classical
  by_cases hi : ∃ i, D.faceLE k i ∧ p ∈ S.cell i
  · obtain ⟨i, hki, hpi⟩ := hi
    have hei := hmin i hpi
    have hpBad : S.fold p ∈ Bad := hcross i e hki hei hke (S.fold_mem_core hp)
    have hpNot : S.fold p ∉ D.core k := by
      intro hpcore
      rw [← S.image_cell k] at hpcore
      obtain ⟨y, hy, hyq⟩ := hpcore
      have hpy : p = y := S.fold_injective_cell i hpi (S.cell_mono k i hki hy) hyq.symm
      have hpk : p ∈ S.cell k := hpy.symm ▸ hy
      exact hek (hmin k hpk)
    obtain ⟨V, hV, hpV, hidentity⟩ := cutoffAffineFlatten_local_identity F Bad
      (M.compact _ (D.polytope_core k)).isClosed hbad hb hc0 hc1 hα0 hα1 hpBad hpNot
    apply hQ.locally_identity_of_model S hintrinsic
    filter_upwards [hV.mem_nhds hpV] with z hz
    exact hidentity z hz
  · apply hQ.locally_identity_outside_incident S
    intro i hki hpi
    exact hi ⟨i, hki, hpi⟩

end FoldedSource
end Affine

end BrehmApprox
