module

public import BrehmApprox.SourceFlattening
public import BrehmApprox.CutoffStages

/-!+# Cardinality-independent stages on the actual source

An active source face map can occur only in cells containing its face. Thus
two maps active at one point would have cofacial indices, even when unrelated
folded images overlap. Model disjointness and model stability therefore lift
to source stages, whose Lipschitz estimate is `L²` independently of their size.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

universe u v

section Metric

variable {X : Type u} [MetricSpace X]

/-- The common metric argument behind disjoint cut-offs in all three models.
Different chart distortions may be absorbed into the coefficient `c`. -/
theorem two_active_feet_impossible (x a b : X) {c : ℝ} (hc : c ≤ 1 / 2)
    (ha : dist x a < c * dist a b) (hb : dist x b < c * dist b a) : False := by
  rw [dist_comm b a] at hb
  have htri := dist_triangle a x b
  rw [dist_comm a x] at htri
  have hscale : 2 * c * dist a b ≤ dist a b :=
    mul_le_of_le_one_left dist_nonneg (by linarith)
  linarith

variable {P : Type v} [MetricSpace P]
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

lemma FaceMapRealization.faceLE_of_active {e : Fin N} {A : X → X} {Q : P → P}
    (hQ : S.FaceMapRealization e A Q) {x : P} (hx : Q x ≠ x)
    {i : Fin N} (hxi : x ∈ S.cell i) : D.faceLE e i := by
  by_contra hi
  exact hx (hQ.nonincident i hi x hxi)

lemma FaceMapRealization.model_active_of_active {e : Fin N} {A : X → X} {Q : P → P}
    (hQ : S.FaceMapRealization e A Q) {x : P} (hx : Q x ≠ x) :
    A (S.fold x) ≠ S.fold x := fun h => hx (hQ.fix_of_model_fix S h)

lemma mem_subcell_of_fold_mem {i j : Fin N} (hji : D.faceLE j i)
    {x : P} (hx : x ∈ S.cell i) (hqx : S.fold x ∈ D.core j) : x ∈ S.cell j := by
  rw [← S.image_cell j] at hqx
  obtain ⟨y, hy, hyq⟩ := hqx
  have hxy : x = y := S.fold_injective_cell i hx (S.cell_mono j i hji hy) hyq.symm
  exact hxy.symm ▸ hy

/-- Only cofacial model disjointness is required for genuine source disjointness. -/
theorem source_family_disjoint (I : Finset (Fin N)) (A : Fin N → X → X)
    (Q : Fin N → P → P) (hQ : ∀ e ∈ I, S.FaceMapRealization e (A e) (Q e))
    (hdis : ∀ e ∈ I, ∀ f ∈ I, e ≠ f →
      (∃ i, D.faceLE e i ∧ D.faceLE f i) → ∀ z, A e z ≠ z → A f z = z) :
    DisjointActivity I Q := by
  intro e he f hf hef x hx
  by_contra hfx
  obtain ⟨i, hxi⟩ := S.cover x
  have hei := (hQ e he).faceLE_of_active S hx hxi
  have hfi := (hQ f hf).faceLE_of_active S hfx hxi
  have heModel := (hQ e he).model_active_of_active S hx
  have hfModel := (hQ f hf).model_active_of_active S hfx
  exact hfModel (hdis e he f hf hef ⟨i, hei, hfi⟩ (S.fold x) heModel)

/-- Model stability has a precise geometric form: the active image either
remains active for the same map or lands on that map's face. -/
theorem source_family_stable (I : Finset (Fin N)) (A : Fin N → X → X)
    (Q : Fin N → P → P) (hQ : ∀ e ∈ I, S.FaceMapRealization e (A e) (Q e))
    (hincomparable : ∀ e ∈ I, ∀ f ∈ I, e ≠ f → ¬ D.faceLE e f)
    (hdis : ∀ e ∈ I, ∀ f ∈ I, e ≠ f →
      (∃ i, D.faceLE e i ∧ D.faceLE f i) → ∀ z, A e z ≠ z → A f z = z)
    (himage : ∀ e ∈ I, ∀ z, A e z ≠ z →
      A e (A e z) ≠ A e z ∨ A e z ∈ D.core e) :
    StableActivity I Q := by
  intro e he f hf hef x hx
  obtain ⟨i, hxi⟩ := S.cover x
  have hei := (hQ e he).faceLE_of_active S hx hxi
  have hyi : Q e x ∈ S.cell i := (hQ e he).preserves i hxi
  have hqy : S.fold (Q e x) = A e (S.fold x) := (hQ e he).incident i hei x hxi
  rcases himage e he (S.fold x) ((hQ e he).model_active_of_active S hx) with hactive | hface
  · have hyactive : Q e (Q e x) ≠ Q e x := by
      intro heq
      have hmodel := (hQ e he).incident i hei (Q e x) hyi
      rw [heq, hqy] at hmodel
      exact hactive hmodel.symm
    exact S.source_family_disjoint I A Q hQ hdis e he f hf hef (Q e x) hyactive
  · have hye : Q e x ∈ S.cell e :=
      S.mem_subcell_of_fold_mem hei hyi (hqy.symm ▸ hface)
    exact (hQ f hf).nonincident e
      (hincomparable f hf e he (fun h => hef h.symm)) (Q e x) hye

theorem source_stage_lipschitz (I : Finset (Fin N)) (A : Fin N → X → X)
    (Q : Fin N → P → P) (hQ : ∀ e ∈ I, S.FaceMapRealization e (A e) (Q e))
    (hincomparable : ∀ e ∈ I, ∀ f ∈ I, e ≠ f → ¬ D.faceLE e f)
    (hdis : ∀ e ∈ I, ∀ f ∈ I, e ≠ f →
      (∃ i, D.faceLE e i ∧ D.faceLE f i) → ∀ z, A e z ≠ z → A f z = z)
    (himage : ∀ e ∈ I, ∀ z, A e z ≠ z →
      A e (A e z) ≠ A e z ∨ A e z ∈ D.core e)
    {C : NNReal} (hC : 1 ≤ C) (hLip : ∀ e ∈ I, LipschitzWith C (Q e)) :
    LipschitzWith (C * C) (disjointStage I Q) :=
  disjointStage_lipschitz I Q (S.source_family_disjoint I A Q hQ hdis)
    (S.source_family_stable I A Q hQ hincomparable hdis himage) hC hLip

/-- A metric foot estimate proves model disjointness without any common
coordinate chart. This is the form used for curved faces with different poles. -/
theorem source_stage_lipschitz_of_feet (I : Finset (Fin N))
    (A : Fin N → X → X) (Bad : Fin N → Set X) (Q : Fin N → P → P)
    (hQ : ∀ e ∈ I, S.FaceMapRealization e (A e) (Q e))
    (hincomparable : ∀ e ∈ I, ∀ f ∈ I, e ≠ f → ¬ D.faceLE e f)
    (hcross : ∀ k i j, D.faceLE k i → D.faceLE j i → ¬ D.faceLE k j → D.core j ⊆ Bad k)
    {d : ℝ} (hd : d ≤ 1 / 2)
    (hfoot : ∀ e ∈ I, ∀ z, A e z ≠ z → ∃ t ∈ D.core e,
      ∀ y ∈ Bad e, dist z t < d * dist t y)
    (himage : ∀ e ∈ I, ∀ z, A e z ≠ z →
      A e (A e z) ≠ A e z ∨ A e z ∈ D.core e)
    {C : NNReal} (hC : 1 ≤ C) (hLip : ∀ e ∈ I, LipschitzWith C (Q e)) :
    LipschitzWith (C * C) (disjointStage I Q) := by
  apply S.source_stage_lipschitz I A Q hQ hincomparable
  · intro e he f hf hef hcofacial z hez
    by_contra hfz
    obtain ⟨i, hei, hfi⟩ := hcofacial
    obtain ⟨t, ht, htz⟩ := hfoot e he z hez
    obtain ⟨s, hs, hsz⟩ := hfoot f hf z hfz
    have hsBad := hcross e i f hei hfi (hincomparable e he f hf hef) hs
    have htBad := hcross f i e hfi hei (hincomparable f hf e he (fun h => hef h.symm)) ht
    exact two_active_feet_impossible z t s hd (htz s hsBad) (hsz t htBad)
  · exact himage
  · exact hC
  · exact hLip

lemma source_stage_mapsTo (I : Finset (Fin N)) (A : Fin N → X → X)
    (Q : Fin N → P → P) (hQ : ∀ e ∈ I, S.FaceMapRealization e (A e) (Q e)) (i : Fin N) :
    Set.MapsTo (disjointStage I Q) (S.cell i) (S.cell i) :=
  disjointStage_mapsTo I Q (fun e he => (hQ e he).preserves i)

end FoldedSource
end Metric

section Euclidean

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : Type v} [MetricSpace P]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

/-- The generic source stage conditions are all proved for the actual
Euclidean distance-cutoff maps. -/
theorem cutoff_source_stage_lipschitz (I : Finset (Fin N))
    (F : Fin N → AffineSubspace ℝ E)
    [∀ i, Nonempty (F i)] [∀ i, (F i).direction.HasOrthogonalProjection]
    (Bad : Fin N → Set E) (b : Fin N → ℝ) {c α : ℝ} (Q : Fin N → P → P)
    (hQ : ∀ e ∈ I,
      S.FaceMapRealization e (cutoffAffineFlatten (F e) (Bad e) (b e) c α) (Q e))
    (hincomparable : ∀ e ∈ I, ∀ f ∈ I, e ≠ f → ¬ D.faceLE e f)
    (hbad : ∀ e ∈ I, (F e : Set E) \ D.core e ⊆ Bad e)
    (hcross : ∀ k i j, D.faceLE k i → D.faceLE j i → ¬ D.faceLE k j → D.core j ⊆ Bad k)
    (hb : ∀ e ∈ I, 0 ≤ b e) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (hα0 : 0 < α) (hα1 : α < 1)
    {C : NNReal} (hC : 1 ≤ C) (hLip : ∀ e ∈ I, LipschitzWith C (Q e)) :
    LipschitzWith (C * C) (disjointStage I Q) := by
  apply S.source_stage_lipschitz I _ Q hQ hincomparable
  · intro e he f hf hef hcofacial z hz
    obtain ⟨i, hei, hfi⟩ := hcofacial
    exact cutoffAffineFlatten_disjoint_activity (F e) (F f) (Bad e) (Bad f)
      (hbad e he) (hbad f hf)
      (hcross f i e hfi hei (hincomparable f hf e he (fun h => hef h.symm)))
      (hcross e i f hei hfi (hincomparable e he f hf hef))
      (hb e he) (hb f hf) hc0 hc1 hα0.le hα1 hz
  · intro e he z hz
    exact cutoffAffineFlatten_image_active_or_face (F e) (Bad e) (hbad e he)
      (hb e he) hα0 hα1 hz
  · exact hC
  · exact hLip

end FoldedSource
end Euclidean

end BrehmApprox
