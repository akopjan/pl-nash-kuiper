module

public import BrehmApprox.CellwiseLifting
public import BrehmApprox.DistanceCutoff

/-!+# An actual normal collapse on a folded polyhedral source

For one face, the model collapse is applied only in source cells containing
that face. It is the identity in every other source cell. Compatibility on
common faces follows from the distance cut-off; unrelated overlapping folded
images are never identified.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

universe u v

section Model

namespace ReferenceAtlas

variable {X : Type u} [MetricSpace X] {Good : (X → X) → Prop}
variable {M : PolytopeModel X Good} {N : ℕ} {L : ℝ}
variable (D : ReferenceAtlas M N L)

/-- Use a face map only on cells which contain that face. -/
def faceModelMap (e : Fin N) (Q : X → X) (i : Fin N) (x : X) : X := by
  classical
  exact if D.faceLE e i then Q x else x

lemma faceModelMap_incident (e : Fin N) (Q : X → X) {i : Fin N}
    (hi : D.faceLE e i) (x : X) : D.faceModelMap e Q i x = Q x := by
  classical
  simp only [faceModelMap, ite_eq_left hi]

lemma faceModelMap_nonincident (e : Fin N) (Q : X → X) {i : Fin N}
    (hi : ¬ D.faceLE e i) (x : X) : D.faceModelMap e Q i x = x := by
  classical
  simp only [faceModelMap, ite_eq_right hi]

lemma faceModelMap_mapsTo (e : Fin N) (Q : X → X)
    (hpres : ∀ i, D.faceLE e i → Set.MapsTo Q (D.core i) (D.core i)) :
    ∀ i, Set.MapsTo (D.faceModelMap e Q i) (D.core i) (D.core i) := by
  intro i x hx
  by_cases hi : D.faceLE e i
  · rw [D.faceModelMap_incident e Q hi]
    exact hpres i hi hx
  · rw [D.faceModelMap_nonincident e Q hi]
    exact hx

/-- The map fixes every nonincident subface of a cell incident to `e`.
This is precisely where the cofacial bad set enters. -/
lemma faceModelMap_compatible {P : Type v} [MetricSpace P] (S : FoldedSource D P)
    (e : Fin N) (Q : X → X)
    (hpres : ∀ i, D.faceLE e i → Set.MapsTo Q (D.core i) (D.core i))
    (hfix : ∀ i j, D.faceLE e i → D.faceLE j i → ¬ D.faceLE e j →
      ∀ x ∈ D.core j, Q x = x) :
    S.LiftCompatible (D.faceModelMap e Q) := by
  intro i j x hx
  by_cases hi : D.faceLE e i
  · rw [D.faceModelMap_incident e Q hi]
    by_cases hj : D.faceLE e j
    · rw [D.faceModelMap_incident e Q hj]
      refine ⟨rfl, ?_⟩
      by_cases hm : D.faceLE e (D.meet i j)
      · exact hpres _ hm hx
      · rw [hfix i (D.meet i j) hi (D.meet_le_left i j) hm x hx]
        exact hx
    · rw [D.faceModelMap_nonincident e Q hj]
      have hm : ¬ D.faceLE e (D.meet i j) :=
        fun h => hj (D.le_trans _ _ _ h (D.meet_le_right i j))
      have heq := hfix i (D.meet i j) hi (D.meet_le_left i j) hm x hx
      exact ⟨heq, heq.symm ▸ hx⟩
  · rw [D.faceModelMap_nonincident e Q hi]
    by_cases hj : D.faceLE e j
    · rw [D.faceModelMap_incident e Q hj]
      have hm : ¬ D.faceLE e (D.meet i j) :=
        fun h => hi (D.le_trans _ _ _ h (D.meet_le_left i j))
      exact ⟨(hfix j (D.meet i j) hj (D.meet_le_right i j) hm x hx).symm, hx⟩
    · rw [D.faceModelMap_nonincident e Q hj]
      exact ⟨rfl, hx⟩

lemma faceModelMap_lipschitz (e : Fin N) (Q : X → X) {C : NNReal} (hC : 1 ≤ C)
    (hQ : ∀ i, D.faceLE e i → ∀ x ∈ D.core i, ∀ y ∈ D.core i,
      dist (Q x) (Q y) ≤ C * dist x y) :
    ∀ i, ∀ x ∈ D.core i, ∀ y ∈ D.core i,
      dist (D.faceModelMap e Q i x) (D.faceModelMap e Q i y) ≤ C * dist x y := by
  intro i x hx y hy
  by_cases hi : D.faceLE e i
  · rw [D.faceModelMap_incident e Q hi, D.faceModelMap_incident e Q hi]
    exact hQ i hi x hx y hy
  · rw [D.faceModelMap_nonincident e Q hi, D.faceModelMap_nonincident e Q hi]
    exact (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ C from hC) (dist_nonneg : 0 ≤ dist x y))

lemma faceModelMap_displacement (e : Fin N) (Q : X → X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : ∀ i, D.faceLE e i → ∀ x ∈ D.core i, dist (Q x) x ≤ δ) :
    ∀ i, ∀ x ∈ D.core i, dist (D.faceModelMap e Q i x) x ≤ δ := by
  intro i x hx
  by_cases hi : D.faceLE e i
  · rw [D.faceModelMap_incident e Q hi]
    exact hQ i hi x hx
  · rw [D.faceModelMap_nonincident e Q hi, dist_self]
    exact hδ

end ReferenceAtlas
end Model

section Affine

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : Type v} [MetricSpace P]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

/-- A distance-cutoff collapse is lifted to the actual source. All geometric
conditions are ordinary inclusions of explicitly given face sets. The theorem
constructs the source map and proves its global metric bounds. -/
theorem exists_cutoff_face_lift (S : FoldedSource D P)
    (hintrinsic : ChainGenerated S.cell) (e : Fin N)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (Bad : Set E) (hbad : (F : Set E) \ D.core e ⊆ Bad)
    (hconvex : ∀ i, Convex ℝ (D.core i))
    (hcross : ∀ i j, D.faceLE e i → D.faceLE j i → ¬ D.faceLE e j → D.core j ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ Q : P → P,
      (∀ x y, dist (Q x) (Q y) ≤ ((1 + α * c) / (1 - α)) * dist x y) ∧
      (∀ i, Set.MapsTo Q (S.cell i) (S.cell i)) ∧
      (∀ i, D.faceLE e i → ∀ x ∈ S.cell i,
        S.fold (Q x) = cutoffAffineFlatten F Bad b c α (S.fold x)) ∧
      (∀ i, ¬ D.faceLE e i → ∀ x ∈ S.cell i, Q x = x) ∧
      ∀ x, dist (Q x) x ≤ α * (c * b) := by
  let A : E → E := cutoffAffineFlatten F Bad b c α
  have hpres : ∀ i, D.faceLE e i → Set.MapsTo A (D.core i) (D.core i) := by
    intro i hi
    exact cutoffAffineFlatten_mapsTo_convex F Bad hbad (D.core_mono e i hi)
      (hconvex i) hb hα0 hα1
  have hfix : ∀ i j, D.faceLE e i → D.faceLE j i → ¬ D.faceLE e j →
      ∀ x ∈ D.core j, A x = x := by
    intro i j hi hj hej x hx
    exact cutoffAffineFlatten_fix_on_bad F Bad hc0 hc1 hα0 hα1
      (hcross i j hi hj hej hx)
  have hmaps := D.faceModelMap_mapsTo e A hpres
  have hcompat := D.faceModelMap_compatible S e A hpres hfix
  let Q := S.cellwiseLift (D.faceModelMap e A) hmaps
  have hCL : 1 ≤ (1 + α * c) / (1 - α) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - α)).2
    nlinarith [mul_nonneg hα0 hc0]
  let C : NNReal := ⟨(1 + α * c) / (1 - α), le_trans zero_le_one hCL⟩
  have hLip : LipschitzWith C Q := S.cellwiseLift_lipschitz _ hmaps hcompat hintrinsic
    (D.faceModelMap_lipschitz e A (show 1 ≤ C from hCL) (by
      intro i hi x hx y hy
      exact cutoffAffineFlatten_lipschitz F Bad hb hc0 hα0 hα1 x y))
  refine ⟨Q, ?_, S.cellwiseLift_mapsTo _ hmaps hcompat, ?_, ?_, ?_⟩
  · intro x y
    exact hLip.dist_le_mul x y
  · intro i hi x hx
    rw [S.fold_cellwiseLift _ hmaps hcompat i hx]
    exact D.faceModelMap_incident e A hi (S.fold x)
  · intro i hi x hx
    apply S.cellwiseLift_fix _ hmaps hcompat hx
    exact D.faceModelMap_nonincident e A hi (S.fold x)
  · apply S.cellwiseLift_displacement _ hmaps hcompat
    apply D.faceModelMap_displacement e A (mul_nonneg hα0 (mul_nonneg hc0 hb))
    intro i hi x hx
    exact cutoffAffineFlatten_displacement F Bad hb hc0 hα0 hα1 x

end FoldedSource
end Affine

end BrehmApprox
