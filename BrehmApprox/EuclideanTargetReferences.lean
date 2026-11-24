module

public import BrehmApprox.EuclideanReferenceAtlas
public import BrehmApprox.EuclideanPreparation

/-!+# Euclidean source preparation with an arbitrary metric target

The source charts and their nearest-face projections are Euclidean, while the
target may be any metric space. In particular this separates the Euclidean
chain-metric preparation inside one projective chart from the original curved
target metric. Empty faces use an explicitly supplied target point.
-/

@[expose] public section

noncomputable section

open scoped Topology
open Filter

namespace BrehmApprox

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {P : Type v} [MetricSpace P] {Y : Type w}
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good} {N : ℕ}

namespace FoldedGeometry

variable (G : FoldedGeometry (P := P) M N) (T : SimplicialFaceData G.toPolyhedralFaceData)

def euclideanTargetReference (o : Y) (i : Fin N) (f : P → Y) : E → Y := by
  classical
  exact if hi : (G.core i).Nonempty then
    (G.constantSource 0).referenceFromCore i (G.euclideanCoreProjection T i hi) f
  else fun _ => o

omit [FiniteDimensional ℝ E] in
lemma euclideanTargetReference_on_cell (o : Y) (i : Fin N) (f : P → Y)
    {x : P} (hx : x ∈ G.cell i) : G.euclideanTargetReference T o i f (G.fold x) = f x := by
  classical
  have hi : (G.core i).Nonempty := ⟨G.fold x, G.fold_mem_core hx⟩
  simp only [euclideanTargetReference, dite_eq_left hi]
  exact (G.constantSource 0).referenceFromCore_on_cell i (G.euclideanCoreProjection T i hi)
    (fun z hz => G.euclideanCoreProjection_fix T i hi hz) f hx

/-- Whole-face agreement uses only equality in the target; no target vector
space structure or target projection theorem is needed. -/
theorem euclideanTargetReference_agreement (o : Y) (f : P → Y)
    (hflat : ∀ e (he : (G.core e).Nonempty) p, p ∈ G.cell e →
      PositiveConvexCombination (T.vertices e) (G.fold p) →
      f =ᶠ[𝓝 p] (fun x => f (G.euclideanRetraction T e he x)))
    {i j : Fin N} (hij : G.faceLE i j) :
    ∃ U : Set E, IsOpen U ∧ G.core i ⊆ U ∧
      ∀ z ∈ U, G.euclideanTargetReference T o i f z = G.euclideanTargetReference T o j f z := by
  classical
  by_cases hi : (G.core i).Nonempty
  · have hj : (G.core j).Nonempty := hi.mono (G.core_mono i j hij)
    let S := G.constantSource 0
    let ri := G.euclideanCoreProjection T i hi
    let rj := G.euclideanCoreProjection T j hj
    obtain ⟨U, hU, hcoreU, hagree⟩ := S.whole_face_reference_agreement i j hij ri rj f
      (G.euclideanCoreProjection_short T i hi).continuous
      (G.euclideanCoreProjection_short T j hj).continuous
      (fun z hz => G.euclideanCoreProjection_fix T i hi hz)
      (fun z hz => G.euclideanCoreProjection_fix T j hj hz) (by
        intro p hp
        obtain ⟨k, hki, hpk, hpos, _, _⟩ := G.relativeInterior_face_cover T i hp
        have hk : (G.core k).Nonempty := ⟨G.fold p, G.fold_mem_core hpk⟩
        refine ⟨k, G.euclideanCoreProjection T k hk, hflat k hk p hpk hpos, ?_, ?_⟩
        · exact G.euclideanCoreProjection_eventually_comp T hki hk hi hpos
        · exact G.euclideanCoreProjection_eventually_comp T (G.le_trans _ _ _ hki hij) hk hj hpos)
    refine ⟨U, hU, hcoreU, ?_⟩
    intro z hz
    simpa only [euclideanTargetReference, dite_eq_left hi, dite_eq_left hj] using hagree z hz
  · refine ⟨∅, isOpen_empty, ?_, fun _ hx => hx.elim⟩
    exact (Set.not_nonempty_iff_eq_empty.mp hi).le

section MetricTarget

variable [MetricSpace Y]

omit [FiniteDimensional ℝ E] in
theorem euclideanTargetReference_lipschitz (o : Y) (i : Fin N) (f : P → Y) {C : NNReal}
    (hf : LipschitzWith C f) : LipschitzWith C (G.euclideanTargetReference T o i f) := by
  classical
  by_cases hi : (G.core i).Nonempty
  · simp only [euclideanTargetReference, dite_eq_left hi]
    simpa only [mul_one] using (G.constantSource 0).referenceFromCore_lipschitz i
      (G.euclideanCoreProjection T i hi) f hf (G.euclideanCoreProjection_short T i hi)
  · simp only [euclideanTargetReference, dite_eq_right hi]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_self]
    positivity

/-- Explicit compatible ambient references with an arbitrary metric target. -/
theorem exists_euclidean_target_references (o : Y) (f : P → Y) {C : NNReal}
    (hf : LipschitzWith C f)
    (hflat : ∀ e (he : (G.core e).Nonempty) p, p ∈ G.cell e →
      PositiveConvexCombination (T.vertices e) (G.fold p) →
      f =ᶠ[𝓝 p] (fun x => f (G.euclideanRetraction T e he x))) :
    ∃ u : Fin N → E → Y,
      (∀ i, LipschitzWith C (u i)) ∧
      (∀ i, ∀ x ∈ G.cell i, u i (G.fold x) = f x) ∧
      ∀ i j, G.faceLE i j → ∃ U : Set E, IsOpen U ∧ G.core i ⊆ U ∧
        ∀ z ∈ U, u i z = u j z :=
  ⟨fun i => G.euclideanTargetReference T o i f,
    fun i => G.euclideanTargetReference_lipschitz T o i f hf,
    fun i _ hx => G.euclideanTargetReference_on_cell T o i f hx,
    fun _ _ hij => G.euclideanTargetReference_agreement T o f hflat hij⟩

include T in
/-- Complete preparation and reference construction for a strictly short map
to any metric target. The only geometric source input is the actual folded
simplicial geometry. -/
theorem prepare_euclidean_target_references (o : Y) (f : P → Y) {C : NNReal}
    (hf : LipschitzWith C f) (hC : (C : ℝ) < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, (K : ℝ) < 1 ∧ ∃ f₀ : P → Y, ∃ u : Fin N → E → Y,
      LipschitzWith K f₀ ∧ (∀ x, dist (f₀ x) (f x) < ε) ∧
      (∀ i, LipschitzWith K (u i)) ∧
      (∀ i, ∀ x ∈ G.cell i, u i (G.fold x) = f₀ x) ∧
      ∀ i j, G.faceLE i j → ∃ U : Set E, IsOpen U ∧ G.core i ⊆ U ∧
        ∀ z ∈ U, u i z = u j z := by
  obtain ⟨K, hK, f₀, hf₀, hnear, hflat⟩ :=
    G.exists_strict_flat_approximation T f hf hC hε
  obtain ⟨u, hu, hexact, hagree⟩ := G.exists_euclidean_target_references T o f₀ hf₀ hflat
  exact ⟨K, hK, f₀, u, hf₀, hnear, hu, hexact, hagree⟩

include T in
/-- Keeping the quantitative spare factor explicit is useful when a curved
chart has a prescribed additional Lipschitz constant. -/
theorem prepare_euclidean_target_references_with_factor (o : Y) (f : P → Y)
    {C : NNReal} (hf : LipschitzWith C f) {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    ∃ f₀ : P → Y, ∃ u : Fin N → E → Y,
      (∀ x y, dist (f₀ x) (f₀ y) ≤ ((C : ℝ) * (1 + β)) * dist x y) ∧
      (∀ x, dist (f₀ x) (f x) < ε) ∧
      (∀ i x y, dist (u i x) (u i y) ≤ ((C : ℝ) * (1 + β)) * dist x y) ∧
      (∀ i, ∀ x ∈ G.cell i, u i (G.fold x) = f₀ x) ∧
      ∀ i j, G.faceLE i j → ∃ U : Set E, IsOpen U ∧ G.core i ⊆ U ∧
        ∀ z ∈ U, u i z = u j z := by
  let η : ℝ := ε / ((C : ℝ) + 1)
  have hden : 0 < (C : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  have hηeq : η * ((C : ℝ) + 1) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨H, hH, _, hnear, hflat⟩ := G.exists_euclidean_flattening T hβ hη
  let B : NNReal := ⟨1 + β, by positivity⟩
  have hLipH : LipschitzWith B H := LipschitzWith.of_dist_le_mul hH
  let f₀ := fun x => f (H x)
  have hf₀ : LipschitzWith (C * B) f₀ := hf.comp hLipH
  have hflat₀ : ∀ e (he : (G.core e).Nonempty) p, p ∈ G.cell e →
      PositiveConvexCombination (T.vertices e) (G.fold p) →
      f₀ =ᶠ[𝓝 p] (fun x => f₀ (G.euclideanRetraction T e he x)) := by
    intro e he p hp hpos
    exact (hflat e he p hp hpos).fun_comp f
  obtain ⟨u, hu, hexact, hagree⟩ := G.exists_euclidean_target_references T o f₀ hf₀ hflat₀
  refine ⟨f₀, u, ?_, ?_, ?_, hexact, hagree⟩
  · intro x y
    exact hf₀.dist_le_mul x y
  · intro x
    have h₁ := hf.dist_le_mul (H x) x
    have h₂ := mul_le_mul_of_nonneg_left (hnear x).le C.coe_nonneg
    change dist (f (H x)) (f x) < ε
    nlinarith
  · intro i x y
    exact (hu i).dist_le_mul x y

end MetricTarget
end FoldedGeometry
end BrehmApprox
