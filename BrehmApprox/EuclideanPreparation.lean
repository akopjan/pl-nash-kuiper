module

public import BrehmApprox.CanonicalBadSets
public import BrehmApprox.SourceFiniteFlattening
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Algebra.BigOperators.Ring.List

/-!+# Euclidean preparation of an actual folded simplicial source

Starting only from the genuine folded source and its actual independent
simplex vertex data, this module constructs all closed bad sets and all source
face collapses, chooses one small parameter, and composes the maps. The result
is arbitrarily close to the identity, has Lipschitz constant arbitrarily close
to one, preserves every cell, and is locally constant on normal fibers of every
minimal face. An initial folding remains an explicit geometric input.
-/

@[expose] public section

noncomputable section

open scoped Topology
open Filter

namespace BrehmApprox

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {P : Type v} [MetricSpace P]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good} {N : ℕ}

namespace FoldedGeometry

variable (G : FoldedGeometry (P := P) M N) (T : SimplicialFaceData G.toPolyhedralFaceData)

/-- Complete metric and local geometric preparation for a given folded
simplicial source; no reference maps or approximation maps are assumed. -/
theorem exists_euclidean_flattening {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    ∃ H : P → P,
      (∀ x y, dist (H x) (H y) ≤ (1 + β) * dist x y) ∧
      (∀ i, Set.MapsTo H (G.cell i) (G.cell i)) ∧
      (∀ x, dist (H x) x < ε) ∧
      ∀ e (hne : (G.core e).Nonempty), ∀ p ∈ G.cell e,
        PositiveConvexCombination (T.vertices e) (G.fold p) →
        H =ᶠ[𝓝 p] (fun x => H ((G.constantSource (0 : E)).retractFromCore e
          ((G.constantSource (0 : E)).convexCoreProjection e hne (T.convex_core e)) x)) := by
  classical
  let S := G.constantSource (0 : E)
  let D := G.toPolyhedralFaceData
  let F : Fin N → AffineSubspace ℝ E := fun i => canonicalAffineFace (G.core i)
  let Bad : Fin N → Set E := D.canonicalBad
  let c : ℝ := 1 / 4
  have hc : 0 < c := by norm_num [c]
  have hc1 : c < 1 := by norm_num [c]
  let steps := descendingFaces N
  obtain ⟨α, hα0, hα1, hprod, hsum⟩ :=
    exists_small_common_flattening_parameter steps (fun _ => c) (fun _ => c) hβ hε
  have hEach : ∀ i : Fin N, ∃ Q : P → P,
      S.FaceMapRealization i (cutoffAffineFlatten (F i) (Bad i) 1 c α) Q ∧
      (∀ x y, dist (Q x) (Q y) ≤ ((1 + α * c) / (1 - α)) * dist x y) ∧
      ∀ x, dist (Q x) x ≤ α * c := by
    intro i
    obtain ⟨Q, hQ, hLip, hdisp⟩ := S.exists_cutoff_face_realization G.intrinsic i (F i)
      (Bad i) (D.canonicalBad_complement i) T.convex_core
      (fun j k hj hk hjk => D.core_subset_canonicalBad hj hk hjk)
      (by norm_num : (0 : ℝ) ≤ 1) hc.le hc1.le hα0.le hα1
    refine ⟨Q, hQ, hLip, ?_⟩
    simpa only [mul_one] using hdisp
  choose Q hQ hLip hdisp using hEach
  have hC0 : 0 ≤ (1 + α * c) / (1 - α) := by positivity
  let C : NNReal := ⟨(1 + α * c) / (1 - α), hC0⟩
  have hLipC (i : Fin N) : LipschitzWith C (Q i) :=
    LipschitzWith.of_dist_le_mul (hLip i)
  let H := composeSteps Q steps
  have hH := composeSteps_lipschitz Q steps (fun _ => C) (fun i _ => hLipC i)
  have hprodC : (((steps.map (fun _ => C)).prod : NNReal) : ℝ) < 1 + β := by
    rw [NNReal.coe_list_prod, List.map_map]
    change (steps.map (fun _ => (1 + α * c) / (1 - α))).prod < 1 + β
    exact hprod
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact (hH.dist_le_mul x y).trans (mul_le_mul_of_nonneg_right hprodC.le dist_nonneg)
  · intro i
    exact composeSteps_mapsTo Q steps (fun j _ => (hQ j).preserves i)
  · intro x
    have hd := composeSteps_displacement Q steps (fun _ => α * c) (fun i _ => hdisp i) x
    rw [List.sum_map_mul_left] at hd
    exact hd.trans_lt hsum
  · intro e hne p hp hpos
    apply S.descending_source_cutoffs_flat_at G.intrinsic e F Bad (fun _ => 1) Q hQ
      (fun i => (hLipC i).continuous)
      (fun i => subset_canonicalAffineFace (G.core i))
      (fun i => D.canonicalBad_complement i)
      (fun k i j hki hji hkj => D.core_subset_canonicalBad hki hji hkj)
      (fun _ => by norm_num) (by norm_num) hc hc1 hα0 hα1 hne (T.convex_core e)
      (D.canonicalBad_closed e) hp (T.positive_point_not_canonicalBad hpos)
    intro i hpi
    exact G.faceLE_of_positive_source_point T hp hpi hpos

/-- A strictly short source map can be prepared without losing strictness.
The explicit spare factor uses `(1-κ)/2`, so the zero-Lipschitz case requires
no division by `κ`. -/
theorem exists_strict_flat_approximation {Y : Type w} [MetricSpace Y]
    (f : P → Y) {κ : NNReal} (hf : LipschitzWith κ f) (hκ : (κ : ℝ) < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, (K : ℝ) < 1 ∧ ∃ f₀ : P → Y, LipschitzWith K f₀ ∧
      (∀ x, dist (f₀ x) (f x) < ε) ∧
      ∀ e (hne : (G.core e).Nonempty), ∀ p ∈ G.cell e,
        PositiveConvexCombination (T.vertices e) (G.fold p) →
        f₀ =ᶠ[𝓝 p] (fun x => f₀ ((G.constantSource (0 : E)).retractFromCore e
          ((G.constantSource (0 : E)).convexCoreProjection e hne (T.convex_core e)) x)) := by
  let β : ℝ := (1 - κ) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  obtain ⟨H, hLipH, _, hnear, hflat⟩ := G.exists_euclidean_flattening T hβ hε
  let C : NNReal := ⟨1 + β, by positivity⟩
  have hC : LipschitzWith C H := LipschitzWith.of_dist_le_mul hLipH
  have hK : ((κ * C : NNReal) : ℝ) < 1 := by
    rw [NNReal.coe_mul]
    change (κ : ℝ) * (1 + β) < 1
    have hκ0 := κ.coe_nonneg
    have hsmall : (κ : ℝ) * β ≤ β := by nlinarith
    dsimp [β] at *
    nlinarith
  refine ⟨κ * C, hK, fun x => f (H x), hf.comp hC, ?_, ?_⟩
  · intro x
    exact ((hf.dist_le_mul (H x) x).trans
      (mul_le_of_le_one_left dist_nonneg hκ.le)).trans_lt (hnear x)
  · intro e hne p hp hpos
    exact (hflat e hne p hp hpos).fun_comp f

end FoldedGeometry
end BrehmApprox
