module

public import BrehmApprox.FoldedGeometry
public import BrehmApprox.Relative

/-!
# Arbitrarily small genuine piecewise foldings from finite Brehm

Once an actual initial folded source is given, finite Brehm makes its image
arbitrarily small: approximate a constant map on the compact image and
postcompose. The resulting source map is short and has actual finite
isometric polyhedral pieces, all proved here.

This statement does not assert a new compatible simplex face family for the
postcomposition. Constructing that common finite refinement remains separate
from this small-image construction and from initial-folding existence.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

universe u v

variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good} {N : ℕ}

namespace FoldedGeometry

variable (G : FoldedGeometry (P := P) M N)

/-- A genuine initial folding can be postcomposed with a global Brehm map
whose entire source image lies in any prescribed model ball. -/
theorem exists_small_postcomposition (hB : FiniteExtension Good) (o : X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : X → X, Short H ∧ Good H ∧ LipschitzWith 1 (H ∘ G.fold) ∧
      PolyhedralPiecewiseIsometry M G.fold (H ∘ G.fold) ∧
      ∀ x, dist (H (G.fold x)) o < ε := by
  let : CompactSpace P := G.compactSpace o
  let S := G.constantSource o
  have hq : LipschitzWith 1 G.fold := S.fold_lipschitz G.intrinsic
  have hcompact : IsCompact (Set.range G.fold) := isCompact_range hq.continuous
  have hconstant : ShortOn (fun _ : X => o) (Set.range G.fold ∪ (∅ : Finset X)) := by
    intro x _ y _
    simpa only [dist_self] using (dist_nonneg : 0 ≤ dist x y)
  obtain ⟨H, hH, hGood, _, hnear⟩ := compact_model_approximation hB hcompact ∅ hconstant hε
  have hHLip : LipschitzWith 1 H := LipschitzWith.of_dist_le_mul (by
    intro x y
    simpa only [NNReal.coe_one, one_mul] using hH x y)
  have hcomp : LipschitzWith 1 (H ∘ G.fold) := by
    simpa only [one_mul] using hHLip.comp hq
  have hPL : PolyhedralPiecewiseIsometry M G.fold (H ∘ G.fold) :=
    S.piecewise_of_glued (H := fun _ => H) (fun _ => hGood) (fun _ _ _ => rfl)
  exact ⟨H, hH, hGood, hcomp, hPL, fun x => hnear (G.fold x) (Set.mem_range_self x)⟩

/-- The small folding itself, with no unproved new triangulation packaged
into its conclusion. -/
theorem exists_small_piecewise_folding (hB : FiniteExtension Good) (o : X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : P → X, LipschitzWith 1 q ∧ PolyhedralPiecewiseIsometry M G.fold q ∧
      ∀ x, dist (q x) o < ε := by
  obtain ⟨H, _, _, hLip, hPL, hnear⟩ := G.exists_small_postcomposition hB o hε
  exact ⟨H ∘ G.fold, hLip, hPL, hnear⟩

end FoldedGeometry
end BrehmApprox
