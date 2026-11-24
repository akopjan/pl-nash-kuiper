module

public import BrehmApprox.FoldedGeometry

/-!
# Retaining the ambient maps in the final gluing

The approximation construction supplies one ambient model map on each
original source cell. Retaining these maps makes their finite rigid-motion
branches available when constructing a compatible source triangulation.
-/

@[expose] public section

namespace BrehmApprox.FoldedGeometry

universe u v
variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
    {Good : (X → X) → Prop} {M : PolytopeModel X Good} {N : ℕ}
    (G : FoldedGeometry (P := P) M N)

def RealizedByModelMaps (g : P → X) : Prop :=
  ∃ H : Fin N → X → X, (∀ i, Good (H i)) ∧
    ∀ i, ∀ x ∈ G.cell i, g x = H i (G.fold x)

theorem RealizedByModelMaps.piecewise {g : P → X}
    (h : G.RealizedByModelMaps g) (o : X) : PolyhedralPiecewiseIsometry M G.fold g := by
  obtain ⟨H, hH, hg⟩ := h
  exact (G.constantSource o).piecewise_of_glued hH hg

theorem approximate_with_maps {L : ℝ} (R : G.toPolyhedralFaceData.LocalReferences L)
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : P → X)
    (href : ∀ i, ∀ x ∈ G.cell i, R.reference i (G.fold x) = f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → X, LipschitzWith 1 g ∧ G.RealizedByModelMaps g ∧
      ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨H, hH, hcompat⟩ := R.toAtlas.approximate hB hL0 hL1 hε
  let S := G.withReferences R
  obtain ⟨g, hg⟩ := S.glue hcompat
  refine ⟨g, ?_, ⟨H, fun i => (hH i).2.1, hg⟩, ?_⟩
  · apply lipschitzWith_of_cellwise G.intrinsic
    intro i x hx y hy
    simp only [NNReal.coe_one, one_mul]
    rw [hg i x hx, hg i y hy]
    exact ((hH i).1 (G.fold x) (G.fold y)).trans_eq (G.isometry_cell i x hx y hy)
  · intro x
    obtain ⟨i, hxi⟩ := G.cover x
    rw [hg i x hxi, ← href i x hxi]
    exact (hH i).2.2 _ (S.fold_mem_core hxi)

end BrehmApprox.FoldedGeometry
