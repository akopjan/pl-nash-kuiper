module

public import PLGeometry.FoldedEuclideanPL

/-! # Affine coordinate covers of folded sources -/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox.FoldedGeometry

universe u v w
variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
    {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {GoodX : (X → X) → Prop} {GoodE : (E → E) → Prop}
    {MX : PolytopeModel X GoodX} {ME : PolytopeModel E GoodE} {N : ℕ}
    (G : FoldedGeometry (P := P) MX N)

def coordinatePolytopeCover
    (D : PolyhedralFaceData ME N) (T : SimplicialFaceData D) (Φ : X → E)
    (hface : ∀ i j, D.faceLE i j ↔ G.faceLE i j)
    (hcore : ∀ i, D.core i = Φ '' G.core i)
    (hinj : ∀ i, Set.InjOn Φ (G.core i)) :
    FoldedPolytopeCover (fun x => Φ (G.fold x)) (Fin N) := by
  have himage (i : Fin N) : (fun x => Φ (G.fold x)) '' G.cell i = D.core i := by
    rw [← Set.image_image, G.image_cell, ← hcore]
  refine
    { cell := G.cell
      cover := G.cover
      injective_cell := ?_
      polytope_image := ?_
      convex_inter := ?_
      face_inter := ?_ }
  · intro i x hx y hy heq
    have hx' : G.fold x ∈ G.core i := by
      rw [← G.image_cell i]
      exact Set.mem_image_of_mem G.fold hx
    have hy' : G.fold y ∈ G.core i := by
      rw [← G.image_cell i]
      exact Set.mem_image_of_mem G.fold hy
    have hxy := hinj i hx' hy' heq
    apply dist_eq_zero.mp
    rw [← G.isometry_cell i x hx y hy, hxy, dist_self]
  · intro i
    rw [himage, T.core_eq]
    exact ⟨T.vertices i, rfl⟩
  · intro i j
    rw [G.cell_inter_eq_meet, himage, T.core_eq]
    exact convex_convexHull ℝ _
  · intro i j
    rw [G.cell_inter_eq_meet, himage, himage, T.core_eq, T.core_eq]
    exact isExtreme_convexHull_vertex_subset (T.independent i)
      (T.vertices_mono _ _ ((hface _ _).mpr (G.meet_le_left i j)))

end BrehmApprox.FoldedGeometry
