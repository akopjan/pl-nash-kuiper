module

public import PLGeometry.VoronoiConeRefinement
public import PLGeometry.VertexFolding

/-! # A small source folding from its finite coned vertex data -/

@[expose] public section
noncomputable section

set_option maxHeartbeats 1000000

open Set BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u w
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P) {S : Finset P} {J : Type w} [Finite J]

local instance voronoiVertexFoldingDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance voronoiVertexFoldingCoordinatesEq : DecidableEq (T.Vertex → ℝ) := Classical.decEq _

theorem voronoi_vertex_isometry
    (B : VoronoiBaseFamily T.barycentricProjectiveAtlas S J)
    {η : ℝ} (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S)
    (v : P → Model κ n)
    (hv : ∀ j, ∀ x ∈ B.coneVertices j, ∀ y ∈ B.coneVertices j,
      dist (v x) (v y) = dist (T.chart (B.oldSimplex j) x) (T.chart (B.oldSimplex j) y)) :
    (T.voronoiConeRefinement B hnet hp).IsVertexIsometry v := by
  let F := T.voronoiConeFamily B hnet hp
  intro σ hσ x hx y hy
  obtain ⟨i, hi⟩ := hσ
  have hσ' : σ ∈ F.simplices := ⟨i, hi⟩
  have hxold := (F.oldFace_spec hσ').2 hx
  have hyold := (F.oldFace_spec hσ').2 hy
  rcases i with j | a
  · have hxj := B.cone_vertices_mem_old j (hi hx)
    have hyj := B.cone_vertices_mem_old j (hi hy)
    exact (hv j x (hi hx) y (hi hy)).trans
      (T.metric_coherence (B.oldSimplex j) (B.oldSimplex_mem j) (F.oldFace σ)
        (F.oldFace_spec hσ').1 x ⟨hxj, hxold⟩ y ⟨hyj, hyold⟩)
  · have hxa : x = a.val := Finset.mem_singleton.mp (hi hx)
    have hya : y = a.val := Finset.mem_singleton.mp (hi hy)
    rw [hxa, hya, dist_self, dist_self]

/-- The only metric input is a consistent isometric assignment on each
finite cone vertex set. The genuine refinement, continuity, and small-image
bound are consequences of the proved Voronoi construction. -/
theorem small_folding_of_voronoi_vertex_data
    (B : VoronoiBaseFamily T.barycentricProjectiveAtlas S J)
    {η : ℝ} (hη : 0 < η) (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S)
    (o : Model κ n) (v : P → Model κ n) (hsite : ∀ a ∈ S, v a = o)
    (hv : ∀ j, ∀ x ∈ B.coneVertices j, ∀ y ∈ B.coneVertices j,
      dist (v x) (v y) = dist (T.chart (B.oldSimplex j) x) (T.chart (B.oldSimplex j) y)) :
    ∃ U : FiniteChartedComplex κ n P, U.Refines T ∧
      ∃ q : P → Model κ n, Continuous q ∧
        (∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
          dist (q x) (q y) = dist (U.chart σ x) (U.chart σ y)) ∧
        ∀ x, dist (q x) o < η := by
  let F := T.voronoiConeFamily B hnet hp
  let U := T.voronoiConeRefinement B hnet hp
  obtain ⟨q, hq, hiso, hvertex⟩ := U.exists_folding_of_vertex_isometry v
    (T.voronoi_vertex_isometry B hnet hp v hv)
  refine ⟨U, T.voronoiConeRefinement_refines B hnet hp, q, hq, hiso, ?_⟩
  intro x
  rcases T.voronoi_cone_cover B hnet hp x with hxS | ⟨j, hxj⟩
  · have hsing : ({x} : Finset P) ∈ U.simplices :=
      ⟨.inr ⟨x, hxS⟩, Finset.Subset.refl _⟩
    rw [hvertex {x} hsing x (Finset.mem_singleton_self x), hsite x hxS, dist_self]
    exact hη
  · let σ := B.coneVertices j
    have hσ : σ ∈ F.simplices := ⟨.inl j, Finset.Subset.refl _⟩
    have hxσ : x ∈ U.cell σ := hxj
    have haσ : B.apex j ∈ U.cell σ := F.vertices_mem σ (Finset.mem_insert_self _ _)
    have hqa : q (B.apex j) = o :=
      (hvertex σ hσ (B.apex j) (Finset.mem_insert_self _ _)).trans (hsite _ (B.apex_mem_sites j))
    have hxpiece : x ∈ T.voronoiPiece S (B.oldSimplex j) (B.apex j) := by
      obtain ⟨y, hy, he⟩ := B.cone_hull_subset_piece j hxj
      exact T.barycentricCoords_injective he ▸ hy
    have hxold := F.cell_subset_old hσ hxσ
    have haold := F.cell_subset_old hσ haσ
    rw [← hqa, hiso σ hσ x hxσ (B.apex j) haσ]
    change dist (T.chart (F.oldFace σ) x) (T.chart (F.oldFace σ) (B.apex j)) < η
    rw [T.metric_coherence (F.oldFace σ) (F.oldFace_spec hσ).1 (B.oldSimplex j)
      (B.oldSimplex_mem j) x ⟨hxold, hxpiece.1⟩ (B.apex j) ⟨haold, B.apex_mem_old j⟩]
    exact T.voronoiPiece_radius_lt hnet (B.oldSimplex_mem j) hxpiece

end ArchivePLGeometry.FiniteChartedComplex
