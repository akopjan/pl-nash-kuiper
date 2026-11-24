module

public import PLGeometry.VoronoiVertexFolding
public import PLGeometry.VoronoiConeVertexMap
public import PLGeometry.FiniteFoldingBase

/-! # Finite small-range folding of a protected Voronoi cone refinement -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry

universe u v w
local instance voronoiConeFoldingDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

namespace VoronoiBaseFamily

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ (n + 1) P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : ProjectiveVoronoiAtlas T E} {S : Finset P} {J : Type w}
    (B : VoronoiBaseFamily A S J)

theorem cone_vertex_metric {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (o : Model κ (n + 1)) (v : P → Model κ (n + 1))
    (hsite : ∀ a ∈ S, v a = o)
    (hradius : ∀ j, ∀ x ∈ B.vertices j, dist (v x) o = T.nearestRadius hnet x)
    (hbase : ∀ j, ∀ x ∈ B.vertices j, ∀ y ∈ B.vertices j,
      dist (v x) (v y) = dist (T.chart (B.oldSimplex j) x) (T.chart (B.oldSimplex j) y))
    (j : J) {x y : P} (hx : x ∈ B.coneVertices j) (hy : y ∈ B.coneVertices j) :
    dist (v x) (v y) = dist (T.chart (B.oldSimplex j) x) (T.chart (B.oldSimplex j) y) := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rcases Finset.mem_insert.mp hy with rfl | hy
    · simp only [dist_self]
    · rw [hsite _ (B.apex_mem_sites j), dist_comm, hradius j y hy,
        T.nearestRadius_eq hnet hp (B.oldSimplex_mem j) (B.vertex_mem_piece j hy), dist_comm]
  · rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [hsite _ (B.apex_mem_sites j), hradius j x hx,
        T.nearestRadius_eq hnet hp (B.oldSimplex_mem j) (B.vertex_mem_piece j hx)]
    · exact hbase j x hx y hy

end VoronoiBaseFamily

end ArchivePLGeometry
