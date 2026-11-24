module

public import PLGeometry.VoronoiConeFolding

/-!
# The dimension-reducing folding step

A protected finite net and a finite folding of its spherical angular
complex produce an actual finite geodesic folding of the source. The
image radius is bounded by the mesh of the net.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ (n + 1) P) [LinearOrder (T.Vertex → ℝ)]

local instance angularFoldingStepDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance angularFoldingStepCoordinateEq : DecidableEq (T.Vertex → ℝ) := Classical.decEq _

theorem small_folding_of_angular_folding (S : Finset P) {η : ℝ}
    (hη0 : 0 < η) (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S)
    (hη : η ≤ Real.pi / 2) (o : Model κ (n + 1))
    (hfold : (T.barycentricProjectiveAtlas.angularData S hnet hp hη).toChartedComplex.HasFiniteFolding) :
    ∃ R : FiniteChartedComplex κ (n + 1) P, R.Refines T ∧
      ∃ f : P → Model κ (n + 1), Continuous f ∧
        (∀ σ ∈ R.simplices, ∀ x ∈ R.cell σ, ∀ y ∈ R.cell σ,
          dist (f x) (f y) = dist (R.chart σ x) (R.chart σ y)) ∧
        ∀ x, dist (f x) o < η := by
  let A := T.barycentricProjectiveAtlas
  let D := A.angularData S hnet hp hη
  have hsmall : κ = .spherical → η < Real.pi := by
    intro _
    linarith [Real.pi_pos]
  obtain ⟨U, hU, q, _, hq⟩ := hfold
  let F := A.angularTiePoint S hnet hp hsmall
  let B := A.angularRefinementBaseFamily S rfl hnet hp hsmall D U hU
  let v := A.coneVertexMap S hnet hp hsmall q o
  have hsite : ∀ a ∈ S, v a = o := fun a ha =>
    A.coneVertexMap_site S hnet hp hsmall q o ha
  have hradius : ∀ j, ∀ x ∈ B.vertices j, dist (v x) o = T.nearestRadius hnet x := by
    intro j x hx
    change x ∈ j.val.2.val.image F at hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact A.coneVertexMap_angular_dist_pole S hnet hp hsmall q o w
  have hbase : ∀ j, ∀ x ∈ B.vertices j, ∀ y ∈ B.vertices j,
      dist (v x) (v y) = dist (T.chart (B.oldSimplex j) x) (T.chart (B.oldSimplex j) y) := by
    intro j x hx y hy
    have hxold := (B.vertex_mem_piece j hx).1
    have hyold := (B.vertex_mem_piece j hy).1
    change x ∈ j.val.2.val.image F at hx
    change y ∈ j.val.2.val.image F at hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact A.coneVertexMap_angular_cell_metric S hnet hp hη hsmall U hU q hq o
      j.val.2.property (U.vertices_mem _ j.val.2.property hw)
      (U.vertices_mem _ j.val.2.property hz) (B.oldSimplex_mem j) hxold hyold
  exact T.small_folding_of_voronoi_vertex_data B hη0 hnet hp o v hsite
    (fun j x hx y hy => B.cone_vertex_metric hnet hp o v hsite hradius hbase j hx hy)

omit [LinearOrder (T.Vertex → ℝ)] in
/-- Protected meshes of arbitrary size and the spherical folding theorem
in one lower dimension imply arbitrarily small finite foldings. -/
theorem hasSmallFiniteFolding_of_protected_nets
    (hnets : ∀ δ : ℝ, 0 < δ → ∃ S : Finset P,
      T.IsCellwiseNet S δ ∧ T.IsCellwiseProtected S)
    (hangular : ∀ {Q : Type u} [TopologicalSpace Q] [T2Space Q]
      (D : FiniteChartedComplex .spherical n Q), D.HasFiniteFolding) :
    T.HasSmallFiniteFolding := by
  let : LinearOrder (T.Vertex → ℝ) :=
    IsWellOrder.linearOrder (WellOrderingRel : (T.Vertex → ℝ) → (T.Vertex → ℝ) → Prop)
  intro o η hη
  let δ := min η (Real.pi / 2)
  have hδ0 : 0 < δ := lt_min hη (by positivity)
  obtain ⟨S, hnet, hp⟩ := hnets δ hδ0
  have hδ : δ ≤ Real.pi / 2 := min_le_right _ _
  obtain ⟨R, hR, q, hq, hiso, hsmall⟩ := T.small_folding_of_angular_folding
    S hδ0 hnet hp hδ o (hangular _)
  exact ⟨R, hR, q, hq, hiso, fun x => (hsmall x).trans_le (min_le_left _ _)⟩

end ArchivePLGeometry.FiniteChartedComplex
