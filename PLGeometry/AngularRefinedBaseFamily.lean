module

public import PLGeometry.AngularTieCoordinateGeometry
public import PLGeometry.SphericalRealizationRefinement
public import PLGeometry.BarycentricProjectiveAtlas

/-!
# Every angular refinement gives a genuine refined Voronoi base family

The construction transports actual angular vertices through the positive
reweighting homeomorphism. Projective geometry proves independence and
the exact convex hulls; extreme-face restriction provides coverage for
every incident old Voronoi tie piece.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P} [LinearOrder (T.Vertex → ℝ)]
    (A : ProjectiveVoronoiAtlas T (T.Vertex → ℝ)) (S : Finset P)
    (hA : A.coord = T.barycentricCoords)

include hA

local instance angularRefinedBaseDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance angularRefinedBaseCoordinateEq : DecidableEq (T.Vertex → ℝ) := Classical.decEq _

def angularRefinementBaseFamily {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    {m : ℕ} (D : Barycentric.SphericalData (A.toVoronoiAtlas.tieComplex S) m)
    (U : FiniteChartedComplex .spherical m (A.toVoronoiAtlas.tieComplex S).Space)
    (hU : U.Refines D.toChartedComplex) :
    VoronoiBaseFamily A S
      (TransportedTieIndex A S U (A.angularTiePoint S hnet hp hsmall)) := by
  let B := A.toVoronoiAtlas
  let f := A.angularTiePoint S hnet hp hsmall
  have hgeometry : ∀ V ∈ U.simplices,
      AffineIndependent ℝ ((↑) : V.image (A.coord ∘ f) → (T.Vertex → ℝ)) ∧
      (A.coord ∘ f) '' U.cell V = convexHull ℝ (V.image (A.coord ∘ f) : Set _) := by
    intro V hV
    obtain ⟨W, hW, hc, _⟩ := hU.cell V hV
    have hσ := D.labels_mem hW
    have hcell : ∀ x ∈ U.cell V, x.val ∈ Barycentric.weightsOn ((B.tieComplex S).labels W) :=
      fun x hx => hc hx
    have hv (v) (hv : v ∈ V) := hcell v (U.vertices_mem V hV hv)
    have hcoords := D.refinement_coordinate_geometry U hU hV
    have hcoords' : (Subtype.val : (B.tieComplex S).Space → _) '' U.cell V =
        convexHull ℝ (V.image Subtype.val : Set _) := by
      simpa only [Finset.coe_image] using hcoords.2
    exact ⟨A.angularTiePoint_coord_independent S hA hnet hp hsmall hσ V hv hcoords.1,
      A.angularTiePoint_coord_image_cell S hA U hnet hp hsmall hσ hV hcell hcoords'⟩
  apply transportedVoronoiBaseFamily A S U f hnet hp
    (A.angularTiePoint_injective S hnet hp hsmall) hgeometry
  · intro V hV
    obtain ⟨W, hW, hc, _⟩ := hU.cell V hV
    have hσ := D.labels_mem hW
    let σ := (B.tieComplex S).labels W
    let i := B.tieFaceIndex S σ hσ
    refine ⟨i, ?_⟩
    intro z hz
    rw [← (hgeometry V hV).2] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxσ : x.val ∈ Barycentric.weightsOn σ := hc hx
    have hfx := (A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ x).mpr hxσ
    exact Pulling.family_face_subset_cell (B.tiePiece S) (B.tiePiece_polytope S)
      (B.tieFaceIndex_spec S σ hσ) hfx
  · intro i z hz
    obtain ⟨y, he, _, _⟩ := B.tiePiece_source S i hz
    have hy : y ∈ A.tieLocus S := by
      rw [A.tieLocus_eq S]
      exact Set.mem_iUnion.mpr ⟨i, he.symm ▸ hz⟩
    let x := (A.angularTieHomeomorph S hnet hp hsmall).symm ⟨y, hy⟩
    have hfx : f x = y := congrArg Subtype.val
      ((A.angularTieHomeomorph S hnet hp hsmall).apply_symm_apply ⟨y, hy⟩)
    exact ⟨x, (congrArg A.coord hfx).trans he⟩

end ArchivePLGeometry.ProjectiveVoronoiAtlas
