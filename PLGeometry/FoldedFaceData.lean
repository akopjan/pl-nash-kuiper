module

public import PLGeometry.CellRigidity
public import PLGeometry.FoldedTransport

/-!
# Genuine folded face data from metric foldings

The model-cell rigidity theorem derives all geometric face data from a
cellwise isometric map on a finite source triangulation.
-/

@[expose] public section
noncomputable section

open BrehmApprox

namespace ArchivePLGeometry.Triangulation

universe u
variable {n : ℕ} {P : Type u} [MetricSpace P]

local instance foldedFaceDataDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance foldedFaceDataEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance foldedFaceDataSDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance foldedFaceDataHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _

section Euclidean

variable (T : Triangulation .euclidean n P) (e : FaceEnumeration T.simplices)
    (q : P → Model .euclidean n)
    (hq : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist x y) (hT : Intrinsic T)

def euclideanFoldedGeometry : FoldedGeometry (P := P) (euclideanPolytopeModel n) e.count :=
  T.toFoldedGeometry (euclideanPolytopeModel n) e q hq
    (fun σ hσ => ⟨σ.image q, (T.folding_cell_geometry σ hσ q (hq σ hσ)).2⟩) hT

def euclideanFoldedFaceData : SimplicialFaceData
    (T.euclideanFoldedGeometry e q hq hT).toPolyhedralFaceData where
  vertices i := (e.face i).val.image q
  core_eq i := (T.folding_cell_geometry _ (e.face i).property q (hq _ (e.face i).property)).2
  independent i := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using
      (T.folding_cell_geometry _ (e.face i).property q (hq _ (e.face i).property)).1
  vertices_mono _ _ h := Finset.image_subset_image h
  all_subfaces i W hW := T.folded_vertices_all_subfaces e q i W hW
  face_of_vertices i j k hij hjk h := T.face_of_folded_vertices e q hq i j k hij hjk h

end Euclidean

section Spherical

variable (T : Triangulation .spherical n P) (e : FaceEnumeration T.simplices)
    (q : P → Model .spherical n)
    (hq : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist x y) (hT : Intrinsic T)

def sphericalFoldedGeometry : FoldedGeometry (P := P) (sphericalPolytopeModel n) e.count :=
  T.toFoldedGeometry (sphericalPolytopeModel n) e q hq
    (fun σ hσ => ⟨σ.image q,
      (T.folding_cell_geometry σ hσ q (hq σ hσ)).1.1,
      (T.folding_cell_geometry σ hσ q (hq σ hσ)).2⟩) hT

def sphericalFoldedFaceData : SphericalSimplicialFaceData
    (T.sphericalFoldedGeometry e q hq hT).toPolyhedralFaceData where
  vertices i := (e.face i).val.image q
  core_eq i := (T.folding_cell_geometry _ (e.face i).property q (hq _ (e.face i).property)).2
  independent i := by
    simpa only [Finset.coe_sort_coe] using
      (T.folding_cell_geometry _ (e.face i).property q (hq _ (e.face i).property)).1.2
  vertices_mono _ _ h := Finset.image_subset_image h
  all_subfaces i W hW := T.folded_vertices_all_subfaces e q i W hW
  face_of_vertices i j k hij hjk h := T.face_of_folded_vertices e q hq i j k hij hjk h

end Spherical

section Hyperbolic

variable (T : Triangulation .hyperbolic n P) (e : FaceEnumeration T.simplices)
    (q : P → Model .hyperbolic n)
    (hq : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist x y) (hT : Intrinsic T)

def hyperbolicFoldedGeometry : FoldedGeometry (P := P) (hyperbolicPolytopeModel n) e.count :=
  T.toFoldedGeometry (hyperbolicPolytopeModel n) e q hq
    (fun σ hσ => ⟨σ.image q, (T.folding_cell_geometry σ hσ q (hq σ hσ)).2⟩) hT

def hyperbolicFoldedFaceData : HyperbolicSimplicialFaceData
    (T.hyperbolicFoldedGeometry e q hq hT).toPolyhedralFaceData where
  vertices i := (e.face i).val.image q
  core_eq i := (T.folding_cell_geometry _ (e.face i).property q (hq _ (e.face i).property)).2
  independent i := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using
      (T.folding_cell_geometry _ (e.face i).property q (hq _ (e.face i).property)).1
  vertices_mono _ _ h := Finset.image_subset_image h
  all_subfaces i W hW := T.folded_vertices_all_subfaces e q i W hW
  face_of_vertices i j k hij hjk h := T.face_of_folded_vertices e q hq i j k hij hjk h

end Hyperbolic
end ArchivePLGeometry.Triangulation
