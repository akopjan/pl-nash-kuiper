module

public import PLGeometry.ProtectedVoronoiPolytope
public import PLGeometry.SphericalComplexRealization
public import BrehmApprox.PolytopeIntersection

/-!
# The finite complex of Voronoi ties

The bases used for radial folding are common faces of two Voronoi cells
with distinct sites. One ambient pulling order triangulates every such
base compatibly. Its vertices are labelled by actual source points.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.VoronoiAtlas

universe u v

local instance protectedVoronoiTieDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : VoronoiAtlas T E)

/-- An old simplex and two distinct sites belonging to it. -/
def TieIndex (S : Finset P) :=
  {i : T.simplices × (S × S) |
    i.2.1.val ≠ i.2.2.val ∧ i.2.1.val ∈ T.cell i.1.val ∧ i.2.2.val ∈ T.cell i.1.val}

instance tieIndexFinite (S : Finset P) : Finite (TieIndex (T := T) S) := by
  let : Finite T.simplices := T.finite_simplices.to_subtype
  unfold TieIndex
  infer_instance

def tiePiece (S : Finset P) (i : TieIndex (T := T) S) : Set E :=
  A.coord '' T.voronoiPiece S i.val.1.val i.val.2.1.val ∩
  A.coord '' T.voronoiPiece S i.val.1.val i.val.2.2.val

theorem tiePiece_polytope (S : Finset P) (i : TieIndex (T := T) S) :
    IsFinitePolytope (A.tiePiece S i) := by
  obtain ⟨V, hV⟩ := A.voronoiPiece_polytope S i.val.1.property i.val.2.1.val
  obtain ⟨W, hW⟩ := A.voronoiPiece_polytope S i.val.1.property i.val.2.2.val
  unfold tiePiece
  rw [hV, hW]
  exact exists_finset_convexHull_inter V W

theorem tiePiece_face_inter {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (hprotected : T.IsCellwiseProtected S)
    (i j : TieIndex (T := T) S) :
    _root_.IsExtreme ℝ (A.tiePiece S i) (A.tiePiece S i ∩ A.tiePiece S j) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  have hleft := (A.voronoiPiece_face_inter hnet hprotected
    i.val.1.property j.val.1.property i.val.2.1.val j.val.2.1.val).left_mem_of_mem_openSegment
      hx.1 hy.1 ⟨hz.1.1, hz.2.1⟩ hseg
  have hright := (A.voronoiPiece_face_inter hnet hprotected
    i.val.1.property j.val.1.property i.val.2.1.val j.val.2.2.val).left_mem_of_mem_openSegment
      hx.1 hy.1 ⟨hz.1.1, hz.2.2⟩ hseg
  exact ⟨hx, hleft.2, hright.2⟩

theorem tiePiece_source (S : Finset P) (i : TieIndex (T := T) S)
    {z : E} (hz : z ∈ A.tiePiece S i) :
    ∃ x : P, A.coord x = z ∧
      x ∈ T.voronoiPiece S i.val.1.val i.val.2.1.val ∧
      x ∈ T.voronoiPiece S i.val.1.val i.val.2.2.val := by
  obtain ⟨x, hx, hxe⟩ := hz.1
  obtain ⟨y, hy, hye⟩ := hz.2
  have hyx := A.injective (hye.trans hxe.symm)
  exact ⟨x, hxe, hx, Eq.mp (congrArg
    (fun q : P => q ∈ T.voronoiPiece S i.val.1.val i.val.2.2.val) hyx) hy⟩

section Ordered

variable [LinearOrder E]

local instance protectedVoronoiTieEDecidableEq : DecidableEq E := Classical.decEq E

def tieFaces (S : Finset P) : Set (Finset E) :=
  Pulling.familyFaces (A.tiePiece S) (A.tiePiece_polytope S)

theorem tieFaces_finite (S : Finset P) : (A.tieFaces S).Finite := by
  have he : A.tieFaces S = ⋃ i : TieIndex (T := T) S,
      (Pulling.faces (polytopeVertices (A.tiePiece S i) (A.tiePiece_polytope S i)) : Set (Finset E)) := by
    ext V
    simp only [tieFaces, Pulling.familyFaces, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe]
  rw [he]
  exact Set.finite_iUnion (fun i => (Pulling.faces
    (polytopeVertices (A.tiePiece S i) (A.tiePiece_polytope S i))).finite_toSet)

def tieVertexSet (S : Finset P) : Set E := ⋃ V ∈ A.tieFaces S, (V : Set E)

theorem tieVertexSet_finite (S : Finset P) : (A.tieVertexSet S).Finite :=
  (A.tieFaces_finite S).biUnion (fun V _ => V.finite_toSet)

abbrev TieVertex (S : Finset P) := A.tieVertexSet S

instance tieVertexFintype (S : Finset P) : Fintype (A.TieVertex S) :=
  (A.tieVertexSet_finite S).fintype

def tieCoordinateFace (S : Finset P) (σ : Finset (A.TieVertex S)) : Finset E :=
  σ.image Subtype.val

def tieComplex (S : Finset P) : Barycentric.Complex (A.TieVertex S) where
  faces := {σ | A.tieCoordinateFace S σ ∈ A.tieFaces S}
  downward := by
    intro σ hσ τ hτσ
    exact Pulling.family_face_downward (A.tiePiece S) (A.tiePiece_polytope S) hσ
      (Finset.image_subset_image hτσ)
  singleton := by
    intro v
    change A.tieCoordinateFace S {v} ∈ A.tieFaces S
    obtain ⟨V, hV, hv⟩ := Set.mem_iUnion₂.mp v.property
    have hsub : ({v.val} : Finset E) ⊆ V := Finset.singleton_subset_iff.mpr hv
    have hs := Pulling.family_face_downward (A.tiePiece S) (A.tiePiece_polytope S) hV hsub
    have he : A.tieCoordinateFace S {v} = {v.val} := by
      ext x
      simp [tieCoordinateFace]
    rw [he]
    exact hs

theorem tieVertex_mem_range (S : Finset P) (v : A.TieVertex S) : v.val ∈ Set.range A.coord := by
  obtain ⟨V, ⟨i, hV⟩, hv⟩ := Set.mem_iUnion₂.mp v.property
  have hvi := Pulling.family_face_subset_cell (A.tiePiece S) (A.tiePiece_polytope S) hV
    (subset_convexHull ℝ (V : Set E) hv)
  obtain ⟨x, hx, _, _⟩ := A.tiePiece_source S i hvi
  exact ⟨x, hx⟩

def tieSource (S : Finset P) (v : A.TieVertex S) : P :=
  (A.tieVertex_mem_range S v).choose

@[simp] theorem coord_tieSource (S : Finset P) (v : A.TieVertex S) :
    A.coord (A.tieSource S v) = v.val := (A.tieVertex_mem_range S v).choose_spec

theorem tieSource_injective (S : Finset P) : Function.Injective (A.tieSource S) := by
  intro v w hvw
  apply Subtype.ext
  rw [← A.coord_tieSource S v, ← A.coord_tieSource S w, hvw]

def tieSourceFace (S : Finset P) (σ : Finset (A.TieVertex S)) : Finset P :=
  σ.image (A.tieSource S)

def tieFaceIndex (S : Finset P) (σ : Finset (A.TieVertex S))
    (hσ : σ ∈ (A.tieComplex S).faces) : TieIndex (T := T) S := hσ.choose

theorem tieFaceIndex_spec (S : Finset P) (σ : Finset (A.TieVertex S))
    (hσ : σ ∈ (A.tieComplex S).faces) :
    A.tieCoordinateFace S σ ∈ Pulling.faces (polytopeVertices
      (A.tiePiece S (A.tieFaceIndex S σ hσ))
      (A.tiePiece_polytope S (A.tieFaceIndex S σ hσ))) := hσ.choose_spec

theorem tieFace_source_mem (S : Finset P) {σ : Finset (A.TieVertex S)}
    (hσ : σ ∈ (A.tieComplex S).faces) {v : A.TieVertex S} (hv : v ∈ σ) :
    A.tieSource S v ∈ T.voronoiPiece S (A.tieFaceIndex S σ hσ).val.1.val
      (A.tieFaceIndex S σ hσ).val.2.1.val ∧
    A.tieSource S v ∈ T.voronoiPiece S (A.tieFaceIndex S σ hσ).val.1.val
      (A.tieFaceIndex S σ hσ).val.2.2.val := by
  have hvi := Pulling.family_face_subset_cell (A.tiePiece S) (A.tiePiece_polytope S)
    (A.tieFaceIndex_spec S σ hσ) (subset_convexHull ℝ
      (A.tieCoordinateFace S σ : Set E) (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  obtain ⟨x, hx, hxa, hxb⟩ := A.tiePiece_source S (A.tieFaceIndex S σ hσ) hvi
  have hxe : x = A.tieSource S v := A.injective (hx.trans (A.coord_tieSource S v).symm)
  subst x
  exact ⟨hxa, hxb⟩

theorem tieFace_independent (S : Finset P) {σ : Finset (A.TieVertex S)}
    (hσ : σ ∈ (A.tieComplex S).faces) :
    AffineIndependent ℝ (fun v : σ => A.coord (A.tieSource S v.val)) := by
  let e : σ → A.tieCoordinateFace S σ := fun v =>
    ⟨v.val.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
  have he : Function.Injective e := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A.tieCoordinateFace S σ => z.val) hvw
  have hh := (Pulling.family_face_independent (A.tiePiece S) (A.tiePiece_polytope S) hσ).comp_embedding ⟨e, he⟩
  convert hh using 1
  funext v
  exact A.coord_tieSource S v.val

theorem tieFace_intersection {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (hprotected : T.IsCellwiseProtected S)
    {σ τ : Finset (A.TieVertex S)} (hσ : σ ∈ (A.tieComplex S).faces)
    (hτ : τ ∈ (A.tieComplex S).faces) :
    convexHull ℝ (A.tieCoordinateFace S σ : Set E) ∩
      convexHull ℝ (A.tieCoordinateFace S τ : Set E) =
      convexHull ℝ (A.tieCoordinateFace S (σ ∩ τ) : Set E) := by
  rw [Pulling.family_faces_intersection (A.tiePiece S) (A.tiePiece_polytope S)
    (A.tiePiece_face_inter hnet hprotected) hσ hτ]
  apply congrArg (convexHull ℝ)
  rw [← Finset.coe_inter]
  apply congrArg (fun V : Finset E => (V : Set E))
  exact (Finset.image_inter σ τ Subtype.val_injective).symm

end Ordered

end ArchivePLGeometry.VoronoiAtlas
