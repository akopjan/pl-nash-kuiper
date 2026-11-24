module

public import PLGeometry.Definitions
public import BrehmApprox.FoldedArrangement
public import BrehmApprox.SimplexExtreme
public import BrehmApprox.GluedMotionSelection
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Finite affine selections on a folded Euclidean source

A finite equality arrangement and source-labelled pulling triangulations
turn finite ambient motion selection into the concrete PL-isometry used in
the Challenge. Different folded sheets need not have disjoint images.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry

universe u
variable {P : Type u} [MetricSpace P] {n : ℕ} {I : Type*}
    {q : P → EuclideanSpace ℝ (Fin n)}

local instance foldedEuclideanPLDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def euclideanTriangulationOfFoldedCover [Finite I] [LinearOrder P]
    (K : FoldedPolytopeCover q I)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y) : Triangulation .euclidean n P where
  simplices := K.simplices
  cell := K.simplexCell
  chart _ := q
  cover := K.simplex_cover
  locallyFinite := by
    let : Finite K.simplices := K.simplices_finite.to_subtype
    exact locallyFinite_of_finite _
  vertices_mem _ hS := K.vertices_mem_simplex hS
  simplex _ hS := K.simplex_independent hS
  image_cell S hS := by
    obtain ⟨i, hi⟩ := hS
    exact K.image_simplexCell S i (K.simplex_vertices_subset hi)
  isometry_cell S hS x hx y hy := by
    obtain ⟨i, hi⟩ := hS
    rw [K.simplexCell_eq S i (K.simplex_vertices_subset hi)] at hx hy
    exact hiso i x hx.1 y hy.1
  faces _ hS _ hTS := K.simplices_downward hS hTS
  image_face S hS T hTS := by
    obtain ⟨i, hi⟩ := hS
    exact K.image_simplexCell T i
      ((Finset.coe_subset.mpr hTS).trans (K.simplex_vertices_subset hi))
  intersection _ hS _ hT := K.simplex_intersection hS hT

theorem plIsometry_euclidean_of_folded_motion_selection
    [Finite I] (K : FoldedPolytopeCover q I)
    (hc : ∀ i, IsCompact (K.cell i)) (hq : Continuous q)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y)
    {J : Type*} [Finite J]
    (r : J → EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    {g : P → EuclideanSpace ℝ (Fin n)} (hg : Continuous g)
    (hsel : ∀ x, ∃ j, g x = r j (q x)) : PLIsometry .euclidean n g := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : LinearOrder P := IsWellOrder.linearOrder (WellOrderingRel : P → P → Prop)
  let a := fun j => (r j).toAffineMap
  let A := K.arrangement (affineEqualityLinear a) (affineEqualityBound a)
  have hisoA : ∀ i, ∀ x ∈ A.cell i, ∀ y ∈ A.cell i,
      dist (q x) (q y) = dist x y :=
    fun i x hx y hy => hiso i.val.1 x hx.1 y hy.1
  let T := euclideanTriangulationOfFoldedCover A hisoA
  refine ⟨hg, T, ?_⟩
  intro S hS x hx y hy
  obtain ⟨i, hi⟩ := hS
  change x ∈ A.simplexCell S at hx
  change y ∈ A.simplexCell S at hy
  rw [A.simplexCell_eq S i (A.simplex_vertices_subset hi)] at hx hy
  obtain ⟨j, hj⟩ := K.affine_selection_eqOn_arrangement hc hq a hg hsel i
  rw [hj x hx.1, hj y hy.1]
  exact ((r j).isometry.dist_eq (q x) (q y)).trans (hisoA i x hx.1 y hy.1)

end ArchivePLGeometry

namespace BrehmApprox.FoldedGeometry

theorem cell_inter_eq_meet {X P : Type*} [MetricSpace X] [MetricSpace P]
    {Good : (X → X) → Prop} {M : PolytopeModel X Good} {N : ℕ}
    (G : FoldedGeometry (P := P) M N) (i j : Fin N) :
    G.cell i ∩ G.cell j = G.cell (G.meet i j) :=
  Set.Subset.antisymm (G.intersection i j)
    (Set.subset_inter (G.cell_mono _ _ (G.meet_le_left i j))
      (G.cell_mono _ _ (G.meet_le_right i j)))

variable {P : Type*} [MetricSpace P] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Good : (E → E) → Prop} {M : PolytopeModel E Good} {N : ℕ}
    (G : FoldedGeometry (P := P) M N)

def euclideanPolytopeCover (T : SimplicialFaceData G.toPolyhedralFaceData) :
    FoldedPolytopeCover G.fold (Fin N) where
  cell := G.cell
  cover := G.cover
  injective_cell i x hx y hy heq := by
    apply dist_eq_zero.mp
    rw [← G.isometry_cell i x hx y hy, heq, dist_self]
  polytope_image i := by
    rw [G.image_cell i, T.core_eq i]
    exact ⟨T.vertices i, rfl⟩
  convex_inter i j := by
    rw [G.cell_inter_eq_meet, G.image_cell, T.core_eq]
    exact convex_convexHull ℝ _
  face_inter i j := by
    rw [G.image_cell, G.cell_inter_eq_meet, G.image_cell, T.core_eq, T.core_eq]
    exact isExtreme_convexHull_vertex_subset (T.independent i)
      (T.vertices_mono _ _ (G.meet_le_left i j))

end BrehmApprox.FoldedGeometry

namespace ArchivePLGeometry

variable {P : Type*} [MetricSpace P] {n N : ℕ}
    (G : FoldedGeometry (P := P) (euclideanPolytopeModel n) N)
    (T : SimplicialFaceData G.toPolyhedralFaceData)

include T in
theorem plIsometry_euclidean_of_folded_geometry_selection
    {J : Type*} [Finite J]
    (r : J → EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    {g : P → EuclideanSpace ℝ (Fin n)} (hg : Continuous g)
    (hsel : ∀ x, ∃ j, g x = r j (G.fold x)) : PLIsometry .euclidean n g := by
  exact plIsometry_euclidean_of_folded_motion_selection (G.euclideanPolytopeCover T)
    (G.compact_cell 0) ((G.constantSource 0).fold_lipschitz G.intrinsic).continuous
    G.isometry_cell r hg hsel

include T in
theorem plIsometry_euclidean_of_model_maps
    {g : P → EuclideanSpace ℝ (Fin n)} (hg : Continuous g)
    (hm : G.RealizedByModelMaps g) : PLIsometry .euclidean n g := by
  obtain ⟨R, hR⟩ := hm.euclidean_motions
  apply plIsometry_euclidean_of_folded_geometry_selection G T (fun r : R => r.val) hg
  intro x
  obtain ⟨r, hr, heq⟩ := hR x
  exact ⟨⟨r, hr⟩, heq⟩

end ArchivePLGeometry
