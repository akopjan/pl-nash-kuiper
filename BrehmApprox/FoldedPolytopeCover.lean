module

public import BrehmApprox.LabelledPulling
public import BrehmApprox.PolytopeVertices

/-!
# Compatible triangulation of a folded polyhedral cover

The coordinate map is injective on each source cell. Distinct source cells
may have overlapping coordinate images. Only intersections in the source
are required to be common extreme faces. Ordering source vertices makes the
pulling triangulations compatible despite these overlaps.
-/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox

variable {P E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite family is obtained by supplying a finite index type. The fields
describe only the given cells, coordinates, and their geometric faces. -/
structure FoldedPolytopeCover (q : P → E) (I : Type*) where
  cell : I → Set P
  cover : ∀ x, ∃ i, x ∈ cell i
  injective_cell : ∀ i, Set.InjOn q (cell i)
  polytope_image : ∀ i, IsFinitePolytope (q '' cell i)
  convex_inter : ∀ i j, Convex ℝ (q '' (cell i ∩ cell j))
  face_inter : ∀ i j, _root_.IsExtreme ℝ (q '' cell i) (q '' (cell i ∩ cell j))

namespace FoldedPolytopeCover

variable {q : P → E} (K : FoldedPolytopeCover q I)

local instance foldedPolytopeCoverDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def vertexSet (i : I) : Set P :=
  {x | x ∈ K.cell i ∧ q x ∈ (q '' K.cell i).extremePoints ℝ}

theorem finite_vertexSet (i : I) : (K.vertexSet i).Finite := by
  have h : (q '' K.vertexSet i).Finite :=
    (K.polytope_image i).finite_extremePoints.subset (by
      rintro y ⟨x, hx, rfl⟩
      exact hx.2)
  exact h.of_finite_image ((K.injective_cell i).mono (fun _ hx => hx.1))

def vertices (i : I) : Finset P := (K.finite_vertexSet i).toFinset

@[simp] theorem mem_vertices (i : I) (x : P) : x ∈ K.vertices i ↔
    x ∈ K.cell i ∧ q x ∈ (q '' K.cell i).extremePoints ℝ :=
  Set.Finite.mem_toFinset _

theorem vertices_subset_cell (i : I) : (K.vertices i : Set P) ⊆ K.cell i :=
  fun x hx => ((K.mem_vertices i x).mp hx).1

theorem image_vertices (i : I) :
    (K.vertices i).image q = polytopeVertices (q '' K.cell i) (K.polytope_image i) := by
  apply Finset.coe_injective
  rw [coe_polytopeVertices]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ((K.mem_vertices i x).mp hx).2
  · intro hy
    obtain ⟨x, hx, rfl⟩ := extremePoints_subset hy
    exact Finset.mem_image.mpr ⟨x, (K.mem_vertices i x).mpr ⟨hx, hy⟩, rfl⟩

theorem convexHull_vertices (i : I) :
    convexHull ℝ ((K.vertices i).image q : Set E) = q '' K.cell i := by
  rw [K.image_vertices, convexHull_polytopeVertices]

theorem vertex_mem_other {i j : I} {x : P} (hx : x ∈ K.vertices i)
    (hxj : x ∈ K.cell j) : x ∈ K.vertices j := by
  obtain ⟨hxi, hxe⟩ := (K.mem_vertices i x).mp hx
  have hxface : q x ∈ (q '' (K.cell i ∩ K.cell j)).extremePoints ℝ := by
    rw [(K.face_inter i j).extremePoints_eq]
    exact ⟨⟨x, ⟨hxi, hxj⟩, rfl⟩, hxe⟩
  have hji : _root_.IsExtreme ℝ (q '' K.cell j) (q '' (K.cell i ∩ K.cell j)) := by
    simpa only [Set.inter_comm] using K.face_inter j i
  exact (K.mem_vertices j x).mpr ⟨hxj, hji.extremePoints_subset_extremePoints hxface⟩

theorem vertex_mem_other_of_coordinate {i j : I} {x : P}
    (hx : x ∈ K.vertices i) (hqx : q x ∈ q '' (K.cell i ∩ K.cell j)) :
    x ∈ K.vertices j := by
  obtain ⟨y, hy, hq⟩ := hqx
  have heq : y = x := K.injective_cell i hy.1 (K.vertices_subset_cell i hx) hq
  exact K.vertex_mem_other hx (heq ▸ hy.2)

/-- The convex hull lifted to the source through any cell containing its
vertices. The next lemma proves that this definition is independent of the
chosen containing cell. -/
def simplexCell (S : Finset P) : Set P :=
  {x | ∃ i, (S : Set P) ⊆ K.cell i ∧ x ∈ K.cell i ∧
    q x ∈ convexHull ℝ (S.image q : Set E)}

theorem simplexCell_eq (S : Finset P) (i : I) (hSi : (S : Set P) ⊆ K.cell i) :
    K.simplexCell S = K.cell i ∩ q ⁻¹' convexHull ℝ (S.image q : Set E) := by
  ext x
  constructor
  · rintro ⟨j, hSj, hxj, hqx⟩
    have hvertices : (S.image q : Set E) ⊆ q '' (K.cell i ∩ K.cell j) := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨p, ⟨hSi hp, hSj hp⟩, rfl⟩
    have hmean := convexHull_min hvertices (K.convex_inter i j) hqx
    obtain ⟨y, hy, heq⟩ := hmean
    have hyx : y = x := K.injective_cell j hy.2 hxj heq
    exact ⟨hyx ▸ hy.1, hqx⟩
  · rintro ⟨hxi, hqx⟩
    exact ⟨i, hSi, hxi, hqx⟩

theorem image_simplexCell (S : Finset P) (i : I) (hSi : (S : Set P) ⊆ K.cell i) :
    q '' K.simplexCell S = convexHull ℝ (S.image q : Set E) := by
  rw [K.simplexCell_eq S i hSi]
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    have hvertices : (S.image q : Set E) ⊆ q '' K.cell i := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨p, hSi hp, rfl⟩
    obtain ⟨x, hx, rfl⟩ := convexHull_min hvertices (K.polytope_image i).convex hy
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

theorem simplexCell_mono {S T : Finset P} (i : I) (hSi : (S : Set P) ⊆ K.cell i)
    (hTS : T ⊆ S) : K.simplexCell T ⊆ K.simplexCell S := by
  have hTi : (T : Set P) ⊆ K.cell i := (Finset.coe_subset.mpr hTS).trans hSi
  rw [K.simplexCell_eq S i hSi, K.simplexCell_eq T i hTi]
  exact fun _ hx => ⟨hx.1,
    convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image hTS)) hx.2⟩

variable [LinearOrder P]

def simplices : Set (Finset P) :=
  {S | ∃ i, S ∈ LabelledPulling.faces q (K.vertices i)}

theorem simplices_finite [Finite I] : K.simplices.Finite := by
  have heq : K.simplices =
      ⋃ i, (LabelledPulling.faces q (K.vertices i) : Set (Finset P)) := by
    ext S
    simp only [simplices, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe]
  rw [heq]
  exact Set.finite_iUnion (fun i => (LabelledPulling.faces q (K.vertices i)).finite_toSet)

theorem simplex_vertices_subset {S : Finset P} {i : I}
    (hS : S ∈ LabelledPulling.faces q (K.vertices i)) : (S : Set P) ⊆ K.cell i :=
  (Finset.coe_subset.mpr (LabelledPulling.face_subset hS)).trans (K.vertices_subset_cell i)

theorem simplex_independent {S : Finset P} (hS : S ∈ K.simplices) :
    AffineIndependent ℝ ((↑) : S.image q → E) := by
  obtain ⟨i, hi⟩ := hS
  exact LabelledPulling.face_independent hi

theorem simplex_independent_image {S : Finset P} (hS : S ∈ K.simplices) :
    AffineIndependent ℝ ((↑) : q '' (S : Set P) → E) := by
  rw [← Finset.coe_image]
  exact K.simplex_independent hS

theorem simplex_cover (x : P) : ∃ S ∈ K.simplices, x ∈ K.simplexCell S := by
  obtain ⟨i, hxi⟩ := K.cover x
  have hqx : q x ∈ convexHull ℝ ((K.vertices i).image q : Set E) := by
    rw [K.convexHull_vertices i]
    exact Set.mem_image_of_mem q hxi
  rw [LabelledPulling.faces_cover q (K.vertices i)] at hqx
  obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hqx
  exact ⟨S, ⟨i, hS⟩, i, K.simplex_vertices_subset hS, hxi, hxS⟩

theorem vertices_mem_simplex {S : Finset P} (hS : S ∈ K.simplices) :
    (S : Set P) ⊆ K.simplexCell S := by
  obtain ⟨i, hi⟩ := hS
  intro x hx
  exact ⟨i, K.simplex_vertices_subset hi, K.simplex_vertices_subset hi hx,
    subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩

theorem simplices_downward {S T : Finset P} (hS : S ∈ K.simplices) (hTS : T ⊆ S) :
    T ∈ K.simplices := by
  obtain ⟨i, hi⟩ := hS
  exact ⟨i, LabelledPulling.face_downward hi hTS⟩

theorem simplex_intersection {S T : Finset P} (hS : S ∈ K.simplices)
    (hT : T ∈ K.simplices) :
    K.simplexCell S ∩ K.simplexCell T = K.simplexCell (S ∩ T) := by
  obtain ⟨i, hi⟩ := hS
  obtain ⟨j, hj⟩ := hT
  have hSi := K.simplex_vertices_subset hi
  have hTj := K.simplex_vertices_subset hj
  apply Set.Subset.antisymm
  · intro x hx
    have hxS := hx.1
    have hxT := hx.2
    rw [K.simplexCell_eq S i hSi] at hxS
    rw [K.simplexCell_eq T j hTj] at hxT
    refine ⟨i, (Finset.coe_subset.mpr Finset.inter_subset_left).trans hSi, hxS.1, ?_⟩
    apply LabelledPulling.intersection_over_extreme
      (D := q '' (K.cell i ∩ K.cell j))
      (V := K.vertices i) (W := K.vertices j)
    · rw [K.convexHull_vertices i]
      exact K.face_inter i j
    · rw [K.convexHull_vertices j]
      simpa only [Set.inter_comm] using K.face_inter j i
    · exact fun _ hp hqp => K.vertex_mem_other_of_coordinate hp hqp
    · intro p hp hqp
      apply K.vertex_mem_other_of_coordinate hp
      simpa only [Set.inter_comm] using hqp
    · exact hi
    · exact hj
    · exact hxS.2
    · exact hxT.2
    · exact ⟨x, ⟨hxS.1, hxT.1⟩, rfl⟩
  · exact Set.subset_inter
      (K.simplexCell_mono i hSi Finset.inter_subset_left)
      (K.simplexCell_mono j hTj Finset.inter_subset_right)

end FoldedPolytopeCover
end BrehmApprox
