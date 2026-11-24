module

public import BrehmApprox.AffineArrangement
public import BrehmApprox.PolytopeVertices
public import BrehmApprox.IntegerCubeComplex

/-!
# Locally finite polyhedral covers adapted to finite affine selections

A locally finite family of compact polytopes with facial intersections stays
such a family after cutting by a finite affine arrangement. The nonempty sign
strata determine precisely the closed cells required for a continuous finite
selection.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology

namespace BrehmApprox

variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure PolytopeCover (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Type*) where
  cell : I → Set E
  polytope : ∀ i, IsFinitePolytope (cell i)
  cover : ∀ x : E, ∃ i, x ∈ cell i
  locallyFinite : LocallyFinite cell
  face_inter : ∀ i j, _root_.IsExtreme ℝ (cell i) (cell i ∩ cell j)

theorem locallyFinite_prod_left {X : Type*} [TopologicalSpace X]
    {C : I → Set X} (hC : LocallyFinite C) [Finite J] :
    LocallyFinite (fun p : I × J => C p.1) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := hC x
  refine ⟨U, hU, ?_⟩
  exact (hfin.prod (Set.finite_univ : (Set.univ : Set J).Finite)).subset
    (fun p hp => ⟨hp, Set.mem_univ p.2⟩)

namespace PolytopeCover

variable [FiniteDimensional ℝ E] [Fintype J]
    (K : PolytopeCover E I) (L : J → E →ₗ[ℝ] ℝ) (b : J → ℝ)

def ArrangementIndex :=
  {p : I × (J → AffineSign) // (affineStratum (K.cell p.1) L b p.2).Nonempty}

def arrangementCell (p : K.ArrangementIndex L b) : Set E :=
  affineWeakCell (K.cell p.val.1) L b p.val.2

theorem arrangementCell_polytope (p : K.ArrangementIndex L b) :
    IsFinitePolytope (K.arrangementCell L b p) := by
  obtain ⟨V, hV⟩ := K.polytope p.val.1
  unfold arrangementCell
  rw [hV]
  exact exists_finset_affineWeakCell V L b p.val.2

theorem arrangementCell_cover (x : E) : ∃ p, x ∈ K.arrangementCell L b p := by
  obtain ⟨i, hi⟩ := K.cover x
  let s : J → AffineSign := fun j => AffineSign.ofCompare (L j x) (b j)
  have hx : x ∈ affineStratum (K.cell i) L b s :=
    ⟨hi, fun j => AffineSign.holds_ofCompare _ _⟩
  exact ⟨⟨(i, s), x, hx⟩, affineStratum_subset_weakCell (K.cell i) L b s hx⟩

theorem arrangementCell_locallyFinite : LocallyFinite (K.arrangementCell L b) := by
  have h := (locallyFinite_prod_left (J := J → AffineSign) K.locallyFinite).comp_injective
    (Subtype.val_injective : Function.Injective (Subtype.val : K.ArrangementIndex L b → _))
  exact h.subset fun p => Set.inter_subset_left

theorem arrangementCell_face_inter (p q : K.ArrangementIndex L b) :
    _root_.IsExtreme ℝ (K.arrangementCell L b p)
      (K.arrangementCell L b p ∩ K.arrangementCell L b q) :=
  isExtreme_affineWeakCell_inter_of_base (K.face_inter p.val.1 q.val.1) L b p.val.2 q.val.2

def arrangement : PolytopeCover E (K.ArrangementIndex L b) where
  cell := K.arrangementCell L b
  polytope := K.arrangementCell_polytope L b
  cover := K.arrangementCell_cover L b
  locallyFinite := K.arrangementCell_locallyFinite L b
  face_inter := K.arrangementCell_face_inter L b

end PolytopeCover

def integerCubeCover (ι : Type*) [Fintype ι] : PolytopeCover (ι → ℝ) (ι → ℤ) where
  cell := integerCube
  polytope k := ⟨integerCubeVertices k, integerCube_eq_convexHull k⟩
  cover := integerCube_cover
  locallyFinite := locallyFinite_integerCubes
  face_inter := isExtreme_integerCubes_inter

end BrehmApprox
