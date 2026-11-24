module

public import BrehmApprox.FoldedPolytopeCover
public import BrehmApprox.AffineSelectionCells
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Equality arrangements on folded source complexes

One coordinate arrangement cuts all source cells. It preserves their genuine
facial intersections, even when unrelated sheets overlap in coordinates.
Every continuous finite affine selection becomes one branch on each cell.
-/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox

variable {P E F I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_affineWeakCell {C : Set E} (hC : Convex ℝ C)
    (L : J → E →ₗ[ℝ] ℝ) (b : J → ℝ) (s : J → AffineSign) :
    Convex ℝ (affineWeakCell C L b s) := by
  apply hC.inter
  rw [Set.ofPred_forall]
  apply convex_iInter
  intro j
  cases s j with
  | negative => exact convex_halfSpace_le (L j).isLinear (b j)
  | zero => exact convex_hyperplane (L j).isLinear (b j)
  | positive => exact convex_halfSpace_ge (L j).isLinear (b j)

namespace FoldedPolytopeCover

variable {q : P → E} (K : FoldedPolytopeCover q I)
    (L : J → E →ₗ[ℝ] ℝ) (b : J → ℝ)

def ArrangementIndex :=
  {p : I × (J → AffineSign) // (affineStratum (q '' K.cell p.1) L b p.2).Nonempty}

instance arrangementIndexFinite [Finite I] [Finite J] : Finite (K.ArrangementIndex L b) := by
  unfold ArrangementIndex
  infer_instance

def arrangementCell (p : K.ArrangementIndex L b) : Set P :=
  K.cell p.val.1 ∩ {x | ∀ j, (p.val.2 j).weakMatches (L j (q x)) (b j)}

theorem arrangementCell_image (p : K.ArrangementIndex L b) :
    q '' K.arrangementCell L b p = affineWeakCell (q '' K.cell p.val.1) L b p.val.2 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, hx.2⟩
  · rintro ⟨⟨x, hx, rfl⟩, hs⟩
    exact ⟨x, ⟨hx, hs⟩, rfl⟩

theorem arrangementCell_inter_image (p r : K.ArrangementIndex L b) :
    q '' (K.arrangementCell L b p ∩ K.arrangementCell L b r) =
      affineWeakCell
        (affineWeakCell (q '' (K.cell p.val.1 ∩ K.cell r.val.1)) L b p.val.2)
        L b r.val.2 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨⟨x, ⟨hx.1.1, hx.2.1⟩, rfl⟩, hx.1.2⟩, hx.2.2⟩
  · rintro ⟨⟨⟨x, hx, rfl⟩, hp⟩, hr⟩
    exact ⟨x, ⟨⟨hx.1, hp⟩, ⟨hx.2, hr⟩⟩, rfl⟩

theorem arrangementCell_cover (x : P) : ∃ p, x ∈ K.arrangementCell L b p := by
  obtain ⟨i, hi⟩ := K.cover x
  let s : J → AffineSign := fun j => AffineSign.ofCompare (L j (q x)) (b j)
  have hx : q x ∈ affineStratum (q '' K.cell i) L b s :=
    ⟨Set.mem_image_of_mem q hi, fun j => AffineSign.holds_ofCompare _ _⟩
  exact ⟨⟨(i, s), q x, hx⟩, hi, fun j => AffineSign.holds_weak (hx.2 j)⟩

theorem arrangementCell_face_inter (p r : K.ArrangementIndex L b) :
    _root_.IsExtreme ℝ (q '' K.arrangementCell L b p)
      (q '' (K.arrangementCell L b p ∩ K.arrangementCell L b r)) := by
  rw [K.arrangementCell_image, K.arrangementCell_inter_image]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact ⟨(K.face_inter p.val.1 r.val.1).subset hx.1.1, hx.1.2⟩
  · intro x hx y hy z hz hseg
    have hxbase : x ∈ q '' (K.cell p.val.1 ∩ K.cell r.val.1) :=
      (K.face_inter p.val.1 r.val.1).left_mem_of_mem_openSegment hx.1 hy.1 hz.1.1 hseg
    obtain ⟨a, d, ha, hd, had, rfl⟩ := hseg
    refine ⟨⟨hxbase, hx.2⟩, fun j => ?_⟩
    have hzj := hz.2 j
    simp only [map_add, map_smul, smul_eq_mul] at hzj
    exact AffineSign.weak_at_left_of_combo (p.val.2 j) (r.val.2 j)
      (hx.2 j) (hy.2 j) hzj ha hd had

variable [FiniteDimensional ℝ E] [Fintype J]

theorem arrangementCell_polytope (p : K.ArrangementIndex L b) :
    IsFinitePolytope (q '' K.arrangementCell L b p) := by
  rw [K.arrangementCell_image]
  obtain ⟨V, hV⟩ := K.polytope_image p.val.1
  rw [hV]
  exact exists_finset_affineWeakCell V L b p.val.2

def arrangement : FoldedPolytopeCover q (K.ArrangementIndex L b) where
  cell := K.arrangementCell L b
  cover := K.arrangementCell_cover L b
  injective_cell p := (K.injective_cell p.val.1).mono Set.inter_subset_left
  polytope_image := K.arrangementCell_polytope L b
  convex_inter p r := by
    rw [K.arrangementCell_inter_image]
    exact convex_affineWeakCell
      (convex_affineWeakCell (K.convex_inter p.val.1 r.val.1) L b p.val.2) L b r.val.2
  face_inter := K.arrangementCell_face_inter L b

omit [FiniteDimensional ℝ E] [Fintype J] in
def cellEquiv (i : I) : K.cell i ≃ q '' K.cell i :=
  Equiv.ofBijective (fun x => ⟨q x.val, Set.mem_image_of_mem q x.property⟩)
    ⟨fun x y h => Subtype.ext (K.injective_cell i x.property y.property (congrArg Subtype.val h)),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := y.property
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

omit [FiniteDimensional ℝ E] [Fintype J] in
def cellHomeomorph [TopologicalSpace P]
    (hc : ∀ i, IsCompact (K.cell i)) (hq : Continuous q) (i : I) :
    K.cell i ≃ₜ q '' K.cell i := by
  let : CompactSpace (K.cell i) := isCompact_iff_compactSpace.mp (hc i)
  have he : Continuous (K.cellEquiv i) := (hq.comp continuous_subtype_val).subtype_mk _
  exact (K.cellEquiv i).toHomeomorphOfContinuousClosed he he.isClosedMap

variable [TopologicalSpace P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]

theorem affine_selection_eqOn_arrangement
    (hc : ∀ i, IsCompact (K.cell i)) (hq : Continuous q)
    (a : J → E →ᵃ[ℝ] F) {f : P → F} (hf : Continuous f)
    (hsel : ∀ x, ∃ j, f x = a j (q x))
    (p : K.ArrangementIndex (affineEqualityLinear a) (affineEqualityBound a)) :
    ∃ j, ∀ x ∈ K.arrangementCell (affineEqualityLinear a) (affineEqualityBound a) p,
      f x = a j (q x) := by
  classical
  let e := K.cellHomeomorph hc hq p.val.1
  let F : E → F := fun y => if hy : y ∈ q '' K.cell p.val.1 then
    f (e.symm ⟨y, hy⟩).val else 0
  have hF : ContinuousOn F (q '' K.cell p.val.1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he := hf.comp (continuous_subtype_val.comp e.symm.continuous)
    convert he using 1
    funext y
    simp only [Set.domRestrict_apply, F, dite_eq_left y.property, Function.comp_def]
  have hFq (x : P) (hx : x ∈ K.cell p.val.1) : F (q x) = f x := by
    have hqx : q x ∈ q '' K.cell p.val.1 := Set.mem_image_of_mem q hx
    dsimp only [F]
    rw [dite_eq_left hqx]
    have heq : (⟨q x, hqx⟩ : q '' K.cell p.val.1) = e ⟨x, hx⟩ := rfl
    rw [heq, e.symm_apply_apply]
  have hselect : ∀ y ∈ q '' K.cell p.val.1, ∃ j, F y = a j y := by
    rintro y ⟨x, hx, rfl⟩
    rw [hFq x hx]
    exact hsel x
  obtain ⟨j, hj⟩ := BrehmApprox.affine_selection_eqOn_weakCell
    (K.polytope_image p.val.1) a hF hselect p.val.2 p.property
  refine ⟨j, fun x hx => ?_⟩
  rw [← hFq x hx.1]
  exact hj ⟨Set.mem_image_of_mem q hx.1, hx.2⟩

end FoldedPolytopeCover
end BrehmApprox
