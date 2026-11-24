module

public import BrehmApprox.UnitBallPolytopeCover

/-!
# Carrier-relative polyhedral refinements of finite affine selections

A fixed finite affine arrangement refines a facial polyhedral cover while
preserving local finiteness on its carrier. Choosing the arrangement from
the equality loci of finitely many affine maps makes a continuous selection
equal to a single candidate on every refined polytope.
-/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox.PolytopeCoverOn

variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype J] {A : Set E}
  (K : PolytopeCoverOn E I A) (L : J → E →ₗ[ℝ] ℝ) (b : J → ℝ)

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

omit [FiniteDimensional ℝ E] [Fintype J] in
theorem arrangementCell_subset (p : K.ArrangementIndex L b) :
    K.arrangementCell L b p ⊆ A :=
  Set.inter_subset_left.trans (K.cell_subset p.val.1)

theorem arrangementCell_cover (x : E) (hx : x ∈ A) :
    ∃ p, x ∈ K.arrangementCell L b p := by
  obtain ⟨i, hi⟩ := K.cover x hx
  let s : J → AffineSign := fun j => AffineSign.ofCompare (L j x) (b j)
  have hxs : x ∈ affineStratum (K.cell i) L b s :=
    ⟨hi, fun j => AffineSign.holds_ofCompare _ _⟩
  exact ⟨⟨(i, s), x, hxs⟩, affineStratum_subset_weakCell (K.cell i) L b s hxs⟩

omit [FiniteDimensional ℝ E] in
theorem arrangementCell_locallyFinite :
    LocallyFinite (fun p : K.ArrangementIndex L b =>
      (Subtype.val : A → E) ⁻¹' K.arrangementCell L b p) := by
  have h := (locallyFinite_prod_left (J := J → AffineSign) K.locallyFinite).comp_injective
    (Subtype.val_injective : Function.Injective (Subtype.val : K.ArrangementIndex L b → _))
  exact h.subset fun p => Set.preimage_mono Set.inter_subset_left

theorem arrangementCell_face_inter (p q : K.ArrangementIndex L b) :
    IsExtreme ℝ (K.arrangementCell L b p)
      (K.arrangementCell L b p ∩ K.arrangementCell L b q) :=
  isExtreme_affineWeakCell_inter_of_base (K.face_inter p.val.1 q.val.1) L b p.val.2 q.val.2

def arrangement : PolytopeCoverOn E (K.ArrangementIndex L b) A where
  cell := K.arrangementCell L b
  polytope := K.arrangementCell_polytope L b
  cell_subset := K.arrangementCell_subset L b
  cover := K.arrangementCell_cover L b
  locallyFinite := K.arrangementCell_locallyFinite L b
  face_inter := K.arrangementCell_face_inter L b

theorem selection_eqOn_arrangementCell
    {Y T : Type*} [MetricSpace Y] [Finite T]
    {f : E → Y} {F : T → E → Y}
    (hf : ContinuousOn f A) (hF : ∀ i, ContinuousOn (F i) A)
    (hsel : ∀ x ∈ A, ∃ i, f x = F i x)
    (heq : ∀ x ∈ A, ∀ y ∈ A,
      (∀ k, L k x = b k ↔ L k y = b k) →
      ∀ i j, F i x = F j x → F i y = F j y)
    (p : K.ArrangementIndex L b) :
    ∃ i, Set.EqOn f (F i) (K.arrangementCell L b p) := by
  have hs : affineStratum (K.cell p.val.1) L b p.val.2 ⊆ A :=
    Set.inter_subset_left.trans (K.cell_subset p.val.1)
  obtain ⟨i, hi⟩ := finite_selection_eqOn_of_eqOn_propagates
    (convex_affineStratum (K.polytope p.val.1).convex L b p.val.2).isPreconnected p.property
    (hf.mono hs) (fun i => (hF i).mono hs)
    (fun x hx => hsel x (hs hx))
    (fun x hx i j hij y hy => heq x (hs hx) y (hs hy)
      (fun k => AffineSign.holds_eq_iff (hx.2 k) (hy.2 k)) i j hij)
  refine ⟨i, ?_⟩
  have hw := K.arrangementCell_subset L b p
  apply hi.of_subset_closure (hf.mono hw) ((hF i).mono hw)
    (affineStratum_subset_weakCell (K.cell p.val.1) L b p.val.2)
  rw [closure_affineStratum (K.polytope p.val.1).convex
    (K.polytope p.val.1).isCompact.isClosed L b p.val.2 p.property]
  exact Set.Subset.rfl

end BrehmApprox.PolytopeCoverOn

namespace BrehmApprox

/-- A finite affine selection has a compatible locally finite polyhedral
refinement on any carrier already supplied with a genuine facial cover. -/
theorem refine_polytopeCoverOn_affine_selection
    {E F I J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Finite J] {A : Set E}
    (K : PolytopeCoverOn E I A) (a : J → E →ᵃ[ℝ] F) {f : E → F}
    (hf : ContinuousOn f A) (hsel : ∀ x ∈ A, ∃ j, f x = a j x) :
    ∃ (I' : Type) (R : PolytopeCoverOn E I' A),
      ∀ i, ∃ j, Set.EqOn f (a j) (R.cell i) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let B := Module.finBasis ℝ F
  let Q := J × J × Fin (Module.finrank ℝ F)
  let φ : Q → E →ᵃ[ℝ] ℝ := fun k =>
    (B.coord k.2.2).toAffineMap.comp (a k.1 - a k.2.1)
  let L : Q → E →ₗ[ℝ] ℝ := fun k => (φ k).linear
  let b : Q → ℝ := fun k => -(φ k) 0
  have hφ (k : Q) (x : E) :
      L k x = b k ↔ B.coord k.2.2 (a k.1 x - a k.2.1 x) = 0 := by
    have hd := congrFun (AffineMap.decomp (φ k)) x
    change (φ k) x = (φ k).linear x + (φ k) 0 at hd
    have heval : (φ k) x = B.coord k.2.2 (a k.1 x - a k.2.1 x) := rfl
    change (φ k).linear x = -(φ k) 0 ↔ _
    rw [← heval, hd]
    constructor <;> intro h <;> linarith
  refine ⟨K.ArrangementIndex L b, K.arrangement L b, ?_⟩
  intro p
  apply K.selection_eqOn_arrangementCell L b hf
    (fun j => (a j).continuous_of_finiteDimensional.continuousOn) hsel ?_ p
  intro x _ y _ hzero i j hij
  apply sub_eq_zero.mp
  apply B.forall_coord_eq_zero_iff.mp
  intro k
  apply (hφ (i, j, k) y).mp
  apply (hzero (i, j, k)).mp
  apply (hφ (i, j, k) x).mpr
  rw [hij, sub_self, map_zero]

end BrehmApprox
