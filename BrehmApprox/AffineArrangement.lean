module

public import BrehmApprox.PolytopeHalfspaces
public import BrehmApprox.FiniteSelectionRigidity
public import Mathlib.Analysis.Convex.Topology

/-!
# Finite affine arrangements

The closures of the sign strata of a finite affine arrangement are finite
polytopes. A continuous finite selection of affine maps is one fixed map on
each such polytope.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

inductive AffineSign where
  | negative
  | zero
  | positive
  deriving DecidableEq

instance : Fintype AffineSign where
  elems := {.negative, .zero, .positive}
  complete x := by cases x <;> simp

namespace AffineSign

def holds : AffineSign → ℝ → ℝ → Prop
  | .negative, a, b => a < b
  | .zero, a, b => a = b
  | .positive, a, b => b < a

def weakMatches : AffineSign → ℝ → ℝ → Prop
  | .negative, a, b => a ≤ b
  | .zero, a, b => a = b
  | .positive, a, b => b ≤ a

theorem holds_weak {s : AffineSign} {a b : ℝ} (h : s.holds a b) :
    s.weakMatches a b := by
  cases s <;> simp_all [holds, weakMatches, le_of_lt]

theorem holds_eq_iff {s : AffineSign} {a b c : ℝ}
    (ha : s.holds a c) (hb : s.holds b c) : a = c ↔ b = c := by
  cases s <;> simp_all [holds, ne_of_lt, ne_of_gt]

def ofCompare (a b : ℝ) : AffineSign :=
  if a < b then .negative else if a = b then .zero else .positive

theorem holds_ofCompare (a b : ℝ) : (ofCompare a b).holds a b := by
  unfold ofCompare
  split_ifs with h h'
  · exact h
  · exact h'
  · exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm h')

end AffineSign

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

def affineStratum (C : Set E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (s : ι → AffineSign) : Set E :=
  C ∩ {x | ∀ i, (s i).holds (L i x) (b i)}

def affineWeakCell (C : Set E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (s : ι → AffineSign) : Set E :=
  C ∩ {x | ∀ i, (s i).weakMatches (L i x) (b i)}

theorem affineStratum_subset_weakCell
    (C : Set E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (s : ι → AffineSign) :
    affineStratum C L b s ⊆ affineWeakCell C L b s :=
  fun _ hx => ⟨hx.1, fun i => AffineSign.holds_weak (hx.2 i)⟩

theorem convex_affineStratum
    {C : Set E} (hC : Convex ℝ C) (L : ι → E →ₗ[ℝ] ℝ)
    (b : ι → ℝ) (s : ι → AffineSign) : Convex ℝ (affineStratum C L b s) := by
  apply hC.inter
  rw [Set.ofPred_forall]
  apply convex_iInter
  intro i
  cases s i with
  | negative => exact convex_halfSpace_lt (L i).isLinear (b i)
  | zero => exact convex_hyperplane (L i).isLinear (b i)
  | positive => exact convex_halfSpace_gt (L i).isLinear (b i)

theorem isClosed_affineWeakCell
    {C : Set E} (hC : IsClosed C) (L : ι → E →ₗ[ℝ] ℝ)
    (b : ι → ℝ) (s : ι → AffineSign) : IsClosed (affineWeakCell C L b s) := by
  apply hC.inter
  rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  have hL := (L i).continuous_of_finiteDimensional
  cases s i with
  | negative => exact isClosed_le hL continuous_const
  | zero => exact isClosed_eq hL continuous_const
  | positive => exact isClosed_le continuous_const hL

theorem closure_affineStratum
    {C : Set E} (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (s : ι → AffineSign)
    (hne : (affineStratum C L b s).Nonempty) :
    closure (affineStratum C L b s) = affineWeakCell C L b s := by
  apply Set.Subset.antisymm
  · exact closure_minimal (affineStratum_subset_weakCell C L b s)
      (isClosed_affineWeakCell hclosed L b s)
  · obtain ⟨x, hx⟩ := hne
    intro y hy
    have hseg : openSegment ℝ x y ⊆ affineStratum C L b s := by
      rintro z ⟨a, d, ha, hd, had, rfl⟩
      refine ⟨hconv hx.1 hy.1 ha.le hd.le had, fun i => ?_⟩
      have hxi := hx.2 i
      have hyi := hy.2 i
      simp only [map_add, map_smul, smul_eq_mul]
      cases hsi : s i <;> simp only [hsi, AffineSign.holds,
        AffineSign.weakMatches] at hxi hyi ⊢
      · calc
          a * L i x + d * L i y < a * b i + d * b i :=
            add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxi ha)
              (mul_le_mul_of_nonneg_left hyi hd.le)
          _ = b i := by rw [← add_mul, had, one_mul]
      · rw [hxi, hyi, ← add_mul, had, one_mul]
      · calc
          b i = a * b i + d * b i := by rw [← add_mul, had, one_mul]
          _ < a * L i x + d * L i y :=
            add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxi ha)
              (mul_le_mul_of_nonneg_left hyi hd.le)
    exact (closure_mono hseg) (segment_subset_closure_openSegment (right_mem_segment ℝ x y))

def affineSignLinear (L : ι → E →ₗ[ℝ] ℝ) (s : ι → AffineSign) :
    (ι × Bool) → E →ₗ[ℝ] ℝ := fun j =>
  match s j.1, j.2 with
  | .negative, _ => L j.1
  | .zero, false => L j.1
  | .zero, true => -L j.1
  | .positive, _ => -L j.1

def affineSignBound (b : ι → ℝ) (s : ι → AffineSign) : (ι × Bool) → ℝ := fun j =>
  match s j.1, j.2 with
  | .negative, _ => b j.1
  | .zero, false => b j.1
  | .zero, true => -b j.1
  | .positive, _ => -b j.1

theorem affineWeakCell_eq_halfspaces
    (C : Set E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (s : ι → AffineSign) :
    affineWeakCell C L b s =
      C ∩ {x | ∀ j, affineSignLinear L s j x ≤ affineSignBound b s j} := by
  ext x
  simp only [affineWeakCell, mem_inter_iff, mem_ofPred_eq]
  apply and_congr_right
  intro _
  constructor
  · intro h j
    obtain ⟨i, d⟩ := j
    have hi := h i
    cases hsi : s i <;> cases d <;>
      simp_all [AffineSign.weakMatches, affineSignLinear, affineSignBound]
  · intro h i
    have h0 := h (i, false)
    have h1 := h (i, true)
    cases hsi : s i <;>
      simp_all [AffineSign.weakMatches, affineSignLinear, affineSignBound] <;> linarith

theorem exists_finset_affineWeakCell
    (V : Finset E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (s : ι → AffineSign) :
    ∃ W : Finset E,
      affineWeakCell (convexHull ℝ (V : Set E)) L b s = convexHull ℝ (W : Set E) := by
  rw [affineWeakCell_eq_halfspaces]
  exact exists_finset_convexHull_inter_halfspaces V (affineSignLinear L s) (affineSignBound b s)

theorem AffineSign.weak_at_left_of_combo
    (s t : AffineSign) {x y c a d : ℝ}
    (hx : s.weakMatches x c) (hy : s.weakMatches y c)
    (hz : t.weakMatches (a * x + d * y) c)
    (ha : 0 < a) (hd : 0 < d) (had : a + d = 1) :
    t.weakMatches x c := by
  have hc : a * c + d * c = c := by rw [← add_mul, had, one_mul]
  have hle (hx : x ≤ c) (hy : y ≤ c) (hz : c ≤ a * x + d * y) : x = c := by
    apply le_antisymm hx
    by_contra h
    have hlt := add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left (lt_of_not_ge h) ha)
      (mul_le_mul_of_nonneg_left hy hd.le)
    rw [hc] at hlt
    exact (not_lt_of_ge hz) hlt
  have hge (hx : c ≤ x) (hy : c ≤ y) (hz : a * x + d * y ≤ c) : x = c := by
    apply le_antisymm _ hx
    by_contra h
    have hlt := add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left (lt_of_not_ge h) ha)
      (mul_le_mul_of_nonneg_left hy hd.le)
    rw [hc] at hlt
    exact (not_lt_of_ge hz) hlt
  cases s <;> cases t <;> simp only [AffineSign.weakMatches] at hx hy hz ⊢
  · exact hx
  · exact hle hx hy hz.ge
  · exact (hle hx hy hz).ge
  · exact hx.le
  · exact hx
  · exact hx.ge
  · exact (hge hx hy hz).le
  · exact hge hx hy hz.le
  · exact hx

/-- Two cells of one affine arrangement meet in a face of each cell. -/
theorem isExtreme_affineWeakCell_inter
    (C : Set E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (s t : ι → AffineSign) :
    IsExtreme ℝ (affineWeakCell C L b s)
      (affineWeakCell C L b s ∩ affineWeakCell C L b t) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, d, ha, hd, had, rfl⟩ := hseg
  refine ⟨hx, hx.1, fun i => ?_⟩
  have hzi := hz.2.2 i
  simp only [map_add, map_smul, smul_eq_mul] at hzi
  exact AffineSign.weak_at_left_of_combo (s i) (t i) (hx.2 i) (hy.2 i) hzi ha hd had

theorem isExtreme_affineWeakCell_inter_of_base
    {C D : Set E} (hCD : IsExtreme ℝ C (C ∩ D))
    (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (s t : ι → AffineSign) :
    IsExtreme ℝ (affineWeakCell C L b s)
      (affineWeakCell C L b s ∩ affineWeakCell D L b t) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  have hxD : x ∈ D :=
    (hCD.left_mem_of_mem_openSegment hx.1 hy.1 ⟨hz.1.1, hz.2.1⟩ hseg).2
  obtain ⟨a, d, ha, hd, had, rfl⟩ := hseg
  refine ⟨hx, hxD, fun i => ?_⟩
  have hzi := hz.2.2 i
  simp only [map_add, map_smul, smul_eq_mul] at hzi
  exact AffineSign.weak_at_left_of_combo (s i) (t i) (hx.2 i) (hy.2 i) hzi ha hd had

theorem finite_selection_polytope_cover_of_zero_pattern
    {Y J : Type*} [MetricSpace Y] [Finite J]
    (V : Finset E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {f : E → Y} {F : J → E → Y}
    (hf : ContinuousOn f (convexHull ℝ (V : Set E)))
    (hF : ∀ j, ContinuousOn (F j) (convexHull ℝ (V : Set E)))
    (hsel : ∀ x ∈ convexHull ℝ (V : Set E), ∃ j, f x = F j x)
    (heq : ∀ x ∈ convexHull ℝ (V : Set E),
      ∀ y ∈ convexHull ℝ (V : Set E),
      (∀ k, L k x = b k ↔ L k y = b k) →
      ∀ i j, F i x = F j x → F i y = F j y) :
    ∃ C : Finset (Finset E),
      convexHull ℝ (V : Set E) = ⋃ W ∈ C, convexHull ℝ (W : Set E) ∧
      ∀ W ∈ C, ∃ j, Set.EqOn f (F j) (convexHull ℝ (W : Set E)) := by
  classical
  let K := convexHull ℝ (V : Set E)
  choose W hW using fun s : ι → AffineSign => exists_finset_affineWeakCell V L b s
  let S : Finset (ι → AffineSign) :=
    Finset.univ.filter (fun s => (affineStratum K L b s).Nonempty)
  refine ⟨S.image W, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      let s : ι → AffineSign := fun k => AffineSign.ofCompare (L k x) (b k)
      have hxs : x ∈ affineStratum K L b s :=
        ⟨hx, fun k => AffineSign.holds_ofCompare _ _⟩
      have hs : s ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxs⟩⟩
      refine Set.mem_iUnion₂.mpr ⟨W s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
      rw [← hW s]
      exact affineStratum_subset_weakCell K L b s hxs
    · intro hx
      obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hT
      rw [← hW s] at hxT
      exact hxT.1
  · intro T hT
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hT
    have hne := (Finset.mem_filter.mp hs).2
    have hsub : affineStratum K L b s ⊆ K := fun _ hx => hx.1
    obtain ⟨j, hj⟩ := finite_selection_eqOn_of_eqOn_propagates
      (convex_affineStratum (convex_convexHull ℝ (V : Set E)) L b s).isPreconnected hne
      (hf.mono hsub) (fun j => (hF j).mono hsub)
      (fun x hx => hsel x hx.1)
      (fun x hx i j hij y hy => heq x hx.1 y hy.1
        (fun k => AffineSign.holds_eq_iff (hx.2 k) (hy.2 k)) i j hij)
    refine ⟨j, ?_⟩
    rw [← hW s]
    have hweak : affineWeakCell K L b s ⊆ K := fun _ hx => hx.1
    apply hj.of_subset_closure (hf.mono hweak) ((hF j).mono hweak)
      (affineStratum_subset_weakCell K L b s)
    rw [closure_affineStratum (convex_convexHull ℝ (V : Set E))
      (V.finite_toSet.isClosed_convexHull ℝ) L b s hne]

theorem finite_selection_affine_polytope_cover
    {F J : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Finite J]
    (V : Finset E) (a : J → E →ᵃ[ℝ] F) {f : E → F}
    (hf : ContinuousOn f (convexHull ℝ (V : Set E)))
    (hsel : ∀ x ∈ convexHull ℝ (V : Set E), ∃ j, f x = a j x) :
    ∃ C : Finset (Finset E),
      convexHull ℝ (V : Set E) = ⋃ W ∈ C, convexHull ℝ (W : Set E) ∧
      ∀ W ∈ C, ∃ j, Set.EqOn f (a j) (convexHull ℝ (W : Set E)) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  let B := Module.finBasis ℝ F
  let I := J × J × Fin (Module.finrank ℝ F)
  let φ : I → E →ᵃ[ℝ] ℝ := fun k =>
    (B.coord k.2.2).toAffineMap.comp (a k.1 - a k.2.1)
  let L : I → E →ₗ[ℝ] ℝ := fun k => (φ k).linear
  let b : I → ℝ := fun k => -(φ k) 0
  have hφ (k : I) (x : E) :
      L k x = b k ↔ B.coord k.2.2 (a k.1 x - a k.2.1 x) = 0 := by
    have hd := congrFun (AffineMap.decomp (φ k)) x
    change (φ k) x = (φ k).linear x + (φ k) 0 at hd
    have heval : (φ k) x = B.coord k.2.2 (a k.1 x - a k.2.1 x) := rfl
    change (φ k).linear x = -(φ k) 0 ↔ _
    rw [← heval, hd]
    constructor <;> intro h <;> linarith
  apply finite_selection_polytope_cover_of_zero_pattern V L b hf
    (fun j => (a j).continuous_of_finiteDimensional.continuousOn) hsel
  intro x hx y hy hzero i j hij
  apply sub_eq_zero.mp
  apply B.forall_coord_eq_zero_iff.mp
  intro k
  apply (hφ (i, j, k) y).mp
  apply (hzero (i, j, k)).mp
  apply (hφ (i, j, k) x).mpr
  rw [hij, sub_self, map_zero]

end BrehmApprox
