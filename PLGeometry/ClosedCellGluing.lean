module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Homeomorph.Lemmas

/-! # Gluing maps on a finite closed cover -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u v w

structure FiniteClosedCover (P : Type u) [TopologicalSpace P] (I : Type v) [Finite I] where
  cell : I → Set P
  cover : ∀ x, ∃ i, x ∈ cell i
  closed : ∀ i, IsClosed (cell i)

namespace FiniteClosedCover

variable {P : Type u} [TopologicalSpace P] {I : Type v} [Finite I]
    {Y : Type w} [TopologicalSpace Y] (C : FiniteClosedCover P I)

def glue (f : ∀ i, C.cell i → Y) (x : P) : Y :=
  f (C.cover x).choose ⟨x, (C.cover x).choose_spec⟩

theorem glue_eq (f : ∀ i, C.cell i → Y)
    (hagree : ∀ i j (x : P) (hi : x ∈ C.cell i) (hj : x ∈ C.cell j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) (i : I) (x : C.cell i) :
    C.glue f x.val = f i x :=
  hagree _ _ x.val (C.cover x.val).choose_spec x.property

theorem continuous_glue (f : ∀ i, C.cell i → Y) (hf : ∀ i, Continuous (f i))
    (hagree : ∀ i j (x : P) (hi : x ∈ C.cell i) (hj : x ∈ C.cell j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) : Continuous (C.glue f) := by
  apply (locallyFinite_of_finite C.cell).continuous
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact C.cover x
  · exact C.closed
  · intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (C.cell i).domRestrict (C.glue f) = f i := by
      funext x
      exact C.glue_eq f hagree i x
    rw [he]
    exact hf i

end FiniteClosedCover
end ArchivePLGeometry
