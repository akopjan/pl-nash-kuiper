module

public import Mathlib.Data.Fintype.Sort
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Finite face enumeration

A finite family of faces can be enumerated so that every proper subface
precedes its cofaces. The enumeration uses cardinality first and an arbitrary
finite tie-breaking order second.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u

/-- Enumerate a finite type with smaller ranks appearing first. -/
theorem exists_enumeration_by_rank {I : Type u} [Finite I] (rank : I → ℕ) :
    ∃ N : ℕ, ∃ e : Fin N ≃ I,
      ∀ i j, rank (e i) < rank (e j) → i < j := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let tie := Fintype.equivFin I
  let key : I → ℕ ×ₗ Fin (Fintype.card I) := fun i => toLex (rank i, tie i)
  have hkey : Function.Injective key := by
    intro i j hij
    apply tie.injective
    exact congrArg (fun z : ℕ ×ₗ Fin (Fintype.card I) => (ofLex z).2) hij
  letI : LinearOrder I := LinearOrder.lift' key hkey
  let e := monoEquivOfFin I rfl
  refine ⟨Fintype.card I, e.toEquiv, ?_⟩
  intro i j hij
  apply e.lt_iff_lt.mp
  exact Prod.Lex.left _ _ hij

/-- An ordered enumeration of a finite family of finite vertex sets. -/
structure FaceEnumeration {P : Type u} (S : Set (Finset P)) where
  count : ℕ
  face : Fin count ≃ S
  index_strict : ∀ i j, (face i).val ⊆ (face j).val → i ≠ j → i < j

namespace FaceEnumeration

variable {P : Type u} {S : Set (Finset P)}

def ofFinite (hS : S.Finite) : FaceEnumeration S := by
  classical
  letI : Finite S := hS.to_subtype
  apply Classical.choice
  obtain ⟨N, e, he⟩ := exists_enumeration_by_rank (fun σ : S => σ.val.card)
  refine ⟨⟨N, e, ?_⟩⟩
  intro i j hij hne
  apply he
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hij, fun heq =>
    hne (e.injective (Subtype.ext heq))⟩

end FaceEnumeration
end ArchivePLGeometry
