module

public import BrehmApprox.SimplexFaces
public import BrehmApprox.RankedStages
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!+# Genuine simplex ranks for simultaneous face stages

The rank is the number of vertices, including rank zero for the empty face.
Strict incidence strictly increases this rank. Affine independence bounds the
number of ranks by ambient dimension plus two, independently of subdivision.
-/

@[expose] public section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good} {N : ℕ}
variable {D : PolyhedralFaceData M N}

namespace SimplicialFaceData

variable (T : SimplicialFaceData D)

omit [FiniteDimensional ℝ E] in
theorem vertices_card_lt_of_faceLE {i j : Fin N} (hij : D.faceLE i j) (hne : i ≠ j) :
    (T.vertices i).card < (T.vertices j).card := by
  have hsub := T.vertices_mono i j hij
  have hneV : T.vertices i ≠ T.vertices j := by
    intro heq
    have hji : D.faceLE j i := T.face_of_vertices j i j (D.le_refl j) hij (by rw [heq])
    exact Nat.lt_asymm (D.index_strict i j hij hne)
      (D.index_strict j i hji (fun h => hne h.symm))
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hneV⟩)

theorem vertices_card_le_dimension (i : Fin N) :
    (T.vertices i).card ≤ Module.finrank ℝ E + 1 := by
  have h := (T.independent i).card_le_finrank_succ
  have hrank := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : T.vertices i → E)))
  exact (show (T.vertices i).card ≤
    Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : T.vertices i → E))) + 1 by
      simpa only [Fintype.card_coe] using h).trans (Nat.add_le_add_right hrank 1)

def faceRank (i : Fin N) : Fin (Module.finrank ℝ E + 2) :=
  ⟨(T.vertices i).card, Nat.lt_succ_of_le (T.vertices_card_le_dimension i)⟩

theorem faceRank_strict {i j : Fin N} (hij : D.faceLE i j) (hne : i ≠ j) :
    T.faceRank i < T.faceRank j := T.vertices_card_lt_of_faceLE hij hne

theorem equal_rank_incomparable {i j : Fin N}
    (hrank : T.faceRank i = T.faceRank j) (hne : i ≠ j) : ¬ D.faceLE i j := by
  intro hij
  exact (ne_of_lt (T.faceRank_strict hij hne)) hrank

theorem rankMembers_incomparable (k : Fin (Module.finrank ℝ E + 2)) :
    ∀ i ∈ rankMembers T.faceRank k, ∀ j ∈ rankMembers T.faceRank k,
      i ≠ j → ¬ D.faceLE i j := by
  intro i hi j hj hij
  exact T.equal_rank_incomparable
    (((mem_rankMembers T.faceRank k i).mp hi).trans ((mem_rankMembers T.faceRank k j).mp hj).symm) hij

end SimplicialFaceData
end BrehmApprox
