module

public import BrehmApprox.SimplexFaces

/-!+# Canonical closed bad sets for Euclidean face collapses

For a nonempty face, the bad set contains the complement of its relative
interior inside its affine span and every cofacial face which does not contain
it. Empty faces use the whole ambient space, so their collapse is the identity.
Closedness, all required inclusions, and avoidance at genuine positive
barycentric face points are proved here.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Use the affine span for a nonempty face, and the ambient space for an
empty face so that its orthogonal projection is still defined. -/
def canonicalAffineFace (A : Set E) : AffineSubspace ℝ E := by
  classical
  exact if A.Nonempty then affineSpan ℝ A else ⊤

instance canonicalAffineFace_nonempty (A : Set E) : Nonempty (canonicalAffineFace A) := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨p, hp⟩ := hA
    refine ⟨⟨p, ?_⟩⟩
    simpa only [canonicalAffineFace, ite_eq_left (show A.Nonempty from ⟨p, hp⟩), SetLike.mem_coe] using
      subset_affineSpan ℝ A hp
  · refine ⟨⟨0, ?_⟩⟩
    simp only [canonicalAffineFace, ite_eq_right hA, AffineSubspace.mem_top]

omit [FiniteDimensional ℝ E] in
lemma canonicalAffineFace_eq {A : Set E} (hA : A.Nonempty) :
    canonicalAffineFace A = affineSpan ℝ A := by
  classical
  simp only [canonicalAffineFace, ite_eq_left hA]

omit [FiniteDimensional ℝ E] in
lemma subset_canonicalAffineFace (A : Set E) : A ⊆ canonicalAffineFace A := by
  intro p hp
  rw [canonicalAffineFace_eq (show A.Nonempty from ⟨p, hp⟩)]
  exact subset_affineSpan ℝ A hp

/-- The complement of relative interior inside the affine span is closed in
the ambient finite-dimensional space. -/
lemma isClosed_affineSpan_diff_intrinsicInterior (A : Set E) :
    IsClosed ((affineSpan ℝ A : Set E) \ intrinsicInterior ℝ A) := by
  let B : Set (affineSpan ℝ A) := (interior ((↑) ⁻¹' A))ᶜ
  have hB : IsClosed B := isOpen_interior.isClosed_compl
  have himage : (Subtype.val '' B : Set E) =
      (affineSpan ℝ A : Set E) \ intrinsicInterior ℝ A := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      intro hp
      obtain ⟨z, hz, hzy⟩ := mem_intrinsicInterior.mp hp
      have heq : z = y := Subtype.ext hzy
      subst z
      exact hy hz
    · rintro ⟨hpF, hpnot⟩
      refine ⟨⟨p, hpF⟩, ?_, rfl⟩
      intro hpint
      exact hpnot (mem_intrinsicInterior.mpr ⟨⟨p, hpF⟩, hpint, rfl⟩)
  rw [← himage]
  exact (affineSpan ℝ A).isClosed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isClosedMap B hB

lemma isClosed_canonicalAffineFace_diff_intrinsicInterior (A : Set E) :
    IsClosed ((canonicalAffineFace A : Set E) \ intrinsicInterior ℝ A) := by
  classical
  by_cases hA : A.Nonempty
  · rw [canonicalAffineFace_eq hA]
    exact isClosed_affineSpan_diff_intrinsicInterior A
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    rw [canonicalAffineFace, ite_eq_right hA, he, intrinsicInterior_empty, Set.sdiff_empty]
    change IsClosed (Set.univ : Set E)
    exact isClosed_univ

variable {Good : (E → E) → Prop} {M : PolytopeModel E Good} {N : ℕ}

namespace PolyhedralFaceData

variable (D : PolyhedralFaceData M N)

def Cofacial (i j : Fin N) : Prop := ∃ k, D.faceLE i k ∧ D.faceLE j k

def cofacialBad (e : Fin N) : Set E := by
  classical
  exact ⋃ j ∈ Finset.univ.filter (fun j => D.Cofacial e j ∧ ¬ D.faceLE e j), D.core j

def canonicalBad (e : Fin N) : Set E :=
  ((canonicalAffineFace (D.core e) : Set E) \ intrinsicInterior ℝ (D.core e)) ∪ D.cofacialBad e

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma cofacialBad_closed (e : Fin N) : IsClosed (D.cofacialBad e) := by
  classical
  apply isClosed_biUnion_finset
  intro j hj
  exact (M.compact _ (D.polytope_core j)).isClosed

lemma canonicalBad_closed (e : Fin N) : IsClosed (D.canonicalBad e) :=
  (isClosed_canonicalAffineFace_diff_intrinsicInterior (D.core e)).union (D.cofacialBad_closed e)

omit [FiniteDimensional ℝ E] in
lemma canonicalBad_complement (e : Fin N) :
    (canonicalAffineFace (D.core e) : Set E) \ D.core e ⊆ D.canonicalBad e := by
  intro p hp
  exact Or.inl ⟨hp.1, fun h => hp.2 (intrinsicInterior_subset h)⟩

omit [FiniteDimensional ℝ E] in
lemma core_subset_canonicalBad {e i j : Fin N}
    (hei : D.faceLE e i) (hji : D.faceLE j i) (hej : ¬ D.faceLE e j) :
    D.core j ⊆ D.canonicalBad e := by
  classical
  intro p hp
  apply Or.inr
  apply Set.mem_iUnion₂.mpr
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, hei, hji⟩, hej⟩, hp⟩

omit [FiniteDimensional ℝ E] in
lemma canonicalBad_eq_univ_of_empty {e : Fin N} (he : D.core e = ∅) :
    D.canonicalBad e = Set.univ := by
  classical
  have hne : ¬ (D.core e).Nonempty := by rw [he]; exact Set.not_nonempty_empty
  rw [canonicalBad, canonicalAffineFace, ite_eq_right hne, he, intrinsicInterior_empty, Set.sdiff_empty]
  change (Set.univ : Set E) ∪ D.cofacialBad e = Set.univ
  exact Set.univ_union _

end PolyhedralFaceData

namespace SimplicialFaceData

variable {D : PolyhedralFaceData M N} (T : SimplicialFaceData D)

/-- A genuine relative-interior simplex point avoids the complete canonical
bad set. The cofacial incidence assertion follows from barycentric independence. -/
theorem positive_point_not_canonicalBad {e : Fin N} {p : E}
    (hp : PositiveConvexCombination (T.vertices e) p) : p ∉ D.canonicalBad e := by
  have hpint : p ∈ intrinsicInterior ℝ (D.core e) := by
    rw [T.core_eq e]
    exact hp.intrinsicInterior
  intro hbad
  rcases hbad with hbase | hcofacial
  · exact hbase.2 hpint
  · classical
    obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp hcofacial
    obtain ⟨_, ⟨k, hek, hjk⟩, hej⟩ := Finset.mem_filter.mp hj
    exact hej (T.faceLE_of_positive_point hek hjk hp hpj)

end SimplicialFaceData

end BrehmApprox
