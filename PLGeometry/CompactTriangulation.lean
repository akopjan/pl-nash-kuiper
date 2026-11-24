module

public import PLGeometry.FoldedFaceData
public import PLGeometry.IntrinsicRefinement

/-! # Finite triangulations and genuine folded data on compact sources -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]

/-- A locally finite triangulation of a compact source has finitely many simplices. -/
theorem Triangulation.finite_of_compact [CompactSpace P] (T : Triangulation κ n P) :
    T.simplices.Finite := by
  classical
  have h := T.locallyFinite.finite_nonempty_of_compact
  have hf := h.image (Subtype.val : T.simplices → Finset P)
  apply (hf.insert ∅).subset
  intro σ hσ
  by_cases hσ0 : σ = ∅
  · exact Or.inl hσ0
  · right
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hσ0
    exact ⟨⟨σ, hσ⟩, ⟨x, T.vertices_mem σ hσ hx⟩, rfl⟩

theorem PLIsometry.exists_finite_triangulation [CompactSpace P]
    {q : P → Model κ n} (hq : PLIsometry κ n q) :
    ∃ T : Triangulation κ n P, T.simplices.Finite ∧
      ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
        dist (q x) (q y) = dist x y := by
  obtain ⟨_, T, hiso⟩ := hq
  exact ⟨T, T.finite_of_compact, hiso⟩

theorem IsFinitePolyhedron.intrinsic_triangulation
    (hP : IsFinitePolyhedron κ n P) {κ' : Geometry} {m : ℕ}
    (U : Triangulation κ' m P) : Intrinsic U := by
  let : CompactSpace P := hP.compactSpace
  obtain ⟨T, _, hT⟩ := hP
  exact T.intrinsic_of_finite_triangulation hT U U.finite_of_compact

end ArchivePLGeometry
