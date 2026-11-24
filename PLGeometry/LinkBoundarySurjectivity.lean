module

public import PLGeometry.LinkBoundaryInclusion

/-! # Every old face avoiding the center is represented in the stellar link -/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance linkBoundarySurjectivityDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance linkBoundarySurjectivityVertexEq : DecidableEq T.Vertex := Classical.decEq _
local instance linkBoundarySurjectivityLabelEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem vertex_mem_link_of_face {p : P} {σ U : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hUσ : U ⊆ σ) (hpU : p ∉ T.cell U)
    {v : P} (hv : v ∈ U) : v ∈ T.linkVertexSet p := by
  refine ⟨?_, σ, hσ, hpσ, hUσ hv⟩
  intro he
  apply hpU
  exact he ▸ T.vertices_mem U (T.faces σ hσ U hUσ) hv

theorem linkSourceVertices_linkLabels_of_face {p : P} {σ U : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) (hUσ : U ⊆ σ) (hpU : p ∉ T.cell U) :
    T.linkSourceVertices (T.linkLabels p U) = U := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := T.mem_linkSourceVertices.mp hv
    exact (T.mem_linkLabels p U i).mp hi
  · intro hv
    let i : T.LinkVertex p := ⟨v, T.vertex_mem_link_of_face hσ hpσ hUσ hpU hv⟩
    exact T.mem_linkSourceVertices.mpr ⟨i, (T.mem_linkLabels p U i).mpr hv, rfl⟩

theorem linkLabels_face_of_face {p : P} {σ U : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) (hUσ : U ⊆ σ) (hpU : p ∉ T.cell U) :
    T.linkLabels p U ∈ (T.linkComplex p).faces := by
  refine ⟨σ, hσ, hpσ, ?_, ?_⟩
  · rw [T.linkSourceVertices_linkLabels_of_face hσ hpσ hUσ hpU]
    exact hUσ
  · rw [T.linkSourceVertices_linkLabels_of_face hσ hpσ hUσ hpU]
    exact hpU

/-- The source inclusion maps the corresponding link region onto every old
face avoiding the stellar center. -/
theorem exists_linkBoundaryInclusion_of_face {p : P} {σ U : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) (hUσ : U ⊆ σ) (hpU : p ∉ T.cell U)
    {z : P} (hz : z ∈ T.cell U) :
    ∃ x ∈ T.linkRegion p U, T.linkBoundaryInclusion p x = z := by
  have hU := T.faces σ hσ U hUσ
  let w : T.LinkVertex p → ℝ := fun i => T.barycentricCoords z (T.linkVertexEmbedding p i)
  have hw0 (i : T.LinkVertex p) : 0 ≤ w i := T.barycentricCoords_nonneg z _
  have hwzero (i : T.LinkVertex p) (hi : i ∉ T.linkLabels p U) : w i = 0 := by
    apply T.barycentricCoords_zero_of_not_mem hU hz
    intro hv
    exact hi ((T.mem_linkLabels p U i).mpr hv)
  have he : T.linkCoordinates p w = T.barycentricCoords z := by
    funext v
    by_cases hv : v.val ∈ U
    · let i : T.LinkVertex p := ⟨v.val, T.vertex_mem_link_of_face hσ hpσ hUσ hpU hv⟩
      have hev : T.linkVertexEmbedding p i = v := Subtype.ext rfl
      rw [← hev, T.linkCoordinates_apply]
    · have hzv := T.barycentricCoords_zero_of_not_mem hU hz v hv
      rw [hzv]
      unfold linkCoordinates
      rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hvi : v = T.linkVertexEmbedding p i
      · subst v
        rw [Pi.single_eq_same]
        exact T.barycentricCoords_zero_of_not_mem hU hz _ hv
      · exact Pi.single_eq_of_ne hvi _
  have hw : w ∈ Barycentric.weightsOn (T.linkLabels p U) := by
    refine ⟨⟨hw0, ?_⟩, hwzero⟩
    rw [← T.linkCoordinates_sum p w, he]
    exact T.barycentricCoords_sum z
  let x : (T.linkComplex p).Space :=
    ⟨w, Set.mem_iUnion₂.mpr ⟨T.linkLabels p U,
      T.linkLabels_face_of_face hσ hpσ hUσ hpU, hw⟩⟩
  refine ⟨x, (T.mem_linkRegion_iff_weightsOn p U x).mpr hw, ?_⟩
  apply T.barycentricCoords_injective
  rw [T.barycentricCoords_linkBoundaryInclusion]
  exact he

end ArchivePLGeometry.FiniteChartedComplex
