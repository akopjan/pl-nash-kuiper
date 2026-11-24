module

public import PLGeometry.LinkRegions

/-! # The finite cells of an old-simplex angular region -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance linkRegionCellsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def linkRegionPieces (p : P) (σ : Finset P) : Finset (Finset (T.linkComplex p).Space) := by
  classical
  exact (Finset.univ.filter fun τ : Finset (T.LinkVertex p) =>
    τ ∈ T.linkFaces p ∧ T.linkSourceVertices τ ⊆ σ).image (T.linkComplex p).vertices

theorem mem_linkRegionPieces {p : P} {σ : Finset P} {S : Finset (T.linkComplex p).Space} :
    S ∈ T.linkRegionPieces p σ ↔
      ∃ τ ∈ T.linkFaces p, T.linkSourceVertices τ ⊆ σ ∧ (T.linkComplex p).vertices τ = S := by
  classical
  simp only [linkRegionPieces, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  aesop

theorem linkRegionPieces_valid {p : P} {σ : Finset P} {S : Finset (T.linkComplex p).Space}
    (hS : S ∈ T.linkRegionPieces p σ) : S ∈ (T.linkComplex p).simplices := by
  obtain ⟨τ, hτ, _, rfl⟩ := T.mem_linkRegionPieces.mp hS
  exact ⟨τ, hτ, rfl⟩

theorem linkRegionPieces_contained {p : P} {σ : Finset P} {S : Finset (T.linkComplex p).Space}
    (hS : S ∈ T.linkRegionPieces p σ) : (T.linkComplex p).cell S ⊆ T.linkRegion p σ := by
  obtain ⟨τ, _, hsub, rfl⟩ := T.mem_linkRegionPieces.mp hS
  exact T.link_cell_subset_region hsub

theorem linkRegionPieces_cover {p : P} {σ : Finset P} {x : (T.linkComplex p).Space}
    (hx : x ∈ T.linkRegion p σ) :
    ∃ S ∈ T.linkRegionPieces p σ, x ∈ (T.linkComplex p).cell S := by
  refine ⟨(T.linkComplex p).vertices ((T.linkComplex p).support x), ?_, ?_⟩
  · exact T.mem_linkRegionPieces.mpr ⟨_, (T.linkComplex p).support_mem x, hx, rfl⟩
  · exact ((T.linkComplex p).mem_cell_vertices_iff_support_subset x _).mpr (fun _ h => h)

end ArchivePLGeometry.FiniteChartedComplex
