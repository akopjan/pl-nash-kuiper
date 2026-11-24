module

public import PLGeometry.LinkCombinatorics
public import PLGeometry.BarycentricSupport

/-! # The part of a link contained in an old source cell -/

@[expose] public section
noncomputable section

open Set

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance linkRegionsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance linkRegionsVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def linkRegion (p : P) (σ : Finset P) : Set (T.linkComplex p).Space :=
  {x | T.linkSourceVertices ((T.linkComplex p).support x) ⊆ σ}

def linkLabels (p : P) (σ : Finset P) : Finset (T.LinkVertex p) :=
  Finset.univ.filter fun v => v.val ∈ σ

@[simp] theorem mem_linkLabels (p : P) (σ : Finset P) (v : T.LinkVertex p) :
    v ∈ T.linkLabels p σ ↔ v.val ∈ σ := by simp only [linkLabels, Finset.mem_filter,
      Finset.mem_univ, true_and]

theorem linkSourceVertices_subset_iff {p : P} (τ : Finset (T.LinkVertex p)) (σ : Finset P) :
    T.linkSourceVertices τ ⊆ σ ↔ τ ⊆ T.linkLabels p σ := by
  constructor
  · intro h v hv
    exact (T.mem_linkLabels p σ v).mpr (h (T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩))
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := T.mem_linkSourceVertices.mp hv
    exact (T.mem_linkLabels p σ w).mp (h hw)

theorem mem_linkRegion_iff_weightsOn (p : P) (σ : Finset P) (x : (T.linkComplex p).Space) :
    x ∈ T.linkRegion p σ ↔ x.val ∈ Barycentric.weightsOn (T.linkLabels p σ) := by
  change T.linkSourceVertices ((T.linkComplex p).support x) ⊆ σ ↔ _
  rw [T.linkSourceVertices_subset_iff, (T.linkComplex p).mem_weightsOn_iff_support_subset]

theorem isClosed_linkRegion (p : P) (σ : Finset P) : IsClosed (T.linkRegion p σ) := by
  have he : T.linkRegion p σ =
      (Subtype.val : (T.linkComplex p).Space → _) ⁻¹' Barycentric.weightsOn (T.linkLabels p σ) := by
    ext x
    exact T.mem_linkRegion_iff_weightsOn p σ x
  rw [he]
  exact (Barycentric.isClosed_weightsOn _).preimage continuous_subtype_val

theorem link_cell_subset_region {p : P} {τ : Finset (T.LinkVertex p)} {σ : Finset P}
    (hsub : T.linkSourceVertices τ ⊆ σ) :
    (T.linkComplex p).cell ((T.linkComplex p).vertices τ) ⊆ T.linkRegion p σ := by
  intro x hx
  exact (T.linkSourceVertices_mono
    (((T.linkComplex p).mem_cell_vertices_iff_support_subset x τ).mp hx)).trans hsub

theorem linkRegion_eq_union_cells (p : P) (σ : Finset P) :
    T.linkRegion p σ = ⋃ τ ∈ T.linkFaces p, ⋃ (_ : T.linkSourceVertices τ ⊆ σ),
      (T.linkComplex p).cell ((T.linkComplex p).vertices τ) := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion₂.mpr ⟨(T.linkComplex p).support x,
      (T.linkComplex p).support_mem x, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hx, ?_⟩
    exact ((T.linkComplex p).mem_cell_vertices_iff_support_subset x _).mpr (fun _ h => h)
  · intro hx
    obtain ⟨τ, hτ, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hsub, hx⟩ := Set.mem_iUnion.mp hx
    exact T.link_cell_subset_region hsub hx

end ArchivePLGeometry.FiniteChartedComplex
