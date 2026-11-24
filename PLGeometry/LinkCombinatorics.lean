module

public import PLGeometry.ChartedIncidence
public import PLGeometry.BarycentricRealization

/-!
# The finite abstract link at an arbitrary source point

Stellar link faces are old faces avoiding the center and contained in an
old coface incident to it. Vertices are the original vertices in that star,
with the center itself removed if it was already a vertex.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

local instance linkCombinatoricsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

def linkVertexSet (p : P) : Set P :=
  {v | v ≠ p ∧ ∃ σ ∈ T.simplices, p ∈ T.cell σ ∧ v ∈ σ}

theorem finite_linkVertexSet (p : P) : (T.linkVertexSet p).Finite := by
  apply T.finite_vertexSet.subset
  rintro v ⟨_, σ, hσ, _, hv⟩
  exact Set.mem_iUnion₂.mpr ⟨σ, hσ, hv⟩

abbrev LinkVertex (p : P) := T.linkVertexSet p

instance linkVertexFintype (p : P) : Fintype (T.LinkVertex p) :=
  (T.finite_linkVertexSet p).fintype

/-- Forget the link labels to their original source vertices. -/
def linkSourceVertices {p : P} (τ : Finset (T.LinkVertex p)) : Finset P :=
  τ.map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_linkSourceVertices {p : P} {τ : Finset (T.LinkVertex p)} {v : P} :
    v ∈ T.linkSourceVertices τ ↔ ∃ w ∈ τ, w.val = v := by
  simp only [linkSourceVertices, Finset.mem_map, Function.Embedding.coeFn_mk]

theorem linkSourceVertices_mono {p : P} {τ ν : Finset (T.LinkVertex p)} (h : τ ⊆ ν) :
    T.linkSourceVertices τ ⊆ T.linkSourceVertices ν := Finset.map_subset_map.mpr h

@[simp] theorem linkSourceVertices_singleton {p : P} (v : T.LinkVertex p) :
    T.linkSourceVertices {v} = {v.val} := by simp [linkSourceVertices]

theorem center_not_mem_linkSourceVertices {p : P} (τ : Finset (T.LinkVertex p)) :
    p ∉ T.linkSourceVertices τ := by
  intro hp
  obtain ⟨v, _, hv⟩ := T.mem_linkSourceVertices.mp hp
  exact v.property.1 hv

def linkFaces (p : P) : Set (Finset (T.LinkVertex p)) :=
  {τ | ∃ σ ∈ T.simplices, p ∈ T.cell σ ∧ T.linkSourceVertices τ ⊆ σ ∧
    p ∉ T.cell (T.linkSourceVertices τ)}

theorem linkFaces_downward {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) (ν : Finset (T.LinkVertex p)) (hντ : ν ⊆ τ) :
    ν ∈ T.linkFaces p := by
  obtain ⟨σ, hσ, hpσ, hτσ, hpτ⟩ := hτ
  have hsub := T.linkSourceVertices_mono hντ
  refine ⟨σ, hσ, hpσ, hsub.trans hτσ, ?_⟩
  exact fun hpν => hpτ (T.cell_mono (T.faces σ hσ _ hτσ) hsub hpν)

theorem linkFaces_singleton {p : P} (v : T.LinkVertex p) :
    ({v} : Finset (T.LinkVertex p)) ∈ T.linkFaces p := by
  obtain ⟨hvp, σ, hσ, hpσ, hvσ⟩ := v.property
  refine ⟨σ, hσ, hpσ, ?_, ?_⟩
  · rw [T.linkSourceVertices_singleton]
    exact Finset.singleton_subset_iff.mpr hvσ
  · rw [T.linkSourceVertices_singleton,
      T.cell_singleton (T.faces σ hσ {v.val} (Finset.singleton_subset_iff.mpr hvσ))]
    exact fun hpv => hvp hpv.symm

def linkComplex (p : P) : Barycentric.Complex (T.LinkVertex p) where
  faces := T.linkFaces p
  downward := by intro τ hτ ν hντ; exact T.linkFaces_downward hτ ν hντ
  singleton := T.linkFaces_singleton

/-- Choose an incident old coface for each link face. Geometry on different
choices will be identified by the original metric coherence. -/
def linkCoface (p : P) (τ : Finset (T.LinkVertex p)) : Finset P := by
  classical
  exact if h : τ ∈ T.linkFaces p then h.choose else ∅

theorem linkCoface_spec {p : P} {τ : Finset (T.LinkVertex p)} (hτ : τ ∈ T.linkFaces p) :
    T.linkCoface p τ ∈ T.simplices ∧ p ∈ T.cell (T.linkCoface p τ) ∧
      T.linkSourceVertices τ ⊆ T.linkCoface p τ ∧
      p ∉ T.cell (T.linkSourceVertices τ) := by
  simp only [linkCoface, dite_eq_left hτ]
  exact hτ.choose_spec

theorem linkSourceVertices_mem {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) : T.linkSourceVertices τ ∈ T.simplices := by
  obtain ⟨σ, hσ, _, hsub, _⟩ := hτ
  exact T.faces σ hσ _ hsub

/-- Every link face has fewer vertices than an incident source coface. -/
theorem linkFace_card_lt {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) : τ.card < (T.linkCoface p τ).card := by
  obtain ⟨_, hpσ, hsub, hpτ⟩ := T.linkCoface_spec hτ
  have hne : T.linkSourceVertices τ ≠ T.linkCoface p τ := by
    intro he
    exact hpτ (he ▸ hpσ)
  have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  simpa only [linkSourceVertices, Finset.card_map] using hcard

end ArchivePLGeometry.FiniteChartedComplex
