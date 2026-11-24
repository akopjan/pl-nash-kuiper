module

public import PLGeometry.Basic

/-!
# Finite charted complexes

This auxiliary category retains the actual geodesic metric on each simplex
and its compatibility on common faces, without requiring a global source
metric. Links and angular quotient complexes naturally belong here. A
metric triangulation is a particular charted complex.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u

local instance chartedComplexLocalInstance1 (α : Type*) : DecidableEq α := Classical.decEq α

structure FiniteChartedComplex (κ : Geometry) (n : ℕ) (P : Type u)
    [TopologicalSpace P] [T2Space P] where
  simplices : Set (Finset P)
  finite_simplices : simplices.Finite
  cell : Finset P → Set P
  chart : Finset P → P → Model κ n
  cover : ∀ x : P, ∃ σ ∈ simplices, x ∈ cell σ
  vertices_mem : ∀ σ ∈ simplices, (σ : Set P) ⊆ cell σ
  simplex : ∀ σ ∈ simplices, simplexVertices κ n (σ.image (chart σ))
  image_cell : ∀ σ ∈ simplices, chart σ '' cell σ = hull κ n (σ.image (chart σ))
  cellHomeomorph : ∀ σ, ∀ hσ : σ ∈ simplices,
    cell σ ≃ₜ hull κ n (σ.image (chart σ))
  cellHomeomorph_apply : ∀ σ, ∀ hσ : σ ∈ simplices, ∀ x : cell σ,
    (cellHomeomorph σ hσ x : Model κ n) = chart σ x
  faces : ∀ σ ∈ simplices, ∀ τ ⊆ σ, τ ∈ simplices
  image_face : ∀ σ ∈ simplices, ∀ τ ⊆ σ,
    chart σ '' cell τ = hull κ n (τ.image (chart σ))
  intersection : ∀ σ ∈ simplices, ∀ τ ∈ simplices, cell σ ∩ cell τ = cell (σ ∩ τ)
  metric_coherence : ∀ σ ∈ simplices, ∀ τ ∈ simplices,
    ∀ x ∈ cell σ ∩ cell τ, ∀ y ∈ cell σ ∩ cell τ,
      dist (chart σ x) (chart σ y) = dist (chart τ x) (chart τ y)

namespace FiniteChartedComplex

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

theorem compact_cell (σ : Finset P) (hσ : σ ∈ T.simplices) : IsCompact (T.cell σ) := by
  let : CompactSpace (hull κ n (σ.image (T.chart σ))) :=
    isCompact_iff_compactSpace.mp (compact_hull κ n _ (T.simplex σ hσ))
  exact isCompact_iff_compactSpace.mpr (T.cellHomeomorph σ hσ).symm.compactSpace

theorem closed_cell (σ : Finset P) (hσ : σ ∈ T.simplices) : IsClosed (T.cell σ) :=
  (T.compact_cell σ hσ).isClosed

include T in
theorem compactSpace : CompactSpace P := by
  have hc := T.finite_simplices.isCompact_biUnion (fun σ hσ => T.compact_cell σ hσ)
  have he : (⋃ σ ∈ T.simplices, T.cell σ) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨σ, hσ, hx⟩ := T.cover x
    exact ⟨σ, hσ, hx⟩
  exact isCompact_univ_iff.mp (he ▸ hc)

theorem chart_injectiveOn (σ : Finset P) (hσ : σ ∈ T.simplices) :
    Set.InjOn (T.chart σ) (T.cell σ) := by
  intro x hx y hy hxy
  have he : T.cellHomeomorph σ hσ ⟨x, hx⟩ = T.cellHomeomorph σ hσ ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa only [T.cellHomeomorph_apply] using hxy
  exact congrArg Subtype.val ((T.cellHomeomorph σ hσ).injective he)

theorem chart_continuousOn (σ : Finset P) (hσ : σ ∈ T.simplices) :
    ContinuousOn (T.chart σ) (T.cell σ) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (T.cell σ).domRestrict (T.chart σ) =
      fun x => (T.cellHomeomorph σ hσ x : Model κ n) := by
    funext x
    exact (T.cellHomeomorph_apply σ hσ x).symm
  rw [he]
  exact continuous_subtype_val.comp (T.cellHomeomorph σ hσ).continuous

theorem cell_mono {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτσ : τ ⊆ σ) :
    T.cell τ ⊆ T.cell σ := by
  have ht := T.faces σ hσ τ hτσ
  have he := T.intersection τ ht σ hσ
  rw [Finset.inter_eq_left.mpr hτσ] at he
  exact Set.inter_eq_left.mp he

end FiniteChartedComplex

namespace Triangulation

variable {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]
    (T : Triangulation κ n P)

def toFiniteChartedComplex (hfin : T.simplices.Finite) : FiniteChartedComplex κ n P where
  simplices := T.simplices
  finite_simplices := hfin
  cell := T.cell
  chart := T.chart
  cover := T.cover
  vertices_mem := T.vertices_mem
  simplex := T.simplex
  image_cell := T.image_cell
  cellHomeomorph σ hσ := (T.cellChart σ hσ).toHomeomorph
  cellHomeomorph_apply σ hσ x := T.cellChart_apply σ hσ x
  faces := T.faces
  image_face := T.image_face
  intersection := T.intersection
  metric_coherence := by
    intro σ hσ τ hτ x hx y hy
    rw [T.isometry_cell σ hσ x hx.1 y hy.1, T.isometry_cell τ hτ x hx.2 y hy.2]

end Triangulation

namespace FiniteChartedComplex

variable {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]
    (T : FiniteChartedComplex κ n P)

def toTriangulation
    (hmetric : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (T.chart σ x) (T.chart σ y) = dist x y) : Triangulation κ n P where
  simplices := T.simplices
  cell := T.cell
  chart := T.chart
  cover := T.cover
  locallyFinite := by
    letI : Finite T.simplices := T.finite_simplices.to_subtype
    exact locallyFinite_of_finite _
  vertices_mem := T.vertices_mem
  simplex := T.simplex
  image_cell := T.image_cell
  isometry_cell := hmetric
  faces := T.faces
  image_face := T.image_face
  intersection := T.intersection

end FiniteChartedComplex

end ArchivePLGeometry
