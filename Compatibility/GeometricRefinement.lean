module

public import Compatibility.SourceAtlas
public import Compatibility.GeometricRealization
public import PLGeometry.ChartedRefinement

/-! Finite charted refinements preserve the original geometric PL structure.
The original chart axiom applies to every finite subset of a cell, including
the new vertices, so no affine parametrization of the old chart is assumed. -/

@[expose] public section
noncomputable section

namespace PLGeometry.Polyhedron

open Set

variable {κ : Geometry} {d m : ℕ} (K : Polyhedron κ d m)

local instance geometricRefinementDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem sourceCell_subset_of_vertices {σ τ : Finset ↥K.K.space}
    (hτ : τ ∈ K.sourceFaces) (hσ : (σ : Set ↥K.K.space) ⊆ K.sourceCell τ) :
    K.sourceCell σ ⊆ K.sourceCell τ := by
  intro x hx
  apply convexHull_min ?_ (convex_convexHull ℝ _) hx
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  exact hσ hz

theorem sourceChart_image_geometric_hull {τ : Finset ↥K.K.space}
    (hτ : τ ∈ K.sourceFaces) (σ : Finset ↥K.K.space)
    (hσ : (σ : Set ↥K.K.space) ⊆ K.sourceCell τ) :
    K.sourceChart τ '' K.sourceCell σ =
      ArchivePLGeometry.hull κ.toArchive d (σ.image (K.sourceChart τ)) := by
  rcases hτ with rfl | hτ
  · have hσe : σ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := hσ hx
      rw [K.sourceCell_empty] at h
      exact h
    subst σ
    simp only [K.sourceCell_empty, Set.image_empty, Finset.image_empty,
      ArchivePLGeometry.hull_empty]
  have hverts : (σ.image Subtype.val : Set (E m)) ⊆ cell (τ.image Subtype.val) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hσ hx
  have hc : cell (σ.image Subtype.val) ⊆ cell (τ.image Subtype.val) :=
    convexHull_min hverts (convex_convexHull ℝ _)
  have hspace : cell (σ.image Subtype.val) ⊆ K.K.space :=
    hc.trans (K.K.convexHull_subset_space hτ)
  let f : E m → ArchivePLGeometry.Model κ.toArchive d :=
    fun x => modelEquiv κ d ((K.simplex _ hτ).toModel x)
  have him : K.sourceChart τ '' K.sourceCell σ =
      f '' cell (σ.image Subtype.val) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, (K.sourceChart_of_mem hτ x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hspace hx⟩, hx, K.sourceChart_of_mem hτ _⟩
  rw [him]
  dsimp only [f, cell]
  rw [(K.simplex _ hτ).archive_image_hull _ hverts]
  congr 1
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact (K.sourceChart_of_mem hτ x).symm

theorem sourceCell_image (σ : Finset ↥K.K.space)
    (hσ : cell (σ.image Subtype.val) ⊆ K.K.space) :
    Subtype.val '' K.sourceCell σ = cell (σ.image Subtype.val) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hσ hx⟩, hx, rfl⟩

/-- Each refined charted simplex is exactly the convex hull of its actual
source vertices in the original Euclidean ambient space. -/
theorem refinement_cell_geometric
    (T : ArchivePLGeometry.FiniteChartedComplex κ.toArchive d ↥K.K.space)
    (hfaces : T.simplices = K.sourceFaces)
    (hcell : T.cell = K.sourceCell)
    (hchart : T.chart = K.sourceChart)
    (U : ArchivePLGeometry.FiniteChartedComplex κ.toArchive d ↥K.K.space)
    (hU : U.Refines T) (σ : Finset ↥K.K.space) (hσ : σ ∈ U.simplices) :
    Subtype.val '' U.cell σ = cell (σ.image Subtype.val) := by
  obtain ⟨τ, hτ, hsub, hmetric⟩ := hU.cell σ hσ
  rw [hfaces] at hτ
  rw [hcell] at hsub
  rw [hchart] at hmetric
  have hverts : (σ : Set ↥K.K.space) ⊆ K.sourceCell τ :=
    (U.vertices_mem σ hσ).trans hsub
  have hconv := K.sourceCell_subset_of_vertices hτ hverts
  have him := (U.folding_cell_geometry σ hσ (K.sourceChart τ)
    (fun x hx y hy => (hmetric x hx y hy).symm)).2
  have himages : K.sourceChart τ '' U.cell σ = K.sourceChart τ '' K.sourceCell σ := by
    rw [him, K.sourceChart_image_geometric_hull hτ σ hverts]
  have heq : U.cell σ = K.sourceCell σ := by
    ext x
    constructor
    · intro hx
      have hi : K.sourceChart τ x ∈ K.sourceChart τ '' U.cell σ := ⟨x, hx, rfl⟩
      rw [himages] at hi
      obtain ⟨y, hy, he⟩ := hi
      exact (K.sourceChart_injective hτ (hconv hy) (hsub hx) he) ▸ hy
    · intro hx
      have hi : K.sourceChart τ x ∈ K.sourceChart τ '' K.sourceCell σ := ⟨x, hx, rfl⟩
      rw [← himages] at hi
      obtain ⟨y, hy, he⟩ := hi
      exact (K.sourceChart_injective hτ (hsub hy) (hconv hx) he) ▸ hy
  rw [heq]
  apply K.sourceCell_image
  rcases hτ with rfl | hτ
  · have hσe : σ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := hverts hx
      rw [K.sourceCell_empty] at h
      exact h
    simp [hσe, cell]
  · exact (convexHull_min (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hverts hy) (convex_convexHull ℝ _)).trans
        (K.K.convexHull_subset_space hτ)

/-- A genuine finite charted refinement gives exactly the old Challenge's
geometric subdivision, with its original simplex metric on each new face. -/
theorem plIsometry_of_charted_refinement {r : ℕ}
    (T : ArchivePLGeometry.FiniteChartedComplex κ.toArchive d ↥K.K.space)
    (hfaces : T.simplices = K.sourceFaces)
    (hcell : T.cell = K.sourceCell)
    (hchart : T.chart = K.sourceChart)
    (U : ArchivePLGeometry.FiniteChartedComplex κ.toArchive d ↥K.K.space)
    (hU : U.Refines T) (g : ↥K.K.space → Model κ r)
    (hg : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      modelDist κ r (g x) (g y) = dist (U.chart σ x) (U.chart σ y)) :
    PLIsometry K g := by
  have hgeo := K.refinement_cell_geometric T hfaces hcell hchart U hU
  have hhull : ∀ σ ∈ U.simplices,
      Subtype.val '' U.cell σ = convexHull ℝ (Subtype.val '' (σ : Set ↥K.K.space)) := by
    intro σ hσ
    simpa only [cell, Finset.coe_image] using hgeo σ hσ
  let C := ChartedRealization.complex U Subtype.val Subtype.val_injective hhull
  have hspace : C.space = K.K.space := by
    rw [ChartedRealization.complex_space]
    exact Subtype.range_coe_subtype
  refine ⟨C, ChartedRealization.complex_finite U Subtype.val Subtype.val_injective hhull,
    hspace, ?_⟩
  intro σ hσ
  obtain ⟨V, hV, rfl⟩ := ChartedRealization.face_origin U Subtype.val
    Subtype.val_injective hhull hσ
  obtain ⟨τ, hτ, hsub, hmetric⟩ := hU.cell V hV
  rw [hfaces] at hτ
  rw [hcell] at hsub
  rw [hchart] at hmetric
  have hτold : τ.image Subtype.val ∈ K.K.faces := by
    rcases hτ with rfl | hτ
    · have hVe : V = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have h := hsub (U.vertices_mem V hV hx)
        rw [K.sourceCell_empty] at h
        exact h
      have hne := C.nonempty_of_mem_faces hσ
      simpa [hVe] using hne
    · exact hτ
  have hmem (x : ↥K.K.space) (hx : x.val ∈ cell (V.image Subtype.val)) :
      x ∈ U.cell V := by
    rw [← hgeo V hV] at hx
    obtain ⟨y, hy, heq⟩ := hx
    exact Subtype.val_injective heq ▸ hy
  refine ⟨τ.image Subtype.val, hτold, ?_, ?_⟩
  · intro x hx
    rw [← hgeo V hV] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hsub hy
  · intro x y hx hy
    have hxU := hmem x hx
    have hyU := hmem y hy
    rw [hg V hV x hxU y hyU, hmetric x hxU y hyU,
      K.sourceChart_of_mem hτold, K.sourceChart_of_mem hτold, modelEquiv_dist]

end PLGeometry.Polyhedron
