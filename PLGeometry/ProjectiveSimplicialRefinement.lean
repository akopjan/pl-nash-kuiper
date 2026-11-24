module

public import PLGeometry.ProjectiveVoronoiAtlas
public import PLGeometry.ChartedRefinement
public import BrehmApprox.SimplexStellar

/-!
# From a finite coordinate simplex family to a geodesic refinement

The input consists of actual source vertices and their finite affine hulls
in a projective atlas. Independence, coverage, and common-face intersections
construct every chart and topology field of the refined complex.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry

universe u v w

local instance projectiveSimplicialRefinementDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : ProjectiveVoronoiAtlas T E) (I : Type w)

/-- A finite geometric family in the common projective coordinates. -/
structure ProjectiveSimplexFamily where
  vertices : I → Finset P
  independent : ∀ i, AffineIndependent ℝ ((↑) : (vertices i).image A.coord → E)
  cover : ∀ x : P, ∃ i, A.coord x ∈ convexHull ℝ ((vertices i).image A.coord : Set E)
  intersection : ∀ i j,
    convexHull ℝ ((vertices i).image A.coord : Set E) ∩
      convexHull ℝ ((vertices j).image A.coord : Set E) =
      convexHull ℝ (((vertices i ∩ vertices j).image A.coord) : Set E)
  oldCell : ∀ i, ∃ σ ∈ T.simplices, (vertices i : Set P) ⊆ T.cell σ

namespace ProjectiveSimplexFamily

variable {A I} (F : ProjectiveSimplexFamily A I)

def simplices : Set (Finset P) := {σ | ∃ i, σ ⊆ F.vertices i}

theorem finite_simplices [Finite I] : F.simplices.Finite := by
  have he : F.simplices = ⋃ i, ((F.vertices i).powerset : Set (Finset P)) := by
    ext σ
    simp only [simplices, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe, Finset.mem_powerset]
  rw [he]
  exact Set.finite_iUnion (fun i => (F.vertices i).powerset.finite_toSet)

def cell (_F : ProjectiveSimplexFamily A I) (σ : Finset P) : Set P :=
  A.coord ⁻¹' convexHull ℝ (σ.image A.coord : Set E)

def oldFace (σ : Finset P) : Finset P :=
  if hσ : σ ∈ F.simplices then (F.oldCell hσ.choose).choose else ∅

theorem oldFace_spec {σ : Finset P} (hσ : σ ∈ F.simplices) :
    F.oldFace σ ∈ T.simplices ∧ (σ : Set P) ⊆ T.cell (F.oldFace σ) := by
  rw [oldFace, dite_eq_left hσ]
  exact ⟨(F.oldCell hσ.choose).choose_spec.1,
    (Finset.coe_subset.mpr hσ.choose_spec).trans (F.oldCell hσ.choose).choose_spec.2⟩

def chart (σ : Finset P) : P → Model κ n := T.chart (F.oldFace σ)

theorem cell_subset_old {σ : Finset P} (hσ : σ ∈ F.simplices) :
    F.cell σ ⊆ T.cell (F.oldFace σ) := by
  intro x hx
  have hm : A.coord x ∈ A.coord '' T.cell (F.oldFace σ) := by
    apply convexHull_min ?_ (A.cell_polytope _ (F.oldFace_spec hσ).1).convex hx
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨y, (F.oldFace_spec hσ).2 hy, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hm
  exact (A.injective hyx) ▸ hy

theorem cell_mono {σ τ : Finset P} (hτσ : τ ⊆ σ) : F.cell τ ⊆ F.cell σ :=
  Set.preimage_mono (convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image hτσ)))

theorem closed_cell (σ : Finset P) : IsClosed (F.cell σ) :=
  ((σ.image A.coord).finite_toSet.isClosed_convexHull (𝕜 := ℝ)).preimage A.continuous

theorem compact_cell (σ : Finset P) : IsCompact (F.cell σ) := by
  let : CompactSpace P := T.compactSpace
  exact (F.closed_cell σ).isCompact

theorem vertices_mem (σ : Finset P) {x : P} (hx : x ∈ σ) : x ∈ F.cell σ :=
  subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

theorem simplex_independent {σ : Finset P} (hσ : σ ∈ F.simplices) :
    AffineIndependent ℝ ((↑) : σ.image A.coord → E) := by
  obtain ⟨i, hi⟩ := hσ
  exact (F.independent i).mono (Finset.coe_subset.mpr (Finset.image_subset_image hi))

theorem simplex {σ : Finset P} (hσ : σ ∈ F.simplices) :
    simplexVertices κ n (σ.image (F.chart σ)) :=
  A.simplex_transfer _ (F.oldFace_spec hσ).1 σ (F.oldFace_spec hσ).2 (F.simplex_independent hσ)

theorem image_cell {σ : Finset P} (hσ : σ ∈ F.simplices) :
    F.chart σ '' F.cell σ = hull κ n (σ.image (F.chart σ)) :=
  A.hull_transfer _ (F.oldFace_spec hσ).1 σ (F.oldFace_spec hσ).2

theorem chart_injectiveOn {σ : Finset P} (hσ : σ ∈ F.simplices) :
    Set.InjOn (F.chart σ) (F.cell σ) :=
  (T.chart_injectiveOn _ (F.oldFace_spec hσ).1).mono (F.cell_subset_old hσ)

theorem chart_continuousOn {σ : Finset P} (hσ : σ ∈ F.simplices) :
    ContinuousOn (F.chart σ) (F.cell σ) :=
  (T.chart_continuousOn _ (F.oldFace_spec hσ).1).mono (F.cell_subset_old hσ)

def cellMap (σ : Finset P) (hσ : σ ∈ F.simplices) :
    F.cell σ → hull κ n (σ.image (F.chart σ)) := fun x =>
  ⟨F.chart σ x.val, by rw [← F.image_cell hσ]; exact ⟨x.val, x.property, rfl⟩⟩

theorem cellMap_bijective (σ : Finset P) (hσ : σ ∈ F.simplices) :
    Function.Bijective (F.cellMap σ hσ) := by
  constructor
  · intro x y h
    exact Subtype.ext (F.chart_injectiveOn hσ x.property y.property (congrArg Subtype.val h))
  · intro y
    have hy : y.val ∈ F.chart σ '' F.cell σ :=
      Eq.mpr (congrArg (fun U : Set (Model κ n) => y.val ∈ U) (F.image_cell hσ)) y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

def cellHomeomorph (σ : Finset P) (hσ : σ ∈ F.simplices) :
    F.cell σ ≃ₜ hull κ n (σ.image (F.chart σ)) := by
  let : CompactSpace (F.cell σ) := isCompact_iff_compactSpace.mp (F.compact_cell σ)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (F.cellMap σ hσ) (F.cellMap_bijective σ hσ))
    ((F.chart_continuousOn hσ).domRestrict.subtype_mk _)

theorem cellHomeomorph_apply (σ : Finset P) (hσ : σ ∈ F.simplices)
    (x : F.cell σ) : (F.cellHomeomorph σ hσ x).val = F.chart σ x.val := rfl

theorem faces {σ τ : Finset P} (hσ : σ ∈ F.simplices) (hτσ : τ ⊆ σ) :
    τ ∈ F.simplices := ⟨hσ.choose, hτσ.trans hσ.choose_spec⟩

theorem image_face {σ τ : Finset P} (hσ : σ ∈ F.simplices) (hτσ : τ ⊆ σ) :
    F.chart σ '' F.cell τ = hull κ n (τ.image (F.chart σ)) :=
  A.hull_transfer _ (F.oldFace_spec hσ).1 τ
    ((Finset.coe_subset.mpr hτσ).trans (F.oldFace_spec hσ).2)

theorem cell_intersection {σ τ : Finset P} (hσ : σ ∈ F.simplices) (hτ : τ ∈ F.simplices) :
    F.cell σ ∩ F.cell τ = F.cell (σ ∩ τ) := by
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨j, hj⟩ := hτ
  have hmax := F.intersection i j
  have hemax : (F.vertices i ∩ F.vertices j).image A.coord =
      (F.vertices i).image A.coord ∩ (F.vertices j).image A.coord :=
    Finset.image_inter _ _ A.injective
  rw [hemax] at hmax
  have hh := convexHull_subfaces_intersection (F.independent i) (F.independent j) hmax
    (Finset.image_subset_image hi) (Finset.image_subset_image hj)
  have he : (σ ∩ τ).image A.coord = σ.image A.coord ∩ τ.image A.coord :=
    Finset.image_inter _ _ A.injective
  ext x
  change (A.coord x ∈ convexHull ℝ (σ.image A.coord : Set E) ∧
    A.coord x ∈ convexHull ℝ (τ.image A.coord : Set E)) ↔
      A.coord x ∈ convexHull ℝ ((σ ∩ τ).image A.coord : Set E)
  rw [he, ← hh]
  rfl

theorem metric_coherence {σ τ : Finset P} (hσ : σ ∈ F.simplices) (hτ : τ ∈ F.simplices)
    {x y : P} (hx : x ∈ F.cell σ ∩ F.cell τ) (hy : y ∈ F.cell σ ∩ F.cell τ) :
    dist (F.chart σ x) (F.chart σ y) = dist (F.chart τ x) (F.chart τ y) :=
  T.metric_coherence _ (F.oldFace_spec hσ).1 _ (F.oldFace_spec hτ).1 _
    ⟨F.cell_subset_old hσ hx.1, F.cell_subset_old hτ hx.2⟩ _
    ⟨F.cell_subset_old hσ hy.1, F.cell_subset_old hτ hy.2⟩

/-- Every finite compatible coordinate family is an actual geodesic refinement. -/
def toChartedComplex [Finite I] : FiniteChartedComplex κ n P where
  simplices := F.simplices
  finite_simplices := F.finite_simplices
  cell := F.cell
  chart := F.chart
  cover x := by
    obtain ⟨i, hi⟩ := F.cover x
    exact ⟨F.vertices i, ⟨i, Finset.Subset.refl _⟩, hi⟩
  vertices_mem := fun σ _ _ hx => F.vertices_mem σ hx
  simplex := fun _ hσ => F.simplex hσ
  image_cell := fun _ hσ => F.image_cell hσ
  cellHomeomorph := F.cellHomeomorph
  cellHomeomorph_apply := F.cellHomeomorph_apply
  faces := fun _ hσ _ hτσ => F.faces hσ hτσ
  image_face := fun _ hσ _ hτσ => F.image_face hσ hτσ
  intersection := fun _ hσ _ hτ => F.cell_intersection hσ hτ
  metric_coherence := fun _ hσ _ hτ _ hx _ hy => F.metric_coherence hσ hτ hx hy

theorem refines [Finite I] : F.toChartedComplex.Refines T := by
  constructor
  intro σ hσ
  exact ⟨F.oldFace σ, (F.oldFace_spec hσ).1, F.cell_subset_old hσ,
    fun _ _ _ _ => rfl⟩

end ProjectiveSimplexFamily

end ArchivePLGeometry
