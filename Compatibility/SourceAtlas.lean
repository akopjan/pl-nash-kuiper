module

public import Compatibility.ModelHemisphere
public import Compatibility.SourceVertices
public import PLGeometry.ChartedIncidence

/-! The original embedded polyhedron as a finite charted complex. -/

@[expose] public section
noncomputable section

namespace PLGeometry

open Set

local instance sourceAtlasDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def archiveBasepoint (κ : Geometry) (d : ℕ) : ArchivePLGeometry.Model κ.toArchive d := by
  cases κ with
  | euclidean => exact 0
  | hyperbolic => exact ⟨0⟩
  | spherical => exact GeodesicSphere.northPole d

namespace Polyhedron

variable {κ : Geometry} {d m : ℕ} (K : Polyhedron κ d m)

local instance sourceAtlasCarrierDecEq : DecidableEq ↥K.K.space := Classical.decEq _

def sourceFaces : Set (Finset ↥K.K.space) :=
  {σ | σ = ∅ ∨ σ.image Subtype.val ∈ K.K.faces}

def sourceCell (σ : Finset ↥K.K.space) : Set ↥K.K.space :=
  {x | x.val ∈ cell (σ.image Subtype.val)}

def sourceChart (σ : Finset ↥K.K.space) :
    ↥K.K.space → ArchivePLGeometry.Model κ.toArchive d := by
  classical
  exact if hσ : σ.image Subtype.val ∈ K.K.faces then
    fun x => modelEquiv κ d ((K.simplex (σ.image Subtype.val) hσ).toModel x.val)
  else fun _ => archiveBasepoint κ d

@[simp] theorem sourceCell_empty : K.sourceCell ∅ = ∅ := by
  ext x
  simp [sourceCell, cell]

theorem sourceChart_of_mem {σ : Finset ↥K.K.space}
    (hσ : σ.image Subtype.val ∈ K.K.faces) (x : ↥K.K.space) :
    K.sourceChart σ x =
      modelEquiv κ d ((K.simplex (σ.image Subtype.val) hσ).toModel x.val) := by
  simp only [sourceChart, dite_eq_left hσ]

theorem finite_sourceFaces : K.sourceFaces.Finite := by
  have hpre : {σ : Finset ↥K.K.space | σ.image Subtype.val ∈ K.K.faces}.Finite :=
    Set.Finite.preimage (Finset.image_injective Subtype.val_injective).injOn K.finite
  exact (Set.finite_singleton ∅).union hpre

theorem compact_space : IsCompact K.K.space := by
  apply K.finite.isCompact_biUnion
  intro σ _
  exact σ.finite_toSet.isCompact_convexHull ℝ

theorem sourceCompactSpace : CompactSpace ↥K.K.space :=
  isCompact_iff_compactSpace.mp K.compact_space

theorem sourceCell_closed (σ : Finset ↥K.K.space) : IsClosed (K.sourceCell σ) :=
  ((σ.image Subtype.val).finite_toSet.isClosed_convexHull (𝕜 := ℝ)).preimage
    continuous_subtype_val

theorem sourceCell_compact (σ : Finset ↥K.K.space) : IsCompact (K.sourceCell σ) := by
  letI := K.sourceCompactSpace
  exact (K.sourceCell_closed σ).isCompact

def liftedFace (σ : Finset (E m)) (hσ : σ ∈ K.K.faces) : Finset ↥K.K.space :=
  σ.attach.image (fun v => ⟨v.val, K.K.subset_space hσ v.property⟩)

@[simp] theorem liftedFace_image (σ : Finset (E m)) (hσ : σ ∈ K.K.faces) :
    (K.liftedFace σ hσ).image Subtype.val = σ := by
  ext x
  simp [liftedFace]
  intro hx
  exact K.K.subset_space hσ hx

theorem sourceCover (x : ↥K.K.space) : ∃ σ ∈ K.sourceFaces, x ∈ K.sourceCell σ := by
  obtain ⟨σ, hσ, hx⟩ := _root_.Geometry.SimplicialComplex.mem_space_iff.mp x.property
  refine ⟨K.liftedFace σ hσ, Or.inr ?_, ?_⟩
  · simpa only [K.liftedFace_image] using hσ
  · simpa only [sourceCell, Set.mem_setOf_eq, K.liftedFace_image, cell] using hx

theorem sourceVertices (σ : Finset ↥K.K.space) : (σ : Set ↥K.K.space) ⊆ K.sourceCell σ := by
  intro x hx
  exact subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

theorem sourceFaces_down {σ τ : Finset ↥K.K.space}
    (hσ : σ ∈ K.sourceFaces) (hτσ : τ ⊆ σ) : τ ∈ K.sourceFaces := by
  rcases Finset.eq_empty_or_nonempty τ with hτ | hτ
  · exact Or.inl hτ
  · apply Or.inr
    rcases hσ with rfl | hσ
    · have : τ = ∅ := Finset.subset_empty.mp hτσ
      exact (hτ.ne_empty this).elim
    · exact K.K.down_closed hσ (Finset.image_subset_image hτσ) (hτ.image _)

theorem sourceCell_mono {σ τ : Finset ↥K.K.space} (hτσ : τ ⊆ σ) :
    K.sourceCell τ ⊆ K.sourceCell σ :=
  Set.preimage_mono (convexHull_mono (Finset.coe_subset.mpr
    (Finset.image_subset_image hτσ)))

theorem sourceCell_inter {σ τ : Finset ↥K.K.space}
    (hσ : σ ∈ K.sourceFaces) (hτ : τ ∈ K.sourceFaces) :
    K.sourceCell σ ∩ K.sourceCell τ = K.sourceCell (σ ∩ τ) := by
  rcases hσ with rfl | hσ
  · simp [sourceCell_empty]
  rcases hτ with rfl | hτ
  · simp [sourceCell_empty]
  ext x
  change (x.val ∈ cell (σ.image Subtype.val) ∧ x.val ∈ cell (τ.image Subtype.val)) ↔ _
  have hh := K.K.convexHull_inter_convexHull hσ hτ
  have him : (σ ∩ τ).image Subtype.val = σ.image Subtype.val ∩ τ.image Subtype.val :=
    Finset.image_inter _ _ Subtype.val_injective
  change x.val ∈ cell (σ.image Subtype.val) ∩ cell (τ.image Subtype.val) ↔ _
  rw [show cell (σ.image Subtype.val) ∩ cell (τ.image Subtype.val) =
      cell (σ.image Subtype.val ∩ τ.image Subtype.val) by
        simpa only [cell, Finset.coe_inter] using hh]
  simp only [sourceCell, Set.mem_setOf_eq, him]

theorem sourceChart_injective {σ : Finset ↥K.K.space} (hσ : σ ∈ K.sourceFaces) :
    Set.InjOn (K.sourceChart σ) (K.sourceCell σ) := by
  rcases hσ with rfl | hσ
  · simp [sourceCell_empty, Set.InjOn]
  intro x hx y hy hxy
  apply Subtype.ext
  apply (K.simplex _ hσ).injective hx hy
  apply (modelEquiv κ d).injective
  simpa only [K.sourceChart_of_mem hσ] using hxy

theorem sourceChart_continuous {σ : Finset ↥K.K.space} (hσ : σ ∈ K.sourceFaces) :
    ContinuousOn (K.sourceChart σ) (K.sourceCell σ) := by
  rcases hσ with rfl | hσ
  · simp [sourceCell_empty]
  have hc0 : ContinuousOn (Subtype.val : ↥K.K.space → E m) (K.sourceCell σ) :=
    continuous_subtype_val.continuousOn
  have hm : Set.MapsTo (Subtype.val : ↥K.K.space → E m)
      (K.sourceCell σ) (cell (σ.image Subtype.val)) := fun _ hx => hx
  have hc := (continuous_modelEquiv κ d).comp_continuousOn
    ((K.simplex _ hσ).continuous.comp hc0 hm)
  exact hc.congr (fun x _ => K.sourceChart_of_mem hσ x)

theorem sourceChart_image_face {σ τ : Finset ↥K.K.space}
    (hσ : σ ∈ K.sourceFaces) (hτσ : τ ⊆ σ) :
    K.sourceChart σ '' K.sourceCell τ =
      ArchivePLGeometry.hull κ.toArchive d (τ.image (K.sourceChart σ)) := by
  rcases hσ with rfl | hσ
  · have ht : τ = ∅ := Finset.subset_empty.mp hτσ
    subst τ
    simp [sourceCell_empty, ArchivePLGeometry.hull_empty]
  have hτ : (τ.image Subtype.val : Set (E m)) ⊆ cell (σ.image Subtype.val) :=
    (Finset.coe_subset.mpr (Finset.image_subset_image hτσ)).trans (subset_convexHull ℝ _)
  have hcell : cell (τ.image Subtype.val) ⊆ K.K.space :=
    (convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image hτσ))).trans
      (K.K.convexHull_subset_space hσ)
  let f : E m → ArchivePLGeometry.Model κ.toArchive d :=
    fun x => modelEquiv κ d ((K.simplex _ hσ).toModel x)
  have himage : K.sourceChart σ '' K.sourceCell τ =
      f '' cell (τ.image Subtype.val) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, (K.sourceChart_of_mem hσ x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hcell hx⟩, hx, K.sourceChart_of_mem hσ _⟩
  rw [himage]
  change (fun x => modelEquiv κ d ((K.simplex _ hσ).toModel x)) ''
    convexHull ℝ (τ.image Subtype.val : Set (E m)) = _
  rw [(K.simplex _ hσ).archive_image_hull _ hτ]
  congr 1
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact (K.sourceChart_of_mem hσ x).symm

def sourceCellMap (σ : Finset ↥K.K.space) (hσ : σ ∈ K.sourceFaces) :
    K.sourceCell σ → ArchivePLGeometry.hull κ.toArchive d (σ.image (K.sourceChart σ)) :=
  fun x => ⟨K.sourceChart σ x.val, by
    rw [← K.sourceChart_image_face hσ (Finset.Subset.refl σ)]
    exact ⟨x.val, x.property, rfl⟩⟩

theorem sourceCellMap_bijective (σ : Finset ↥K.K.space) (hσ : σ ∈ K.sourceFaces) :
    Function.Bijective (K.sourceCellMap σ hσ) := by
  constructor
  · intro x y h
    exact Subtype.ext (K.sourceChart_injective hσ x.property y.property (congrArg Subtype.val h))
  · intro y
    have hy : y.val ∈ K.sourceChart σ '' K.sourceCell σ := by
      rw [K.sourceChart_image_face hσ (Finset.Subset.refl σ)]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

def sourceCellHomeomorph (σ : Finset ↥K.K.space) (hσ : σ ∈ K.sourceFaces) :
    K.sourceCell σ ≃ₜ ArchivePLGeometry.hull κ.toArchive d (σ.image (K.sourceChart σ)) := by
  letI : CompactSpace (K.sourceCell σ) := isCompact_iff_compactSpace.mp (K.sourceCell_compact σ)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (K.sourceCellMap σ hσ) (K.sourceCellMap_bijective σ hσ))
    ((K.sourceChart_continuous hσ).domRestrict.subtype_mk _)

theorem sourceMetric_coherence {σ τ : Finset ↥K.K.space}
    (hσ : σ ∈ K.sourceFaces) (hτ : τ ∈ K.sourceFaces)
    (x : ↥K.K.space) (hx : x ∈ K.sourceCell σ ∩ K.sourceCell τ)
    (y : ↥K.K.space) (hy : y ∈ K.sourceCell σ ∩ K.sourceCell τ) :
    dist (K.sourceChart σ x) (K.sourceChart σ y) =
      dist (K.sourceChart τ x) (K.sourceChart τ y) := by
  rcases hσ with rfl | hσ
  · have hx0 : False := by simpa only [K.sourceCell_empty, Set.mem_inter_iff,
      Set.mem_empty_iff_false, false_and] using hx
    exact hx0.elim
  rcases hτ with rfl | hτ
  · have hx0 : False := by simpa only [K.sourceCell_empty, Set.mem_inter_iff,
      Set.mem_empty_iff_false, and_false] using hx
    exact hx0.elim
  rw [K.sourceChart_of_mem hσ, K.sourceChart_of_mem hσ,
    K.sourceChart_of_mem hτ, K.sourceChart_of_mem hτ, modelEquiv_dist, modelEquiv_dist]
  have him : (σ ∩ τ).image Subtype.val = σ.image Subtype.val ∩ τ.image Subtype.val :=
    Finset.image_inter _ _ Subtype.val_injective
  have hx' := hx
  have hy' := hy
  rw [K.sourceCell_inter (Or.inr hσ) (Or.inr hτ)] at hx' hy'
  change x.val ∈ cell ((σ ∩ τ).image Subtype.val) at hx'
  change y.val ∈ cell ((σ ∩ τ).image Subtype.val) at hy'
  rw [him] at hx' hy'
  exact K.compatible _ _ hσ hτ x.val hx' y.val hy'

/-- The charted-complex construction, with vertex independence supplied
separately by the hull-preserving chart lemmas. -/
def toArchiveChartedComplexOfVertices
    (hv : ∀ σ (hσ : σ ∈ K.K.faces), ArchivePLGeometry.simplexVertices κ.toArchive d
      (σ.image (fun x => modelEquiv κ d ((K.simplex σ hσ).toModel x)))) :
    ArchivePLGeometry.FiniteChartedComplex κ.toArchive d ↥K.K.space where
  simplices := K.sourceFaces
  finite_simplices := K.finite_sourceFaces
  cell := K.sourceCell
  chart := K.sourceChart
  cover := K.sourceCover
  vertices_mem := fun σ _ => K.sourceVertices σ
  simplex := by
    intro σ hσ
    rcases hσ with rfl | hσ
    · cases κ <;> simp [ArchivePLGeometry.simplexVertices, Geometry.toArchive,
        BrehmApprox.InOpenHemisphere]
      exact affineIndependent_of_subsingleton ℝ _
    · have h := hv (σ.image Subtype.val) hσ
      have he : (σ.image Subtype.val).image
          (fun x => modelEquiv κ d ((K.simplex (σ.image Subtype.val) hσ).toModel x)) =
          σ.image (K.sourceChart σ) := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro x _
        exact (K.sourceChart_of_mem hσ x).symm
      rwa [he] at h
  image_cell := fun σ hσ => K.sourceChart_image_face hσ (Finset.Subset.refl σ)
  cellHomeomorph := K.sourceCellHomeomorph
  cellHomeomorph_apply := fun _ _ _ => rfl
  faces := fun _ hσ _ hτσ => K.sourceFaces_down hσ hτσ
  image_face := fun _ hσ _ hτσ => K.sourceChart_image_face hσ hτσ
  intersection := fun _ hσ _ hτ => K.sourceCell_inter hσ hτ
  metric_coherence := fun _ hσ _ hτ x hx y hy => K.sourceMetric_coherence hσ hτ x hx y hy

/-- Every polyhedron of the original Challenge gives the finite charted
complex used by the completed folding theorem. -/
def toArchiveChartedComplex :
    ArchivePLGeometry.FiniteChartedComplex κ.toArchive d ↥K.K.space :=
  K.toArchiveChartedComplexOfVertices (fun σ hσ =>
    (K.simplex σ hσ).archive_simplexVertices (K.K.indep hσ))

theorem sourceChart_dist {σ : Finset ↥K.K.space}
    (hσ : σ.image Subtype.val ∈ K.K.faces) (x y : ↥K.K.space) :
    dist (K.toArchiveChartedComplex.chart σ x) (K.toArchiveChartedComplex.chart σ y) =
      modelDist κ d ((K.simplex (σ.image Subtype.val) hσ).toModel x.val)
        ((K.simplex (σ.image Subtype.val) hσ).toModel y.val) := by
  change dist (K.sourceChart σ x) (K.sourceChart σ y) = _
  rw [K.sourceChart_of_mem hσ, K.sourceChart_of_mem hσ, modelEquiv_dist]

end Polyhedron
end PLGeometry
