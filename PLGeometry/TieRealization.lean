module

public import PLGeometry.ProjectiveTieGeometry
public import PLGeometry.FinsetBarycentricWeights
public import PLGeometry.ClosedCellGluing
public import PLGeometry.ComplexReweighting

/-!
# Geometric realization of the triangulated tie locus

The standard barycentric realization is mapped to the source by genuine
model barycentric interpolation. Model isometries preserve these weights,
so the local maps agree on common faces in all three geometries.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance tieRealizationDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance tieRealizationEDecidableEq : DecidableEq E := Classical.decEq E

def tieCell (σ : Finset (A.toVoronoiAtlas.TieVertex S)) : Set P :=
  A.coord ⁻¹' convexHull ℝ (A.toVoronoiAtlas.tieCoordinateFace S σ : Set E)

theorem tieCell_mono {σ τ : Finset (A.toVoronoiAtlas.TieVertex S)} (h : σ ⊆ τ) :
    A.tieCell S σ ⊆ A.tieCell S τ :=
  Set.preimage_mono (convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image h)))

theorem tieCell_subset_old {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    A.tieCell S σ ⊆ T.cell (A.toVoronoiAtlas.tieFaceIndex S σ hσ).val.1.val := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  intro x hx
  have hv : (B.tieCoordinateFace S σ : Set E) ⊆ A.coord '' T.cell i.val.1.val := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨B.tieSource S v, (B.tieFace_source_mem S hσ hv).1.1, B.coord_tieSource S v⟩
  obtain ⟨y, hy, he⟩ := convexHull_min hv (A.cell_polytope _ i.val.1.property).convex hx
  exact A.injective he ▸ hy

theorem tieCell_closed (σ : Finset (A.toVoronoiAtlas.TieVertex S)) :
    IsClosed (A.tieCell S σ) :=
  ((A.toVoronoiAtlas.tieCoordinateFace S σ).finite_toSet.isCompact_convexHull ℝ).isClosed.preimage
    A.continuous

theorem tieCell_compact (σ : Finset (A.toVoronoiAtlas.TieVertex S)) :
    IsCompact (A.tieCell S σ) := by
  let : CompactSpace P := T.compactSpace
  exact (A.tieCell_closed S σ).isCompact

theorem tie_image_coord (σ : Finset (A.toVoronoiAtlas.TieVertex S)) :
    (A.toVoronoiAtlas.tieSourceFace S σ).image A.coord =
      A.toVoronoiAtlas.tieCoordinateFace S σ := by
  ext z
  simp only [VoronoiAtlas.tieSourceFace, VoronoiAtlas.tieCoordinateFace, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (A.toVoronoiAtlas.coord_tieSource S v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨A.toVoronoiAtlas.tieSource S v, ⟨v, hv, rfl⟩,
      A.toVoronoiAtlas.coord_tieSource S v⟩

theorem tieCell_chart_image {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    A.toVoronoiAtlas.tieChart S hσ '' A.tieCell S σ =
      hull κ n ((A.toVoronoiAtlas.tieSourceFace S σ).image
        (A.toVoronoiAtlas.tieChart S hσ)) := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  have hv : (B.tieSourceFace S σ : Set P) ⊆ T.cell i.val.1.val := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (B.tieFace_source_mem S hσ hv).1.1
  have h := A.hull_transfer i.val.1.val i.val.1.property (B.tieSourceFace S σ) hv
  rw [A.tie_image_coord S σ] at h
  exact h

def tieCellHomeomorph {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    A.tieCell S σ ≃ₜ hull κ n ((A.toVoronoiAtlas.tieSourceFace S σ).image
      (A.toVoronoiAtlas.tieChart S hσ)) := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  let f : A.tieCell S σ → hull κ n ((B.tieSourceFace S σ).image (B.tieChart S hσ)) :=
    fun x => ⟨B.tieChart S hσ x.val, by rw [← A.tieCell_chart_image S hσ]; exact ⟨x.val, x.property, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      exact T.chart_injectiveOn i.val.1.val i.val.1.property
        (A.tieCell_subset_old S hσ x.property) (A.tieCell_subset_old S hσ y.property)
        (congrArg Subtype.val he)
    · intro y
      have hy : y.val ∈ B.tieChart S hσ '' A.tieCell S σ :=
        (A.tieCell_chart_image S hσ).symm.subset y.property
      obtain ⟨x, hx, he⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  let : CompactSpace (A.tieCell S σ) := isCompact_iff_compactSpace.mp (A.tieCell_compact S σ)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    (((T.chart_continuousOn i.val.1.val i.val.1.property).mono
      (A.tieCell_subset_old S hσ)).domRestrict.subtype_mk _)

@[simp] theorem tieCellHomeomorph_apply {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) (x : A.tieCell S σ) :
    (A.tieCellHomeomorph S hσ x).val = A.toVoronoiAtlas.tieChart S hσ x.val := rfl

theorem tie_vertex_independent {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    ModelBarycentric.Independent κ n (fun v : σ =>
      A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val)) := by
  let B := A.toVoronoiAtlas
  let e : σ ↪ (B.tieSourceFace S σ).image (B.tieChart S hσ) :=
    { toFun := fun v => ⟨B.tieChart S hσ (B.tieSource S v.val),
        Finset.mem_image.mpr ⟨B.tieSource S v.val,
          Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩, rfl⟩⟩
      inj' := by
        intro v w he
        apply Subtype.ext
        apply B.tieSource_injective S
        apply T.chart_injectiveOn _ (B.tieFaceIndex S σ hσ).val.1.property
          (B.tieFace_source_mem S hσ v.property).1.1 (B.tieFace_source_mem S hσ w.property).1.1
        exact congrArg Subtype.val he }
  have hs := A.tieFace_simplex S hσ
  cases κ with
  | euclidean => exact hs.comp_embedding e
  | spherical => exact hs.2.comp e e.injective
  | hyperbolic => exact hs.comp e e.injective

theorem tie_image_univ_chart {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    Finset.univ.image (fun v : σ =>
      A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val)) =
      (A.toVoronoiAtlas.tieSourceFace S σ).image (A.toVoronoiAtlas.tieChart S hσ) := by
  ext z
  simp only [VoronoiAtlas.tieSourceFace, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨A.toVoronoiAtlas.tieSource S v.val, ⟨v.val, v.property, rfl⟩, hv⟩
  · rintro ⟨x, ⟨v, hv, rfl⟩, he⟩
    exact ⟨⟨v, hv⟩, he⟩

def tieWeightsHomeomorph {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    Barycentric.weightsOn σ ≃ₜ A.tieCell S σ :=
  (Barycentric.restrictHomeomorph σ).trans
    ((ModelBarycentric.homeomorph (fun v : σ =>
      A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val))
        (A.tie_vertex_independent S hσ)).trans
      ((Homeomorph.setCongr (congrArg (hull κ n) (A.tie_image_univ_chart S hσ))).trans
        (A.tieCellHomeomorph S hσ).symm))

def tieLocalPoint {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (w : Barycentric.weightsOn σ) : P := (A.tieWeightsHomeomorph S hσ w).val

theorem tieLocalPoint_mem {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) (w : Barycentric.weightsOn σ) :
    A.tieLocalPoint S hσ w ∈ A.tieCell S σ := (A.tieWeightsHomeomorph S hσ w).property

theorem tieLocalPoint_represents {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) (w : Barycentric.weightsOn σ) :
    ModelBarycentric.Represents κ n (fun v : σ =>
      A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val))
      (Barycentric.restrict σ w).val
      (A.toVoronoiAtlas.tieChart S hσ (A.tieLocalPoint S hσ w)) := by
  have he := congrArg Subtype.val ((A.tieCellHomeomorph S hσ).apply_symm_apply
    ((Homeomorph.setCongr (congrArg (hull κ n) (A.tie_image_univ_chart S hσ)))
      (ModelBarycentric.homeomorph (fun v : σ =>
        A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val))
          (A.tie_vertex_independent S hσ) (Barycentric.restrict σ w))))
  change A.toVoronoiAtlas.tieChart S hσ (A.tieLocalPoint S hσ w) =
    ModelBarycentric.point κ n (fun v : σ =>
      A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val))
      (A.tie_vertex_independent S hσ) (Barycentric.restrict σ w) at he
  rw [he]
  exact ModelBarycentric.point_represents _ _ _

theorem tieLocalPoint_injective {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    Function.Injective (A.tieLocalPoint S hσ) := by
  intro x y h
  exact (A.tieWeightsHomeomorph S hσ).injective (Subtype.ext h)

theorem tieLocalPoint_of_subset {σ τ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (hτ : τ ∈ (A.toVoronoiAtlas.tieComplex S).faces) (hτσ : τ ⊆ σ)
    (w : Barycentric.weightsOn τ) :
    A.tieLocalPoint S hσ ⟨w.val, Barycentric.weightsOn_mono hτσ w.property⟩ =
      A.tieLocalPoint S hτ w := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  let j := B.tieFaceIndex S τ hτ
  let y := A.tieLocalPoint S hτ w
  have hyτ := A.tieLocalPoint_mem S hτ w
  have hyσ := A.tieCell_mono S hτσ hyτ
  have hyi := A.tieCell_subset_old S hσ hyσ
  have hyj := A.tieCell_subset_old S hτ hyτ
  have hrep : ModelBarycentric.Represents κ n
      (fun v : τ => B.tieChart S hσ (B.tieSource S v.val))
      (Barycentric.restrict τ w).val (B.tieChart S hσ y) := by
    apply ModelBarycentric.represents_transfer
      (fun v : τ => B.tieChart S hτ (B.tieSource S v.val))
      (fun v : τ => B.tieChart S hσ (B.tieSource S v.val))
      (A.tie_vertex_independent S hτ)
    · intro v z
      exact T.metric_coherence _ j.val.1.property _ i.val.1.property _
        ⟨(B.tieFace_source_mem S hτ v.property).1.1,
          (B.tieFace_source_mem S hσ (hτσ v.property)).1.1⟩ _
        ⟨(B.tieFace_source_mem S hτ z.property).1.1,
          (B.tieFace_source_mem S hσ (hτσ z.property)).1.1⟩
    · intro v
      exact (T.metric_coherence _ j.val.1.property _ i.val.1.property y
        ⟨hyj, hyi⟩ _ ⟨(B.tieFace_source_mem S hτ v.property).1.1,
          (B.tieFace_source_mem S hσ (hτσ v.property)).1.1⟩).symm
    · exact A.tieLocalPoint_represents S hτ w
  have hw : Barycentric.restrict σ ⟨w.val, Barycentric.weightsOn_mono hτσ w.property⟩ =
      ModelBarycentric.extendWeights hτσ (Barycentric.restrict τ w) := by
    apply Subtype.ext
    funext v
    by_cases hv : v.val ∈ τ
    · simp only [Barycentric.restrict, ModelBarycentric.extendWeights, dite_eq_left hv]
    · simp only [Barycentric.restrict, ModelBarycentric.extendWeights, dite_eq_right hv,
        w.property.2 v.val hv]
  have hrep' := ModelBarycentric.represents_extend hτσ (Barycentric.restrict τ w)
    (fun v => B.tieChart S hσ (B.tieSource S v)) (B.tieChart S hσ y) hrep
  rw [← hw] at hrep'
  apply T.chart_injectiveOn _ i.val.1.property
    (A.tieCell_subset_old S hσ (A.tieLocalPoint_mem S hσ _)) hyi
  exact (ModelBarycentric.point_eq_of_represents _ (A.tie_vertex_independent S hσ) _ _
    (A.tieLocalPoint_represents S hσ _)).symm.trans
    (ModelBarycentric.point_eq_of_represents _ (A.tie_vertex_independent S hσ) _ _ hrep')

theorem tieLocalPoint_agree {σ τ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (hτ : τ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (w : A.toVoronoiAtlas.TieVertex S → ℝ)
    (hwσ : w ∈ Barycentric.weightsOn σ) (hwτ : w ∈ Barycentric.weightsOn τ) :
    A.tieLocalPoint S hσ ⟨w, hwσ⟩ = A.tieLocalPoint S hτ ⟨w, hwτ⟩ := by
  have hστ := (A.toVoronoiAtlas.tieComplex S).downward σ hσ (σ ∩ τ) Finset.inter_subset_left
  have hw : w ∈ Barycentric.weightsOn (σ ∩ τ) := by
    refine ⟨hwσ.1, fun i hi => ?_⟩
    by_cases his : i ∈ σ
    · exact hwτ.2 i (fun hit => hi (Finset.mem_inter.mpr ⟨his, hit⟩))
    · exact hwσ.2 i his
  exact (A.tieLocalPoint_of_subset S hσ hστ Finset.inter_subset_left ⟨w, hw⟩).trans
    (A.tieLocalPoint_of_subset S hτ hστ Finset.inter_subset_right ⟨w, hw⟩).symm

def tieRealizationCover : FiniteClosedCover (A.toVoronoiAtlas.tieComplex S).Space
    (A.toVoronoiAtlas.tieComplex S).faces where
  cell σ := (Subtype.val : (A.toVoronoiAtlas.tieComplex S).Space → _) ⁻¹'
    Barycentric.weightsOn σ.val
  cover x := by
    obtain ⟨σ, hσ, hx⟩ := Set.mem_iUnion₂.mp x.property
    exact ⟨⟨σ, hσ⟩, hx⟩
  closed σ := (Barycentric.isClosed_weightsOn σ.val).preimage continuous_subtype_val

def tieRealization : (A.toVoronoiAtlas.tieComplex S).Space → P :=
  (A.tieRealizationCover S).glue (fun σ x => A.tieLocalPoint S σ.property ⟨x.val.val, x.property⟩)

theorem tieRealization_eq {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ) :
    A.tieRealization S x = A.tieLocalPoint S hσ ⟨x.val, hx⟩ :=
  (A.tieRealizationCover S).glue_eq _
    (fun i j x hi hj => A.tieLocalPoint_agree S i.property j.property x.val hi hj)
    ⟨σ, hσ⟩ ⟨x, hx⟩

theorem continuous_tieRealization : Continuous (A.tieRealization S) := by
  apply (A.tieRealizationCover S).continuous_glue
  · intro σ
    exact continuous_subtype_val.comp ((A.tieWeightsHomeomorph S σ.property).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
  · intro i j x hi hj
    exact A.tieLocalPoint_agree S i.property j.property x.val hi hj

def tieLocus : Set P := ⋃ σ ∈ (A.toVoronoiAtlas.tieComplex S).faces, A.tieCell S σ

theorem tieCoordinateFace_surjective {V : Finset E} (hV : V ∈ A.toVoronoiAtlas.tieFaces S) :
    ∃ σ ∈ (A.toVoronoiAtlas.tieComplex S).faces,
      A.toVoronoiAtlas.tieCoordinateFace S σ = V := by
  let B := A.toVoronoiAtlas
  let σ : Finset (B.TieVertex S) := Finset.univ.filter fun v => v.val ∈ V
  have he : B.tieCoordinateFace S σ = V := by
    ext z
    constructor
    · intro hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hv).2
    · intro hz
      let v : B.TieVertex S := ⟨z, Set.mem_iUnion₂.mpr ⟨V, hV, hz⟩⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩
  exact ⟨σ, by change B.tieCoordinateFace S σ ∈ B.tieFaces S; rw [he]; exact hV, he⟩

theorem tieLocus_eq : A.tieLocus S =
    A.coord ⁻¹' ⋃ i : VoronoiAtlas.TieIndex (T := T) S, A.toVoronoiAtlas.tiePiece S i := by
  let B := A.toVoronoiAtlas
  ext y
  constructor
  · intro hy
    obtain ⟨σ, hσ, hy⟩ := Set.mem_iUnion₂.mp hy
    exact Set.mem_iUnion.mpr ⟨B.tieFaceIndex S σ hσ,
      Pulling.family_face_subset_cell (B.tiePiece S) (B.tiePiece_polytope S)
        (B.tieFaceIndex_spec S σ hσ) hy⟩
  · intro hy
    have hy' : A.coord y ∈ ⋃ V ∈ B.tieFaces S, convexHull ℝ (V : Set E) := by
      exact (Pulling.family_faces_cover (B.tiePiece S) (B.tiePiece_polytope S)).subset hy
    obtain ⟨V, hV, hyV⟩ := Set.mem_iUnion₂.mp hy'
    obtain ⟨σ, hσ, he⟩ := A.tieCoordinateFace_surjective S hV
    refine Set.mem_iUnion₂.mpr ⟨σ, hσ, ?_⟩
    change A.coord y ∈ convexHull ℝ (B.tieCoordinateFace S σ : Set E)
    rw [he]
    exact hyV

theorem range_tieRealization : Set.range (A.tieRealization S) = A.tieLocus S := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨σ, hσ, hx⟩ := Set.mem_iUnion₂.mp x.property
    rw [A.tieRealization_eq S hσ x hx]
    exact Set.mem_iUnion₂.mpr ⟨σ, hσ, A.tieLocalPoint_mem S hσ ⟨x.val, hx⟩⟩
  · intro hy
    obtain ⟨σ, hσ, hy⟩ := Set.mem_iUnion₂.mp hy
    let w := (A.tieWeightsHomeomorph S hσ).symm ⟨y, hy⟩
    let x : (A.toVoronoiAtlas.tieComplex S).Space :=
      ⟨w.val, Set.mem_iUnion₂.mpr ⟨σ, hσ, w.property⟩⟩
    refine ⟨x, ?_⟩
    rw [A.tieRealization_eq S hσ x w.property]
    exact congrArg Subtype.val ((A.tieWeightsHomeomorph S hσ).apply_symm_apply ⟨y, hy⟩)

theorem tieCell_intersection {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) {σ τ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (hτ : τ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    A.tieCell S σ ∩ A.tieCell S τ = A.tieCell S (σ ∩ τ) := by
  change A.coord ⁻¹' _ ∩ A.coord ⁻¹' _ = A.coord ⁻¹' _
  rw [← Set.preimage_inter, A.toVoronoiAtlas.tieFace_intersection hnet hp hσ hτ]

theorem tieRealization_injective {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) : Function.Injective (A.tieRealization S) := by
  intro x y hxy
  obtain ⟨σ, hσ, hx⟩ := Set.mem_iUnion₂.mp x.property
  obtain ⟨τ, hτ, hy⟩ := Set.mem_iUnion₂.mp y.property
  have hσy : A.tieRealization S x ∈ A.tieCell S σ := by
    rw [A.tieRealization_eq S hσ x hx]
    exact A.tieLocalPoint_mem S hσ _
  have hτy : A.tieRealization S x ∈ A.tieCell S τ := by
    rw [hxy, A.tieRealization_eq S hτ y hy]
    exact A.tieLocalPoint_mem S hτ _
  have hz : A.tieRealization S x ∈ A.tieCell S (σ ∩ τ) := by
    rw [← A.tieCell_intersection S hnet hp hσ hτ]
    exact ⟨hσy, hτy⟩
  have hστ := (A.toVoronoiAtlas.tieComplex S).downward σ hσ (σ ∩ τ) Finset.inter_subset_left
  let w := (A.tieWeightsHomeomorph S hστ).symm ⟨A.tieRealization S x, hz⟩
  have hw : A.tieLocalPoint S hστ w = A.tieRealization S x :=
    congrArg Subtype.val ((A.tieWeightsHomeomorph S hστ).apply_symm_apply _)
  have heσ : (⟨x.val, hx⟩ : Barycentric.weightsOn σ) =
      ⟨w.val, Barycentric.weightsOn_mono Finset.inter_subset_left w.property⟩ := by
    apply A.tieLocalPoint_injective S hσ
    rw [A.tieLocalPoint_of_subset S hσ hστ Finset.inter_subset_left, hw,
      A.tieRealization_eq S hσ x hx]
  have heτ : (⟨y.val, hy⟩ : Barycentric.weightsOn τ) =
      ⟨w.val, Barycentric.weightsOn_mono Finset.inter_subset_right w.property⟩ := by
    apply A.tieLocalPoint_injective S hτ
    rw [A.tieLocalPoint_of_subset S hτ hστ Finset.inter_subset_right, hw, hxy,
      A.tieRealization_eq S hτ y hy]
  apply Subtype.ext
  exact (congrArg Subtype.val heσ).trans (congrArg Subtype.val heτ).symm

def tieRealizationHomeomorph {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) :
    (A.toVoronoiAtlas.tieComplex S).Space ≃ₜ A.tieLocus S := by
  let K := A.toVoronoiAtlas.tieComplex S
  have hc : IsCompact K.carrier :=
    (Set.toFinite K.faces).isCompact_biUnion (fun σ _ => Barycentric.isCompact_weightsOn σ)
  let : CompactSpace K.Space := isCompact_iff_compactSpace.mp hc
  let f : K.Space → A.tieLocus S := fun x =>
    ⟨A.tieRealization S x, by rw [← A.range_tieRealization S]; exact Set.mem_range_self x⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y he
      exact A.tieRealization_injective S hnet hp (congrArg Subtype.val he)
    · intro y
      have hy : y.val ∈ Set.range (A.tieRealization S) :=
        (A.range_tieRealization S).symm.subset y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    ((A.continuous_tieRealization S).subtype_mk _)

end ArchivePLGeometry.ProjectiveVoronoiAtlas
