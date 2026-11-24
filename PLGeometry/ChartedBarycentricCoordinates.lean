module

public import PLGeometry.FinsetBarycentricWeights
public import PLGeometry.ChartedIncidence
public import PLGeometry.ClosedCellGluing
public import PLGeometry.BarycentricRealization

/-!
# Canonical coordinates on a finite charted complex

Local barycentric coordinates agree on every common face. Extending them
by zero therefore gives one continuous coordinate map into the vector
space indexed by all vertices of the source complex.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance chartedBarycentricDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance chartedBarycentricEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance chartedBarycentricSDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance chartedBarycentricHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _
local instance chartedBarycentricModelDecidableEq : DecidableEq (Model κ n) := Classical.decEq _

theorem chart_vertex_independent {σ : Finset P} (hσ : σ ∈ T.simplices) :
    ModelBarycentric.Independent κ n (fun v : σ => T.chart σ v.val) := by
  let e : σ ↪ σ.image (T.chart σ) :=
    { toFun := fun v => ⟨T.chart σ v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
      inj' := by
        intro v w h
        apply Subtype.ext
        apply T.chart_injectiveOn σ hσ
          (T.vertices_mem σ hσ v.property) (T.vertices_mem σ hσ w.property)
        exact congrArg Subtype.val h }
  have hv := T.simplex σ hσ
  cases κ with
  | euclidean =>
    have h : AffineIndependent ℝ ((↑) : σ.image (T.chart σ) → Model .euclidean n) := by
      simpa only [simplexVertices, Finset.coe_sort_coe] using hv
    exact h.comp_embedding e
  | spherical =>
    have h : LinearIndependent ℝ (fun v : σ.image (T.chart σ) => v.val.val) := by
      simpa only [simplexVertices, Finset.coe_sort_coe] using hv.2
    exact h.comp e e.injective
  | hyperbolic =>
    have h : LinearIndependent ℝ (fun v : σ.image (T.chart σ) => HyperbolicSpace.lift v.val) := by
      simpa only [simplexVertices, Finset.coe_sort_coe] using hv
    exact h.comp e e.injective

theorem image_univ_chart (σ : Finset P) :
    Finset.univ.image (fun v : σ => T.chart σ v.val) = σ.image (T.chart σ) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists]
  constructor <;> rintro ⟨a, ha, he⟩ <;> exact ⟨a, ha, he⟩

def cellWeights (σ : Finset P) (hσ : σ ∈ T.simplices) :
    T.cell σ ≃ₜ ModelBarycentric.Weights σ :=
  ((T.cellHomeomorph σ hσ).trans
    (Homeomorph.setCongr (congrArg (hull κ n) (T.image_univ_chart σ).symm))).trans
    (ModelBarycentric.homeomorph (fun v : σ => T.chart σ v.val) (T.chart_vertex_independent hσ)).symm

theorem cellWeights_represents (σ : Finset P) (hσ : σ ∈ T.simplices) (x : T.cell σ) :
    ModelBarycentric.Represents κ n (fun v : σ => T.chart σ v.val)
      (T.cellWeights σ hσ x).val (T.chart σ x.val) := by
  have h := ModelBarycentric.point_represents (fun v : σ => T.chart σ v.val)
    (T.chart_vertex_independent hσ) (T.cellWeights σ hσ x)
  have he : ModelBarycentric.point κ n (fun v : σ => T.chart σ v.val)
      (T.chart_vertex_independent hσ) (T.cellWeights σ hσ x) = T.chart σ x.val := by
    have hh := (ModelBarycentric.homeomorph (fun v : σ => T.chart σ v.val)
      (T.chart_vertex_independent hσ)).apply_symm_apply
      ((Homeomorph.setCongr (congrArg (hull κ n) (T.image_univ_chart σ).symm))
        (T.cellHomeomorph σ hσ x))
    have hh' := congrArg Subtype.val hh
    change ModelBarycentric.point κ n (fun v : σ => T.chart σ v.val)
      (T.chart_vertex_independent hσ) (T.cellWeights σ hσ x) = (T.cellHomeomorph σ hσ x).val at hh'
    exact hh'.trans (T.cellHomeomorph_apply σ hσ x)
  rw [he] at h
  exact h

theorem cellWeights_of_face {σ τ : Finset P} (hσ : σ ∈ T.simplices)
    (hτσ : τ ⊆ σ) (x : T.cell τ) :
    T.cellWeights σ hσ ⟨x.val, T.cell_mono hσ hτσ x.property⟩ =
      ModelBarycentric.extendWeights hτσ (T.cellWeights τ (T.faces σ hσ τ hτσ) x) := by
  have hτ := T.faces σ hσ τ hτσ
  apply ModelBarycentric.weights_unique (fun v : σ => T.chart σ v.val)
    (T.chart_vertex_independent hσ) _ _ (T.chart σ x.val)
  · exact T.cellWeights_represents σ hσ _
  · apply ModelBarycentric.represents_extend hτσ
    apply ModelBarycentric.represents_transfer
      (fun v : τ => T.chart τ v.val) (fun v : τ => T.chart σ v.val)
      (T.chart_vertex_independent hτ)
    · intro i j
      exact T.metric_coherence τ hτ σ hσ i.val
        ⟨T.vertices_mem τ hτ i.property, T.vertices_mem σ hσ (hτσ i.property)⟩ j.val
        ⟨T.vertices_mem τ hτ j.property, T.vertices_mem σ hσ (hτσ j.property)⟩
    · intro i
      exact (T.metric_coherence τ hτ σ hσ x.val
        ⟨x.property, T.cell_mono hσ hτσ x.property⟩ i.val
        ⟨T.vertices_mem τ hτ i.property, T.vertices_mem σ hσ (hτσ i.property)⟩).symm
    · exact T.cellWeights_represents τ hτ x

def vertexFinset : Finset P := T.finite_vertexSet.toFinset

abbrev Vertex := T.vertexFinset

@[simp] theorem mem_vertexFinset (v : P) : v ∈ T.vertexFinset ↔ v ∈ T.vertexSet :=
  Set.Finite.mem_toFinset _

theorem vertex_mem {σ : Finset P} (hσ : σ ∈ T.simplices) {v : P} (hv : v ∈ σ) :
    v ∈ T.vertexFinset :=
  (T.mem_vertexFinset v).mpr (Set.mem_iUnion₂.mpr ⟨σ, hσ, hv⟩)

def faceLabels (σ : Finset P) : Finset T.Vertex := Finset.univ.filter (fun v => v.val ∈ σ)

@[simp] theorem mem_faceLabels (σ : Finset P) (v : T.Vertex) : v ∈ T.faceLabels σ ↔ v.val ∈ σ := by
  simp only [faceLabels, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem faceLabels_inter (σ τ : Finset P) :
    T.faceLabels (σ ∩ τ) = T.faceLabels σ ∩ T.faceLabels τ := by
  ext v
  simp only [mem_faceLabels, Finset.mem_inter]

def localCoords (σ : Finset P) (hσ : σ ∈ T.simplices) (x : T.cell σ) : T.Vertex → ℝ :=
  fun v => if hv : v.val ∈ σ then (T.cellWeights σ hσ x).val ⟨v.val, hv⟩ else 0

theorem continuous_localCoords (σ : Finset P) (hσ : σ ∈ T.simplices) :
    Continuous (T.localCoords σ hσ) := by
  apply continuous_pi
  intro v
  by_cases hv : v.val ∈ σ
  · have he : (fun x => T.localCoords σ hσ x v) =
        fun x => (T.cellWeights σ hσ x).val ⟨v.val, hv⟩ := by
      funext x
      simp only [localCoords, dite_eq_left hv]
    rw [he]
    exact (continuous_apply ⟨v.val, hv⟩).comp
      (continuous_subtype_val.comp (T.cellWeights σ hσ).continuous)
  · have he : (fun x => T.localCoords σ hσ x v) = fun _ => (0 : ℝ) := by
      funext x
      simp only [localCoords, dite_eq_right hv]
    rw [he]
    exact continuous_const

theorem localCoords_of_face {σ τ : Finset P} (hσ : σ ∈ T.simplices)
    (hτσ : τ ⊆ σ) (x : T.cell τ) :
    T.localCoords σ hσ ⟨x.val, T.cell_mono hσ hτσ x.property⟩ =
      T.localCoords τ (T.faces σ hσ τ hτσ) x := by
  funext v
  by_cases hvτ : v.val ∈ τ
  · have hvσ := hτσ hvτ
    simp only [localCoords, dite_eq_left hvσ, dite_eq_left hvτ, T.cellWeights_of_face hσ hτσ,
      ModelBarycentric.extendWeights]
  · by_cases hvσ : v.val ∈ σ
    · simp only [localCoords, dite_eq_left hvσ, dite_eq_right hvτ,
        T.cellWeights_of_face hσ hτσ, ModelBarycentric.extendWeights]
    · simp only [localCoords, dite_eq_right hvσ, dite_eq_right hvτ]

theorem localCoords_agree {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
    (x : P) (hxσ : x ∈ T.cell σ) (hxτ : x ∈ T.cell τ) :
    T.localCoords σ hσ ⟨x, hxσ⟩ = T.localCoords τ hτ ⟨x, hxτ⟩ := by
  have hx : x ∈ T.cell (σ ∩ τ) := by rw [← T.intersection σ hσ τ hτ]; exact ⟨hxσ, hxτ⟩
  exact (T.localCoords_of_face hσ Finset.inter_subset_left ⟨x, hx⟩).trans
    (T.localCoords_of_face hτ Finset.inter_subset_right ⟨x, hx⟩).symm

local instance chartedBarycentricFiniteFaces : Finite T.simplices := T.finite_simplices.to_subtype

def closedCover : FiniteClosedCover P T.simplices :=
  { cell := fun σ => T.cell σ.val
    cover := fun x => by obtain ⟨σ, hσ, hx⟩ := T.cover x; exact ⟨⟨σ, hσ⟩, hx⟩
    closed := fun σ => T.closed_cell σ.val σ.property }

def barycentricCoords : P → (T.Vertex → ℝ) :=
  T.closedCover.glue (fun σ => T.localCoords σ.val σ.property)

theorem barycentricCoords_eq {σ : Finset P} (hσ : σ ∈ T.simplices) {x : P} (hx : x ∈ T.cell σ) :
    T.barycentricCoords x = T.localCoords σ hσ ⟨x, hx⟩ :=
  T.closedCover.glue_eq (fun τ => T.localCoords τ.val τ.property)
    (fun _ _ x hi hj => T.localCoords_agree _ _ x hi hj) ⟨σ, hσ⟩ ⟨x, hx⟩

theorem continuous_barycentricCoords : Continuous T.barycentricCoords :=
  T.closedCover.continuous_glue (fun σ => T.localCoords σ.val σ.property)
    (fun σ => T.continuous_localCoords σ.val σ.property)
    (fun _ _ x hi hj => T.localCoords_agree _ _ x hi hj)

end ArchivePLGeometry.FiniteChartedComplex
