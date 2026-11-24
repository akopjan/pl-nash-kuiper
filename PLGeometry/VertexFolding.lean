module

public import PLGeometry.ChartedComplex
public import PLGeometry.ModelMotions
public import PLGeometry.ModelBarycentricNaturality
public import PLGeometry.ClosedCellGluing
public import PLGeometry.ChartedIncidence

/-!
# Folding a finite charted complex from its vertex distances

A consistent assignment of model points to source vertices extends to a
continuous cellwise isometry whenever it preserves every simplex's vertex
distances. Finite congruence supplies a motion on each cell. Their restrictions
to a common face agree because distances to its vertices determine its points.
-/

@[expose] public section
noncomputable section

open BrehmApprox

namespace ArchivePLGeometry

universe u
local instance vertexFoldingDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- A point in a model hull is determined by its distances to its vertices. -/
theorem eq_of_mem_hull_of_dist_eq (κ : Geometry) (n : ℕ)
    {V : Finset (Model κ n)} {x y : Model κ n} (hx : x ∈ hull κ n V)
    (hd : ∀ v ∈ V, dist x v = dist y v) : x = y := by
  cases κ with
  | euclidean => exact eq_of_mem_convexHull_of_dist_eq hx hd
  | spherical => exact eq_of_mem_sphericalCell_of_dist_eq hx hd
  | hyperbolic => exact eq_of_mem_hyperbolicCell_of_dist_eq hx hd

/-- Congruent independent finite vertex families extend to a model motion. -/
theorem exists_model_vertex_motion {ι : Type*} [Fintype ι]
    (κ : Geometry) (n : ℕ) (v w : ι → Model κ n)
    (hv : ModelBarycentric.Independent κ n v)
    (hd : ∀ i j, dist (v i) (v j) = dist (w i) (w j)) :
    ∃ R : ModelEmbedding κ n n, ∀ i, R.toFun (v i) = w i := by
  cases κ with
  | euclidean =>
    obtain ⟨R, hR⟩ := exists_ambient_distance_isometry v w hv hd
    exact ⟨euclideanMotionEmbedding R, hR⟩
  | spherical =>
    obtain ⟨R, hR⟩ := exists_spherical_vertex_motion v w hv hd
    exact ⟨sphericalMotionEmbedding R, hR⟩
  | hyperbolic =>
    obtain ⟨R, hR⟩ := HyperbolicSpace.exists_vertex_motion v w hv hd
    exact ⟨hyperbolicMotionEmbedding R, hR⟩

namespace FiniteChartedComplex

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance vertexFoldingModelDecidableEq : DecidableEq (Model κ n) := Classical.decEq _
local instance vertexFoldingEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance vertexFoldingSDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance vertexFoldingHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _

def vertexModelEmbedding (σ : Finset P) (hσ : σ ∈ T.simplices) :
    σ ↪ σ.image (T.chart σ) where
  toFun x := ⟨T.chart σ x.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact T.chart_injectiveOn σ hσ (T.vertices_mem σ hσ x.property)
      (T.vertices_mem σ hσ y.property)
      (congrArg (fun z : σ.image (T.chart σ) => z.val) hxy)

theorem vertexModel_independent (σ : Finset P) (hσ : σ ∈ T.simplices) :
    ModelBarycentric.Independent κ n (fun x : σ => T.chart σ x.val) := by
  have h := T.simplex σ hσ
  cases κ with
  | euclidean =>
    have hi : AffineIndependent ℝ ((↑) : σ.image (T.chart σ) → Model .euclidean n) := by
      simpa only [simplexVertices, Finset.coe_sort_coe] using h
    exact hi.comp_embedding (T.vertexModelEmbedding σ hσ)
  | spherical =>
    have hi : LinearIndependent ℝ (fun x : σ.image (T.chart σ) => x.val.val) := by
      simpa only [simplexVertices, Finset.coe_sort_coe] using h.2
    exact hi.comp (T.vertexModelEmbedding σ hσ) (T.vertexModelEmbedding σ hσ).injective
  | hyperbolic =>
    have hi : LinearIndependent ℝ
        (fun x : σ.image (T.chart σ) => HyperbolicSpace.lift x.val) := by
      simpa only [simplexVertices, Finset.coe_sort_coe] using h
    exact hi.comp (T.vertexModelEmbedding σ hσ) (T.vertexModelEmbedding σ hσ).injective

/-- An assignment preserving the distances of every finite vertex simplex. -/
def IsVertexIsometry (v : P → Model κ n) : Prop :=
  ∀ σ ∈ T.simplices, ∀ x ∈ σ, ∀ y ∈ σ,
    dist (v x) (v y) = dist (T.chart σ x) (T.chart σ y)

theorem exists_cell_vertex_motion (v : P → Model κ n) (hv : T.IsVertexIsometry v)
    (σ : Finset P) (hσ : σ ∈ T.simplices) :
    ∃ R : ModelEmbedding κ n n, ∀ x ∈ σ, R.toFun (T.chart σ x) = v x := by
  obtain ⟨R, hR⟩ := exists_model_vertex_motion κ n (fun x : σ => T.chart σ x.val)
    (fun x : σ => v x.val) (T.vertexModel_independent σ hσ)
    (fun x y => (hv σ hσ x.val x.property y.val y.property).symm)
  exact ⟨R, fun x hx => hR ⟨x, hx⟩⟩

theorem cell_vertex_motions_agree (v : P → Model κ n)
    (σ τ : Finset P) (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
    (Rσ Rτ : ModelEmbedding κ n n)
    (hRσ : ∀ x ∈ σ, Rσ.toFun (T.chart σ x) = v x)
    (hRτ : ∀ x ∈ τ, Rτ.toFun (T.chart τ x) = v x)
    (x : P) (hxσ : x ∈ T.cell σ) (hxτ : x ∈ T.cell τ) :
    Rσ.toFun (T.chart σ x) = Rτ.toFun (T.chart τ x) := by
  let υ := σ ∩ τ
  have hυσ : υ ⊆ σ := Finset.inter_subset_left
  have hυτ : υ ⊆ τ := Finset.inter_subset_right
  have hxυ : x ∈ T.cell υ := by
    rw [← T.intersection σ hσ τ hτ]
    exact ⟨hxσ, hxτ⟩
  have hV : (υ.image (T.chart σ)).image Rσ.toFun = υ.image v := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro z hz
    exact hRσ z (hυσ hz)
  have hmem : Rσ.toFun (T.chart σ x) ∈ hull κ n (υ.image v) := by
    rw [← hV, ← Rσ.image_hull, ← T.image_face σ hσ υ hυσ]
    exact Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hxυ)
  apply eq_of_mem_hull_of_dist_eq κ n hmem
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  rw [← hRσ a (hυσ ha), Rσ.isometry.dist_eq, hRσ a (hυσ ha),
    ← hRτ a (hυτ ha), Rτ.isometry.dist_eq]
  exact T.metric_coherence σ hσ τ hτ x ⟨hxσ, hxτ⟩ a
    ⟨T.vertices_mem σ hσ (hυσ ha), T.vertices_mem τ hτ (hυτ ha)⟩

/-- A vertex isometry extends over every cell, with compatibility proved on
all common faces. -/
theorem exists_folding_of_vertex_isometry (v : P → Model κ n) (hv : T.IsVertexIsometry v) :
    ∃ q : P → Model κ n, Continuous q ∧
      (∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
        dist (q x) (q y) = dist (T.chart σ x) (T.chart σ y)) ∧
      ∀ σ ∈ T.simplices, ∀ x ∈ σ, q x = v x := by
  letI : Finite T.simplices := T.finite_simplices.to_subtype
  let R (σ : T.simplices) : ModelEmbedding κ n n :=
    (T.exists_cell_vertex_motion v hv σ.val σ.property).choose
  have hR (σ : T.simplices) : ∀ x ∈ σ.val, (R σ).toFun (T.chart σ.val x) = v x :=
    (T.exists_cell_vertex_motion v hv σ.val σ.property).choose_spec
  let C : FiniteClosedCover P T.simplices :=
    ⟨fun σ => T.cell σ.val, fun x => by
      obtain ⟨σ, hσ, hx⟩ := T.cover x
      exact ⟨⟨σ, hσ⟩, hx⟩, fun σ => T.closed_cell σ.val σ.property⟩
  let f (σ : T.simplices) (x : C.cell σ) : Model κ n := (R σ).toFun (T.chart σ.val x.val)
  have hf (σ : T.simplices) : Continuous (f σ) := by
    exact (R σ).isometry.continuous.comp
      (continuousOn_iff_continuous_domRestrict.mp (T.chart_continuousOn σ.val σ.property))
  have hagree : ∀ (σ τ : T.simplices) (x : P) (hxσ : x ∈ C.cell σ) (hxτ : x ∈ C.cell τ),
      f σ ⟨x, hxσ⟩ = f τ ⟨x, hxτ⟩ := by
    intro σ τ x hxσ hxτ
    exact T.cell_vertex_motions_agree v σ.val τ.val σ.property τ.property
      (R σ) (R τ) (hR σ) (hR τ) x hxσ hxτ
  refine ⟨C.glue f, C.continuous_glue f hf hagree, ?_, ?_⟩
  · intro σ hσ x hx y hy
    rw [C.glue_eq f hagree ⟨σ, hσ⟩ ⟨x, hx⟩, C.glue_eq f hagree ⟨σ, hσ⟩ ⟨y, hy⟩]
    exact (R ⟨σ, hσ⟩).isometry.dist_eq _ _
  · intro σ hσ x hx
    rw [C.glue_eq f hagree ⟨σ, hσ⟩ ⟨x, T.vertices_mem σ hσ hx⟩]
    exact hR ⟨σ, hσ⟩ x hx

end FiniteChartedComplex
end ArchivePLGeometry
