module

public import PLGeometry.ChartedBarycentricLinear
public import PLGeometry.BarycentricPolytopes
public import PLGeometry.ModelProjectiveGeometry
public import BrehmApprox.PositiveHullTransitivity

/-! # Genuine geodesic simplex transport through source barycentric coordinates -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry

local instance chartedProjectiveDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem hull_transitive (κ : Geometry) (n : ℕ) (A B : Finset (Model κ n))
    (h : (A : Set (Model κ n)) ⊆ hull κ n B) : hull κ n A ⊆ hull κ n B := by
  cases κ with
  | euclidean => exact convexHull_min h (convex_convexHull ℝ _)
  | spherical => exact positiveRayHull_transitive GeodesicSphere.val A B h
  | hyperbolic => exact positiveRayHull_transitive HyperbolicSpace.lift A B h

namespace FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance chartedProjectiveModelEq : DecidableEq (Model κ n) := Classical.decEq _
local instance chartedProjectiveCoordinateEq : DecidableEq (T.Vertex → ℝ) := Classical.decEq _
local instance chartedProjectiveEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance chartedProjectiveSDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance chartedProjectiveHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _

def subcellVertexChartEquiv {σ : Finset P} (hσ : σ ∈ T.simplices) (V : Finset P)
    (hV : (V : Set P) ⊆ T.cell σ) : V ≃ V.image (T.chart σ) :=
  Equiv.ofBijective (fun v => ⟨T.chart σ v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩) (by
    constructor
    · intro v w he
      apply Subtype.ext
      apply T.chart_injectiveOn σ hσ (hV v.property) (hV w.property)
      exact congrArg Subtype.val he
    · intro z
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp z.property
      exact ⟨⟨v, hv⟩, Subtype.ext he⟩)

theorem chart_subcellVertexChartEquiv_symm {σ : Finset P} (hσ : σ ∈ T.simplices)
    (V : Finset P) (hV : (V : Set P) ⊆ T.cell σ) (z : V.image (T.chart σ)) :
    T.chart σ ((T.subcellVertexChartEquiv hσ V hV).symm z).val = z.val := by
  have he := congrArg Subtype.val ((T.subcellVertexChartEquiv hσ V hV).apply_symm_apply z)
  exact he

theorem barycentric_simplex_transfer {σ : Finset P} (hσ : σ ∈ T.simplices)
    (V : Finset P) (hV : (V : Set P) ⊆ T.cell σ)
    (hi : AffineIndependent ℝ ((↑) : V.image T.barycentricCoords → (T.Vertex → ℝ))) :
    simplexVertices κ n (V.image (T.chart σ)) := by
  let p : V → T.cell σ := fun v => ⟨v.val, hV v.property⟩
  let e : V ↪ V.image T.barycentricCoords :=
    { toFun := fun v => ⟨T.barycentricCoords v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
      inj' := by
        intro v w he
        exact Subtype.ext (T.barycentricCoords_injective (congrArg Subtype.val he)) }
  have hip : AffineIndependent ℝ (fun v : V => T.barycentricCoords (p v).val) :=
    hi.comp_embedding e
  have hiw := T.cellWeights_independent_of_coords hσ p hip
  have him := ModelBarycentric.independent_of_barycentric
    (fun v : σ => T.chart σ v.val) (T.chart_vertex_independent hσ)
    (fun v : V => T.chart σ v.val) (fun v => T.cellWeights σ hσ (p v))
    (fun v => T.cellWeights_represents σ hσ (p v)) hiw
  let q := (T.subcellVertexChartEquiv hσ V hV).symm.toEmbedding
  have hq (z : V.image (T.chart σ)) : T.chart σ (q z).val = z.val :=
    T.chart_subcellVertexChartEquiv_symm hσ V hV z
  cases κ with
  | euclidean =>
    change AffineIndependent ℝ (fun v : V => T.chart σ v.val) at him
    have h := him.comp_embedding q
    change AffineIndependent ℝ ((↑) : V.image (T.chart σ) → Model .euclidean n)
    convert h using 1
    funext z
    exact (hq z).symm
  | spherical =>
    refine ⟨?_, ?_⟩
    · obtain ⟨o, ho⟩ := (T.simplex σ hσ).1
      refine ⟨o, ?_⟩
      intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      apply sphericalCell_inner_pos (σ.image (T.chart σ)) o ho
      change T.chart σ v ∈ hull .spherical n (σ.image (T.chart σ))
      rw [← T.image_cell σ hσ]
      exact ⟨v, hV hv, rfl⟩
    · change LinearIndependent ℝ (fun v : V => (T.chart σ v.val).val) at him
      have h := him.comp q q.injective
      change LinearIndependent ℝ (fun z : V.image (T.chart σ) => z.val.val)
      convert h using 1
      funext z
      exact (congrArg GeodesicSphere.val (hq z)).symm
  | hyperbolic =>
    change LinearIndependent ℝ (fun v : V => HyperbolicSpace.lift (T.chart σ v.val)) at him
    have h := him.comp q q.injective
    change LinearIndependent ℝ (fun z : V.image (T.chart σ) => HyperbolicSpace.lift z.val)
    convert h using 1
    funext z
    exact (congrArg HyperbolicSpace.lift (hq z)).symm

theorem barycentric_hull_iff {σ : Finset P} (hσ : σ ∈ T.simplices)
    (V : Finset P) (hV : (V : Set P) ⊆ T.cell σ) (x : T.cell σ) :
    T.chart σ x.val ∈ hull κ n (V.image (T.chart σ)) ↔
      T.barycentricCoords x.val ∈ convexHull ℝ (V.image T.barycentricCoords : Set (T.Vertex → ℝ)) := by
  let p : V → T.cell σ := fun v => ⟨v.val, hV v.property⟩
  have hinj : Function.Injective (fun v : V => T.chart σ v.val) := by
    intro v w he
    exact Subtype.ext (T.chart_injectiveOn σ hσ (hV v.property) (hV w.property) he)
  have hp := ModelBarycentric.represents_hull_iff
    (fun v : σ => T.chart σ v.val) (T.chart_vertex_independent hσ)
    (fun v : V => T.chart σ v.val) hinj (fun v => T.cellWeights σ hσ (p v))
    (fun v => T.cellWeights_represents σ hσ (p v))
    (T.cellWeights σ hσ x) (T.chart σ x.val) (T.cellWeights_represents σ hσ x)
  have hmodel : Finset.univ.image (fun v : V => T.chart σ v.val) = V.image (T.chart σ) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists]
    constructor <;> rintro ⟨v, hv, he⟩ <;> exact ⟨v, hv, he⟩
  rw [hmodel] at hp
  have hc := T.barycentricCoords_convexHull_iff hσ p x
  have hcoords : Set.range (fun v : V => T.barycentricCoords (p v).val) =
      (V.image T.barycentricCoords : Set (T.Vertex → ℝ)) := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩
    · intro hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨⟨v, hv⟩, rfl⟩
  rw [hcoords] at hc
  exact hp.trans hc.symm

theorem barycentricCoords_cell_convex {σ : Finset P} (hσ : σ ∈ T.simplices) :
    Convex ℝ (T.barycentricCoords '' T.cell σ) := by
  rw [T.barycentricCoords_image_cell hσ]
  exact (Barycentric.weightsOn_polytope _).convex

theorem mem_cell_of_barycentric_hull {σ : Finset P} (hσ : σ ∈ T.simplices)
    (V : Finset P) (hV : (V : Set P) ⊆ T.cell σ) {x : P}
    (hx : T.barycentricCoords x ∈ convexHull ℝ (V.image T.barycentricCoords : Set (T.Vertex → ℝ))) :
    x ∈ T.cell σ := by
  have hv : (V.image T.barycentricCoords : Set (T.Vertex → ℝ)) ⊆ T.barycentricCoords '' T.cell σ := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨v, hV hv, rfl⟩
  obtain ⟨y, hy, he⟩ := convexHull_min hv (T.barycentricCoords_cell_convex hσ) hx
  exact T.barycentricCoords_injective he ▸ hy

theorem barycentric_hull_transfer {σ : Finset P} (hσ : σ ∈ T.simplices)
    (V : Finset P) (hV : (V : Set P) ⊆ T.cell σ) :
    T.chart σ '' (T.barycentricCoords ⁻¹' convexHull ℝ (V.image T.barycentricCoords : Set (T.Vertex → ℝ))) =
      hull κ n (V.image (T.chart σ)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (T.barycentric_hull_iff hσ V hV ⟨x, T.mem_cell_of_barycentric_hull hσ V hV hx⟩).mpr hx
  · intro hy
    have hvertices : (V.image (T.chart σ) : Set (Model κ n)) ⊆ hull κ n (σ.image (T.chart σ)) := by
      intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      rw [← T.image_cell σ hσ]
      exact ⟨v, hV hv, rfl⟩
    have hyold := hull_transitive κ n _ _ hvertices hy
    rw [← T.image_cell σ hσ] at hyold
    obtain ⟨x, hx, rfl⟩ := hyold
    exact ⟨x, (T.barycentric_hull_iff hσ V hV ⟨x, hx⟩).mp hy, rfl⟩

end FiniteChartedComplex
end ArchivePLGeometry
