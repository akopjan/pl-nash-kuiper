module

public import PLGeometry.BarycentricRealization
public import PLGeometry.ChartedComplex
public import BrehmApprox.SphericalCrossPolytope

/-!
# Realization of a finite spherical complex

Each abstract face has independent hemispherical unit-vector coordinates.
Equality of the Gram matrices on shared vertices is the entire compatibility
condition. Normalized barycentric coordinates construct the charted complex;
no global folding or intrinsic metric is assumed.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.Barycentric

universe u
variable {ι : Type u} [Fintype ι] {n : ℕ}

local instance sphericalRealizationDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalRealizationSphereDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _

def chartPoint (v : ι → GeodesicSphere n) (w : ι → ℝ) : GeodesicSphere n :=
  CrossPolytope.sphereNormalize (SphericalBarycentric.vector v w)

theorem vector_restrict (σ : Finset ι) (v : ι → GeodesicSphere n) (w : weightsOn σ) :
    SphericalBarycentric.vector v w.val =
      SphericalBarycentric.vector (fun i : σ => v i.val) (restrict σ w).val := by
  simp only [SphericalBarycentric.vector, restrict]
  rw [Finset.sum_coe_sort σ (fun i => w.val i • (v i).val)]
  exact (Finset.sum_subset (Finset.subset_univ σ) (fun i _ hi => by
    rw [w.property.2 i hi, zero_smul])).symm

theorem chartPoint_restrict (σ : Finset ι) (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i : σ => (v i.val).val)) (w : weightsOn σ) :
    chartPoint v w.val = SphericalBarycentric.point (fun i : σ => v i.val) hv (restrict σ w) := by
  unfold chartPoint
  rw [vector_restrict σ v w]
  simp only [CrossPolytope.sphereNormalize,
    dite_eq_right (SphericalBarycentric.vector_ne_zero _ hv (restrict σ w)),
    SphericalBarycentric.point]

theorem image_univ_subtype (σ : Finset ι) (v : ι → GeodesicSphere n) :
    Finset.univ.image (fun i : σ => v i.val) = σ.image v := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.property, hi⟩
  · rintro ⟨i, hi, hix⟩
    exact ⟨⟨i, hi⟩, hix⟩

theorem chartPoint_image (σ : Finset ι) (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i : σ => (v i.val).val)) :
    chartPoint v '' weightsOn σ = sphericalCell (σ.image v) := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [chartPoint_restrict σ v hv ⟨w, hw⟩]
    have h := SphericalBarycentric.point_mem (fun i : σ => v i.val) hv (restrict σ ⟨w, hw⟩)
    simpa only [image_univ_subtype] using h
  · intro hx
    have hx' : x ∈ Set.range (SphericalBarycentric.point (fun i : σ => v i.val) hv) := by
      rw [SphericalBarycentric.range_point, image_univ_subtype]
      exact hx
    obtain ⟨a, ha⟩ := hx'
    obtain ⟨w, hw⟩ := restrict_surjective σ a
    refine ⟨w.val, w.property, ?_⟩
    rw [chartPoint_restrict σ v hv w, hw, ha]

theorem chartPoint_single (v : ι → GeodesicSphere n) (i : ι) :
    chartPoint v (Pi.single i 1) = v i := by
  have he : SphericalBarycentric.vector v (Pi.single i 1) = (v i).val := by
    simp [SphericalBarycentric.vector, Pi.single_apply, ite_smul]
  apply GeodesicSphere.ext
  rw [chartPoint, he, CrossPolytope.sphereNormalize_val (v i).val_ne_zero,
    NormedSpace.normalize_eq_self_of_norm_eq_one (v i).norm_val]

theorem independent_image (σ : Finset ι) (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i : σ => (v i.val).val)) :
    LinearIndependent ℝ (fun x : σ.image v => x.val.val) := by
  let e : σ → σ.image v := fun i => ⟨v i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  have hbij : Function.Bijective e := by
    constructor
    · intro i j hij
      exact hv.injective (congrArg (fun x : σ.image v => x.val.val) hij)
    · intro x
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp x.property
      exact ⟨⟨i, hi⟩, Subtype.ext hix⟩
  let e' := Equiv.ofBijective e hbij
  have h := hv.comp e'.symm e'.symm.injective
  convert h using 1
  funext x
  exact (congrArg (fun y : σ.image v => y.val.val) (e'.apply_symm_apply x)).symm

structure SphericalData (K : Complex ι) (n : ℕ) where
  vertex : Finset ι → ι → GeodesicSphere n
  independent : ∀ σ ∈ K.faces, LinearIndependent ℝ (fun i : σ => (vertex σ i.val).val)
  hemisphere : ∀ σ ∈ K.faces, InOpenHemisphere (σ.image (vertex σ))
  gram : ∀ σ ∈ K.faces, ∀ τ ∈ K.faces, ∀ i ∈ σ ∩ τ, ∀ j ∈ σ ∩ τ,
    ⟪(vertex σ i).val, (vertex σ j).val⟫_ℝ =
      ⟪(vertex τ i).val, (vertex τ j).val⟫_ℝ

namespace SphericalData

variable {K : Complex ι} (D : SphericalData K n)

local instance sphericalRealizationSpaceDecidableEq : DecidableEq K.Space := Classical.decEq _

def chart (S : Finset K.Space) (x : K.Space) : GeodesicSphere n :=
  chartPoint (D.vertex (K.labels S)) x.val

include D in
theorem labels_mem {S : Finset K.Space} (hS : S ∈ K.simplices) : K.labels S ∈ K.faces := by
  obtain ⟨σ, hσ, rfl⟩ := hS
  simpa only [K.labels_vertices] using hσ

include D in
theorem vertices_labels {S : Finset K.Space} (hS : S ∈ K.simplices) : K.vertices (K.labels S) = S := by
  obtain ⟨σ, _, rfl⟩ := hS
  rw [K.labels_vertices]

@[simp] theorem chart_vertex (S : Finset K.Space) (i : ι) :
    D.chart S (K.vertex i) = D.vertex (K.labels S) i := chartPoint_single _ _

theorem image_chart_vertices (S T : Finset K.Space) (hT : T ∈ K.simplices) :
    T.image (D.chart S) = (K.labels T).image (D.vertex (K.labels S)) := by
  calc
    T.image (D.chart S) = (K.vertices (K.labels T)).image (D.chart S) :=
      congrArg (fun U : Finset K.Space => U.image (D.chart S)) (D.vertices_labels hT).symm
    _ = _ := by
      simp only [Complex.vertices, Finset.image_image, Function.comp_def, D.chart_vertex]

include D in
theorem independent_subface {S T : Finset K.Space} (hS : S ∈ K.simplices) (hTS : T ⊆ S) :
    LinearIndependent ℝ (fun i : K.labels T => (D.vertex (K.labels S) i.val).val) := by
  let e : K.labels T ↪ K.labels S :=
    { toFun := fun i => ⟨i.val, K.labels_mono hTS i.property⟩
      inj' := fun _ _ h => Subtype.ext (congrArg (fun j : K.labels S => j.val) h) }
  exact (D.independent _ (D.labels_mem hS)).comp e e.injective

theorem image_cell_with_chart (S T : Finset K.Space) (hT : T ∈ K.simplices)
    (hv : LinearIndependent ℝ (fun i : K.labels T => (D.vertex (K.labels S) i.val).val)) :
    D.chart S '' K.cell T = sphericalCell ((K.labels T).image (D.vertex (K.labels S))) := by
  rw [← chartPoint_image (K.labels T) (D.vertex (K.labels S)) hv]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.val, hy, rfl⟩
  · rintro ⟨w, hw, hx⟩
    let y : K.Space := ⟨w, Set.mem_iUnion₂.mpr ⟨K.labels T, D.labels_mem hT, hw⟩⟩
    exact ⟨y, hw, hx⟩

theorem chart_simplex (S : Finset K.Space) (hS : S ∈ K.simplices) :
    simplexVertices .spherical n (S.image (D.chart S)) := by
  rw [D.image_chart_vertices S S hS]
  refine ⟨D.hemisphere _ (D.labels_mem hS), ?_⟩
  simpa only [Finset.coe_sort_coe] using
    independent_image (K.labels S) (D.vertex (K.labels S)) (D.independent _ (D.labels_mem hS))

theorem chart_image_cell (S : Finset K.Space) (hS : S ∈ K.simplices) :
    D.chart S '' K.cell S = hull .spherical n (S.image (D.chart S)) := by
  rw [D.image_chart_vertices S S hS]
  exact D.image_cell_with_chart S S hS (D.independent _ (D.labels_mem hS))

theorem chart_image_face (S : Finset K.Space) (hS : S ∈ K.simplices)
    (T : Finset K.Space) (hTS : T ⊆ S) :
    D.chart S '' K.cell T = hull .spherical n (T.image (D.chart S)) := by
  have hT := K.simplices_downward hS hTS
  rw [D.image_chart_vertices S T hT]
  exact D.image_cell_with_chart S T hT (D.independent_subface hS hTS)

/-- The cell chart, obtained as a composite of explicit barycentric homeomorphisms. -/
def cellHomeomorph (S : Finset K.Space) (hS : S ∈ K.simplices) :
    K.cell S ≃ₜ hull .spherical n (S.image (D.chart S)) := by
  let σ := K.labels S
  let hσ := D.labels_mem hS
  let e₀ : K.cell S ≃ₜ K.cell (K.vertices σ) :=
    Homeomorph.setCongr (congrArg K.cell (D.vertices_labels hS).symm)
  let e₁ := K.cellWeightsHomeomorph σ hσ
  let e₂ := restrictHomeomorph σ
  let e₃ := SphericalBarycentric.homeomorph (fun i : σ => D.vertex σ i.val) (D.independent σ hσ)
  have he : sphericalCell (Finset.univ.image (fun i : σ => D.vertex σ i.val)) =
      hull .spherical n (S.image (D.chart S)) := by
    rw [image_univ_subtype, D.image_chart_vertices S S hS]
    rfl
  exact e₀.trans (e₁.trans (e₂.trans (e₃.trans (Homeomorph.setCongr he))))

theorem cellHomeomorph_apply (S : Finset K.Space) (hS : S ∈ K.simplices)
    (x : K.cell S) : (D.cellHomeomorph S hS x).val = D.chart S x.val := by
  change SphericalBarycentric.point (fun i : K.labels S => D.vertex (K.labels S) i.val)
    (D.independent _ (D.labels_mem hS)) (restrict (K.labels S) ⟨x.val.val, x.property⟩) =
      chartPoint (D.vertex (K.labels S)) x.val.val
  exact (chartPoint_restrict _ _ _ _).symm

theorem metric_coherence (S : Finset K.Space) (hS : S ∈ K.simplices)
    (T : Finset K.Space) (hT : T ∈ K.simplices)
    (x : K.Space) (hx : x ∈ K.cell S ∩ K.cell T)
    (y : K.Space) (hy : y ∈ K.cell S ∩ K.cell T) :
    dist (D.chart S x) (D.chart S y) = dist (D.chart T x) (D.chart T y) := by
  let σ := K.labels S ∩ K.labels T
  have hσS : σ ⊆ K.labels S := Finset.inter_subset_left
  have hσT : σ ⊆ K.labels T := Finset.inter_subset_right
  have hS' : LinearIndependent ℝ (fun i : σ => (D.vertex (K.labels S) i.val).val) := by
    let e : σ ↪ K.labels S := ⟨fun i => ⟨i.val, hσS i.property⟩, fun _ _ h => Subtype.ext (congrArg (fun j : K.labels S => j.val) h)⟩
    exact (D.independent _ (D.labels_mem hS)).comp e e.injective
  have hT' : LinearIndependent ℝ (fun i : σ => (D.vertex (K.labels T) i.val).val) := by
    let e : σ ↪ K.labels T := ⟨fun i => ⟨i.val, hσT i.property⟩, fun _ _ h => Subtype.ext (congrArg (fun j : K.labels T => j.val) h)⟩
    exact (D.independent _ (D.labels_mem hT)).comp e e.injective
  have hx' : x.val ∈ weightsOn σ := by
    rw [← weightsOn_inter]
    exact hx
  have hy' : y.val ∈ weightsOn σ := by
    rw [← weightsOn_inter]
    exact hy
  change dist (chartPoint _ x.val) (chartPoint _ y.val) = dist (chartPoint _ x.val) (chartPoint _ y.val)
  rw [chartPoint_restrict σ _ hS' ⟨x.val, hx'⟩, chartPoint_restrict σ _ hS' ⟨y.val, hy'⟩,
    chartPoint_restrict σ _ hT' ⟨x.val, hx'⟩, chartPoint_restrict σ _ hT' ⟨y.val, hy'⟩]
  apply SphericalBarycentric.point_dist_eq_of_gram
  intro i j
  exact D.gram _ (D.labels_mem hS) _ (D.labels_mem hT) i.val i.property j.val j.property

/-- A finite spherical charted complex constructed from its vertex Gram data. -/
def toChartedComplex : FiniteChartedComplex .spherical n K.Space where
  simplices := K.simplices
  finite_simplices := K.finite_simplices
  cell := K.cell
  chart := D.chart
  cover := K.cover
  vertices_mem := fun _ hS => K.vertices_mem hS
  simplex := D.chart_simplex
  image_cell := D.chart_image_cell
  cellHomeomorph := D.cellHomeomorph
  cellHomeomorph_apply := D.cellHomeomorph_apply
  faces := fun _ hS _ hTS => K.simplices_downward hS hTS
  image_face := D.chart_image_face
  intersection := by
    intro S _ T _
    convert K.cell_inter S T using 1 <;> congr 1 <;> ext x <;> simp
  metric_coherence := D.metric_coherence

end SphericalData
end ArchivePLGeometry.Barycentric
