module

public import PLGeometry.SphericalComplexRealization
public import PLGeometry.BarycentricRestrictionGeometry
public import PLGeometry.ModelProjectiveConverse
public import PLGeometry.ChartedCellRigidity
public import PLGeometry.ChartedRefinement
public import PLGeometry.BarycentricPolytopes

/-! # Ordinary coordinate simplices of a refined spherical realization -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.Barycentric

universe u
variable {ι : Type u} [Fintype ι] {n : ℕ}

local instance sphericalRefinementDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalRefinementCoordinateEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem chartPoint_injectiveOn (σ : Finset ι) (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i : σ => (v i.val).val)) :
    Set.InjOn (chartPoint v) (weightsOn σ) := by
  intro x hx y hy he
  rw [chartPoint_restrict σ v hv ⟨x, hx⟩, chartPoint_restrict σ v hv ⟨y, hy⟩] at he
  have hh := (restrict_injective σ) (SphericalBarycentric.point_injective _ hv he)
  exact congrArg Subtype.val hh

theorem chartPoint_represents (σ : Finset ι) (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i : σ => (v i.val).val)) (x : weightsOn σ) :
    ModelBarycentric.Represents .spherical n (fun i : σ => v i.val)
      (restrict σ x).val (chartPoint v x.val) := by
  rw [chartPoint_restrict σ v hv x]
  exact ModelBarycentric.point_represents (κ := .spherical) (n := n)
    (fun i : σ => v i.val) hv (restrict σ x)

namespace SphericalData

variable {K : Complex ι} (D : SphericalData K n)
    (U : FiniteChartedComplex .spherical n K.Space)

local instance sphericalRefinementSpaceEq : DecidableEq K.Space := Classical.decEq _

theorem coordinate_cell_geometry
    {V : Finset K.Space} (hV : V ∈ U.simplices) {σ : Finset ι} (hσ : σ ∈ K.faces)
    (hcell : ∀ x ∈ U.cell V, x.val ∈ weightsOn σ)
    (hmetric : ∀ x ∈ U.cell V, ∀ y ∈ U.cell V,
      dist (chartPoint (D.vertex σ) x.val) (chartPoint (D.vertex σ) y.val) =
        dist (U.chart V x) (U.chart V y)) :
    AffineIndependent ℝ (fun v : V => v.val.val) ∧
      (Subtype.val : K.Space → (ι → ℝ)) '' U.cell V =
        convexHull ℝ (V.image Subtype.val : Set (ι → ℝ)) := by
  let q : K.Space → GeodesicSphere n := fun x => chartPoint (D.vertex σ) x.val
  have hgeom := U.folding_cell_geometry V hV q hmetric
  have hqinj : Set.InjOn q {x : K.Space | x.val ∈ weightsOn σ} := by
    intro x hx y hy he
    exact Subtype.ext (chartPoint_injectiveOn σ (D.vertex σ) (D.independent σ hσ) hx hy he)
  let v : V → GeodesicSphere n := fun x => q x.val
  let w : V → SphericalBarycentric.Weights σ :=
    fun x => restrict σ ⟨x.val.val, hcell x.val (U.vertices_mem V hV x.property)⟩
  have hrep (x : V) : ModelBarycentric.Represents .spherical n
      (fun i : σ => D.vertex σ i.val) (w x).val (v x) :=
    chartPoint_represents σ (D.vertex σ) (D.independent σ hσ) _
  have hi : LinearIndependent ℝ (fun x : V => (v x).val) := by
    apply linearIndependent_of_gram_eq (fun x : V => (U.chart V x.val).val) _
      (U.chart_vertex_independent hV)
    intro x y
    rw [← GeodesicSphere.cos_dist, ← GeodesicSphere.cos_dist]
    exact congrArg Real.cos (hmetric x.val (U.vertices_mem V hV x.property)
      y.val (U.vertices_mem V hV y.property)).symm
  have hiw := ModelBarycentric.affineIndependent_of_independent (κ := .spherical) (n := n)
    (fun i : σ => D.vertex σ i.val) v w hrep hi
  have hic : AffineIndependent ℝ (fun x : V => x.val.val) :=
    (affineIndependent_restrict_iff σ (fun x : V =>
      ⟨x.val.val, hcell x.val (U.vertices_mem V hV x.property)⟩)).mp hiw
  refine ⟨hic, ?_⟩
  have hvi : Function.Injective v := by
    intro x y he
    apply Subtype.ext
    exact hqinj (hcell x.val (U.vertices_mem V hV x.property))
      (hcell y.val (U.vertices_mem V hV y.property)) he
  have hfin : Finset.univ.image v = V.image q := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.val, x.property, hx⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨⟨x, hx⟩, he⟩
  have hset : Set.range (fun x : V => x.val.val) = (V.image Subtype.val : Set (ι → ℝ)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨⟨x, hx⟩, rfl⟩
  have hiff (x : K.Space) (hx : x.val ∈ weightsOn σ) :
      q x ∈ hull .spherical n (V.image q) ↔
        x.val ∈ convexHull ℝ (V.image Subtype.val : Set (ι → ℝ)) := by
    have hm := ModelBarycentric.represents_hull_iff (κ := .spherical) (n := n)
      (fun i : σ => D.vertex σ i.val) (D.independent σ hσ) v hvi w hrep
      (restrict σ ⟨x.val, hx⟩) (q x)
      (chartPoint_represents σ (D.vertex σ) (D.independent σ hσ) ⟨x.val, hx⟩)
    rw [hfin] at hm
    have hr := restrict_mem_convexHull_iff σ
      (fun x : V => ⟨x.val.val, hcell x.val (U.vertices_mem V hV x.property)⟩) ⟨x.val, hx⟩
    rw [hset] at hr
    exact hm.trans hr
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (hiff x (hcell x hx)).mp
    rw [← hgeom.2]
    exact ⟨x, hx, rfl⟩
  · intro hz
    have hzw : z ∈ weightsOn σ := by
      apply convexHull_min ?_ (weightsOn_polytope σ).convex hz
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact hcell x (U.vertices_mem V hV hx)
    let x : K.Space := ⟨z, Set.mem_iUnion₂.mpr ⟨σ, hσ, hzw⟩⟩
    have hxq := (hiff x hzw).mpr hz
    rw [← hgeom.2] at hxq
    obtain ⟨y, hy, he⟩ := hxq
    have hyx := hqinj (hcell y hy) hzw he
    exact ⟨x, hyx ▸ hy, rfl⟩

theorem refinement_coordinate_geometry (hU : U.Refines D.toChartedComplex)
    {V : Finset K.Space} (hV : V ∈ U.simplices) :
    AffineIndependent ℝ (fun v : V => v.val.val) ∧
      (Subtype.val : K.Space → (ι → ℝ)) '' U.cell V =
        convexHull ℝ (V.image Subtype.val : Set (ι → ℝ)) := by
  obtain ⟨W, hW, hcell, hm⟩ := hU.cell V hV
  apply D.coordinate_cell_geometry U hV (D.labels_mem hW)
  · exact fun x hx => hcell hx
  · exact fun x hx y hy => (hm x hx y hy).symm

end SphericalData
end ArchivePLGeometry.Barycentric
