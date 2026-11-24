module

public import PLGeometry.EuclideanLinkAtlas
public import PLGeometry.LinkBoundaryInclusion
public import PLGeometry.ComplexReweighting
public import BrehmApprox.RadialBoundaryEmbedding

/-! # Angular coordinates as radial projection of the visible boundary -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean (n + 1) P)

local instance euclideanLinkBoundaryDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance euclideanLinkBoundaryModelEq : DecidableEq (Model .euclidean (n + 1)) := Classical.decEq _
local instance euclideanLinkBoundaryVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem euclidean_link_radius_pos (p : P) (v : T.LinkVertex p) :
    0 < T.radialDistance p v.val := by
  obtain ⟨hvp, σ, hσ, hpσ, hvσ⟩ := v.property
  rw [T.radialDistance_eq p hσ hpσ (T.vertices_mem σ hσ hvσ)]
  apply dist_pos.mpr
  intro he
  exact hvp (T.chart_injectiveOn σ hσ (T.vertices_mem σ hσ hvσ) hpσ he.symm)

def euclideanLinkReweight (p : P) : (T.linkComplex p).Space ≃ₜ (T.linkComplex p).Space :=
  (T.linkComplex p).reweightHomeomorph (fun v => (T.radialDistance p v.val)⁻¹)
    (fun v => inv_pos.mpr (T.euclidean_link_radius_pos p v))

theorem euclideanLinkReweight_mem_region (p : P) (σ : Finset P) (x : (T.linkComplex p).Space) :
    T.euclideanLinkReweight p x ∈ T.linkRegion p σ ↔ x ∈ T.linkRegion p σ := by
  rw [T.mem_linkRegion_iff_weightsOn, T.mem_linkRegion_iff_weightsOn]
  exact (T.linkComplex p).reweight_mem_weightsOn_iff _ _ _ _

def euclideanBoundaryPoint (p : P) (x : (T.linkComplex p).Space) : P :=
  T.linkBoundaryInclusion p (T.euclideanLinkReweight p x)

theorem euclideanBoundaryPoint_injective (p : P) : Function.Injective (T.euclideanBoundaryPoint p) :=
  (T.linkBoundaryInclusion_injective p).comp (T.euclideanLinkReweight p).injective

theorem euclideanBoundaryPoint_mem {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices)
    {x : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) :
    T.euclideanBoundaryPoint p x ∈ T.cell σ :=
  T.linkBoundaryInclusion_mem_of_region hσ ((T.euclideanLinkReweight_mem_region p σ x).mpr hx)

theorem chart_euclideanBoundaryPoint_sub {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    T.chart σ (T.euclideanBoundaryPoint p x) - T.chart σ p =
      (BarycentricReweighting.total (fun v : T.LinkVertex p => (T.radialDistance p v.val)⁻¹) x.val)⁻¹ •
        SphericalBarycentric.vector (T.euclideanAngularVertex p σ) x.val := by
  let y := T.euclideanLinkReweight p x
  have hy : y ∈ T.linkRegion p σ := (T.euclideanLinkReweight_mem_region p σ x).mpr hx
  have hr := T.cellWeights_represents σ hσ
    ⟨T.linkBoundaryInclusion p y, T.linkBoundaryInclusion_mem_of_region hσ hy⟩
  change (∑ v : σ, (T.cellWeights σ hσ
    ⟨T.linkBoundaryInclusion p y, T.linkBoundaryInclusion_mem_of_region hσ hy⟩).val v • T.chart σ v.val) =
      T.chart σ (T.linkBoundaryInclusion p y) at hr
  rw [T.sum_cellWeights_linkBoundaryInclusion hσ y hy (T.chart σ)] at hr
  change T.chart σ (T.linkBoundaryInclusion p y) - T.chart σ p = _
  rw [← hr]
  have hs := (T.linkComplex p).weight_sum y
  have he : (∑ i, y.val i • T.chart σ i.val) - T.chart σ p =
      ∑ i, y.val i • (T.chart σ i.val - T.chart σ p) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul]
  rw [he]
  unfold SphericalBarycentric.vector
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ∈ σ
  · have hn := T.euclideanAngularVertex_ne_zero hσ hpσ i hi
    have hd : T.radialDistance p i.val = ‖T.chart σ i.val - T.chart σ p‖ := by
      rw [T.radialDistance_eq p hσ hpσ (T.vertices_mem σ hσ hi), dist_comm, dist_eq_norm]
    change ((T.radialDistance p i.val)⁻¹ * x.val i /
      BarycentricReweighting.total (fun v : T.LinkVertex p => (T.radialDistance p v.val)⁻¹) x.val) •
      (T.chart σ i.val - T.chart σ p) = _
    rw [euclideanAngularVertex, CrossPolytope.sphereNormalize_val hn]
    simp only [NormedSpace.normalize, smul_smul, hd, div_eq_mul_inv]
    congr 1
    ring
  · have hz : x.val i = 0 := ((T.mem_linkRegion_iff_weightsOn p σ x).mp hx).2 i
      (by simpa only [T.mem_linkLabels] using hi)
    change ((T.radialDistance p i.val)⁻¹ * x.val i / _) • _ = _
    rw [hz, mul_zero, zero_div, zero_smul, zero_smul, smul_zero]

theorem euclideanAngularChart_eq_boundary_projection {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    (T.euclideanAngularChart p σ x).val =
      NormedSpace.normalize (T.chart σ (T.euclideanBoundaryPoint p x) - T.chart σ p) := by
  rw [T.chart_euclideanBoundaryPoint_sub hσ hpσ x hx]
  have ht := BarycentricReweighting.total_pos
    (fun v : T.LinkVertex p => (T.radialDistance p v.val)⁻¹)
    (fun v => inv_pos.mpr (T.euclidean_link_radius_pos p v))
    ⟨x.val, (T.linkComplex p).weight_nonneg x, (T.linkComplex p).weight_sum x⟩
  rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr ht)]
  exact CrossPolytope.sphereNormalize_val (T.euclideanAngularChart_vector_ne_zero hσ hpσ hx)

theorem chart_euclideanBoundaryPoint_mem_visibleBoundary {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    T.chart σ (T.euclideanBoundaryPoint p x) ∈
      visibleBoundary (σ.image (T.chart σ)) (T.chart σ p) := by
  let y := T.euclideanLinkReweight p x
  let U := T.linkSourceVertices ((T.linkComplex p).support y)
  have hsub : U ⊆ σ := (T.euclideanLinkReweight_mem_region p σ x).mpr hx
  have hpU := (T.linkCoface_spec ((T.linkComplex p).support_mem y)).2.2.2
  have hface : T.chart σ '' T.cell U = convexHull ℝ (U.image (T.chart σ) : Set _) :=
    T.image_face σ hσ U hsub
  refine ⟨U.image (T.chart σ), Finset.image_subset_image hsub, ?_, ?_⟩
  · intro h
    rw [← hface] at h
    obtain ⟨z, hz, he⟩ := h
    have hzp := T.chart_injectiveOn σ hσ (T.cell_mono hσ hsub hz) hpσ he
    exact hpU (Eq.mp (congrArg (fun q : P => q ∈ T.cell U) hzp) hz)
  · rw [← hface]
    exact ⟨_, T.linkBoundaryInclusion_mem_support p y, rfl⟩

theorem euclideanAngularChart_injectiveOn {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    Set.InjOn (T.euclideanAngularChart p σ) (T.linkRegion p σ) := by
  intro x hx y hy he
  apply T.euclideanBoundaryPoint_injective p
  apply T.chart_injectiveOn σ hσ (T.euclideanBoundaryPoint_mem hσ hx)
    (T.euclideanBoundaryPoint_mem hσ hy)
  have hV : AffineIndependent ℝ ((↑) : σ.image (T.chart σ) → Model .euclidean (n + 1)) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using T.simplex σ hσ
  have hpV : T.chart σ p ∈ convexHull ℝ (σ.image (T.chart σ) : Set _) := by
    have h := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at h
    exact h
  apply radialProjection_injectiveOn_visibleBoundary _ hV hpV
    (T.chart_euclideanBoundaryPoint_mem_visibleBoundary hσ hpσ x hx)
    (T.chart_euclideanBoundaryPoint_mem_visibleBoundary hσ hpσ y hy)
  change NormedSpace.normalize (T.chart σ (T.euclideanBoundaryPoint p x) - T.chart σ p) =
    NormedSpace.normalize (T.chart σ (T.euclideanBoundaryPoint p y) - T.chart σ p)
  rw [← T.euclideanAngularChart_eq_boundary_projection hσ hpσ x hx,
    ← T.euclideanAngularChart_eq_boundary_projection hσ hpσ y hy, he]

end ArchivePLGeometry.FiniteChartedComplex
