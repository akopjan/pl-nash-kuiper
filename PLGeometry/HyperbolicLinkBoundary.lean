module

public import PLGeometry.HyperbolicLinkAtlas
public import PLGeometry.LinkBoundaryInclusion
public import PLGeometry.ComplexReweighting
public import BrehmApprox.RadialBoundaryEmbedding
public import BrehmApprox.HyperbolicSimplexLink

/-! # Hyperbolic angular charts as radial projections of the Klein boundary -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.HyperbolicSpace BrehmApprox.HyperbolicLink
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

local instance hyperbolicLinkBoundaryDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance hyperbolicLinkBoundaryModelEq : DecidableEq (Model .hyperbolic (n + 1)) := Classical.decEq _
local instance hyperbolicLinkBoundaryVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem hyperbolic_link_radius_pos (p : P) (v : T.LinkVertex p) :
    0 < T.radialDistance p v.val := by
  obtain ⟨hvp, σ, hσ, hpσ, hvσ⟩ := v.property
  rw [T.radialDistance_eq p hσ hpσ (T.vertices_mem σ hσ hvσ)]
  apply dist_pos.mpr
  intro he
  exact hvp (T.chart_injectiveOn σ hσ (T.vertices_mem σ hσ hvσ) hpσ he.symm)

def hyperbolicLinkReweight (p : P) : (T.linkComplex p).Space ≃ₜ (T.linkComplex p).Space :=
  (T.linkComplex p).reweightHomeomorph (fun v => (Real.sinh (T.radialDistance p v.val))⁻¹)
    (fun v => inv_pos.mpr (Real.sinh_pos_iff.mpr (T.hyperbolic_link_radius_pos p v)))

theorem hyperbolicLinkReweight_mem_region (p : P) (σ : Finset P) (x : (T.linkComplex p).Space) :
    T.hyperbolicLinkReweight p x ∈ T.linkRegion p σ ↔ x ∈ T.linkRegion p σ := by
  rw [T.mem_linkRegion_iff_weightsOn, T.mem_linkRegion_iff_weightsOn]
  exact (T.linkComplex p).reweight_mem_weightsOn_iff _ _ _ _

def hyperbolicBoundaryPoint (p : P) (x : (T.linkComplex p).Space) : P :=
  T.linkBoundaryInclusion p (T.hyperbolicLinkReweight p x)

theorem hyperbolicBoundaryPoint_injective (p : P) : Function.Injective (T.hyperbolicBoundaryPoint p) :=
  (T.linkBoundaryInclusion_injective p).comp (T.hyperbolicLinkReweight p).injective

theorem hyperbolicBoundaryPoint_mem {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices)
    {x : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) :
    T.hyperbolicBoundaryPoint p x ∈ T.cell σ :=
  T.linkBoundaryInclusion_mem_of_region hσ ((T.hyperbolicLinkReweight_mem_region p σ x).mpr hx)

theorem hyperbolicAngularChart_eq_boundary_projection {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    (T.hyperbolicAngularChart p σ x).val =
      NormedSpace.normalize (frame (T.chart σ p) (T.chart σ (T.hyperbolicBoundaryPoint p x))) := by
  let y := T.hyperbolicLinkReweight p x
  let a := T.chart σ p
  let z := T.chart σ (T.hyperbolicBoundaryPoint p x)
  have hy : y ∈ T.linkRegion p σ := (T.hyperbolicLinkReweight_mem_region p σ x).mpr hx
  obtain ⟨c, hc, hr⟩ := T.cellWeights_represents σ hσ
    ⟨T.linkBoundaryInclusion p y, T.linkBoundaryInclusion_mem_of_region hσ hy⟩
  change (∑ v : σ, (T.cellWeights σ hσ
    ⟨T.linkBoundaryInclusion p y, T.linkBoundaryInclusion_mem_of_region hσ hy⟩).val v •
    lift (T.chart σ v.val)) = c • lift z at hr
  rw [T.sum_cellWeights_linkBoundaryInclusion hσ y hy (fun v => lift (T.chart σ v))] at hr
  let L := (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin (n + 1)))).comp
    (Hyperboloid.boostLinear a.point)
  have hcoord (v : HyperbolicSpace (n + 1)) : L (lift v) = radialVector a v := rfl
  have hvec := congrArg L hr
  simp only [map_sum, map_smul, hcoord] at hvec
  let total := BarycentricReweighting.total
    (fun v : T.LinkVertex p => (Real.sinh (T.radialDistance p v.val))⁻¹) x.val
  have ht : 0 < total := BarycentricReweighting.total_pos _
    (fun v => inv_pos.mpr (Real.sinh_pos_iff.mpr (T.hyperbolic_link_radius_pos p v)))
    ⟨x.val, (T.linkComplex p).weight_nonneg x, (T.linkComplex p).weight_sum x⟩
  have he : (∑ i, y.val i • radialVector a (T.chart σ i.val)) =
      total⁻¹ • SphericalBarycentric.vector (T.hyperbolicAngularVertex p σ) x.val := by
    unfold SphericalBarycentric.vector
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val ∈ σ
    · have hn := T.hyperbolicAngularVertex_ne_zero hσ hpσ i hi
      have hd : T.radialDistance p i.val = dist a (T.chart σ i.val) :=
        T.radialDistance_eq p hσ hpσ (T.vertices_mem σ hσ hi)
      change ((Real.sinh (T.radialDistance p i.val))⁻¹ * x.val i / total) •
        radialVector a (T.chart σ i.val) = _
      rw [hyperbolicAngularVertex, CrossPolytope.sphereNormalize_val hn]
      simp only [NormedSpace.normalize, norm_radialVector, smul_smul, hd, div_eq_mul_inv]
      congr 1
      ring
    · have hz : x.val i = 0 := ((T.mem_linkRegion_iff_weightsOn p σ x).mp hx).2 i
        (by simpa only [T.mem_linkLabels] using hi)
      change ((_ * x.val i / total) • _) = _
      rw [hz, mul_zero, zero_div, zero_smul, zero_smul, smul_zero]
  have hnorm := congrArg NormedSpace.normalize hvec
  rw [he, NormedSpace.normalize_smul_of_pos (inv_pos.mpr ht),
    NormedSpace.normalize_smul_of_pos hc] at hnorm
  rw [frame, klein, NormedSpace.normalize_smul_of_pos
    (inv_pos.mpr (Hyperboloid.height_pos _))]
  change (T.hyperbolicAngularChart p σ x).val = NormedSpace.normalize (radialVector a z)
  rw [← hnorm]
  exact CrossPolytope.sphereNormalize_val (T.hyperbolicAngularChart_vector_ne_zero hσ hpσ hx)

theorem chart_hyperbolicBoundaryPoint_mem_visibleBoundary {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    frame (T.chart σ p) (T.chart σ (T.hyperbolicBoundaryPoint p x)) ∈
      visibleBoundary (frameVertices (T.chart σ p) (σ.image (T.chart σ))) 0 := by
  let y := T.hyperbolicLinkReweight p x
  let U := T.linkSourceVertices ((T.linkComplex p).support y)
  have hsub : U ⊆ σ := (T.hyperbolicLinkReweight_mem_region p σ x).mpr hx
  have hpU := (T.linkCoface_spec ((T.linkComplex p).support_mem y)).2.2.2
  have hface : T.chart σ '' T.cell U = hyperbolicCell (U.image (T.chart σ)) :=
    T.image_face σ hσ U hsub
  refine ⟨frameVertices (T.chart σ p) (U.image (T.chart σ)),
    Finset.image_subset_image (Finset.image_subset_image hsub), ?_, ?_⟩
  · intro h
    rw [← frame_self (T.chart σ p)] at h
    have hm := (mem_cell_iff_frame_mem_hull (T.chart σ p) (T.chart σ p) _).mpr h
    rw [← hface] at hm
    obtain ⟨z, hz, he⟩ := hm
    have hzp := T.chart_injectiveOn σ hσ (T.cell_mono hσ hsub hz) hpσ he
    exact hpU (Eq.mp (congrArg (fun q : P => q ∈ T.cell U) hzp) hz)
  · apply (mem_cell_iff_frame_mem_hull (T.chart σ p) _ _).mp
    rw [← hface]
    exact ⟨_, T.linkBoundaryInclusion_mem_support p y, rfl⟩

theorem hyperbolicAngularChart_injectiveOn {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    Set.InjOn (T.hyperbolicAngularChart p σ) (T.linkRegion p σ) := by
  intro x hx y hy he
  apply T.hyperbolicBoundaryPoint_injective p
  apply T.chart_injectiveOn σ hσ (T.hyperbolicBoundaryPoint_mem hσ hx)
    (T.hyperbolicBoundaryPoint_mem hσ hy)
  apply frame_injective (T.chart σ p)
  have hV := frameVertices_independent (T.chart σ p) (T.simplex σ hσ)
  have hpV : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈
      convexHull ℝ (frameVertices (T.chart σ p) (σ.image (T.chart σ)) : Set _) := by
    rw [← frame_self (T.chart σ p)]
    apply (mem_cell_iff_frame_mem_hull (T.chart σ p) _ _).mp
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  apply radialProjection_injectiveOn_visibleBoundary _ hV hpV
    (T.chart_hyperbolicBoundaryPoint_mem_visibleBoundary hσ hpσ x hx)
    (T.chart_hyperbolicBoundaryPoint_mem_visibleBoundary hσ hpσ y hy)
  change NormedSpace.normalize (_ - 0) = NormedSpace.normalize (_ - 0)
  simp only [sub_zero]
  rw [← T.hyperbolicAngularChart_eq_boundary_projection hσ hpσ x hx,
    ← T.hyperbolicAngularChart_eq_boundary_projection hσ hpσ y hy, he]

end ArchivePLGeometry.FiniteChartedComplex
