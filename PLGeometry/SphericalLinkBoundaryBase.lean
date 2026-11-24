module

public import PLGeometry.SphericalLinkAtlas
public import PLGeometry.LinkBoundaryInclusion
public import PLGeometry.ComplexReweighting

/-! # The source boundary point of a spherical angular coordinate -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.SphericalLink
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalLinkBoundaryBaseDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalLinkBoundaryBaseModelEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance sphericalLinkBoundaryBaseVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem spherical_link_radius_sin_pos (p : P) (v : T.LinkVertex p) :
    0 < Real.sin (T.radialDistance p v.val) := by
  let τ : Finset (T.LinkVertex p) := {v}
  have hτ : τ ∈ T.linkFaces p := (T.linkComplex p).singleton v
  have hv : v ∈ τ := Finset.mem_singleton_self v
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  rw [T.radialDistance_eq p hγ hpγ
    (T.vertices_mem _ hγ (hτγ (T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩)))]
  rw [← GeodesicSphere.norm_radialVector]
  exact norm_pos_iff.mpr (T.sphericalLinkTangent_ne_zero hτ hv)

theorem sphericalAngularVector_ne_zero {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) (v : T.LinkVertex p)
    (hvσ : v.val ∈ σ) : T.sphericalAngularVector p σ v ≠ 0 := by
  apply norm_pos_iff.mp
  change 0 < ‖GeodesicSphere.radialVector (T.chart σ p) (T.chart σ v.val)‖
  rw [GeodesicSphere.norm_radialVector,
    ← T.radialDistance_eq p hσ hpσ (T.vertices_mem σ hσ hvσ)]
  exact T.spherical_link_radius_sin_pos p v

def sphericalLinkReweight (p : P) : (T.linkComplex p).Space ≃ₜ (T.linkComplex p).Space :=
  (T.linkComplex p).reweightHomeomorph (fun v => (Real.sin (T.radialDistance p v.val))⁻¹)
    (fun v => inv_pos.mpr (T.spherical_link_radius_sin_pos p v))

theorem sphericalLinkReweight_mem_region (p : P) (σ : Finset P) (x : (T.linkComplex p).Space) :
    T.sphericalLinkReweight p x ∈ T.linkRegion p σ ↔ x ∈ T.linkRegion p σ := by
  rw [T.mem_linkRegion_iff_weightsOn, T.mem_linkRegion_iff_weightsOn]
  exact (T.linkComplex p).reweight_mem_weightsOn_iff _ _ _ _

def sphericalBoundaryPoint (p : P) (x : (T.linkComplex p).Space) : P :=
  T.linkBoundaryInclusion p (T.sphericalLinkReweight p x)

theorem sphericalBoundaryPoint_injective (p : P) : Function.Injective (T.sphericalBoundaryPoint p) :=
  (T.linkBoundaryInclusion_injective p).comp (T.sphericalLinkReweight p).injective

theorem sphericalBoundaryPoint_mem {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices)
    {x : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) :
    T.sphericalBoundaryPoint p x ∈ T.cell σ :=
  T.linkBoundaryInclusion_mem_of_region hσ ((T.sphericalLinkReweight_mem_region p σ x).mpr hx)

theorem sphericalAngularChart_eq_boundary_tangent {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    (T.sphericalAngularChart p σ x).val =
      NormedSpace.normalize (tangentLinear (T.chart σ p) (T.chart σ (T.sphericalBoundaryPoint p x)).val) := by
  let y := T.sphericalLinkReweight p x
  let a := T.chart σ p
  let z := T.chart σ (T.sphericalBoundaryPoint p x)
  have hy : y ∈ T.linkRegion p σ := (T.sphericalLinkReweight_mem_region p σ x).mpr hx
  obtain ⟨c, hc, hr⟩ := T.cellWeights_represents σ hσ
    ⟨T.linkBoundaryInclusion p y, T.linkBoundaryInclusion_mem_of_region hσ hy⟩
  change (∑ v : σ, (T.cellWeights σ hσ
    ⟨T.linkBoundaryInclusion p y, T.linkBoundaryInclusion_mem_of_region hσ hy⟩).val v •
    (T.chart σ v.val).val) = c • z.val at hr
  rw [T.sum_cellWeights_linkBoundaryInclusion hσ y hy (fun v => (T.chart σ v).val)] at hr
  have hvec := congrArg (tangentLinear a) hr
  simp only [map_sum, map_smul] at hvec
  let total := BarycentricReweighting.total
    (fun v : T.LinkVertex p => (Real.sin (T.radialDistance p v.val))⁻¹) x.val
  have ht : 0 < total := BarycentricReweighting.total_pos _
    (fun v => inv_pos.mpr (T.spherical_link_radius_sin_pos p v))
    ⟨x.val, (T.linkComplex p).weight_nonneg x, (T.linkComplex p).weight_sum x⟩
  have he : (∑ i, y.val i • tangentLinear a (T.chart σ i.val).val) =
      total⁻¹ • SphericalBarycentric.vector (T.sphericalAngularVertex p σ) x.val := by
    unfold SphericalBarycentric.vector
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val ∈ σ
    · have hn := T.sphericalAngularVector_ne_zero hσ hpσ i hi
      have hd : T.radialDistance p i.val = dist a (T.chart σ i.val) :=
        T.radialDistance_eq p hσ hpσ (T.vertices_mem σ hσ hi)
      change ((Real.sin (T.radialDistance p i.val))⁻¹ * x.val i / total) •
        tangentLinear a (T.chart σ i.val).val = _
      rw [sphericalAngularVertex, CrossPolytope.sphereNormalize_val hn]
      change (_ • GeodesicSphere.radialVector a (T.chart σ i.val)) =
        total⁻¹ • (x.val i • NormedSpace.normalize (GeodesicSphere.radialVector a (T.chart σ i.val)))
      simp only [NormedSpace.normalize, GeodesicSphere.norm_radialVector, smul_smul, hd, div_eq_mul_inv]
      congr 1
      ring
    · have hz : x.val i = 0 := ((T.mem_linkRegion_iff_weightsOn p σ x).mp hx).2 i
        (by simpa only [T.mem_linkLabels] using hi)
      change ((_ * x.val i / total) • _) = _
      rw [hz, mul_zero, zero_div, zero_smul, zero_smul, smul_zero]
  have hnorm := congrArg NormedSpace.normalize hvec
  rw [he, NormedSpace.normalize_smul_of_pos (inv_pos.mpr ht),
    NormedSpace.normalize_smul_of_pos hc] at hnorm
  change (T.sphericalAngularChart p σ x).val = NormedSpace.normalize (tangentLinear a z.val)
  rw [← hnorm]
  exact CrossPolytope.sphereNormalize_val (T.sphericalAngularChart_vector_ne_zero hσ hpσ hx)

end ArchivePLGeometry.FiniteChartedComplex
