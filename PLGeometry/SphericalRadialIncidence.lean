module

public import PLGeometry.SphericalRadialSites
public import BrehmApprox.SphericalRadialSupport

/-! # Exact old-cell incidence of positive spherical radial sites -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalRadialIncidenceDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalRadialIncidenceModelEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance sphericalRadialIncidenceLabelEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem sphericalLinkAngularPoint_positive_combination
    (p : P) (x : (T.linkComplex p).Space) :
    ∃ w : ((T.linkComplex p).support x) → ℝ, (∀ i, 0 < w i) ∧
      ∃ c : ℝ, 0 < c ∧ (T.sphericalLinkAngularPoint p x).val =
        c • (∑ i, w i • T.sphericalLinkTangent p ((T.linkComplex p).support x) i.val) := by
  let τ := (T.linkComplex p).support x
  have hτ := (T.linkComplex p).support_mem x
  let a : Barycentric.weightsOn τ := ⟨x.val, (T.linkComplex p).weightsOn_support x⟩
  let v : τ → GeodesicSphere n := fun i => T.sphericalLinkVertex p τ i.val
  let z := SphericalBarycentric.vector v (Barycentric.restrict τ a).val
  have hz : z ≠ 0 := SphericalBarycentric.vector_ne_zero v
    (T.sphericalLinkVertex_independent hτ) (Barycentric.restrict τ a)
  let w : τ → ℝ := fun i => x.val i.val * ‖T.sphericalLinkTangent p τ i.val‖⁻¹
  have hw (i : τ) : 0 < w i :=
    mul_pos ((T.linkComplex p).mem_support_iff x i.val |>.mp i.property)
      (inv_pos.mpr (norm_pos_iff.mpr (T.sphericalLinkTangent_ne_zero hτ i.property)))
  have he : z = ∑ i : τ, w i • T.sphericalLinkTangent p τ i.val := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [v, SphericalBarycentric.vector, Barycentric.restrict]
    rw [sphericalLinkVertex, CrossPolytope.sphereNormalize_val
      (T.sphericalLinkTangent_ne_zero hτ i.property)]
    simp only [NormedSpace.normalize, smul_smul, w]
    rfl
  refine ⟨w, hw, ‖z‖⁻¹, inv_pos.mpr (norm_pos_iff.mpr hz), ?_⟩
  change (Barycentric.chartPoint (T.sphericalLinkVertex p τ) x.val).val = _
  rw [Barycentric.chartPoint_restrict τ _ (T.sphericalLinkVertex_independent hτ) a]
  change NormedSpace.normalize z = _
  rw [NormedSpace.normalize, he]


theorem support_subset_of_sphericalRadialSite_mem
    (p : P) {r : ℝ} (hr : T.SphericalRadialAdmissible p r)
    (hr0 : 0 < r) (hrπ : r < Real.pi)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hqσ : T.sphericalRadialSite p hr x ∈ T.cell σ) :
    T.linkSourceVertices ((T.linkComplex p).support x) ⊆ σ := by
  let τ := (T.linkComplex p).support x
  let γ := T.linkCoface p τ
  have hτ := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, hsub, _⟩ := T.linkCoface_spec hτ
  let V := γ.image (T.chart γ)
  let U := (γ ∩ σ).image (T.chart γ)
  have hV : LinearIndependent ℝ (fun v : V => v.val.val) := by
    simpa only [Finset.coe_sort_coe] using (T.simplex γ hγ).2
  have hface : T.chart γ '' T.cell (γ ∩ σ) = sphericalCell U :=
    T.image_face γ hγ (γ ∩ σ) Finset.inter_subset_left
  have hpD : T.chart γ p ∈ sphericalCell U := by
    rw [← hface, ← T.intersection γ hγ σ hσ]
    exact ⟨p, ⟨hpγ, hpσ⟩, rfl⟩
  have hqD : T.chart γ (T.sphericalRadialSite p hr x) ∈ sphericalCell U := by
    rw [← hface, ← T.intersection γ hγ σ hσ]
    exact ⟨_, ⟨T.sphericalRadialSite_mem p hr x, hqσ⟩, rfl⟩
  obtain ⟨w, hw, c, hc, he⟩ := T.sphericalLinkAngularPoint_positive_combination p x
  have hrep : (T.chart γ (T.sphericalRadialSite p hr x)).val =
      Real.cos r • (T.chart γ p).val + (Real.sin r * c) •
        ∑ i : τ, w i • SphericalLink.tangentLinear (T.chart γ p) (T.chart γ i.val.val).val := by
    rw [T.chart_sphericalRadialSite p hr x, SphericalLink.radialPoint_val, he, smul_smul]
    rfl
  have hinc := SphericalLink.mem_face_of_positive_tangent_combination V U hV
    (Finset.image_subset_image Finset.inter_subset_left)
    (T.chart γ p) (T.chart γ (T.sphericalRadialSite p hr x)) hpD hqD
    (fun i : τ => T.chart γ i.val.val)
    (fun i => Finset.mem_image.mpr ⟨i.val.val,
      hsub (T.mem_linkSourceVertices.mpr ⟨i.val, i.property, rfl⟩), rfl⟩)
    w hw (Real.cos r) (Real.sin r * c) (mul_pos (Real.sin_pos_of_pos_of_lt_pi hr0 hrπ) hc) hrep
  intro a ha
  obtain ⟨i, hi, rfl⟩ := T.mem_linkSourceVertices.mp ha
  obtain ⟨b, hb, hbi⟩ := Finset.mem_image.mp (hinc ⟨i, hi⟩)
  have hbi' : b = i.val := T.chart_injectiveOn γ hγ
    (T.vertices_mem γ hγ (Finset.mem_inter.mp hb).1)
    (T.vertices_mem γ hγ (hsub (T.mem_linkSourceVertices.mpr ⟨i, hi, rfl⟩))) hbi
  exact hbi' ▸ (Finset.mem_inter.mp hb).2

end ArchivePLGeometry.FiniteChartedComplex
