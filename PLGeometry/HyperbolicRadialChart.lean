module

public import PLGeometry.HyperbolicRadialIncidence
public import PLGeometry.HyperbolicLinkAtlas
public import BrehmApprox.ModelPointRigidity

/-! # The radial site formula in every incident hyperbolic chart -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.HyperbolicSpace BrehmApprox.HyperbolicLink

namespace BrehmApprox.HyperbolicLink

theorem radialVector_radialPoint {n : ℕ} (p : HyperbolicSpace (n + 1))
    (u : GeodesicSphere n) (r : ℝ) : radialVector p (radialPoint p u r) = Real.sinh r • u.val := by
  rw [radialVector, boost_radialPoint]
  rfl

end BrehmApprox.HyperbolicLink

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

local instance hyperbolicRadialChartDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance hyperbolicRadialChartModelEq : DecidableEq (Model .hyperbolic (n + 1)) := Classical.decEq _
local instance hyperbolicRadialChartLabelEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem chart_hyperbolicRadialSite_in_coface
    (p : P) {r : ℝ} (hr : T.HyperbolicRadialAdmissible p r)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hx : x ∈ T.linkRegion p σ) :
    T.chart σ (T.hyperbolicRadialSite p hr x) =
      radialPoint (T.chart σ p) (T.hyperbolicAngularChart p σ x) r := by
  let τ := (T.linkComplex p).support x
  let γ := T.linkCoface p τ
  have hτ := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  obtain ⟨U, hU⟩ := T.exists_hyperbolic_coface_linear_congruence hτ hσ hpσ hx
  let R := radialMotion (T.chart γ p) (T.chart σ p) U
  have hRp : R (T.chart γ p) = T.chart σ p := radialMotion_center _ _ U
  have hRv (v : T.LinkVertex p) (hv : v ∈ τ) : R (T.chart γ v.val) = T.chart σ v.val :=
    radialMotion_apply_of_vector _ _ _ _ U (hU v hv)
  have hqγ := T.hyperbolicRadialSite_mem p hr x
  have hqσ := T.hyperbolicRadialSite_mem_of_support p hr x hσ hpσ hx
  have hqcone : T.chart γ (T.hyperbolicRadialSite p hr x) ∈ hyperbolicCell (T.hyperbolicLinkCone p τ) := by
    rw [T.chart_hyperbolicRadialSite p hr x]
    exact hr τ hτ _ (T.hyperbolicLinkAngularPoint_mem p x)
  have hRq : R (T.chart γ (T.hyperbolicRadialSite p hr x)) =
      T.chart σ (T.hyperbolicRadialSite p hr x) := by
    apply hyperbolicMotion_eq_of_vertex_distances R hqcone
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [hRp]
      exact (T.metric_coherence γ hγ σ hσ _ ⟨hqγ, hqσ⟩ p ⟨hpγ, hpσ⟩).symm
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨w, hw, rfl⟩ := T.mem_linkSourceVertices.mp hz
      rw [hRv w hw]
      exact (T.metric_coherence γ hγ σ hσ _ ⟨hqγ, hqσ⟩ w.val
        ⟨T.vertices_mem γ hγ (hτγ (T.mem_linkSourceVertices.mpr ⟨w, hw, rfl⟩)),
          T.vertices_mem σ hσ (hx (T.mem_linkSourceVertices.mpr ⟨w, hw, rfl⟩))⟩).symm
  have hu : U (T.hyperbolicLinkAngularPoint p x).val = (T.hyperbolicAngularChart p σ x).val :=
    (T.hyperbolicAngularChart_transition hτ hσ hpσ hx U hU x
      ((T.linkComplex p).weightsOn_support x)).symm
  have hpolar : R (radialPoint (T.chart γ p) (T.hyperbolicLinkAngularPoint p x) r) =
      radialPoint (T.chart σ p) (T.hyperbolicAngularChart p σ x) r := by
    apply radialMotion_apply_of_vector _ _ _ _ U
    rw [radialVector_radialPoint, radialVector_radialPoint, map_smul, hu]
  rw [← hRq, T.chart_hyperbolicRadialSite p hr x]
  exact hpolar

end ArchivePLGeometry.FiniteChartedComplex
