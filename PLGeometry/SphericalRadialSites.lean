module

public import PLGeometry.SphericalLinkCones
public import PLGeometry.SphericalChartTransitions
public import PLGeometry.BarycentricSupport
public import PLGeometry.ChartedStars

/-! # Actual small radial sites in a spherical charted complex -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped InnerProductSpace

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalRadialSitesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalRadialSitesModelEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance sphericalRadialSitesLabelEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def SphericalRadialAdmissible (p : P) (r : ℝ) : Prop :=
  ∀ τ ∈ T.linkFaces p, ∀ u ∈ sphericalCell (τ.image (T.sphericalLinkVertex p τ)),
    ∀ hu : inner ℝ (T.chart (T.linkCoface p τ) p).val u.val = 0,
      SphericalLink.radialPoint (T.chart (T.linkCoface p τ) p) u hu r ∈
        sphericalCell (T.sphericalLinkCone p τ)

theorem exists_uniform_spherical_link_radius (p : P) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < Real.pi / 2 ∧
      ∀ r : ℝ, 0 < r → r ≤ ρ → T.SphericalRadialAdmissible p r := by
  let J := {τ : Finset (T.LinkVertex p) // τ ∈ T.linkFaces p}
  let : Fintype J := Fintype.ofFinite J
  choose radius hpos hπ hmem using (fun τ : J => T.exists_spherical_link_face_radius τ.property)
  by_cases hJ : Nonempty J
  · let : Nonempty J := hJ
    let ρ : ℝ := min (Real.pi / 4) (Finset.univ.inf' Finset.univ_nonempty radius)
    have hρ : 0 < ρ := by
      apply lt_min (by positivity)
      rw [Finset.lt_inf'_iff]
      exact fun τ _ => hpos τ
    refine ⟨ρ, hρ, (min_le_left _ _).trans_lt (by linarith [Real.pi_pos]), ?_⟩
    intro r hr hrρ τ hτ u hu huorth
    exact hmem ⟨τ, hτ⟩ r hr
      (hrρ.trans ((min_le_right _ _).trans (Finset.inf'_le radius (Finset.mem_univ (⟨τ, hτ⟩ : J)))))
      u hu huorth
  · refine ⟨Real.pi / 4, by positivity, by linarith [Real.pi_pos], ?_⟩
    intro r hr hrρ τ hτ u hu huorth
    exact (hJ ⟨⟨τ, hτ⟩⟩).elim

def sphericalLinkAngularPoint (p : P) (x : (T.linkComplex p).Space) : GeodesicSphere n :=
  Barycentric.chartPoint (T.sphericalLinkVertex p ((T.linkComplex p).support x)) x.val

theorem sphericalLinkAngularPoint_mem (p : P) (x : (T.linkComplex p).Space) :
    T.sphericalLinkAngularPoint p x ∈ sphericalCell
      (((T.linkComplex p).support x).image
        (T.sphericalLinkVertex p ((T.linkComplex p).support x))) := by
  have hτ := (T.linkComplex p).support_mem x
  have hw := (T.linkComplex p).weightsOn_support x
  rw [← Barycentric.chartPoint_image _ _ (T.sphericalLinkVertex_independent hτ)]
  exact ⟨x.val, hw, rfl⟩

theorem sphericalLinkAngularPoint_tangent (p : P) (x : (T.linkComplex p).Space) :
    inner ℝ (T.chart (T.linkCoface p ((T.linkComplex p).support x)) p).val
      (T.sphericalLinkAngularPoint p x).val = 0 :=
  T.sphericalLinkCell_tangent ((T.linkComplex p).support_mem x) (T.sphericalLinkAngularPoint_mem p x)

def sphericalRadialSite (p : P) {r : ℝ} (hr : T.SphericalRadialAdmissible p r)
    (x : (T.linkComplex p).Space) : P := by
  let τ := (T.linkComplex p).support x
  have hτ := (T.linkComplex p).support_mem x
  let σ := T.linkCoface p τ
  have hσ := (T.linkCoface_spec hτ).1
  let y := SphericalLink.radialPoint (T.chart σ p) (T.sphericalLinkAngularPoint p x)
    (T.sphericalLinkAngularPoint_tangent p x) r
  have hy : y ∈ hull .spherical n (σ.image (T.chart σ)) :=
    T.sphericalLinkCone_subset_hull hτ (hr τ hτ _ (T.sphericalLinkAngularPoint_mem p x) _)
  exact ((T.cellHomeomorph σ hσ).symm ⟨y, hy⟩).val

theorem sphericalRadialSite_mem (p : P) {r : ℝ} (hr : T.SphericalRadialAdmissible p r)
    (x : (T.linkComplex p).Space) :
    T.sphericalRadialSite p hr x ∈ T.cell (T.linkCoface p ((T.linkComplex p).support x)) := by
  unfold sphericalRadialSite
  exact Subtype.property _

theorem chart_sphericalRadialSite (p : P) {r : ℝ} (hr : T.SphericalRadialAdmissible p r)
    (x : (T.linkComplex p).Space) :
    T.chart (T.linkCoface p ((T.linkComplex p).support x)) (T.sphericalRadialSite p hr x) =
      SphericalLink.radialPoint
        (T.chart (T.linkCoface p ((T.linkComplex p).support x)) p)
        (T.sphericalLinkAngularPoint p x) (T.sphericalLinkAngularPoint_tangent p x) r := by
  unfold sphericalRadialSite
  rw [← T.cellHomeomorph_apply _ (T.linkCoface_spec ((T.linkComplex p).support_mem x)).1]
  simp only [Homeomorph.apply_symm_apply]

theorem radialDistance_sphericalRadialSite (p : P) {r : ℝ}
    (hr : T.SphericalRadialAdmissible p r) (hr0 : 0 ≤ r) (hrπ : r ≤ Real.pi)
    (x : (T.linkComplex p).Space) : T.radialDistance p (T.sphericalRadialSite p hr x) = r := by
  have hs := T.linkCoface_spec ((T.linkComplex p).support_mem x)
  rw [T.radialDistance_eq p hs.1 hs.2.1 (T.sphericalRadialSite_mem p hr x),
    T.chart_sphericalRadialSite p hr x, dist_comm]
  exact SphericalLink.radialPoint_dist_p _ _ _ hr0 hrπ

theorem sphericalRadialSite_mem_of_support
    (p : P) {r : ℝ} (hr : T.SphericalRadialAdmissible p r)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ)
    (hsub : T.linkSourceVertices ((T.linkComplex p).support x) ⊆ σ) :
    T.sphericalRadialSite p hr x ∈ T.cell σ := by
  let τ := (T.linkComplex p).support x
  have hτ := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  refine T.mem_common_cell_of_sphericalCell_chart hγ hσ
    (insert p (T.linkSourceVertices τ)) ?_ (T.sphericalRadialSite_mem p hr x) ?_
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨hpγ, hpσ⟩
    · exact ⟨T.vertices_mem _ hγ (hτγ hv), T.vertices_mem _ hσ (hsub hv)⟩
  · rw [T.chart_sphericalRadialSite p hr x]
    simpa only [Finset.image_insert, sphericalLinkCone] using
      hr τ hτ _ (T.sphericalLinkAngularPoint_mem p x) (T.sphericalLinkAngularPoint_tangent p x)

end ArchivePLGeometry.FiniteChartedComplex
