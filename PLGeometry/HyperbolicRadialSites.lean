module

public import PLGeometry.HyperbolicLinkCones
public import PLGeometry.BarycentricSupport
public import PLGeometry.ChartedStars

/-! # Actual uniformly small radial sites in hyperbolic charted complexes -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.HyperbolicSpace BrehmApprox.HyperbolicLink

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

local instance hyperbolicRadialSitesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance hyperbolicRadialSitesModelEq : DecidableEq (Model .hyperbolic (n + 1)) := Classical.decEq _
local instance hyperbolicRadialSitesLabelEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _
local instance hyperbolicRadialSitesSphereEq : DecidableEq (GeodesicSphere n) := Classical.decEq _

def HyperbolicRadialAdmissible (p : P) (r : ℝ) : Prop :=
  ∀ τ ∈ T.linkFaces p, ∀ u ∈ sphericalCell (τ.image (T.hyperbolicLinkPoint p τ)),
    radialPoint (T.chart (T.linkCoface p τ) p) u r ∈ hyperbolicCell (T.hyperbolicLinkCone p τ)

theorem exists_uniform_hyperbolic_link_radius (p : P) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r ≤ ρ → T.HyperbolicRadialAdmissible p r := by
  classical
  let J := {τ : Finset (T.LinkVertex p) // τ ∈ T.linkFaces p}
  let : Fintype J := Fintype.ofFinite J
  choose radius hpos hmem using (fun τ : J => T.exists_hyperbolic_link_face_radius τ.property)
  by_cases hJ : Nonempty J
  · let : Nonempty J := hJ
    let ρ : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
    refine ⟨ρ, ?_, ?_⟩
    · dsimp only [ρ]
      rw [Finset.lt_inf'_iff]
      exact fun τ _ => hpos τ
    · intro r hr hrρ τ hτ u hu
      exact hmem ⟨τ, hτ⟩ r hr
        (hrρ.trans (Finset.inf'_le radius (Finset.mem_univ (⟨τ, hτ⟩ : J)))) u hu
  · refine ⟨1, zero_lt_one, ?_⟩
    intro r hr hr1 τ hτ u hu
    exact (hJ ⟨⟨τ, hτ⟩⟩).elim

def hyperbolicLinkAngularPoint (p : P) (x : (T.linkComplex p).Space) : GeodesicSphere n :=
  Barycentric.chartPoint (T.hyperbolicLinkPoint p ((T.linkComplex p).support x)) x.val

theorem hyperbolicLinkAngularPoint_mem (p : P) (x : (T.linkComplex p).Space) :
    T.hyperbolicLinkAngularPoint p x ∈ sphericalCell
      (((T.linkComplex p).support x).image
        (T.hyperbolicLinkPoint p ((T.linkComplex p).support x))) := by
  have hτ := (T.linkComplex p).support_mem x
  have hweights := (T.linkComplex p).weightsOn_support x
  rw [← Barycentric.chartPoint_image _ _ (T.hyperbolicLinkPoint_independent hτ)]
  exact ⟨x.val, hweights, rfl⟩

def hyperbolicRadialSite (p : P) {r : ℝ} (hr : T.HyperbolicRadialAdmissible p r)
    (x : (T.linkComplex p).Space) : P := by
  let τ := (T.linkComplex p).support x
  have hτ : τ ∈ T.linkFaces p := (T.linkComplex p).support_mem x
  let σ := T.linkCoface p τ
  have hσ := (T.linkCoface_spec hτ).1
  let y := radialPoint (T.chart σ p) (T.hyperbolicLinkAngularPoint p x) r
  have hy : y ∈ hull .hyperbolic (n + 1) (σ.image (T.chart σ)) :=
    T.hyperbolicLinkCone_subset_hull hτ (hr τ hτ _ (T.hyperbolicLinkAngularPoint_mem p x))
  exact ((T.cellHomeomorph σ hσ).symm ⟨y, hy⟩).val

theorem hyperbolicRadialSite_mem (p : P) {r : ℝ} (hr : T.HyperbolicRadialAdmissible p r)
    (x : (T.linkComplex p).Space) :
    T.hyperbolicRadialSite p hr x ∈ T.cell (T.linkCoface p ((T.linkComplex p).support x)) := by
  unfold hyperbolicRadialSite
  exact Subtype.property _

theorem chart_hyperbolicRadialSite (p : P) {r : ℝ} (hr : T.HyperbolicRadialAdmissible p r)
    (x : (T.linkComplex p).Space) :
    T.chart (T.linkCoface p ((T.linkComplex p).support x)) (T.hyperbolicRadialSite p hr x) =
      radialPoint (T.chart (T.linkCoface p ((T.linkComplex p).support x)) p)
        (T.hyperbolicLinkAngularPoint p x) r := by
  unfold hyperbolicRadialSite
  rw [← T.cellHomeomorph_apply _ (T.linkCoface_spec ((T.linkComplex p).support_mem x)).1]
  simp only [Homeomorph.apply_symm_apply]

theorem radialDistance_hyperbolicRadialSite (p : P) {r : ℝ}
    (hr : T.HyperbolicRadialAdmissible p r) (hr0 : 0 ≤ r) (x : (T.linkComplex p).Space) :
    T.radialDistance p (T.hyperbolicRadialSite p hr x) = r := by
  have hs := T.linkCoface_spec ((T.linkComplex p).support_mem x)
  rw [T.radialDistance_eq p hs.1 hs.2.1 (T.hyperbolicRadialSite_mem p hr x),
    T.chart_hyperbolicRadialSite p hr x, dist_comm, radialPoint_dist _ _ hr0]

theorem hyperbolicRadialSite_mem_of_support
    (p : P) {r : ℝ} (hr : T.HyperbolicRadialAdmissible p r)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ)
    (hsub : T.linkSourceVertices ((T.linkComplex p).support x) ⊆ σ) :
    T.hyperbolicRadialSite p hr x ∈ T.cell σ := by
  let τ := (T.linkComplex p).support x
  have hτ : τ ∈ T.linkFaces p := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  refine T.mem_common_cell_of_hull_chart hγ hσ
    (insert p (T.linkSourceVertices τ)) ?_ (T.hyperbolicRadialSite_mem p hr x) ?_
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨hpγ, hpσ⟩
    · exact ⟨T.vertices_mem _ hγ (hτγ hv), T.vertices_mem _ hσ (hsub hv)⟩
  · rw [T.chart_hyperbolicRadialSite p hr x]
    have hm := hr τ hτ _ (T.hyperbolicLinkAngularPoint_mem p x)
    simpa only [Finset.image_insert, hyperbolicLinkCone, hull, τ] using hm

end ArchivePLGeometry.FiniteChartedComplex
