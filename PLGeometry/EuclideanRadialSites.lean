module

public import PLGeometry.EuclideanLinkComplex
public import PLGeometry.EuclideanChartTransitions
public import PLGeometry.BarycentricSupport
public import PLGeometry.ChartedStars

/-!
# Actual radial sites in a Euclidean charted complex

A link point has a canonical positive barycentric support. A sufficiently
small radial point in its selected coface is pulled back through the actual
cell homeomorphism. The resulting source point belongs to every old cell
containing the center and that support.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean (n + 1) P)

local instance euclideanRadialSitesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance euclideanRadialSitesModelDecidableEq :
    DecidableEq (Model .euclidean (n + 1)) := Classical.decEq _
local instance euclideanRadialSitesLabelDecidableEq (p : P) :
    DecidableEq (T.LinkVertex p) := Classical.decEq _
local instance euclideanRadialSitesSphereDecidableEq :
    DecidableEq (GeodesicSphere n) := Classical.decEq _

def EuclideanRadialAdmissible (p : P) (r : ℝ) : Prop :=
  ∀ τ ∈ T.linkFaces p, ∀ u ∈ sphericalCell (τ.image (T.euclideanLinkPoint p τ)),
    T.chart (T.linkCoface p τ) p + r • u.val ∈
      convexHull ℝ (T.euclideanLinkCone p τ : Set _)

theorem exists_uniform_euclidean_link_radius (p : P) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r ≤ ρ → T.EuclideanRadialAdmissible p r := by
  classical
  let J := {τ : Finset (T.LinkVertex p) // τ ∈ T.linkFaces p}
  let : Fintype J := Fintype.ofFinite J
  choose radius hpos hmem using
    (fun τ : J => T.exists_euclidean_link_face_radius τ.property)
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

def euclideanLinkAngularPoint (p : P) (x : (T.linkComplex p).Space) : GeodesicSphere n :=
  Barycentric.chartPoint (T.euclideanLinkPoint p ((T.linkComplex p).support x)) x.val

theorem euclideanLinkAngularPoint_mem (p : P) (x : (T.linkComplex p).Space) :
    T.euclideanLinkAngularPoint p x ∈ sphericalCell
      (((T.linkComplex p).support x).image
        (T.euclideanLinkPoint p ((T.linkComplex p).support x))) := by
  have hτ := (T.linkComplex p).support_mem x
  have hweights := (T.linkComplex p).weightsOn_support x
  rw [← Barycentric.chartPoint_image _ _ (T.euclideanLinkPoint_independent hτ)]
  exact ⟨x.val, hweights, rfl⟩

/-- The actual source point at radius `r` in the direction of a link point. -/
def euclideanRadialSite (p : P) {r : ℝ} (hr : T.EuclideanRadialAdmissible p r)
    (x : (T.linkComplex p).Space) : P := by
  let τ := (T.linkComplex p).support x
  have hτ : τ ∈ T.linkFaces p := (T.linkComplex p).support_mem x
  let σ := T.linkCoface p τ
  have hσ := (T.linkCoface_spec hτ).1
  let y := T.chart σ p + r • (T.euclideanLinkAngularPoint p x).val
  have hy : y ∈ hull .euclidean (n + 1) (σ.image (T.chart σ)) :=
    T.euclideanLinkCone_subset_hull hτ (hr τ hτ _ (T.euclideanLinkAngularPoint_mem p x))
  exact ((T.cellHomeomorph σ hσ).symm ⟨y, hy⟩).val

theorem euclideanRadialSite_mem (p : P) {r : ℝ} (hr : T.EuclideanRadialAdmissible p r)
    (x : (T.linkComplex p).Space) :
    T.euclideanRadialSite p hr x ∈
      T.cell (T.linkCoface p ((T.linkComplex p).support x)) := by
  unfold euclideanRadialSite
  exact Subtype.property _

theorem chart_euclideanRadialSite (p : P) {r : ℝ} (hr : T.EuclideanRadialAdmissible p r)
    (x : (T.linkComplex p).Space) :
    T.chart (T.linkCoface p ((T.linkComplex p).support x)) (T.euclideanRadialSite p hr x) =
      T.chart (T.linkCoface p ((T.linkComplex p).support x)) p +
        r • (T.euclideanLinkAngularPoint p x).val := by
  unfold euclideanRadialSite
  rw [← T.cellHomeomorph_apply _ (T.linkCoface_spec ((T.linkComplex p).support_mem x)).1]
  simp only [Homeomorph.apply_symm_apply]

theorem radialDistance_euclideanRadialSite (p : P) {r : ℝ}
    (hr : T.EuclideanRadialAdmissible p r) (hr0 : 0 ≤ r) (x : (T.linkComplex p).Space) :
    T.radialDistance p (T.euclideanRadialSite p hr x) = r := by
  have hs := T.linkCoface_spec ((T.linkComplex p).support_mem x)
  rw [T.radialDistance_eq p hs.1 hs.2.1 (T.euclideanRadialSite_mem p hr x),
    T.chart_euclideanRadialSite p hr x, dist_comm, dist_eq_norm,
    add_sub_cancel_left, norm_smul, (T.euclideanLinkAngularPoint p x).norm_val,
    Real.norm_eq_abs, abs_of_nonneg hr0, mul_one]

theorem euclideanRadialSite_mem_of_support
    (p : P) {r : ℝ} (hr : T.EuclideanRadialAdmissible p r)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ)
    (hsub : T.linkSourceVertices ((T.linkComplex p).support x) ⊆ σ) :
    T.euclideanRadialSite p hr x ∈ T.cell σ := by
  let τ := (T.linkComplex p).support x
  have hτ : τ ∈ T.linkFaces p := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  refine T.mem_common_cell_of_convexHull_chart hγ hσ
    (insert p (T.linkSourceVertices τ)) ?_ (T.euclideanRadialSite_mem p hr x) ?_
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨hpγ, hpσ⟩
    · exact ⟨T.vertices_mem _ hγ (hτγ hv), T.vertices_mem _ hσ (hsub hv)⟩
  · rw [T.chart_euclideanRadialSite p hr x]
    have hm := hr τ hτ _ (T.euclideanLinkAngularPoint_mem p x)
    simpa only [Finset.image_insert, euclideanLinkCone] using hm

end ArchivePLGeometry.FiniteChartedComplex
