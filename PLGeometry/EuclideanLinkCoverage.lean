module

public import PLGeometry.EuclideanLinkBoundary
public import PLGeometry.LinkBoundarySurjectivity
public import BrehmApprox.RadialDomains

/-! # Coverage and short-arc convexity of a coarse Euclidean angular region -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean (n + 1) P)

local instance euclideanLinkCoverageDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance euclideanLinkCoverageModelEq : DecidableEq (Model .euclidean (n + 1)) := Classical.decEq _
local instance euclideanLinkCoverageVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem exists_euclidean_boundary_source_same_direction
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {z : Model .euclidean (n + 1)}
    (hz : z ∈ hull .euclidean (n + 1) (σ.image (T.chart σ)))
    (hzp : z ≠ T.chart σ p) :
    ∃ U : Finset P, U ⊆ σ ∧ p ∉ T.cell U ∧ ∃ y ∈ T.cell U,
      NormedSpace.normalize (T.chart σ y - T.chart σ p) =
        NormedSpace.normalize (z - T.chart σ p) := by
  have hV : AffineIndependent ℝ ((↑) : σ.image (T.chart σ) → Model .euclidean (n + 1)) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using T.simplex σ hσ
  have hpV : T.chart σ p ∈ convexHull ℝ (σ.image (T.chart σ) : Set _) := by
    have h := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at h
    exact h
  obtain ⟨y, ⟨W, hWV, hpW, hyW⟩, he⟩ :=
    exists_visibleBoundary_same_direction _ hV hpV hz hzp
  let U := σ.filter fun v => T.chart σ v ∈ W
  have hUσ : U ⊆ σ := Finset.filter_subset _ _
  have hUimage : U.image (T.chart σ) = W := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2
    · intro hw
      obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp (hWV hw)
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hve ▸ hw⟩, hve⟩
  have hface : T.chart σ '' T.cell U = convexHull ℝ (W : Set _) := by
    have h := T.image_face σ hσ U hUσ
    rw [hUimage] at h
    exact h
  have hpU : p ∉ T.cell U := by
    intro hp
    apply hpW
    rw [← hface]
    exact ⟨p, hp, rfl⟩
  rw [← hface] at hyW
  obtain ⟨q, hq, hqy⟩ := hyW
  exact ⟨U, hUσ, hpU, q, hq, hqy ▸ he⟩

theorem exists_euclideanAngularChart_direction
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {z : Model .euclidean (n + 1)}
    (hz : z ∈ hull .euclidean (n + 1) (σ.image (T.chart σ)))
    (hzp : z ≠ T.chart σ p) :
    ∃ x ∈ T.linkRegion p σ, (T.euclideanAngularChart p σ x).val =
      NormedSpace.normalize (z - T.chart σ p) := by
  obtain ⟨U, hUσ, hpU, y, hy, he⟩ :=
    T.exists_euclidean_boundary_source_same_direction hσ hpσ hz hzp
  obtain ⟨a, ha, hya⟩ := T.exists_linkBoundaryInclusion_of_face hσ hpσ hUσ hpU hy
  let x := (T.euclideanLinkReweight p).symm a
  have haσ : a ∈ T.linkRegion p σ := ha.trans hUσ
  have hx : x ∈ T.linkRegion p σ :=
    (T.euclideanLinkReweight_mem_region p σ x).mp (by
      simpa only [x, Homeomorph.apply_symm_apply] using haσ)
  refine ⟨x, hx, ?_⟩
  rw [T.euclideanAngularChart_eq_boundary_projection hσ hpσ x hx]
  have hb : T.euclideanBoundaryPoint p x = y := by
    simpa only [euclideanBoundaryPoint, x, Homeomorph.apply_symm_apply] using hya
  rw [hb]
  exact he

theorem image_euclideanAngularChart
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    T.euclideanAngularChart p σ '' T.linkRegion p σ =
      radialDirections (hull .euclidean (n + 1) (σ.image (T.chart σ))) (T.chart σ p) := by
  apply Set.Subset.antisymm
  · rintro u ⟨x, hx, rfl⟩
    obtain ⟨ρ, hρ, hrad⟩ := T.exists_uniform_euclidean_link_radius p
    let hr := hrad ρ hρ le_rfl
    refine ⟨ρ, hρ, ?_⟩
    rw [← T.chart_euclideanRadialSite_in_coface p hr x hσ hpσ hx]
    have hm := Set.mem_image_of_mem (T.chart σ)
      (T.euclideanRadialSite_mem_of_support p hr x hσ hpσ hx)
    rw [T.image_cell σ hσ] at hm
    exact hm
  · rintro u ⟨r, hr, hu⟩
    have hne : T.chart σ p + r • u.val ≠ T.chart σ p := by
      intro he
      have hz : r • u.val = 0 := add_left_cancel (he.trans (add_zero _).symm)
      exact smul_ne_zero hr.ne' u.val_ne_zero hz
    obtain ⟨x, hx, he⟩ := T.exists_euclideanAngularChart_direction hσ hpσ hu hne
    refine ⟨x, hx, ?_⟩
    apply GeodesicSphere.ext
    rw [he, add_sub_cancel_left, NormedSpace.normalize_smul_of_pos hr,
      NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_val]

theorem geodesic_mem_image_euclideanAngularChart
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x y : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) (hy : y ∈ T.linkRegion p σ)
    (hπ : dist (T.euclideanAngularChart p σ x) (T.euclideanAngularChart p σ y) < Real.pi)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    GeodesicSphere.geodesic (T.euclideanAngularChart p σ x)
      (T.euclideanAngularChart p σ y) hπ t ∈ T.euclideanAngularChart p σ '' T.linkRegion p σ := by
  rw [T.image_euclideanAngularChart hσ hpσ]
  apply geodesic_mem_radialDirections (convex_convexHull ℝ _)
    _ _ hπ ht
  · change T.euclideanAngularChart p σ x ∈
      radialDirections (hull .euclidean (n + 1) (σ.image (T.chart σ))) (T.chart σ p)
    rw [← T.image_euclideanAngularChart hσ hpσ]
    exact ⟨x, hx, rfl⟩
  · change T.euclideanAngularChart p σ y ∈
      radialDirections (hull .euclidean (n + 1) (σ.image (T.chart σ))) (T.chart σ p)
    rw [← T.image_euclideanAngularChart hσ hpσ]
    exact ⟨y, hy, rfl⟩

end ArchivePLGeometry.FiniteChartedComplex
