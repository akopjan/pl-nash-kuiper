module

public import PLGeometry.HyperbolicLinkBoundary
public import PLGeometry.LinkBoundarySurjectivity
public import BrehmApprox.RadialDomains

/-! # Coverage and short-arc convexity of hyperbolic angular regions -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.HyperbolicSpace BrehmApprox.HyperbolicLink

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

local instance hyperbolicLinkCoverageDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance hyperbolicLinkCoverageModelEq : DecidableEq (Model .hyperbolic (n + 1)) := Classical.decEq _
local instance hyperbolicLinkCoverageVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem exists_hyperbolic_boundary_source_same_direction
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {z : Model .hyperbolic (n + 1)}
    (hz : z ∈ hull .hyperbolic (n + 1) (σ.image (T.chart σ)))
    (hzp : z ≠ T.chart σ p) :
    ∃ U : Finset P, U ⊆ σ ∧ p ∉ T.cell U ∧ ∃ y ∈ T.cell U,
      NormedSpace.normalize (frame (T.chart σ p) (T.chart σ y)) =
        NormedSpace.normalize (frame (T.chart σ p) z) := by
  let a := T.chart σ p
  let V := frameVertices a (σ.image (T.chart σ))
  have hV := frameVertices_independent a (T.simplex σ hσ)
  have hpV : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ convexHull ℝ (V : Set _) := by
    rw [← frame_self a]
    apply (mem_cell_iff_frame_mem_hull a a _).mp
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  have hzf : frame a z ∈ convexHull ℝ (V : Set _) := (mem_cell_iff_frame_mem_hull a z _).mp hz
  have hzf0 : frame a z ≠ 0 := by
    intro he
    exact hzp (frame_injective a (he.trans (frame_self a).symm))
  obtain ⟨y, ⟨W, hWV, hpW, hyW⟩, he⟩ :=
    exists_visibleBoundary_same_direction V hV hpV hzf hzf0
  let U := σ.filter fun v => frame a (T.chart σ v) ∈ W
  have hUσ : U ⊆ σ := Finset.filter_subset _ _
  have hUimage : frameVertices a (U.image (T.chart σ)) = W := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hq).2
    · intro hw
      obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp (hWV hw)
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨T.chart σ q, Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨hq, hve ▸ hw⟩, rfl⟩, hve⟩
  have hface : T.chart σ '' T.cell U = hyperbolicCell (U.image (T.chart σ)) :=
    T.image_face σ hσ U hUσ
  have hpU : p ∉ T.cell U := by
    intro hp
    apply hpW
    rw [← hUimage, ← frame_self a]
    apply (mem_cell_iff_frame_mem_hull a a _).mp
    rw [← hface]
    exact ⟨p, hp, rfl⟩
  rw [← hUimage, ← frame_image_cell] at hyW
  obtain ⟨m, hm, hmy⟩ := hyW
  rw [← hface] at hm
  obtain ⟨q, hq, hqm⟩ := hm
  refine ⟨U, hUσ, hpU, q, hq, ?_⟩
  change NormedSpace.normalize (frame a (T.chart σ q)) = NormedSpace.normalize (frame a z)
  rw [hqm, hmy]
  simpa only [sub_zero] using he

theorem exists_hyperbolicAngularChart_direction
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {z : Model .hyperbolic (n + 1)}
    (hz : z ∈ hull .hyperbolic (n + 1) (σ.image (T.chart σ)))
    (hzp : z ≠ T.chart σ p) :
    ∃ x ∈ T.linkRegion p σ, (T.hyperbolicAngularChart p σ x).val =
      NormedSpace.normalize (frame (T.chart σ p) z) := by
  obtain ⟨U, hUσ, hpU, y, hy, he⟩ :=
    T.exists_hyperbolic_boundary_source_same_direction hσ hpσ hz hzp
  obtain ⟨a, ha, hya⟩ := T.exists_linkBoundaryInclusion_of_face hσ hpσ hUσ hpU hy
  let x := (T.hyperbolicLinkReweight p).symm a
  have haσ : a ∈ T.linkRegion p σ := ha.trans hUσ
  have hx : x ∈ T.linkRegion p σ :=
    (T.hyperbolicLinkReweight_mem_region p σ x).mp (by
      simpa only [x, Homeomorph.apply_symm_apply] using haσ)
  refine ⟨x, hx, ?_⟩
  rw [T.hyperbolicAngularChart_eq_boundary_projection hσ hpσ x hx]
  have hb : T.hyperbolicBoundaryPoint p x = y := by
    simpa only [hyperbolicBoundaryPoint, x, Homeomorph.apply_symm_apply] using hya
  rw [hb]
  exact he

theorem image_hyperbolicAngularChart
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    T.hyperbolicAngularChart p σ '' T.linkRegion p σ =
      radialDirections (convexHull ℝ (frameVertices (T.chart σ p) (σ.image (T.chart σ)) : Set _)) 0 := by
  apply Set.Subset.antisymm
  · rintro u ⟨x, hx, rfl⟩
    let z := frame (T.chart σ p) (T.chart σ (T.hyperbolicBoundaryPoint p x))
    have hz0 : z ≠ 0 := by
      intro he
      have hh := frame_injective (T.chart σ p) (he.trans (frame_self _).symm)
      have hxp := T.chart_injectiveOn σ hσ (T.hyperbolicBoundaryPoint_mem hσ hx) hpσ hh
      exact T.linkBoundaryInclusion_ne_center p (T.hyperbolicLinkReweight p x) hxp
    refine ⟨‖z‖, norm_pos_iff.mpr hz0, ?_⟩
    rw [zero_add, T.hyperbolicAngularChart_eq_boundary_projection hσ hpσ x hx,
      NormedSpace.norm_smul_normalize]
    apply (mem_cell_iff_frame_mem_hull (T.chart σ p) _ _).mp
    have hm := Set.mem_image_of_mem (T.chart σ) (T.hyperbolicBoundaryPoint_mem hσ hx)
    rw [T.image_cell σ hσ] at hm
    exact hm
  · rintro u ⟨r, hr, hu⟩
    rw [zero_add, ← frame_image_cell] at hu
    obtain ⟨z, hz, hzr⟩ := hu
    have hzp : z ≠ T.chart σ p := by
      intro he
      rw [he, frame_self] at hzr
      exact smul_ne_zero hr.ne' u.val_ne_zero hzr.symm
    obtain ⟨x, hx, he⟩ := T.exists_hyperbolicAngularChart_direction hσ hpσ hz hzp
    refine ⟨x, hx, ?_⟩
    apply GeodesicSphere.ext
    rw [he, hzr, NormedSpace.normalize_smul_of_pos hr,
      NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_val]

theorem geodesic_mem_image_hyperbolicAngularChart
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x y : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) (hy : y ∈ T.linkRegion p σ)
    (hπ : dist (T.hyperbolicAngularChart p σ x) (T.hyperbolicAngularChart p σ y) < Real.pi)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    GeodesicSphere.geodesic (T.hyperbolicAngularChart p σ x)
      (T.hyperbolicAngularChart p σ y) hπ t ∈ T.hyperbolicAngularChart p σ '' T.linkRegion p σ := by
  rw [T.image_hyperbolicAngularChart hσ hpσ]
  apply geodesic_mem_radialDirections (convex_convexHull ℝ _) _ _ hπ ht
  · rw [← T.image_hyperbolicAngularChart hσ hpσ]
    exact ⟨x, hx, rfl⟩
  · rw [← T.image_hyperbolicAngularChart hσ hpσ]
    exact ⟨y, hy, rfl⟩

end ArchivePLGeometry.FiniteChartedComplex
