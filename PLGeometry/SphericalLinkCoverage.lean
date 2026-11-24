module

public import PLGeometry.SphericalLinkBoundary
public import PLGeometry.LinkBoundarySurjectivity
public import BrehmApprox.RadialDomains

/-! # Coverage and short-arc convexity of spherical angular regions -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.SphericalLink

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalLinkCoverageDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalLinkCoverageModelEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance sphericalLinkCoverageVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem exists_spherical_boundary_source_same_direction
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {z : GeodesicSphere n} (hz : z ∈ sphericalCell (σ.image (T.chart σ)))
    (hzp : z ≠ T.chart σ p) :
    ∃ U : Finset P, U ⊆ σ ∧ p ∉ T.cell U ∧ ∃ y ∈ T.cell U,
      NormedSpace.normalize (T.sphericalFrame p σ hσ (T.chart σ y)) =
        NormedSpace.normalize (T.sphericalFrame p σ hσ z) := by
  let V := σ.image (T.chart σ)
  have hV : LinearIndependent ℝ (fun v : V => v.val.val) := (T.simplex σ hσ).2
  let a := T.chart σ p
  have hpV : a ∈ sphericalCell V := by
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  let W₀ := T.sphericalFrameVertices p σ hσ σ
  have hW₀ := frameVertices_independent V hV hpV
  have hp0 : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ convexHull ℝ (W₀ : Set _) := by
    rw [← frame_self V hV a]
    exact (mem_face_iff_frame_mem_hull hV hpV (Finset.Subset.refl _) hpV).mp hpV
  have hzf : T.sphericalFrame p σ hσ z ∈ convexHull ℝ (W₀ : Set _) :=
    (mem_face_iff_frame_mem_hull hV hpV (Finset.Subset.refl _) hz).mp hz
  have hzf0 : T.sphericalFrame p σ hσ z ≠ 0 := by
    intro he
    exact hzp (frame_injectiveOn V hV hpV hz hpV (he.trans (frame_self V hV a).symm))
  obtain ⟨y, ⟨W, hWV, hpW, hyW⟩, he⟩ :=
    exists_visibleBoundary_same_direction W₀ hW₀ hp0 hzf hzf0
  let U := σ.filter fun v => T.sphericalFrame p σ hσ (T.chart σ v) ∈ W
  have hUσ : U ⊆ σ := Finset.filter_subset _ _
  have hUimage : T.sphericalFrameVertices p σ hσ U = W := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hq).2
    · intro hw
      obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp (hWV hw)
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      have hwq : T.sphericalFrame p σ hσ (T.chart σ q) ∈ W := by
        change frame (σ.image (T.chart σ)) (T.simplex σ hσ).2 (T.chart σ p) (T.chart σ q) ∈ W
        rwa [hve]
      exact Finset.mem_image.mpr ⟨T.chart σ q, Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨hq, hwq⟩, rfl⟩, hve⟩
  have hface : T.chart σ '' T.cell U = sphericalCell (U.image (T.chart σ)) :=
    T.image_face σ hσ U hUσ
  have hpU : p ∉ T.cell U := by
    intro hp
    apply hpW
    rw [← hUimage, ← frame_self V hV a]
    apply (mem_face_iff_frame_mem_hull hV hpV (Finset.image_subset_image hUσ) hpV).mp
    rw [← hface]
    exact ⟨p, hp, rfl⟩
  have himage : T.sphericalFrame p σ hσ '' sphericalCell (U.image (T.chart σ)) =
      convexHull ℝ (T.sphericalFrameVertices p σ hσ U : Set _) :=
    frame_image_face V hV a (Finset.image_subset_image hUσ)
  rw [← hUimage, ← himage] at hyW
  obtain ⟨m, hm, hmy⟩ := hyW
  rw [← hface] at hm
  obtain ⟨q, hq, hqm⟩ := hm
  refine ⟨U, hUσ, hpU, q, hq, ?_⟩
  rw [hqm, hmy]
  simpa only [sub_zero] using he

theorem exists_sphericalAngularChart_direction
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {z : GeodesicSphere n} (hz : z ∈ sphericalCell (σ.image (T.chart σ)))
    (hzp : z ≠ T.chart σ p) :
    ∃ x ∈ T.linkRegion p σ, (T.sphericalAngularChart p σ x).val =
      NormedSpace.normalize (tangentLinear (T.chart σ p) z.val) := by
  obtain ⟨U, hUσ, hpU, y, hy, he⟩ :=
    T.exists_spherical_boundary_source_same_direction hσ hpσ hz hzp
  obtain ⟨a, ha, hya⟩ := T.exists_linkBoundaryInclusion_of_face hσ hpσ hUσ hpU hy
  let x := (T.sphericalLinkReweight p).symm a
  have haσ : a ∈ T.linkRegion p σ := ha.trans hUσ
  have hx : x ∈ T.linkRegion p σ :=
    (T.sphericalLinkReweight_mem_region p σ x).mp (by
      simpa only [x, Homeomorph.apply_symm_apply] using haσ)
  refine ⟨x, hx, ?_⟩
  rw [T.sphericalAngularChart_eq_boundary_projection hσ hpσ x hx]
  have hb : T.sphericalBoundaryPoint p x = y := by
    simpa only [sphericalBoundaryPoint, x, Homeomorph.apply_symm_apply] using hya
  rw [hb, he]
  exact normalize_frame (σ.image (T.chart σ)) (T.simplex σ hσ).2 (T.chart σ p) hz

theorem image_sphericalAngularChart
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    T.sphericalAngularChart p σ '' T.linkRegion p σ =
      radialDirections (convexHull ℝ (T.sphericalFrameVertices p σ hσ σ : Set _)) 0 := by
  let V := σ.image (T.chart σ)
  have hV : LinearIndependent ℝ (fun v : V => v.val.val) := (T.simplex σ hσ).2
  let a := T.chart σ p
  have hpV : a ∈ sphericalCell V := by
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  apply Set.Subset.antisymm
  · rintro u ⟨x, hx, rfl⟩
    let z := T.sphericalFrame p σ hσ (T.chart σ (T.sphericalBoundaryPoint p x))
    have hxV : T.chart σ (T.sphericalBoundaryPoint p x) ∈ sphericalCell V := by
      have hm := Set.mem_image_of_mem (T.chart σ) (T.sphericalBoundaryPoint_mem hσ hx)
      rw [T.image_cell σ hσ] at hm
      exact hm
    have hz0 : z ≠ 0 := by
      intro he
      have hh := frame_injectiveOn V hV hpV hxV hpV (he.trans (frame_self V hV a).symm)
      have hxp := T.chart_injectiveOn σ hσ (T.sphericalBoundaryPoint_mem hσ hx) hpσ hh
      exact T.linkBoundaryInclusion_ne_center p (T.sphericalLinkReweight p x) hxp
    refine ⟨‖z‖, norm_pos_iff.mpr hz0, ?_⟩
    rw [zero_add, T.sphericalAngularChart_eq_boundary_projection hσ hpσ x hx,
      NormedSpace.norm_smul_normalize]
    exact (mem_face_iff_frame_mem_hull hV hpV (Finset.Subset.refl _) hxV).mp hxV
  · rintro u ⟨r, hr, hu⟩
    have himage : T.sphericalFrame p σ hσ '' sphericalCell V =
        convexHull ℝ (T.sphericalFrameVertices p σ hσ σ : Set _) :=
      frame_image_face V hV a (Finset.Subset.refl _)
    rw [zero_add, ← himage] at hu
    obtain ⟨z, hz, hzr⟩ := hu
    have hzp : z ≠ a := by
      intro he
      rw [he, show T.sphericalFrame p σ hσ a = 0 from frame_self V hV a] at hzr
      exact smul_ne_zero hr.ne' u.val_ne_zero hzr.symm
    obtain ⟨x, hx, he⟩ := T.exists_sphericalAngularChart_direction hσ hpσ hz hzp
    refine ⟨x, hx, ?_⟩
    apply GeodesicSphere.ext
    rw [he, ← normalize_frame V hV a hz]
    change NormedSpace.normalize (T.sphericalFrame p σ hσ z) = u.val
    rw [hzr, NormedSpace.normalize_smul_of_pos hr,
      NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_val]

theorem geodesic_mem_image_sphericalAngularChart
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x y : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) (hy : y ∈ T.linkRegion p σ)
    (hπ : dist (T.sphericalAngularChart p σ x) (T.sphericalAngularChart p σ y) < Real.pi)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    GeodesicSphere.geodesic (T.sphericalAngularChart p σ x)
      (T.sphericalAngularChart p σ y) hπ t ∈ T.sphericalAngularChart p σ '' T.linkRegion p σ := by
  rw [T.image_sphericalAngularChart hσ hpσ]
  apply geodesic_mem_radialDirections (convex_convexHull ℝ _) _ _ hπ ht
  · rw [← T.image_sphericalAngularChart hσ hpσ]
    exact ⟨x, hx, rfl⟩
  · rw [← T.image_sphericalAngularChart hσ hpσ]
    exact ⟨y, hy, rfl⟩

end ArchivePLGeometry.FiniteChartedComplex
