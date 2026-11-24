module

public import PLGeometry.SphericalLinkBoundaryBase
public import BrehmApprox.SphericalAffineFrame
public import BrehmApprox.SphericalActiveProjection
public import BrehmApprox.RadialBoundaryEmbedding

/-! # Injective angular charts on the visible spherical boundary -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.SphericalLink

namespace BrehmApprox.SphericalLink

variable {n : ℕ}

theorem mem_face_iff_frame_mem_hull {V W : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) {p x : GeodesicSphere n}
    (hp : p ∈ sphericalCell V) (hWV : W ⊆ V) (hx : x ∈ sphericalCell V) :
    x ∈ sphericalCell W ↔ frame V hV p x ∈
      convexHull ℝ (frameVertices V hV p W : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  rw [← frame_image_face (V := V) (hV := hV) (p := p) hWV]
  constructor
  · exact Set.mem_image_of_mem _
  · rintro ⟨y, hy, he⟩
    have hyV := sphericalCell_mono hWV hy
    exact frame_injectiveOn (V := V) (hV := hV) (p := p) hp hyV hx he ▸ hy

end BrehmApprox.SphericalLink

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalLinkBoundaryDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalLinkBoundaryModelEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance sphericalLinkBoundaryVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def sphericalFrame (p : P) (σ : Finset P) (hσ : σ ∈ T.simplices) :
    GeodesicSphere n → EuclideanSpace ℝ (Fin (n + 1)) :=
  frame (σ.image (T.chart σ)) (T.simplex σ hσ).2 (T.chart σ p)

def sphericalFrameVertices (p : P) (σ : Finset P) (hσ : σ ∈ T.simplices)
    (U : Finset P) : Finset (EuclideanSpace ℝ (Fin (n + 1))) :=
  frameVertices (σ.image (T.chart σ)) (T.simplex σ hσ).2 (T.chart σ p) (U.image (T.chart σ))

theorem sphericalAngularChart_eq_boundary_projection {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    (T.sphericalAngularChart p σ x).val = NormedSpace.normalize
      (T.sphericalFrame p σ hσ (T.chart σ (T.sphericalBoundaryPoint p x))) := by
  have hxV : T.chart σ (T.sphericalBoundaryPoint p x) ∈ sphericalCell (σ.image (T.chart σ)) := by
    have hm := Set.mem_image_of_mem (T.chart σ) (T.sphericalBoundaryPoint_mem hσ hx)
    rw [T.image_cell σ hσ] at hm
    exact hm
  rw [sphericalFrame, normalize_frame (V := σ.image (T.chart σ))
    (hV := (T.simplex σ hσ).2) (p := T.chart σ p) hxV]
  exact T.sphericalAngularChart_eq_boundary_tangent hσ hpσ x hx

theorem chart_sphericalBoundaryPoint_mem_visibleBoundary {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) :
    T.sphericalFrame p σ hσ (T.chart σ (T.sphericalBoundaryPoint p x)) ∈
      visibleBoundary (T.sphericalFrameVertices p σ hσ σ) 0 := by
  let y := T.sphericalLinkReweight p x
  let U := T.linkSourceVertices ((T.linkComplex p).support y)
  have hsub : U ⊆ σ := (T.sphericalLinkReweight_mem_region p σ x).mpr hx
  have hpU := (T.linkCoface_spec ((T.linkComplex p).support_mem y)).2.2.2
  have hface : T.chart σ '' T.cell U = sphericalCell (U.image (T.chart σ)) :=
    T.image_face σ hσ U hsub
  have hpV : T.chart σ p ∈ sphericalCell (σ.image (T.chart σ)) := by
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  refine ⟨T.sphericalFrameVertices p σ hσ U,
    Finset.image_subset_image (Finset.image_subset_image hsub), ?_, ?_⟩
  · intro h
    rw [← frame_self (σ.image (T.chart σ)) (T.simplex σ hσ).2 (T.chart σ p)] at h
    have hm := (mem_face_iff_frame_mem_hull (T.simplex σ hσ).2 hpV
      (Finset.image_subset_image hsub) hpV).mpr h
    rw [← hface] at hm
    obtain ⟨z, hz, he⟩ := hm
    have hzp := T.chart_injectiveOn σ hσ (T.cell_mono hσ hsub hz) hpσ he
    exact hpU (Eq.mp (congrArg (fun q : P => q ∈ T.cell U) hzp) hz)
  · have hxV : T.chart σ (T.sphericalBoundaryPoint p x) ∈
        sphericalCell (σ.image (T.chart σ)) := by
      have hm := Set.mem_image_of_mem (T.chart σ) (T.sphericalBoundaryPoint_mem hσ hx)
      rw [T.image_cell σ hσ] at hm
      exact hm
    apply (mem_face_iff_frame_mem_hull (T.simplex σ hσ).2 hpV
      (Finset.image_subset_image hsub) hxV).mp
    rw [← hface]
    exact ⟨_, T.linkBoundaryInclusion_mem_support p y, rfl⟩

theorem sphericalAngularChart_injectiveOn {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    Set.InjOn (T.sphericalAngularChart p σ) (T.linkRegion p σ) := by
  intro x hx y hy he
  apply T.sphericalBoundaryPoint_injective p
  apply T.chart_injectiveOn σ hσ (T.sphericalBoundaryPoint_mem hσ hx)
    (T.sphericalBoundaryPoint_mem hσ hy)
  have hpV : T.chart σ p ∈ sphericalCell (σ.image (T.chart σ)) := by
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  have hxV : T.chart σ (T.sphericalBoundaryPoint p x) ∈ sphericalCell (σ.image (T.chart σ)) := by
    have hm := Set.mem_image_of_mem (T.chart σ) (T.sphericalBoundaryPoint_mem hσ hx)
    rw [T.image_cell σ hσ] at hm
    exact hm
  have hyV : T.chart σ (T.sphericalBoundaryPoint p y) ∈ sphericalCell (σ.image (T.chart σ)) := by
    have hm := Set.mem_image_of_mem (T.chart σ) (T.sphericalBoundaryPoint_mem hσ hy)
    rw [T.image_cell σ hσ] at hm
    exact hm
  apply frame_injectiveOn (V := σ.image (T.chart σ)) (hV := (T.simplex σ hσ).2)
    (p := T.chart σ p) hpV hxV hyV
  have hV := frameVertices_independent (V := σ.image (T.chart σ))
    (hV := (T.simplex σ hσ).2) (p := T.chart σ p) hpV
  have hp0 : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈
      convexHull ℝ (T.sphericalFrameVertices p σ hσ σ : Set _) := by
    rw [← frame_self (σ.image (T.chart σ)) (T.simplex σ hσ).2 (T.chart σ p)]
    exact (mem_face_iff_frame_mem_hull (T.simplex σ hσ).2 hpV (Finset.Subset.refl _) hpV).mp hpV
  apply radialProjection_injectiveOn_visibleBoundary _ hV hp0
    (T.chart_sphericalBoundaryPoint_mem_visibleBoundary hσ hpσ x hx)
    (T.chart_sphericalBoundaryPoint_mem_visibleBoundary hσ hpσ y hy)
  change NormedSpace.normalize (_ - 0) = NormedSpace.normalize (_ - 0)
  simp only [sub_zero]
  rw [← T.sphericalAngularChart_eq_boundary_projection hσ hpσ x hx,
    ← T.sphericalAngularChart_eq_boundary_projection hσ hpσ y hy, he]

end ArchivePLGeometry.FiniteChartedComplex
