module

public import PLGeometry.VertexFolding
public import PLGeometry.ChartedProjectiveTransport

/-! # Spherical chart changes on common faces -/

@[expose] public section
noncomputable section

open BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalChartTransitionsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalChartTransitionsModelEq : DecidableEq (GeodesicSphere n) := Classical.decEq _

theorem spherical_chart_vertices_independent
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτσ : τ ⊆ σ) :
    LinearIndependent ℝ (fun v : τ => (T.chart σ v.val).val) := by
  let e : τ ↪ σ := ⟨fun v => ⟨v.val, hτσ v.property⟩,
    fun x y h => Subtype.ext (congrArg (fun z : σ => z.val) h)⟩
  exact (T.vertexModel_independent σ hσ).comp e e.injective

theorem exists_spherical_chart_transition
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices) :
    ∃ R : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      ∀ x ∈ T.cell σ ∩ T.cell τ,
        GeodesicSphere.mapEquiv R (T.chart σ x) = T.chart τ x := by
  let V := σ ∩ τ
  have hv (v : V) : v.val ∈ T.cell σ ∩ T.cell τ :=
    ⟨T.vertices_mem σ hσ (Finset.mem_inter.mp v.property).1,
      T.vertices_mem τ hτ (Finset.mem_inter.mp v.property).2⟩
  obtain ⟨R, hR⟩ := exists_spherical_vertex_motion
    (fun v : V => T.chart σ v.val) (fun v : V => T.chart τ v.val)
    (T.spherical_chart_vertices_independent hσ Finset.inter_subset_left)
    (fun v w => T.metric_coherence σ hσ τ hτ v.val (hv v) w.val (hv w))
  refine ⟨R, ?_⟩
  intro x hx
  have hxV : x ∈ T.cell V := by rwa [T.intersection σ hσ τ hτ] at hx
  have hxim : T.chart σ x ∈ sphericalCell (V.image (T.chart σ)) := by
    change T.chart σ x ∈ hull .spherical n (V.image (T.chart σ))
    rw [← T.image_face σ hσ V Finset.inter_subset_left]
    exact Set.mem_image_of_mem _ hxV
  apply sphericalMotion_eq_of_vertex_distances R hxim
  intro v hv'
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv'
  rw [hR ⟨z, hz⟩]
  exact (T.metric_coherence σ hσ τ hτ x hx z (hv ⟨z, hz⟩)).symm

theorem mem_common_cell_of_sphericalCell_chart
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
    (V : Finset P) (hV : ∀ v ∈ V, v ∈ T.cell σ ∩ T.cell τ)
    {x : P} (hx : x ∈ T.cell σ)
    (hqx : T.chart σ x ∈ sphericalCell (V.image (T.chart σ))) : x ∈ T.cell τ := by
  have he := T.image_face σ hσ (σ ∩ τ) Finset.inter_subset_left
  have hsub : hull .spherical n (V.image (T.chart σ)) ⊆
      hull .spherical n ((σ ∩ τ).image (T.chart σ)) := by
    apply hull_transitive
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rw [← he]
    refine ⟨v, ?_, rfl⟩
    rw [← T.intersection σ hσ τ hτ]
    exact hV v hv
  have hm := hsub hqx
  rw [← he] at hm
  obtain ⟨y, hy, hxy⟩ := hm
  have hy' : y ∈ T.cell σ ∩ T.cell τ := by rwa [T.intersection σ hσ τ hτ]
  have hyx := T.chart_injectiveOn σ hσ hy'.1 hx hxy
  exact hyx ▸ hy'.2

end ArchivePLGeometry.FiniteChartedComplex
