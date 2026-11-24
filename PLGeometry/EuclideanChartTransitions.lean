module

public import PLGeometry.ChartedComplex
public import BrehmApprox.FiniteDistanceIsometry

/-!
# Euclidean chart transitions

The compatibility of cell metrics forces the coordinate changes on common
faces to be restrictions of ambient rigid motions. In particular, every
new convex subcell has the same meaning in all charts containing it.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

local instance euclideanChartTransitionsLocalInstance1 (α : Type*) : DecidableEq α := Classical.decEq α

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean n P)

local instance euclideanChartTransitionsLocalInstance2 : DecidableEq (Model .euclidean n) := Classical.decEq _

theorem euclidean_chart_vertices_independent
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτσ : τ ⊆ σ) :
    AffineIndependent ℝ (fun v : τ => T.chart σ v.val) := by
  let e : τ ↪ σ.image (T.chart σ) :=
    { toFun := fun v => ⟨T.chart σ v.val, Finset.mem_image.mpr ⟨v.val, hτσ v.property, rfl⟩⟩
      inj' := by
        intro v w he
        apply Subtype.ext
        apply T.chart_injectiveOn σ hσ
          (T.vertices_mem σ hσ (hτσ v.property))
          (T.vertices_mem σ hσ (hτσ w.property))
        exact congrArg Subtype.val he }
  have hs : AffineIndependent ℝ
      ((↑) : σ.image (T.chart σ) → Model .euclidean n) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using T.simplex σ hσ
  exact hs.comp_embedding e

/-- A common-face transition extends to a Euclidean motion. -/
theorem exists_euclidean_chart_transition
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices) :
    ∃ r : Model .euclidean n ≃ᵃⁱ[ℝ] Model .euclidean n,
      ∀ x ∈ T.cell σ ∩ T.cell τ, r (T.chart σ x) = T.chart τ x := by
  let V := σ ∩ τ
  have hv (v : V) : v.val ∈ T.cell σ ∩ T.cell τ :=
    ⟨T.vertices_mem σ hσ (Finset.mem_inter.mp v.property).1,
      T.vertices_mem τ hτ (Finset.mem_inter.mp v.property).2⟩
  obtain ⟨r, hr⟩ := BrehmApprox.exists_ambient_distance_isometry
    (fun v : V => T.chart σ v.val) (fun v : V => T.chart τ v.val)
    (T.euclidean_chart_vertices_independent hσ Finset.inter_subset_left)
    (fun v w => T.metric_coherence σ hσ τ hτ v.val (hv v) w.val (hv w))
  refine ⟨r, ?_⟩
  intro x hx
  have hxV : x ∈ T.cell V := by rwa [T.intersection σ hσ τ hτ] at hx
  have hxim : T.chart σ x ∈ convexHull ℝ (V.image (T.chart σ) : Set (Model .euclidean n)) := by
    have hm := Set.mem_image_of_mem (T.chart σ) hxV
    have he := T.image_face σ hσ V Finset.inter_subset_left
    rw [he] at hm
    exact hm
  apply BrehmApprox.affineIsometry_eq_of_vertex_distances r hxim
  intro v hv'
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv'
  rw [hr ⟨z, hz⟩]
  exact (T.metric_coherence σ hσ τ hτ x hx z (hv ⟨z, hz⟩)).symm

/-- A convex subcell spanned by points of a common source face remains in
that source face. The spanning points need not be old vertices. -/
theorem mem_common_cell_of_convexHull_chart
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
    (V : Finset P) (hV : ∀ v ∈ V, v ∈ T.cell σ ∩ T.cell τ)
    {x : P} (hx : x ∈ T.cell σ)
    (hqx : T.chart σ x ∈ convexHull ℝ (V.image (T.chart σ) : Set (Model .euclidean n))) :
    x ∈ T.cell τ := by
  have he := T.image_face σ hσ (σ ∩ τ) Finset.inter_subset_left
  have hsub : convexHull ℝ (V.image (T.chart σ) : Set (Model .euclidean n)) ⊆
      hull .euclidean n ((σ ∩ τ).image (T.chart σ)) := by
    apply convexHull_min ?_ (convex_convexHull ℝ _)
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hvc : v ∈ T.cell (σ ∩ τ) := by
      rw [← T.intersection σ hσ τ hτ]
      exact hV v hv
    have hm := Set.mem_image_of_mem (T.chart σ) hvc
    rw [he] at hm
    exact hm
  have hm := hsub hqx
  rw [← he] at hm
  obtain ⟨y, hy, hxy⟩ := hm
  have hy' : y ∈ T.cell σ ∩ T.cell τ := by rwa [T.intersection σ hσ τ hτ]
  have hyx := T.chart_injectiveOn σ hσ hy'.1 hx hxy
  exact hyx ▸ hy'.2

end ArchivePLGeometry.FiniteChartedComplex
