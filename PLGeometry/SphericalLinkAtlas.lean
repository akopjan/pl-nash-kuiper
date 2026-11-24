module

public import PLGeometry.SphericalRadialSites
public import PLGeometry.LinkRegions

/-! # A single angular chart on each old spherical simplex -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalLinkAtlasDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalLinkAtlasModelEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance sphericalLinkAtlasLabelEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def sphericalAngularVector (p : P) (σ : Finset P) (v : T.LinkVertex p) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  SphericalLink.tangentLinear (T.chart σ p) (T.chart σ v.val).val

def sphericalAngularVertex (p : P) (σ : Finset P) (v : T.LinkVertex p) : GeodesicSphere n :=
  CrossPolytope.sphereNormalize (T.sphericalAngularVector p σ v)

def sphericalAngularChart (p : P) (σ : Finset P) (x : (T.linkComplex p).Space) :
    GeodesicSphere n := Barycentric.chartPoint (T.sphericalAngularVertex p σ) x.val

theorem sphericalAngularVector_transition {p : P} {σ γ : Finset P}
    (hpσ : p ∈ T.cell σ) (hpγ : p ∈ T.cell γ)
    (R : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hR : ∀ z ∈ T.cell γ ∩ T.cell σ,
      GeodesicSphere.mapEquiv R (T.chart γ z) = T.chart σ z)
    (v : T.LinkVertex p) (hvγ : v.val ∈ T.cell γ) (hvσ : v.val ∈ T.cell σ) :
    R (T.sphericalAngularVector p γ v) = T.sphericalAngularVector p σ v := by
  have hp : R (T.chart γ p).val = (T.chart σ p).val :=
    congrArg GeodesicSphere.val (hR p ⟨hpγ, hpσ⟩)
  have hv : R (T.chart γ v.val).val = (T.chart σ v.val).val :=
    congrArg GeodesicSphere.val (hR v.val ⟨hvγ, hvσ⟩)
  rw [sphericalAngularVector, SphericalLink.tangentLinear_apply, map_sub, map_smul, hp, hv]
  change _ = (T.chart σ v.val).val - inner ℝ (T.chart σ p).val (T.chart σ v.val).val • (T.chart σ p).val
  rw [← hp, ← hv, R.inner_map_map]

theorem sphericalAngularVertex_transition {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ)
    (R : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hR : ∀ z ∈ T.cell (T.linkCoface p τ) ∩ T.cell σ,
      GeodesicSphere.mapEquiv R (T.chart (T.linkCoface p τ) z) = T.chart σ z)
    (v : T.LinkVertex p) (hv : v ∈ τ) :
    R (T.sphericalLinkVertex p τ v).val = (T.sphericalAngularVertex p σ v).val := by
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  have hvs := T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩
  have he := T.sphericalAngularVector_transition hpσ hpγ R hR v
    (T.vertices_mem _ hγ (hτγ hvs)) (T.vertices_mem _ hσ (hsub hvs))
  have hn := T.sphericalLinkTangent_ne_zero hτ hv
  have hn' : T.sphericalAngularVector p σ v ≠ 0 := by
    rw [← he]
    exact fun h => hn (R.injective (h.trans (map_zero _).symm))
  rw [sphericalLinkVertex, sphericalAngularVertex,
    CrossPolytope.sphereNormalize_val hn, CrossPolytope.sphereNormalize_val hn']
  exact (linearIsometry_map_normalize R.toLinearIsometry _).trans
    (congrArg NormedSpace.normalize he)

theorem sphericalAngularChart_transition {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ)
    (R : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hR : ∀ z ∈ T.cell (T.linkCoface p τ) ∩ T.cell σ,
      GeodesicSphere.mapEquiv R (T.chart (T.linkCoface p τ) z) = T.chart σ z)
    (x : (T.linkComplex p).Space) (hx : x.val ∈ Barycentric.weightsOn τ) :
    (T.sphericalAngularChart p σ x).val =
      R (Barycentric.chartPoint (T.sphericalLinkVertex p τ) x.val).val := by
  let z := SphericalBarycentric.vector (T.sphericalLinkVertex p τ) x.val
  have hz : z ≠ 0 := by
    rw [show z = SphericalBarycentric.vector (T.sphericalLinkVertex p τ) x.val from rfl,
      Barycentric.vector_restrict τ _ ⟨x.val, hx⟩]
    exact SphericalBarycentric.vector_ne_zero _ (T.sphericalLinkVertex_independent hτ) _
  have he : SphericalBarycentric.vector (T.sphericalAngularVertex p σ) x.val = R z := by
    simp only [z, SphericalBarycentric.vector, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ τ
    · rw [T.sphericalAngularVertex_transition hτ hσ hpσ hsub R hR v hv]
    · rw [hx.2 v hv, zero_smul, zero_smul]
  have hz' : SphericalBarycentric.vector (T.sphericalAngularVertex p σ) x.val ≠ 0 := by
    rw [he]
    exact fun h => hz (R.injective (h.trans (map_zero _).symm))
  rw [sphericalAngularChart, Barycentric.chartPoint, Barycentric.chartPoint,
    CrossPolytope.sphereNormalize_val hz', CrossPolytope.sphereNormalize_val hz, he]
  exact (linearIsometry_map_normalize R.toLinearIsometry z).symm

theorem sphericalAngularVertex_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ) :
    LinearIndependent ℝ (fun v : τ => (T.sphericalAngularVertex p σ v.val).val) := by
  obtain ⟨hγ, _, _, _⟩ := T.linkCoface_spec hτ
  obtain ⟨R, hR⟩ := T.exists_spherical_chart_transition hγ hσ
  have hi := (T.sphericalLinkVertex_independent hτ).map'
    R.toLinearMap (LinearMap.ker_eq_bot.mpr R.injective)
  have he : (R.toLinearMap ∘ (fun v : τ => (T.sphericalLinkVertex p τ v.val).val)) =
      (fun v : τ => (T.sphericalAngularVertex p σ v.val).val) := by
    funext v
    exact T.sphericalAngularVertex_transition hτ hσ hpσ hsub R hR v.val v.property
  rwa [he] at hi

theorem sphericalAngularChart_vector_ne_zero {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) :
    SphericalBarycentric.vector (T.sphericalAngularVertex p σ) x.val ≠ 0 := by
  let τ := (T.linkComplex p).support x
  rw [Barycentric.vector_restrict τ _ ⟨x.val, (T.linkComplex p).weightsOn_support x⟩]
  exact SphericalBarycentric.vector_ne_zero _
    (T.sphericalAngularVertex_independent ((T.linkComplex p).support_mem x) hσ hpσ hx) _

theorem continuousOn_sphericalAngularChart {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    ContinuousOn (T.sphericalAngularChart p σ) (T.linkRegion p σ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := GeodesicSphere.continuous_normalizeVector
    (fun x : T.linkRegion p σ => SphericalBarycentric.vector (T.sphericalAngularVertex p σ) x.val.val)
    ((SphericalBarycentric.continuous_vector _).comp (continuous_subtype_val.comp continuous_subtype_val))
    (fun x => T.sphericalAngularChart_vector_ne_zero hσ hpσ x.property)
  convert hc using 1
  funext x
  apply GeodesicSphere.ext
  exact CrossPolytope.sphereNormalize_val (T.sphericalAngularChart_vector_ne_zero hσ hpσ x.property)

theorem sphericalAngularChart_dist_on_face {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ)
    (x y : (T.linkComplex p).Space)
    (hx : x.val ∈ Barycentric.weightsOn τ) (hy : y.val ∈ Barycentric.weightsOn τ) :
    dist (T.sphericalAngularChart p σ x) (T.sphericalAngularChart p σ y) =
      dist (Barycentric.chartPoint (T.sphericalLinkVertex p τ) x.val)
        (Barycentric.chartPoint (T.sphericalLinkVertex p τ) y.val) := by
  obtain ⟨hγ, _, _, _⟩ := T.linkCoface_spec hτ
  obtain ⟨R, hR⟩ := T.exists_spherical_chart_transition hγ hσ
  have he (z : (T.linkComplex p).Space) (hz : z.val ∈ Barycentric.weightsOn τ) :
      T.sphericalAngularChart p σ z =
        GeodesicSphere.mapEquiv R (Barycentric.chartPoint (T.sphericalLinkVertex p τ) z.val) := by
    apply GeodesicSphere.ext
    exact T.sphericalAngularChart_transition hτ hσ hpσ hsub R hR z hz
  rw [he x hx, he y hy, (GeodesicSphere.mapEquiv R).dist_eq]

theorem chart_sphericalRadialSite_in_coface
    (p : P) {r : ℝ} (hr : T.SphericalRadialAdmissible p r)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hx : x ∈ T.linkRegion p σ) :
    (T.chart σ (T.sphericalRadialSite p hr x)).val =
      Real.cos r • (T.chart σ p).val + Real.sin r • (T.sphericalAngularChart p σ x).val := by
  let τ := (T.linkComplex p).support x
  have hτ := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, _, _⟩ := T.linkCoface_spec hτ
  obtain ⟨R, hR⟩ := T.exists_spherical_chart_transition hγ hσ
  have hqσ := T.sphericalRadialSite_mem_of_support p hr x hσ hpσ hx
  have hv := T.sphericalAngularChart_transition hτ hσ hpσ hx R hR x
    ((T.linkComplex p).weightsOn_support x)
  have he := congrArg GeodesicSphere.val (hR _ ⟨T.sphericalRadialSite_mem p hr x, hqσ⟩)
  have hp := congrArg GeodesicSphere.val (hR p ⟨hpγ, hpσ⟩)
  change R (T.chart (T.linkCoface p τ) (T.sphericalRadialSite p hr x)).val = _ at he
  rw [T.chart_sphericalRadialSite p hr x, SphericalLink.radialPoint_val, map_add, map_smul, map_smul] at he
  change R (T.chart (T.linkCoface p τ) p).val = (T.chart σ p).val at hp
  rw [hp, show R (T.sphericalLinkAngularPoint p x).val = (T.sphericalAngularChart p σ x).val from hv.symm] at he
  exact he.symm

end ArchivePLGeometry.FiniteChartedComplex
