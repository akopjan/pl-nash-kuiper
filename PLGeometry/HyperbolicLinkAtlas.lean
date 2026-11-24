module

public import PLGeometry.HyperbolicLinkComplex
public import PLGeometry.LinkRegions
public import PLGeometry.ChartedStars
public import BrehmApprox.HyperbolicRadialFolding

/-! # One angular chart on each old hyperbolic simplex -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.HyperbolicSpace
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

local instance hyperbolicLinkAtlasDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance hyperbolicLinkAtlasModelEq : DecidableEq (Model .hyperbolic (n + 1)) := Classical.decEq _
local instance hyperbolicLinkAtlasVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def hyperbolicAngularVertex (p : P) (σ : Finset P) (v : T.LinkVertex p) : GeodesicSphere n :=
  CrossPolytope.sphereNormalize (radialVector (T.chart σ p) (T.chart σ v.val))

def hyperbolicAngularChart (p : P) (σ : Finset P) (x : (T.linkComplex p).Space) :
    GeodesicSphere n := Barycentric.chartPoint (T.hyperbolicAngularVertex p σ) x.val

theorem hyperbolicAngularVertex_ne_zero {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) (v : T.LinkVertex p)
    (hvσ : v.val ∈ σ) : radialVector (T.chart σ p) (T.chart σ v.val) ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_radialVector, Real.sinh_pos_iff]
  apply dist_pos.mpr
  intro he
  exact v.property.1 (T.chart_injectiveOn σ hσ (T.vertices_mem σ hσ hvσ) hpσ he.symm)

theorem exists_hyperbolic_coface_linear_congruence
    {p : P} {τ : Finset (T.LinkVertex p)} (hτ : τ ∈ T.linkFaces p)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (hsub : T.linkSourceVertices τ ⊆ σ) :
    ∃ U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      ∀ v ∈ τ, U (T.hyperbolicLinkVector p τ v) =
        radialVector (T.chart σ p) (T.chart σ v.val) := by
  let γ := T.linkCoface p τ
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  have hv (v : τ) : v.val.val ∈ T.cell γ ∩ T.cell σ :=
    ⟨T.vertices_mem γ hγ (hτγ (T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩)),
      T.vertices_mem σ hσ (hsub (T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩))⟩
  have hgram (v w : τ) :
      inner ℝ (T.hyperbolicLinkVector p τ v.val) (T.hyperbolicLinkVector p τ w.val) =
      inner ℝ (radialVector (T.chart σ p) (T.chart σ v.val.val))
        (radialVector (T.chart σ p) (T.chart σ w.val.val)) := by
    change inner ℝ (radialVector (T.chart γ p) (T.chart γ v.val.val))
      (radialVector (T.chart γ p) (T.chart γ w.val.val)) = _
    rw [inner_radialVector, inner_radialVector,
      T.metric_coherence γ hγ σ hσ p ⟨hpγ, hpσ⟩ v.val.val (hv v),
      T.metric_coherence γ hγ σ hσ p ⟨hpγ, hpσ⟩ w.val.val (hv w),
      T.metric_coherence γ hγ σ hσ v.val.val (hv v) w.val.val (hv w)]
  obtain ⟨U, hU⟩ := exists_ambient_gram_isometry
    (fun v : τ => T.hyperbolicLinkVector p τ v.val)
    (fun v : τ => radialVector (T.chart σ p) (T.chart σ v.val.val))
    (T.hyperbolicLinkVector_independent hτ) hgram
  exact ⟨U, fun v hv => hU ⟨v, hv⟩⟩

theorem hyperbolicAngularVertex_transition
    {p : P} {τ : Finset (T.LinkVertex p)} (hτ : τ ∈ T.linkFaces p)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (hsub : T.linkSourceVertices τ ⊆ σ)
    (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hU : ∀ v ∈ τ, U (T.hyperbolicLinkVector p τ v) =
      radialVector (T.chart σ p) (T.chart σ v.val))
    {v : T.LinkVertex p} (hv : v ∈ τ) :
    U (T.hyperbolicLinkPoint p τ v).val = (T.hyperbolicAngularVertex p σ v).val := by
  rw [hyperbolicLinkPoint, hyperbolicAngularVertex,
    CrossPolytope.sphereNormalize_val ((T.hyperbolicLinkVector_independent hτ).ne_zero ⟨v, hv⟩),
    CrossPolytope.sphereNormalize_val (T.hyperbolicAngularVertex_ne_zero hσ hpσ v
      (hsub (T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩)))]
  have hn : U (NormedSpace.normalize (T.hyperbolicLinkVector p τ v)) =
      NormedSpace.normalize (U (T.hyperbolicLinkVector p τ v)) :=
    linearIsometry_map_normalize U.toLinearIsometry _
  rw [hn, hU v hv]

theorem hyperbolicAngularChart_transition
    {p : P} {τ : Finset (T.LinkVertex p)} (hτ : τ ∈ T.linkFaces p)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    (hsub : T.linkSourceVertices τ ⊆ σ)
    (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hU : ∀ v ∈ τ, U (T.hyperbolicLinkVector p τ v) =
      radialVector (T.chart σ p) (T.chart σ v.val))
    (x : (T.linkComplex p).Space) (hx : x.val ∈ Barycentric.weightsOn τ) :
    (T.hyperbolicAngularChart p σ x).val =
      U (Barycentric.chartPoint (T.hyperbolicLinkPoint p τ) x.val).val := by
  let z := SphericalBarycentric.vector (T.hyperbolicLinkPoint p τ) x.val
  have hz : z ≠ 0 := by
    rw [show z = SphericalBarycentric.vector (T.hyperbolicLinkPoint p τ) x.val from rfl,
      Barycentric.vector_restrict τ _ ⟨x.val, hx⟩]
    exact SphericalBarycentric.vector_ne_zero _ (T.hyperbolicLinkPoint_independent hτ) _
  have he : SphericalBarycentric.vector (T.hyperbolicAngularVertex p σ) x.val = U z := by
    simp only [z, SphericalBarycentric.vector, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ τ
    · rw [T.hyperbolicAngularVertex_transition hτ hσ hpσ hsub U hU hv]
    · rw [hx.2 v hv, zero_smul, zero_smul]
  have hz' : SphericalBarycentric.vector (T.hyperbolicAngularVertex p σ) x.val ≠ 0 := by
    rw [he]
    exact fun h => hz (U.injective (h.trans (map_zero _).symm))
  rw [hyperbolicAngularChart, Barycentric.chartPoint, Barycentric.chartPoint,
    CrossPolytope.sphereNormalize_val hz', CrossPolytope.sphereNormalize_val hz, he]
  exact (linearIsometry_map_normalize U.toLinearIsometry z).symm

theorem hyperbolicAngularVertex_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ) :
    LinearIndependent ℝ (fun v : τ => (T.hyperbolicAngularVertex p σ v.val).val) := by
  obtain ⟨U, hU⟩ := T.exists_hyperbolic_coface_linear_congruence hτ hσ hpσ hsub
  have hi := (T.hyperbolicLinkPoint_independent hτ).map'
    U.toLinearMap (LinearMap.ker_eq_bot.mpr U.injective)
  convert hi using 1
  funext v
  exact (T.hyperbolicAngularVertex_transition hτ hσ hpσ hsub U hU v.property).symm

theorem hyperbolicAngularChart_vector_ne_zero {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) :
    SphericalBarycentric.vector (T.hyperbolicAngularVertex p σ) x.val ≠ 0 := by
  let τ := (T.linkComplex p).support x
  rw [Barycentric.vector_restrict τ _ ⟨x.val, (T.linkComplex p).weightsOn_support x⟩]
  exact SphericalBarycentric.vector_ne_zero _
    (T.hyperbolicAngularVertex_independent ((T.linkComplex p).support_mem x) hσ hpσ hx) _

theorem continuousOn_hyperbolicAngularChart {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    ContinuousOn (T.hyperbolicAngularChart p σ) (T.linkRegion p σ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := GeodesicSphere.continuous_normalizeVector
    (fun x : T.linkRegion p σ =>
      SphericalBarycentric.vector (T.hyperbolicAngularVertex p σ) x.val.val)
    ((SphericalBarycentric.continuous_vector _).comp
      (continuous_subtype_val.comp continuous_subtype_val))
    (fun x => T.hyperbolicAngularChart_vector_ne_zero hσ hpσ x.property)
  convert hc using 1
  funext x
  apply GeodesicSphere.ext
  exact CrossPolytope.sphereNormalize_val (T.hyperbolicAngularChart_vector_ne_zero hσ hpσ x.property)

theorem hyperbolicAngularChart_dist_on_face {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ)
    (x y : (T.linkComplex p).Space)
    (hx : x.val ∈ Barycentric.weightsOn τ) (hy : y.val ∈ Barycentric.weightsOn τ) :
    dist (T.hyperbolicAngularChart p σ x) (T.hyperbolicAngularChart p σ y) =
      dist (Barycentric.chartPoint (T.hyperbolicLinkPoint p τ) x.val)
        (Barycentric.chartPoint (T.hyperbolicLinkPoint p τ) y.val) := by
  obtain ⟨U, hU⟩ := T.exists_hyperbolic_coface_linear_congruence hτ hσ hpσ hsub
  have he (z : (T.linkComplex p).Space) (hz : z.val ∈ Barycentric.weightsOn τ) :
      T.hyperbolicAngularChart p σ z = GeodesicSphere.mapEquiv U
        (Barycentric.chartPoint (T.hyperbolicLinkPoint p τ) z.val) := by
    apply GeodesicSphere.ext
    exact T.hyperbolicAngularChart_transition hτ hσ hpσ hsub U hU z hz
  rw [he x hx, he y hy, (GeodesicSphere.mapEquiv U).dist_eq]

end ArchivePLGeometry.FiniteChartedComplex
