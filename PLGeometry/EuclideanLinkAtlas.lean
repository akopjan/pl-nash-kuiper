module

public import PLGeometry.EuclideanRadialIncidence
public import PLGeometry.LinkRegions

/-! # One angular chart on each old Euclidean simplex -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean (n + 1) P)

local instance euclideanLinkAtlasDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance euclideanLinkAtlasModelEq : DecidableEq (Model .euclidean (n + 1)) := Classical.decEq _
local instance euclideanLinkAtlasVertexEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def euclideanAngularVertex (p : P) (σ : Finset P) (v : T.LinkVertex p) : GeodesicSphere n :=
  CrossPolytope.sphereNormalize (T.chart σ v.val - T.chart σ p)

def euclideanAngularChart (p : P) (σ : Finset P) (x : (T.linkComplex p).Space) :
    GeodesicSphere n := Barycentric.chartPoint (T.euclideanAngularVertex p σ) x.val

theorem euclideanAngularVertex_ne_zero {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) (v : T.LinkVertex p)
    (hvσ : v.val ∈ σ) : T.chart σ v.val - T.chart σ p ≠ 0 := by
  intro h
  exact v.property.1 (T.chart_injectiveOn σ hσ (T.vertices_mem σ hσ hvσ) hpσ
    (sub_eq_zero.mp h))

theorem euclideanAngularVertex_transition {p : P} {σ γ : Finset P}
    (hσ : σ ∈ T.simplices) (hγ : γ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hpγ : p ∈ T.cell γ)
    (r : Model .euclidean (n + 1) ≃ᵃⁱ[ℝ] Model .euclidean (n + 1))
    (hr : ∀ z ∈ T.cell γ ∩ T.cell σ, r (T.chart γ z) = T.chart σ z)
    (v : T.LinkVertex p) (hvγ : v.val ∈ γ) (hvσ : v.val ∈ σ) :
    r.linearIsometryEquiv (T.euclideanAngularVertex p γ v).val =
      (T.euclideanAngularVertex p σ v).val := by
  rw [euclideanAngularVertex, euclideanAngularVertex,
    CrossPolytope.sphereNormalize_val (T.euclideanAngularVertex_ne_zero hγ hpγ v hvγ),
    CrossPolytope.sphereNormalize_val (T.euclideanAngularVertex_ne_zero hσ hpσ v hvσ)]
  have hn : r.linearIsometryEquiv (NormedSpace.normalize (T.chart γ v.val - T.chart γ p)) =
      NormedSpace.normalize (r.linearIsometryEquiv (T.chart γ v.val - T.chart γ p)) :=
    linearIsometry_map_normalize r.linearIsometryEquiv.toLinearIsometry _
  rw [hn]
  have he : r.linearIsometryEquiv (T.chart γ v.val - T.chart γ p) =
      T.chart σ v.val - T.chart σ p := by
    rw [show T.chart γ v.val - T.chart γ p = T.chart γ v.val -ᵥ T.chart γ p from rfl,
      r.map_vsub, hr v.val ⟨T.vertices_mem γ hγ hvγ, T.vertices_mem σ hσ hvσ⟩,
      hr p ⟨hpγ, hpσ⟩]
    rfl
  rw [he]

theorem euclideanAngularChart_transition {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ)
    (r : Model .euclidean (n + 1) ≃ᵃⁱ[ℝ] Model .euclidean (n + 1))
    (hr : ∀ z ∈ T.cell (T.linkCoface p τ) ∩ T.cell σ,
      r (T.chart (T.linkCoface p τ) z) = T.chart σ z)
    (x : (T.linkComplex p).Space) (hx : x.val ∈ Barycentric.weightsOn τ) :
    (T.euclideanAngularChart p σ x).val =
      r.linearIsometryEquiv (Barycentric.chartPoint (T.euclideanLinkPoint p τ) x.val).val := by
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  let z := SphericalBarycentric.vector (T.euclideanLinkPoint p τ) x.val
  have hz : z ≠ 0 := by
    rw [show z = SphericalBarycentric.vector (T.euclideanLinkPoint p τ) x.val from rfl,
      Barycentric.vector_restrict τ _ ⟨x.val, hx⟩]
    exact SphericalBarycentric.vector_ne_zero _ (T.euclideanLinkPoint_independent hτ) _
  have he : SphericalBarycentric.vector (T.euclideanAngularVertex p σ) x.val =
      r.linearIsometryEquiv z := by
    rw [show z = SphericalBarycentric.vector (T.euclideanLinkPoint p τ) x.val from rfl]
    simp only [SphericalBarycentric.vector, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ τ
    · have hvs := T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩
      have hh := T.euclideanAngularVertex_transition hσ hγ hpσ hpγ r hr v
        (hτγ hvs) (hsub hvs)
      change x.val v • (T.euclideanAngularVertex p σ v).val =
        x.val v • r.linearIsometryEquiv (T.euclideanAngularVertex p (T.linkCoface p τ) v).val
      rw [hh]
    · rw [hx.2 v hv, zero_smul, zero_smul]
  have hz' : SphericalBarycentric.vector (T.euclideanAngularVertex p σ) x.val ≠ 0 := by
    rw [he]
    exact fun h => hz (r.linearIsometryEquiv.injective (h.trans (map_zero _).symm))
  rw [euclideanAngularChart, Barycentric.chartPoint, Barycentric.chartPoint,
    CrossPolytope.sphereNormalize_val hz', CrossPolytope.sphereNormalize_val hz, he]
  exact (linearIsometry_map_normalize r.linearIsometryEquiv.toLinearIsometry z).symm

theorem chart_euclideanRadialSite_in_coface
    (p : P) {r : ℝ} (hr : T.EuclideanRadialAdmissible p r)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hx : x ∈ T.linkRegion p σ) :
    T.chart σ (T.euclideanRadialSite p hr x) =
      T.chart σ p + r • (T.euclideanAngularChart p σ x).val := by
  let τ := (T.linkComplex p).support x
  have hτ := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, _, _⟩ := T.linkCoface_spec hτ
  obtain ⟨e, he⟩ := T.exists_euclidean_chart_transition hγ hσ
  have hqσ := T.euclideanRadialSite_mem_of_support p hr x hσ hpσ hx
  have hv := T.euclideanAngularChart_transition hτ hσ hpσ hx e he x
    ((T.linkComplex p).weightsOn_support x)
  rw [← he _ ⟨T.euclideanRadialSite_mem p hr x, hqσ⟩,
    T.chart_euclideanRadialSite p hr x]
  rw [show T.chart (T.linkCoface p τ) p + r • (T.euclideanLinkAngularPoint p x).val =
    r • (T.euclideanLinkAngularPoint p x).val + T.chart (T.linkCoface p τ) p from add_comm _ _,
    show r • (T.euclideanLinkAngularPoint p x).val +
    T.chart (T.linkCoface p τ) p = r • (T.euclideanLinkAngularPoint p x).val +ᵥ
    T.chart (T.linkCoface p τ) p from rfl, e.map_vadd, map_smul, he p ⟨hpγ, hpσ⟩]
  change r • e.linearIsometryEquiv (T.euclideanLinkAngularPoint p x).val + T.chart σ p = _
  rw [show e.linearIsometryEquiv (T.euclideanLinkAngularPoint p x).val =
    (T.euclideanAngularChart p σ x).val from hv.symm]
  exact add_comm _ _

theorem euclideanAngularVertex_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ) :
    LinearIndependent ℝ (fun v : τ => (T.euclideanAngularVertex p σ v.val).val) := by
  obtain ⟨hγ, hpγ, hτγ, _⟩ := T.linkCoface_spec hτ
  obtain ⟨r, hr⟩ := T.exists_euclidean_chart_transition hγ hσ
  have hi := (T.euclideanLinkPoint_independent hτ).map'
    r.linearIsometryEquiv.toLinearMap (LinearMap.ker_eq_bot.mpr r.linearIsometryEquiv.injective)
  have he : (r.linearIsometryEquiv.toLinearMap ∘
      (fun v : τ => (T.euclideanLinkPoint p τ v.val).val)) =
      (fun v : τ => (T.euclideanAngularVertex p σ v.val).val) := by
    funext v
    exact T.euclideanAngularVertex_transition hσ hγ hpσ hpγ r hr v.val
      (hτγ (T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩))
      (hsub (T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩))
  rwa [he] at hi

theorem euclideanAngularChart_vector_ne_zero {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ)
    {x : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) :
    SphericalBarycentric.vector (T.euclideanAngularVertex p σ) x.val ≠ 0 := by
  let τ := (T.linkComplex p).support x
  rw [Barycentric.vector_restrict τ _ ⟨x.val, (T.linkComplex p).weightsOn_support x⟩]
  exact SphericalBarycentric.vector_ne_zero _
    (T.euclideanAngularVertex_independent ((T.linkComplex p).support_mem x) hσ hpσ hx) _

theorem continuousOn_euclideanAngularChart {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) :
    ContinuousOn (T.euclideanAngularChart p σ) (T.linkRegion p σ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := GeodesicSphere.continuous_normalizeVector
    (fun x : T.linkRegion p σ =>
      SphericalBarycentric.vector (T.euclideanAngularVertex p σ) x.val.val)
    ((SphericalBarycentric.continuous_vector _).comp
      (continuous_subtype_val.comp continuous_subtype_val))
    (fun x => T.euclideanAngularChart_vector_ne_zero hσ hpσ x.property)
  convert hc using 1
  funext x
  apply GeodesicSphere.ext
  exact CrossPolytope.sphereNormalize_val
    (T.euclideanAngularChart_vector_ne_zero hσ hpσ x.property)

theorem euclideanAngularChart_dist_on_face {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hsub : T.linkSourceVertices τ ⊆ σ)
    (x y : (T.linkComplex p).Space)
    (hx : x.val ∈ Barycentric.weightsOn τ) (hy : y.val ∈ Barycentric.weightsOn τ) :
    dist (T.euclideanAngularChart p σ x) (T.euclideanAngularChart p σ y) =
      dist (Barycentric.chartPoint (T.euclideanLinkPoint p τ) x.val)
        (Barycentric.chartPoint (T.euclideanLinkPoint p τ) y.val) := by
  obtain ⟨hγ, hpγ, _, _⟩ := T.linkCoface_spec hτ
  obtain ⟨r, hr⟩ := T.exists_euclidean_chart_transition hγ hσ
  have he (z : (T.linkComplex p).Space) (hz : z.val ∈ Barycentric.weightsOn τ) :
      T.euclideanAngularChart p σ z =
        GeodesicSphere.mapEquiv r.linearIsometryEquiv
          (Barycentric.chartPoint (T.euclideanLinkPoint p τ) z.val) := by
    apply GeodesicSphere.ext
    exact T.euclideanAngularChart_transition hτ hσ hpσ hsub r hr z hz
  rw [he x hx, he y hy, (GeodesicSphere.mapEquiv r.linearIsometryEquiv).dist_eq]

end ArchivePLGeometry.FiniteChartedComplex
