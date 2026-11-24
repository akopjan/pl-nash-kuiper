module

public import PLGeometry.LinkCombinatorics
public import PLGeometry.SphericalComplexRealization
public import BrehmApprox.HyperbolicFaceSpan

/-! # Spherical links of finite hyperbolic charted complexes -/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.FiniteChartedComplex

open BrehmApprox BrehmApprox.CrossPolytope BrehmApprox.RadialLink BrehmApprox.HyperbolicSpace

universe u

local instance hyperbolicLinkComplexDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

/-- The spatial tangent vector in the canonical boosted frame of an incident chart. -/
def hyperbolicLinkVector (p : P) (τ : Finset (T.LinkVertex p)) (v : T.LinkVertex p) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  radialVector (T.chart (T.linkCoface p τ) p) (T.chart (T.linkCoface p τ) v.val)

def hyperbolicLinkPoint (p : P) (τ : Finset (T.LinkVertex p)) (v : T.LinkVertex p) :
    GeodesicSphere n := sphereNormalize (T.hyperbolicLinkVector p τ v)

theorem hyperbolicLinkVector_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    LinearIndependent ℝ (fun v : τ => T.hyperbolicLinkVector p τ v.val) := by
  let C := T.linkCoface p τ
  let W := T.linkSourceVertices τ
  let B := C.image (T.chart C)
  let F := W.image (T.chart C)
  obtain ⟨hC, hpC, hWC, hpW⟩ := T.linkCoface_spec hτ
  have hB : LinearIndependent ℝ (fun v : B => lift v.val) := T.simplex C hC
  have hFB : F ⊆ B := Finset.image_mono _ hWC
  have hpB : T.chart C p ∈ hyperbolicCell B := by
    have h := Set.mem_image_of_mem (T.chart C) hpC
    rw [T.image_cell C hC] at h
    exact h
  have hpF : T.chart C p ∉ hyperbolicCell F := by
    intro h
    have he : T.chart C '' T.cell W = hyperbolicCell F := T.image_face C hC W hWC
    rw [← he] at h
    obtain ⟨q, hq, heq⟩ := h
    have hqp : q = p := T.chart_injectiveOn C hC (T.cell_mono hC hWC hq) hpC heq
    apply hpW
    exact Eq.mp (congrArg (fun z : P => z ∈ T.cell (T.linkSourceVertices τ)) hqp) hq
  have hTF := radial_subface_independent hB hFB hpB hpF
  have hvC (v : τ) : v.val.val ∈ C :=
    hWC (T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩)
  let e : τ ↪ F :=
    { toFun := fun v => ⟨T.chart C v.val.val,
        Finset.mem_image.mpr ⟨v.val.val, T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩, rfl⟩⟩
      inj' := by
        intro v w he
        apply Subtype.ext
        apply Subtype.ext
        exact T.chart_injectiveOn C hC (T.vertices_mem C hC (hvC v))
          (T.vertices_mem C hC (hvC w)) (congrArg (fun z : F => z.val) he) }
  exact hTF.comp e e.injective

theorem hyperbolicLinkPoint_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    LinearIndependent ℝ (fun v : τ => (T.hyperbolicLinkPoint p τ v.val).val) :=
  normalized_family_independent (T.hyperbolicLinkVector_independent hτ)

theorem hyperbolicLinkPoint_hemisphere {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) : InOpenHemisphere (τ.image (T.hyperbolicLinkPoint p τ)) := by
  have h := normalized_family_hemisphere (T.hyperbolicLinkVector_independent hτ)
  have he : Finset.univ.image (fun v : τ => sphereNormalize (T.hyperbolicLinkVector p τ v.val)) =
      τ.image (T.hyperbolicLinkPoint p τ) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hyperbolicLinkPoint]
    constructor
    · rintro ⟨v, hz⟩
      exact ⟨v.val, v.property, hz⟩
    · rintro ⟨v, hv, hz⟩
      exact ⟨⟨v, hv⟩, hz⟩
  rwa [he] at h

theorem hyperbolicLinkPoint_gram {p : P} {σ τ : Finset (T.LinkVertex p)}
    (hσ : σ ∈ T.linkFaces p) (hτ : τ ∈ T.linkFaces p)
    {v w : T.LinkVertex p} (hv : v ∈ σ ∩ τ) (hw : w ∈ σ ∩ τ) :
    inner ℝ (T.hyperbolicLinkPoint p σ v).val (T.hyperbolicLinkPoint p σ w).val =
      inner ℝ (T.hyperbolicLinkPoint p τ v).val (T.hyperbolicLinkPoint p τ w).val := by
  let C := T.linkCoface p σ
  let D := T.linkCoface p τ
  obtain ⟨hC, hpC, hσC, _⟩ := T.linkCoface_spec hσ
  obtain ⟨hD, hpD, hτD, _⟩ := T.linkCoface_spec hτ
  have hvC : v.val ∈ T.cell C := T.vertices_mem C hC
    (hσC (T.mem_linkSourceVertices.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩))
  have hvD : v.val ∈ T.cell D := T.vertices_mem D hD
    (hτD (T.mem_linkSourceVertices.mpr ⟨v, (Finset.mem_inter.mp hv).2, rfl⟩))
  have hwC : w.val ∈ T.cell C := T.vertices_mem C hC
    (hσC (T.mem_linkSourceVertices.mpr ⟨w, (Finset.mem_inter.mp hw).1, rfl⟩))
  have hwD : w.val ∈ T.cell D := T.vertices_mem D hD
    (hτD (T.mem_linkSourceVertices.mpr ⟨w, (Finset.mem_inter.mp hw).2, rfl⟩))
  have hpv := T.metric_coherence C hC D hD p ⟨hpC, hpD⟩ v.val ⟨hvC, hvD⟩
  have hpw := T.metric_coherence C hC D hD p ⟨hpC, hpD⟩ w.val ⟨hwC, hwD⟩
  have hvw := T.metric_coherence C hC D hD v.val ⟨hvC, hvD⟩ w.val ⟨hwC, hwD⟩
  have hvC0 := (T.hyperbolicLinkVector_independent hσ).ne_zero ⟨v, (Finset.mem_inter.mp hv).1⟩
  have hwC0 := (T.hyperbolicLinkVector_independent hσ).ne_zero ⟨w, (Finset.mem_inter.mp hw).1⟩
  have hvD0 := (T.hyperbolicLinkVector_independent hτ).ne_zero ⟨v, (Finset.mem_inter.mp hv).2⟩
  have hwD0 := (T.hyperbolicLinkVector_independent hτ).ne_zero ⟨w, (Finset.mem_inter.mp hw).2⟩
  have hpos (γ : Finset P) (hγ : γ ∈ T.simplices) (hpγ : p ∈ T.cell γ)
      (z : T.LinkVertex p) (hzγ : z.val ∈ T.cell γ) :
      0 < dist (T.chart γ p) (T.chart γ z.val) := by
    apply dist_pos.mpr
    intro he
    exact z.property.1 (T.chart_injectiveOn γ hγ hzγ hpγ he.symm)
  unfold hyperbolicLinkPoint
  rw [sphereNormalize_val hvC0, sphereNormalize_val hwC0,
    sphereNormalize_val hvD0, sphereNormalize_val hwD0]
  simp only [hyperbolicLinkVector, NormedSpace.normalize, norm_radialVector]
  change inner ℝ (radialDirection (T.chart C p) (T.chart C v.val))
      (radialDirection (T.chart C p) (T.chart C w.val)) =
    inner ℝ (radialDirection (T.chart D p) (T.chart D v.val))
      (radialDirection (T.chart D p) (T.chart D w.val))
  rw [radial_gram_formula _ _ _ (hpos C hC hpC v hvC) (hpos C hC hpC w hwC),
    radial_gram_formula _ _ _ (hpos D hD hpD v hvD) (hpos D hD hpD w hwD), hpv, hpw, hvw]

/-- The actual spherical geometry of the finite hyperbolic link. -/
def hyperbolicLinkData (p : P) : Barycentric.SphericalData (T.linkComplex p) n where
  vertex := T.hyperbolicLinkPoint p
  independent := fun _ hτ => T.hyperbolicLinkPoint_independent hτ
  hemisphere := fun _ hτ => T.hyperbolicLinkPoint_hemisphere hτ
  gram := by
    intro σ hσ τ hτ v hv w hw
    apply T.hyperbolicLinkPoint_gram hσ hτ
    · simpa only [Finset.mem_inter] using hv
    · simpa only [Finset.mem_inter] using hw

/-- The finite link with its genuine cellwise angular metrics. -/
def hyperbolicLink (p : P) :
    FiniteChartedComplex .spherical n (T.linkComplex p).Space :=
  (T.hyperbolicLinkData p).toChartedComplex

end ArchivePLGeometry.FiniteChartedComplex
