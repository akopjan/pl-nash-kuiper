module

public import PLGeometry.LinkCombinatorics
public import PLGeometry.SphericalComplexRealization
public import BrehmApprox.SphericalFaceSpan

/-!
# The spherical metric data of a simplex link

Each abstract link face receives the tangent directions in one incident
old chart. The spherical cosine law makes the resulting Gram matrices
independent of that choice on every common face.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.FiniteChartedComplex

open BrehmApprox BrehmApprox.CrossPolytope BrehmApprox.RadialLink BrehmApprox.SphericalLink
open GeodesicSphere

universe u

local instance sphericalLinkComplexDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

def sphericalLinkTangent (p : P) (τ : Finset (T.LinkVertex p)) (v : T.LinkVertex p) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  tangentLinear (T.chart (T.linkCoface p τ) p) (T.chart (T.linkCoface p τ) v.val).val

def sphericalLinkVertex (p : P) (τ : Finset (T.LinkVertex p)) (v : T.LinkVertex p) :
    GeodesicSphere n := sphereNormalize (T.sphericalLinkTangent p τ v)

theorem spherical_link_tangent_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    LinearIndependent ℝ (fun v : τ => T.sphericalLinkTangent p τ v.val) := by
  let C := T.linkCoface p τ
  let W := T.linkSourceVertices τ
  let B := C.image (T.chart C)
  let F := W.image (T.chart C)
  obtain ⟨hC, hpC, hWC, hpW⟩ := T.linkCoface_spec hτ
  have hB : LinearIndependent ℝ (fun v : B => v.val.val) := by
    have h := (T.simplex C hC)
    change InOpenHemisphere B ∧ LinearIndependent ℝ (fun v : B => v.val.val) at h
    exact h.2
  have hFB : F ⊆ B := Finset.image_mono _ hWC
  have hpB : T.chart C p ∈ sphericalCell B := by
    have h := Set.mem_image_of_mem (T.chart C) hpC
    rw [T.image_cell C hC] at h
    exact h
  have hpF : T.chart C p ∉ sphericalCell F := by
    intro h
    have he : T.chart C '' T.cell W = sphericalCell F := T.image_face C hC W hWC
    rw [← he] at h
    obtain ⟨q, hq, heq⟩ := h
    have hqp : q = p := T.chart_injectiveOn C hC (T.cell_mono hC hWC hq) hpC heq
    apply hpW
    exact Eq.mp (congrArg (fun z : P => z ∈ T.cell (T.linkSourceVertices τ)) hqp) hq
  have hTF := tangent_subface_independent hB hFB hpB hpF
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

theorem spherical_link_vertices_hemisphere {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) : InOpenHemisphere (τ.image (T.sphericalLinkVertex p τ)) := by
  have h := normalized_family_hemisphere (T.spherical_link_tangent_independent hτ)
  have he : Finset.univ.image (fun v : τ => sphereNormalize (T.sphericalLinkTangent p τ v.val)) =
      τ.image (T.sphericalLinkVertex p τ) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, sphericalLinkVertex]
    constructor
    · rintro ⟨v, hz⟩
      exact ⟨v.val, v.property, hz⟩
    · rintro ⟨v, hv, hz⟩
      exact ⟨⟨v, hv⟩, hz⟩
  rwa [he] at h

theorem spherical_link_gram {p : P} {σ τ : Finset (T.LinkVertex p)}
    (hσ : σ ∈ T.linkFaces p) (hτ : τ ∈ T.linkFaces p)
    {v w : T.LinkVertex p} (hv : v ∈ σ ∩ τ) (hw : w ∈ σ ∩ τ) :
    inner ℝ (T.sphericalLinkVertex p σ v).val (T.sphericalLinkVertex p σ w).val =
      inner ℝ (T.sphericalLinkVertex p τ v).val (T.sphericalLinkVertex p τ w).val := by
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
  have hvC0 := (T.spherical_link_tangent_independent hσ).ne_zero ⟨v, (Finset.mem_inter.mp hv).1⟩
  have hwC0 := (T.spherical_link_tangent_independent hσ).ne_zero ⟨w, (Finset.mem_inter.mp hw).1⟩
  have hvD0 := (T.spherical_link_tangent_independent hτ).ne_zero ⟨v, (Finset.mem_inter.mp hv).2⟩
  have hwD0 := (T.spherical_link_tangent_independent hτ).ne_zero ⟨w, (Finset.mem_inter.mp hw).2⟩
  change inner ℝ (sphereNormalize (tangentLinear (T.chart C p) (T.chart C v.val).val)).val
      (sphereNormalize (tangentLinear (T.chart C p) (T.chart C w.val).val)).val =
    inner ℝ (sphereNormalize (tangentLinear (T.chart D p) (T.chart D v.val).val)).val
      (sphereNormalize (tangentLinear (T.chart D p) (T.chart D w.val).val)).val
  rw [normalized_tangent_gram _ _ _ hvC0 hwC0, normalized_tangent_gram _ _ _ hvD0 hwD0,
    hpv, hpw, hvw]

/-- The actual spherical geometry of the finite abstract link. -/
def sphericalLinkData (p : P) : Barycentric.SphericalData (T.linkComplex p) n where
  vertex := T.sphericalLinkVertex p
  independent := by
    intro τ hτ
    exact normalized_family_independent (T.spherical_link_tangent_independent hτ)
  hemisphere := by intro τ hτ; exact T.spherical_link_vertices_hemisphere hτ
  gram := by
    intro σ hσ τ hτ v hv w hw
    apply T.spherical_link_gram hσ hτ
    · simpa only [Finset.mem_inter] using hv
    · simpa only [Finset.mem_inter] using hw

/-- The actual finite spherical link, with its cellwise angular metrics. -/
def sphericalLink (p : P) :
    FiniteChartedComplex .spherical n (T.linkComplex p).Space :=
  (T.sphericalLinkData p).toChartedComplex

end ArchivePLGeometry.FiniteChartedComplex
