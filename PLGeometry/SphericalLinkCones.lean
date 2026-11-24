module

public import PLGeometry.SphericalLinkComplex
public import PLGeometry.ChartedProjectiveTransport

/-! # Small radial cones over arbitrary spherical link faces -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P)

local instance sphericalLinkConesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sphericalLinkConesModelEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance sphericalLinkConesLabelEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def sphericalLinkCone (p : P) (τ : Finset (T.LinkVertex p)) : Finset (GeodesicSphere n) :=
  insert (T.chart (T.linkCoface p τ) p)
    ((T.linkSourceVertices τ).image (T.chart (T.linkCoface p τ)))

theorem sphericalLinkCone_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    LinearIndependent ℝ (fun x : T.sphericalLinkCone p τ => x.val.val) := by
  let σ := T.linkCoface p τ
  obtain ⟨hσ, hpσ, hsub, hpU⟩ := T.linkCoface_spec hτ
  have hV : LinearIndependent ℝ (fun x : σ.image (T.chart σ) => x.val.val) := by
    simpa only [Finset.coe_sort_coe] using (T.simplex σ hσ).2
  have hpV : T.chart σ p ∈ sphericalCell (σ.image (T.chart σ)) := by
    change T.chart σ p ∈ hull .spherical n (σ.image (T.chart σ))
    rw [← T.image_cell σ hσ]
    exact Set.mem_image_of_mem _ hpσ
  apply SphericalLink.insert_independent_of_face_avoidance hV
    (Finset.image_subset_image hsub) hpV
  intro hp
  change T.chart σ p ∈ hull .spherical n ((T.linkSourceVertices τ).image (T.chart σ)) at hp
  rw [← T.image_face σ hσ (T.linkSourceVertices τ) hsub] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  exact hpU (T.chart_injectiveOn σ hσ (T.cell_mono hσ hsub hx) hpσ hxp ▸ hx)

theorem sphericalLinkCone_subset_hull {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    sphericalCell (T.sphericalLinkCone p τ) ⊆
      hull .spherical n ((T.linkCoface p τ).image (T.chart (T.linkCoface p τ))) := by
  obtain ⟨hσ, hpσ, hsub, _⟩ := T.linkCoface_spec hτ
  change hull .spherical n (T.sphericalLinkCone p τ) ⊆ _
  apply hull_transitive .spherical n
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · rw [← T.image_cell _ hσ]
    exact Set.mem_image_of_mem _ hpσ
  · exact mem_sphericalCell_of_mem ((Finset.image_subset_image hsub) hz)

theorem sphericalLinkTangent_ne_zero {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {v : T.LinkVertex p} (hv : v ∈ τ) :
    T.sphericalLinkTangent p τ v ≠ 0 :=
  (T.spherical_link_tangent_independent hτ).ne_zero ⟨v, hv⟩

theorem sphericalLinkVertex_image_eq {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    τ.image (T.sphericalLinkVertex p τ) =
      SphericalLink.linkVertices (T.sphericalLinkCone p τ) (T.chart (T.linkCoface p τ) p) := by
  ext u
  simp only [Finset.mem_image, SphericalLink.linkVertices, SphericalLink.tangentVectors,
    CrossPolytope.radialVertices, sphericalLinkCone, Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨T.sphericalLinkTangent p τ v, ⟨T.chart (T.linkCoface p τ) v.val,
      ⟨?_, Or.inr ⟨v.val, T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩, rfl⟩⟩, rfl⟩, rfl⟩
    intro he
    apply T.sphericalLinkTangent_ne_zero hτ hv
    change SphericalLink.tangentLinear (T.chart (T.linkCoface p τ) p)
      (T.chart (T.linkCoface p τ) v.val).val = 0
    rw [he, SphericalLink.tangentLinear_self]
  · rintro ⟨z, ⟨y, ⟨hya, hy⟩, hyz⟩, hzu⟩
    rcases hy with he | ⟨v, hv, hvy⟩
    · exact (hya he).elim
    · obtain ⟨w, hw, hwv⟩ := T.mem_linkSourceVertices.mp hv
      refine ⟨w, hw, ?_⟩
      change CrossPolytope.sphereNormalize
        (SphericalLink.tangentLinear (T.chart (T.linkCoface p τ) p)
          (T.chart (T.linkCoface p τ) w.val).val) = u
      rw [hwv, hvy, hyz, hzu]

theorem sphericalLinkCell_tangent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {u : GeodesicSphere n}
    (hu : u ∈ sphericalCell (τ.image (T.sphericalLinkVertex p τ))) :
    inner ℝ (T.chart (T.linkCoface p τ) p).val u.val = 0 := by
  rw [T.sphericalLinkVertex_image_eq hτ] at hu
  exact SphericalLink.inner_linkCell (T.sphericalLinkCone_independent hτ) (Finset.mem_insert_self _ _) hu

theorem exists_spherical_link_face_radius {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < Real.pi ∧
      ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ u : GeodesicSphere n,
        u ∈ sphericalCell (τ.image (T.sphericalLinkVertex p τ)) →
        ∀ hu : inner ℝ (T.chart (T.linkCoface p τ) p).val u.val = 0,
          SphericalLink.radialPoint (T.chart (T.linkCoface p τ) p) u hu r ∈
            sphericalCell (T.sphericalLinkCone p τ) := by
  obtain ⟨ρ, hρ, hρπ, hmem⟩ := SphericalLink.exists_spherical_link_radius
    (T.sphericalLinkCone_independent hτ) (Finset.mem_insert_self _ _)
  refine ⟨ρ, hρ, hρπ, ?_⟩
  intro r hr hrρ u hu huorth
  apply (hmem r hr hrρ u huorth).mpr
  rwa [← T.sphericalLinkVertex_image_eq hτ]

theorem sphericalLinkVertex_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    LinearIndependent ℝ (fun v : τ => (T.sphericalLinkVertex p τ v.val).val) :=
  (T.sphericalLinkData p).independent τ hτ

end ArchivePLGeometry.FiniteChartedComplex
