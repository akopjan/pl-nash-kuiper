module

public import PLGeometry.HyperbolicLinkComplex
public import PLGeometry.ChartedHullIncidence
public import BrehmApprox.HyperbolicLinkChart

/-! # Genuine cones over hyperbolic link faces -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox BrehmApprox.HyperbolicSpace

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

local instance hyperbolicLinkConesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance hyperbolicLinkConesModelEq : DecidableEq (Model .hyperbolic (n + 1)) := Classical.decEq _
local instance hyperbolicLinkConesLinkEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _
local instance hyperbolicLinkConesSphereEq : DecidableEq (GeodesicSphere n) := Classical.decEq _

def hyperbolicLinkCone (p : P) (τ : Finset (T.LinkVertex p)) :
    Finset (HyperbolicSpace (n + 1)) :=
  insert (T.chart (T.linkCoface p τ) p)
    ((T.linkSourceVertices τ).image (T.chart (T.linkCoface p τ)))

theorem hyperbolicLinkCone_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    LinearIndependent ℝ (fun x : T.hyperbolicLinkCone p τ => lift x.val) := by
  let σ := T.linkCoface p τ
  obtain ⟨hσ, hpσ, hsub, hpU⟩ := T.linkCoface_spec hτ
  have hV : LinearIndependent ℝ (fun v : σ.image (T.chart σ) => lift v.val) := T.simplex σ hσ
  have hpV : T.chart σ p ∈ hyperbolicCell (σ.image (T.chart σ)) := by
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  apply insert_independent_of_face_avoidance hV (Finset.image_subset_image hsub) hpV
  intro hp
  have he : T.chart σ '' T.cell (T.linkSourceVertices τ) =
      hyperbolicCell ((T.linkSourceVertices τ).image (T.chart σ)) :=
    T.image_face σ hσ _ hsub
  rw [← he] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  exact hpU (T.chart_injectiveOn σ hσ (T.cell_mono hσ hsub hx) hpσ hxp ▸ hx)

theorem hyperbolicLinkCone_subset_hull {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    hyperbolicCell (T.hyperbolicLinkCone p τ) ⊆ hull .hyperbolic (n + 1)
      ((T.linkCoface p τ).image (T.chart (T.linkCoface p τ))) := by
  obtain ⟨hσ, hpσ, hsub, _⟩ := T.linkCoface_spec hτ
  apply hull_transitive .hyperbolic (n + 1)
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · have hm := Set.mem_image_of_mem (T.chart (T.linkCoface p τ)) hpσ
    rw [T.image_cell _ hσ] at hm
    exact hm
  · exact mem_hyperbolicCell_of_mem ((Finset.image_subset_image hsub) hz)

theorem hyperbolicLinkVector_ne_zero {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {v : T.LinkVertex p} (hv : v ∈ τ) :
    T.hyperbolicLinkVector p τ v ≠ 0 :=
  (T.hyperbolicLinkVector_independent hτ).ne_zero ⟨v, hv⟩

theorem hyperbolicLinkPoint_image_eq {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    τ.image (T.hyperbolicLinkPoint p τ) =
      HyperbolicLink.linkVertices (T.hyperbolicLinkCone p τ) (T.chart (T.linkCoface p τ) p) := by
  rw [HyperbolicLink.linkVertices_eq_radial]
  ext u
  simp only [Finset.mem_image, Finset.mem_erase, hyperbolicLinkCone, Finset.mem_insert]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨T.chart (T.linkCoface p τ) v.val, ⟨?_, Or.inr ⟨v.val,
      T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩, rfl⟩⟩, rfl⟩
    intro he
    obtain ⟨hσ, hpσ, hsub, _⟩ := T.linkCoface_spec hτ
    exact v.property.1 (T.chart_injectiveOn _ hσ (T.vertices_mem _ hσ
      (hsub (T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩))) hpσ he)
  · rintro ⟨z, ⟨hzp, hz⟩, hzu⟩
    rcases hz with he | ⟨v, hv, hvz⟩
    · exact (hzp he).elim
    · obtain ⟨w, hw, hwv⟩ := T.mem_linkSourceVertices.mp hv
      refine ⟨w, hw, ?_⟩
      change CrossPolytope.sphereNormalize (radialVector (T.chart (T.linkCoface p τ) p)
        (T.chart (T.linkCoface p τ) w.val)) = u
      rw [hwv, hvz, hzu]

theorem exists_hyperbolic_link_face_radius {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ u : GeodesicSphere n,
      u ∈ sphericalCell (τ.image (T.hyperbolicLinkPoint p τ)) →
      HyperbolicLink.radialPoint (T.chart (T.linkCoface p τ) p) u r ∈
        hyperbolicCell (T.hyperbolicLinkCone p τ) := by
  obtain ⟨ρ, hρ, hmem⟩ := HyperbolicLink.exists_radial_link_radius
    (T.hyperbolicLinkCone_independent hτ) (Finset.mem_insert_self _ _)
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ u hu
  apply (hmem r hr hrρ u).mpr
  rwa [← T.hyperbolicLinkPoint_image_eq hτ]

end ArchivePLGeometry.FiniteChartedComplex
