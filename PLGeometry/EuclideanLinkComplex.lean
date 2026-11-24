module

public import PLGeometry.LinkCombinatorics
public import PLGeometry.SphericalComplexRealization
public import BrehmApprox.SimplexStellar
public import BrehmApprox.SimplexRadialLink
public import BrehmApprox.EuclideanFoldingGeometry

/-!
# The spherical link of a finite Euclidean charted complex

The link is constructed at an arbitrary point. Stellar faces give genuine
independent direction simplices; the Euclidean cosine law gives agreement
of their Gram matrices. The standard barycentric realization then supplies
the actual finite spherical charted complex.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean (n + 1) P)

local instance euclideanLinkDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance euclideanLinkModelDecidableEq :
    DecidableEq (Model .euclidean (n + 1)) := Classical.decEq _
local instance euclideanLinkSphereDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance euclideanLinkLabelDecidableEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def euclideanLinkVector (p : P) (τ : Finset (T.LinkVertex p)) (v : T.LinkVertex p) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  T.chart (T.linkCoface p τ) v.val - T.chart (T.linkCoface p τ) p

def euclideanLinkPoint (p : P) (τ : Finset (T.LinkVertex p)) (v : T.LinkVertex p) :
    GeodesicSphere n := CrossPolytope.sphereNormalize (T.euclideanLinkVector p τ v)

def euclideanLinkCone (p : P) (τ : Finset (T.LinkVertex p)) :
    Finset (EuclideanSpace ℝ (Fin (n + 1))) :=
  insert (T.chart (T.linkCoface p τ) p)
    ((T.linkSourceVertices τ).image (T.chart (T.linkCoface p τ)))

theorem euclideanLinkCone_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    AffineIndependent ℝ (fun x : T.euclideanLinkCone p τ => x.val) := by
  let σ := T.linkCoface p τ
  obtain ⟨hσ, hpσ, hsub, hpU⟩ := T.linkCoface_spec hτ
  have hV : AffineIndependent ℝ
      ((↑) : σ.image (T.chart σ) → EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using T.simplex σ hσ
  have hpV : T.chart σ p ∈ convexHull ℝ (σ.image (T.chart σ) : Set _) := by
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  apply affineIndependent_insert_of_hull_face_avoidance _ hV hpV
    (Finset.image_subset_image hsub)
  intro hp
  have he := T.image_face σ hσ (T.linkSourceVertices τ) hsub
  change T.chart σ '' T.cell (T.linkSourceVertices τ) =
    convexHull ℝ ((T.linkSourceVertices τ).image (T.chart σ) : Set _) at he
  rw [← he] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have hpx := T.chart_injectiveOn σ hσ (T.cell_mono hσ hsub hx) hpσ hxp
  exact hpU (hpx ▸ hx)

theorem euclideanLinkCone_subset_hull {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    convexHull ℝ (T.euclideanLinkCone p τ : Set _) ⊆
      hull .euclidean (n + 1)
        ((T.linkCoface p τ).image (T.chart (T.linkCoface p τ))) := by
  obtain ⟨hσ, hpσ, hsub, _⟩ := T.linkCoface_spec hτ
  apply convexHull_min ?_ (convex_convexHull ℝ _)
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · have hm := Set.mem_image_of_mem (T.chart (T.linkCoface p τ)) hpσ
    rw [T.image_cell _ hσ] at hm
    exact hm
  · exact subset_convexHull ℝ _ ((Finset.image_subset_image hsub) hz)

theorem euclideanLinkVector_ne_zero {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) {v : T.LinkVertex p} (hv : v ∈ τ) :
    T.euclideanLinkVector p τ v ≠ 0 := by
  obtain ⟨hσ, hpσ, hsub, _⟩ := T.linkCoface_spec hτ
  have hvσ : v.val ∈ T.cell (T.linkCoface p τ) :=
    T.vertices_mem _ hσ (hsub (T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩))
  intro he
  apply v.property.1
  exact T.chart_injectiveOn _ hσ hvσ hpσ (sub_eq_zero.mp he)

theorem euclideanLinkPoint_image_eq {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    τ.image (T.euclideanLinkPoint p τ) =
      RadialLink.linkVertices (T.euclideanLinkCone p τ) (T.chart (T.linkCoface p τ) p) := by
  classical
  ext u
  simp only [Finset.mem_image, RadialLink.linkVertices, RadialLink.edgeVectors,
    CrossPolytope.radialVertices, euclideanLinkCone, Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨T.euclideanLinkVector p τ v, ⟨T.chart (T.linkCoface p τ) v.val,
      ⟨?_, Or.inr ⟨v.val, T.mem_linkSourceVertices.mpr ⟨v, hv, rfl⟩, rfl⟩⟩, rfl⟩, rfl⟩
    intro he
    exact T.euclideanLinkVector_ne_zero hτ hv (sub_eq_zero.mpr he)
  · rintro ⟨z, ⟨y, ⟨hya, hy⟩, hyz⟩, hzu⟩
    rcases hy with he | ⟨v, hv, hvy⟩
    · exact (hya he).elim
    · obtain ⟨w, hw, hwv⟩ := T.mem_linkSourceVertices.mp hv
      refine ⟨w, hw, ?_⟩
      change CrossPolytope.sphereNormalize (T.chart (T.linkCoface p τ) w.val -
        T.chart (T.linkCoface p τ) p) = u
      rw [hwv, hvy, hyz, hzu]

/-- A positive radius works uniformly over every direction of a link face. -/
theorem exists_euclidean_link_face_radius {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ u : GeodesicSphere n,
      u ∈ sphericalCell (τ.image (T.euclideanLinkPoint p τ)) →
      T.chart (T.linkCoface p τ) p + r • u.val ∈
        convexHull ℝ (T.euclideanLinkCone p τ : Set _) := by
  obtain ⟨ρ, hρ, hmem⟩ := RadialLink.exists_radial_link_radius
    (T.euclideanLinkCone_independent hτ) (Finset.mem_insert_self _ _)
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ u hu
  apply (hmem r hr hrρ u).mpr
  rwa [← T.euclideanLinkPoint_image_eq hτ]

theorem euclideanLinkVector_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    LinearIndependent ℝ (fun v : τ => T.euclideanLinkVector p τ v.val) := by
  let σ := T.linkCoface p τ
  obtain ⟨hσ, hpσ, hsub, hpU⟩ := T.linkCoface_spec hτ
  let U := T.linkSourceVertices τ
  let W := U.image (T.chart σ)
  let V := σ.image (T.chart σ)
  let a := T.chart σ p
  have hV : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using T.simplex σ hσ
  have hWV : W ⊆ V := Finset.image_subset_image hsub
  have haV : a ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    have hm := Set.mem_image_of_mem (T.chart σ) hpσ
    rw [T.image_cell σ hσ] at hm
    exact hm
  have haW : a ∉ convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    intro ha
    have he := T.image_face σ hσ U hsub
    change T.chart σ '' T.cell U = convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) at he
    rw [← he] at ha
    obtain ⟨x, hx, hxa⟩ := ha
    have hxp := T.chart_injectiveOn σ hσ (T.cell_mono hσ hsub hx) hpσ hxa
    apply hpU
    change p ∈ T.cell U
    rw [← hxp]
    exact hx
  have hcone := affineIndependent_insert_of_hull_face_avoidance V hV haV hWV haW
  have hedge := RadialLink.edgeVectors_linearIndependent hcone (Finset.mem_insert_self a W)
  have haW' : a ∉ W := fun h => haW (subset_convexHull ℝ _ h)
  let e : τ ↪ RadialLink.edgeVectors (insert a W) a :=
    { toFun := fun v => ⟨T.euclideanLinkVector p τ v.val, by
        simp only [RadialLink.edgeVectors, Finset.mem_image, Finset.mem_erase]
        refine ⟨T.chart σ v.val.val, ⟨?_, ?_⟩, rfl⟩
        · intro he
          apply haW'
          rw [← he]
          exact Finset.mem_image.mpr ⟨v.val.val,
            T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩, rfl⟩
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v.val.val,
            T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩, rfl⟩)⟩
      inj' := by
        intro v w he
        apply Subtype.ext
        apply Subtype.ext
        have hvσ := T.vertices_mem σ hσ
          (hsub (T.mem_linkSourceVertices.mpr ⟨v.val, v.property, rfl⟩))
        have hwσ := T.vertices_mem σ hσ
          (hsub (T.mem_linkSourceVertices.mpr ⟨w.val, w.property, rfl⟩))
        apply T.chart_injectiveOn σ hσ hvσ hwσ
        have hh := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z + T.chart σ p)
          (congrArg Subtype.val he)
        simpa only [euclideanLinkVector, σ, sub_add_cancel] using hh }
  exact hedge.comp e e.injective

theorem euclideanLinkPoint_independent {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    LinearIndependent ℝ (fun v : τ => (T.euclideanLinkPoint p τ v.val).val) := by
  let units : τ → ℝˣ := fun v => Units.mk0 ‖T.euclideanLinkVector p τ v.val‖⁻¹
    (inv_ne_zero (norm_ne_zero_iff.mpr (T.euclideanLinkVector_ne_zero hτ v.property)))
  have h := (T.euclideanLinkVector_independent hτ).units_smul units
  have he : (units • (fun v : τ => T.euclideanLinkVector p τ v.val)) =
      (fun v : τ => (T.euclideanLinkPoint p τ v.val).val) := by
    funext v
    rw [euclideanLinkPoint, CrossPolytope.sphereNormalize_val
      (T.euclideanLinkVector_ne_zero hτ v.property)]
    rfl
  rwa [he] at h

theorem euclideanLinkPoint_hemisphere {p : P} {τ : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) :
    InOpenHemisphere (τ.image (T.euclideanLinkPoint p τ)) := by
  obtain ⟨ℓ, hℓ⟩ := RadialLink.exists_functional_one (T.euclideanLinkVector_independent hτ)
  have hℓ' : ∀ z ∈ τ.image (T.euclideanLinkVector p τ), ℓ z = 1 := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hℓ ⟨v, hv⟩
  have h := RadialLink.radialVertices_hemisphere_of_functional hℓ'
  have he : τ.image (T.euclideanLinkPoint p τ) =
      CrossPolytope.radialVertices (τ.image (T.euclideanLinkVector p τ)) := by
    ext x
    simp only [CrossPolytope.radialVertices, Finset.mem_image, euclideanLinkPoint]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨T.euclideanLinkVector p τ v, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
  rw [he]
  exact h

theorem euclideanLinkPoint_gram {p : P} {τ ν : Finset (T.LinkVertex p)}
    (hτ : τ ∈ T.linkFaces p) (hν : ν ∈ T.linkFaces p)
    {v w : T.LinkVertex p} (hv : v ∈ τ ∩ ν) (hw : w ∈ τ ∩ ν) :
    inner ℝ (T.euclideanLinkPoint p τ v).val (T.euclideanLinkPoint p τ w).val =
      inner ℝ (T.euclideanLinkPoint p ν v).val (T.euclideanLinkPoint p ν w).val := by
  obtain ⟨hvτ, hvν⟩ := Finset.mem_inter.mp hv
  obtain ⟨hwτ, hwν⟩ := Finset.mem_inter.mp hw
  let σ := T.linkCoface p τ
  let ρ := T.linkCoface p ν
  obtain ⟨hσ, hpσ, hτsub, _⟩ := T.linkCoface_spec hτ
  obtain ⟨hρ, hpρ, hνsub, _⟩ := T.linkCoface_spec hν
  have hvm : v.val ∈ T.cell σ ∩ T.cell ρ :=
    ⟨T.vertices_mem σ hσ (hτsub (T.mem_linkSourceVertices.mpr ⟨v, hvτ, rfl⟩)),
      T.vertices_mem ρ hρ (hνsub (T.mem_linkSourceVertices.mpr ⟨v, hvν, rfl⟩))⟩
  have hwm : w.val ∈ T.cell σ ∩ T.cell ρ :=
    ⟨T.vertices_mem σ hσ (hτsub (T.mem_linkSourceVertices.mpr ⟨w, hwτ, rfl⟩)),
      T.vertices_mem ρ hρ (hνsub (T.mem_linkSourceVertices.mpr ⟨w, hwν, rfl⟩))⟩
  have hpv := T.metric_coherence σ hσ ρ hρ p ⟨hpσ, hpρ⟩ v.val hvm
  have hpw := T.metric_coherence σ hσ ρ hρ p ⟨hpσ, hpρ⟩ w.val hwm
  have hvw := T.metric_coherence σ hσ ρ hρ v.val hvm w.val hwm
  have hpos (γ : Finset P) (hγ : γ ∈ T.simplices) (hpγ : p ∈ T.cell γ)
      (z : T.LinkVertex p) (hzγ : z.val ∈ T.cell γ) :
      0 < dist (T.chart γ p) (T.chart γ z.val) := by
    apply dist_pos.mpr
    intro he
    exact z.property.1 (T.chart_injectiveOn γ hγ hzγ hpγ he.symm)
  simp only [euclideanLinkPoint, CrossPolytope.sphereNormalize_val
    (T.euclideanLinkVector_ne_zero hτ hvτ), CrossPolytope.sphereNormalize_val
    (T.euclideanLinkVector_ne_zero hτ hwτ), CrossPolytope.sphereNormalize_val
    (T.euclideanLinkVector_ne_zero hν hvν), CrossPolytope.sphereNormalize_val
    (T.euclideanLinkVector_ne_zero hν hwν)]
  change inner ℝ (EuclideanFolding.radialDirection (T.chart σ p) (T.chart σ v.val))
      (EuclideanFolding.radialDirection (T.chart σ p) (T.chart σ w.val)) =
    inner ℝ (EuclideanFolding.radialDirection (T.chart ρ p) (T.chart ρ v.val))
      (EuclideanFolding.radialDirection (T.chart ρ p) (T.chart ρ w.val))
  rw [EuclideanFolding.radial_gram_formula _ _ _ (hpos σ hσ hpσ v hvm.1)
      (hpos σ hσ hpσ w hwm.1),
    EuclideanFolding.radial_gram_formula _ _ _ (hpos ρ hρ hpρ v hvm.2)
      (hpos ρ hρ hpρ w hwm.2), hpv, hpw, hvw]

def euclideanLinkData (p : P) : Barycentric.SphericalData (T.linkComplex p) n where
  vertex := T.euclideanLinkPoint p
  independent := fun _ hτ => T.euclideanLinkPoint_independent hτ
  hemisphere := fun _ hτ => T.euclideanLinkPoint_hemisphere hτ
  gram := by
    intro τ hτ ν hν v hv w hw
    exact T.euclideanLinkPoint_gram hτ hν hv hw

/-- The actual finite spherical link, with its cellwise angular metrics. -/
def euclideanLink (p : P) :
    FiniteChartedComplex .spherical n (T.linkComplex p).Space :=
  (T.euclideanLinkData p).toChartedComplex

end ArchivePLGeometry.FiniteChartedComplex
