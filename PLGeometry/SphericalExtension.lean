module

public import BrehmApprox.SphericalRadialTransfer
public import BrehmApprox.SphericalFiniteMotions
public import BrehmApprox.AffineSelectionCells

/-!
# Spherical finite interpolation with an actual geodesic triangulation

The crosspolytope boundary is a common affine radial section of the sphere.
An affine equality arrangement followed by compatible pulling triangulation
produces the locally finite geodesic triangulation in `PLIsometry`.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry

open BrehmApprox BrehmApprox.CrossPolytope GeodesicSphere

variable {n : ℕ}

local instance sphericalExtensionLocalInstance1 (α : Type*) : DecidableEq α := Classical.decEq α

theorem spherical_plIsometry_of_polytope_family
    {I : Type*} [Finite I]
    (C : I → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hC : ∀ i, IsFinitePolytope (C i))
    (hface : ∀ i j, _root_.IsExtreme ℝ (C i) (C i ∩ C j))
    (hfacet : ∀ i, ∃ σ, C i ⊆ facet σ)
    (hcover : ∀ x : GeodesicSphere n, ∃ i, radialSection x ∈ C i)
    {f : GeodesicSphere n → GeodesicSphere n} (hf : Continuous f)
    (hmotion : ∀ i, ∃ r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      ∀ z ∈ C i, f (sphereNormalize z) = mapEquiv r (sphereNormalize z)) :
    PLIsometry .spherical n f := by
  let _ : LinearOrder (EuclideanSpace ℝ (Fin (n + 1))) :=
    IsWellOrder.linearOrder (WellOrderingRel : EuclideanSpace ℝ (Fin (n + 1)) → _ → Prop)
  let A := Pulling.familyFaces C hC
  have hAfin : A.Finite := by
    have hA : A = ⋃ i, (Pulling.faces (polytopeVertices (C i) (hC i)) : Set (Finset _)) := by
      ext S
      simp only [A, Pulling.familyFaces, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe]
    rw [hA]
    exact Set.finite_iUnion (fun i => (Pulling.faces (polytopeVertices (C i) (hC i))).finite_toSet)
  let B : Set (Finset (GeodesicSphere n)) := radialVertices '' A
  have hBfin : B.Finite := hAfin.image radialVertices
  have hSfacet (S : Finset (EuclideanSpace ℝ (Fin (n + 1)))) (hS : S ∈ A) :
      ∃ σ, ∀ v ∈ S, v ∈ facet σ := by
    obtain ⟨i, hi⟩ := hS
    obtain ⟨σ, hσ⟩ := hfacet i
    refine ⟨σ, ?_⟩
    intro v hv
    exact hσ (Pulling.family_face_subset_cell C hC hi (subset_convexHull ℝ _ hv))
  have hBsimplex (W : Finset (GeodesicSphere n)) (hW : W ∈ B) :
      InOpenHemisphere W ∧ LinearIndependent ℝ (fun w : W => w.val.val) := by
    obtain ⟨S, hS, rfl⟩ := hW
    obtain ⟨σ, hσ⟩ := hSfacet S hS
    exact ⟨radialVertices_hemisphere hσ,
      radialVertices_linearIndependent hσ (Pulling.family_face_independent C hC hS)⟩
  let T : Triangulation .spherical n (GeodesicSphere n) :=
    { simplices := B
      cell := sphericalCell
      chart := fun _ => id
      cover := by
        intro x
        obtain ⟨i, hi⟩ := hcover x
        have hx : radialSection x ∈ ⋃ i, C i := Set.mem_iUnion.mpr ⟨i, hi⟩
        rw [Pulling.family_faces_cover C hC] at hx
        obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨σ, hσ⟩ := hSfacet S hS
        refine ⟨radialVertices S, ⟨S, hS, rfl⟩, ?_⟩
        rw [sphericalCell_radialVertices hσ]
        exact ⟨radialSection x, hxS, sphereNormalize_radialSection x⟩
      locallyFinite := by
        let : Finite B := hBfin.to_subtype
        exact locallyFinite_of_finite _
      vertices_mem := fun _ _ _ hv => mem_sphericalCell_of_mem hv
      simplex := by
        intro W hW
        rw [Finset.image_id]
        exact hBsimplex W hW
      image_cell := by intro W _; simp only [Set.image_id, Finset.image_id]; rfl
      isometry_cell := by intro W hW x hx y hy; rfl
      faces := by
        intro W hW U hUW
        obtain ⟨S, hS, rfl⟩ := hW
        obtain ⟨R, hRS, hRU⟩ := exists_radialVertices_subface hUW
        exact ⟨R, Pulling.family_face_downward C hC hS hRS, hRU⟩
      image_face := by intro W hW U hUW; simp only [Set.image_id, Finset.image_id]; rfl
      intersection := by
        intro W hW Z hZ
        obtain ⟨S, hS, rfl⟩ := hW
        obtain ⟨R, hR, rfl⟩ := hZ
        obtain ⟨σ, hσ⟩ := hSfacet S hS
        obtain ⟨τ, hτ⟩ := hSfacet R hR
        apply radialCells_intersection hσ hτ
        simpa only [Finset.coe_inter] using Pulling.family_faces_intersection C hC hface hS hR }
  refine ⟨hf, T, ?_⟩
  intro W hW x hx y hy
  obtain ⟨S, hS, rfl⟩ := hW
  obtain ⟨i, hi⟩ := hS
  obtain ⟨σ, hσ⟩ := hSfacet S ⟨i, hi⟩
  change x ∈ sphericalCell (radialVertices S) at hx
  change y ∈ sphericalCell (radialVertices S) at hy
  rw [sphericalCell_radialVertices hσ] at hx hy
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨r, hr⟩ := hmotion i
  rw [hr z (Pulling.family_face_subset_cell C hC hi hz),
    hr w (Pulling.family_face_subset_cell C hC hi hw)]
  exact (mapEquiv r).dist_eq _ _

def sphericalRadialLift (f : GeodesicSphere n → GeodesicSphere n)
    (z : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  ‖z‖ • (f (sphereNormalize z)).val

theorem continuousOn_sphericalRadialLift {f : GeodesicSphere n → GeodesicSphere n}
    (hf : Continuous f) (σ : Fin (n + 1) → Bool) :
    ContinuousOn (sphericalRadialLift f) (facet σ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hn (z : facet σ) : z.val ≠ 0 := nonzero_of_mem_facet z.property
  have hnorm : Continuous (fun z : facet σ => sphereNormalize z.val) := by
    have h := continuous_normalizeVector ((↑) : facet σ → EuclideanSpace ℝ (Fin (n + 1)))
      continuous_subtype_val hn
    convert h using 1
    funext z
    simp only [sphereNormalize, dite_eq_right (hn z)]
  exact continuous_subtype_val.norm.smul (continuous_val.comp (hf.comp hnorm))

theorem sphericalRadialLift_eq_linear {f : GeodesicSphere n → GeodesicSphere n}
    (r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ≠ 0)
    (h : f (sphereNormalize z) = mapEquiv r (sphereNormalize z)) :
    sphericalRadialLift f z = r z := by
  rw [sphericalRadialLift, h, mapEquiv_apply_val, ← map_smul, norm_smul_sphereNormalize hz]

theorem plIsometry_spherical_of_finite_motions
    {f : GeodesicSphere n → GeodesicSphere n} (hf : Continuous f)
    (hm : FiniteSphericalMotions f) : PLIsometry .spherical n f := by
  obtain ⟨S, hS⟩ := hm
  let a : S → EuclideanSpace ℝ (Fin (n + 1)) →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    fun r => r.val.toLinearEquiv.toLinearMap.toAffineMap
  let L := affineEqualityLinear a
  let b := affineEqualityBound a
  let I := {p : (Fin (n + 1) → Bool) ×
      (AffineEqualityIndex (EuclideanSpace ℝ (Fin (n + 1))) S → AffineSign) //
        (affineStratum (facet p.1) L b p.2).Nonempty}
  let C : I → Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    fun i => affineWeakCell (facet i.val.1) L b i.val.2
  have hpoly (i : I) : IsFinitePolytope (C i) := by
    exact exists_finset_affineWeakCell (facetVertices i.val.1) L b i.val.2
  have hfacial (i j : I) : _root_.IsExtreme ℝ (C i) (C i ∩ C j) :=
    isExtreme_affineWeakCell_inter_of_base (facet_face_inter i.val.1 j.val.1) L b i.val.2 j.val.2
  have hfacet (i : I) : ∃ σ, C i ⊆ facet σ := ⟨i.val.1, fun _ hx => hx.1⟩
  have hcover (x : GeodesicSphere n) : ∃ i, radialSection x ∈ C i := by
    obtain ⟨σ, hx⟩ := exists_facet_of_gauge_eq_one (gauge_radialSection x)
    let s : AffineEqualityIndex (EuclideanSpace ℝ (Fin (n + 1))) S → AffineSign :=
      fun k => AffineSign.ofCompare (L k (radialSection x)) (b k)
    have hxs : radialSection x ∈ affineStratum (facet σ) L b s :=
      ⟨hx, fun k => AffineSign.holds_ofCompare _ _⟩
    exact ⟨⟨(σ, s), radialSection x, hxs⟩, affineStratum_subset_weakCell (facet σ) L b s hxs⟩
  apply spherical_plIsometry_of_polytope_family C hpoly hfacial hfacet hcover hf
  intro i
  have hsel : ∀ z ∈ facet i.val.1, ∃ r : S, sphericalRadialLift f z = a r z := by
    intro z hz
    obtain ⟨r, hr, heq⟩ := hS (sphereNormalize z)
    exact ⟨⟨r, hr⟩, sphericalRadialLift_eq_linear r (nonzero_of_mem_facet hz) heq⟩
  obtain ⟨r, hr⟩ := affine_selection_eqOn_weakCell (facet_isFinitePolytope i.val.1) a
    (continuousOn_sphericalRadialLift hf i.val.1) hsel i.val.2 i.property
  refine ⟨r.val, ?_⟩
  intro z hz
  have hnon := nonzero_of_mem_facet hz.1
  apply GeodesicSphere.ext
  apply smul_right_injective (EuclideanSpace ℝ (Fin (n + 1))) (norm_ne_zero_iff.mpr hnon)
  change sphericalRadialLift f z = sphericalRadialLift (mapEquiv r.val) z
  exact (hr hz).trans (sphericalRadialLift_eq_linear r.val hnon rfl).symm

/-- The spherical component of the Brehm–Akopyan–Tarasov statement. -/
theorem brehm_spherical (n : ℕ)
    (A : Finset (Model .spherical n)) (f : Model .spherical n → Model .spherical n)
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ dist x y) :
    ∃ F : Model .spherical n → Model .spherical n,
      LipschitzWith 1 F ∧ PLIsometry .spherical n F ∧ ∀ x ∈ A, F x = f x := by
  obtain ⟨F, hF, hm, heq⟩ := spherical_finite_extension_motions n A f hf
  have hLip : LipschitzWith 1 F := short_iff_lipschitz.mp hF
  exact ⟨F, hLip, plIsometry_spherical_of_finite_motions hLip.continuous hm, heq⟩

end ArchivePLGeometry
