module

public import BrehmApprox.SphericalPolytopeNeighborhoods
public import BrehmApprox.AffineArrangement

/-!
# Finite orthogonal selections are spherical piecewise isometries

In a gnomonic chart, multiplying the value vector by the source normalizing
factor turns each orthogonal candidate into an affine map. A finite affine
arrangement therefore gives an actual finite spherical polyhedral cover.
-/

@[expose] public section
noncomputable section

namespace BrehmApprox

open GeodesicSphere

variable {n : ℕ}

/-- The affine slice of a central chart before normalization. -/
def sphericalHomogeneous (p : GeodesicSphere n) :
    tangentPlane p →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  AffineMap.const ℝ (tangentPlane p) p.val + (tangentPlane p).subtype.toAffineMap

@[simp] theorem sphericalHomogeneous_apply (p : GeodesicSphere n) (z : tangentPlane p) :
    sphericalHomogeneous p z = p.val + z.val := rfl

/-- The affine expression of an orthogonal motion in the source chart. -/
def sphericalAffine (p : GeodesicSphere n)
    (r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    tangentPlane p →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  r.toLinearEquiv.toLinearMap.toAffineMap.comp (sphericalHomogeneous p)

@[simp] theorem sphericalAffine_apply (p : GeodesicSphere n)
    (r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (z : tangentPlane p) : sphericalAffine p r z = r (p.val + z.val) := rfl

/-- A sphere-valued map, lifted to the affine slice of its source chart. -/
def sphericalLift (p : GeodesicSphere n) (f : GeodesicSphere n → GeodesicSphere n)
    (z : tangentPlane p) : EuclideanSpace ℝ (Fin (n + 1)) :=
  gnomonicScale p z • (f (gnomonicPoint p z)).val

theorem continuous_sphericalLift (p : GeodesicSphere n)
    {f : GeodesicSphere n → GeodesicSphere n} (hf : Continuous f) :
    Continuous (sphericalLift p f) := by
  exact (continuous_const.add continuous_subtype_val).norm.smul
    (continuous_val.comp (hf.comp (continuous_gnomonicPoint p)))

theorem sphericalLift_eq_affine_of_eq (p : GeodesicSphere n)
    (r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {f : GeodesicSphere n → GeodesicSphere n} {z : tangentPlane p}
    (h : f (gnomonicPoint p z) = mapEquiv r (gnomonicPoint p z)) :
    sphericalLift p f z = sphericalAffine p r z := by
  rw [sphericalLift, h, mapEquiv_apply_val, ← map_smul, gnomonicScale_smul_point]
  rfl

theorem eq_of_sphericalLift_eq_affine (p : GeodesicSphere n)
    (r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {f : GeodesicSphere n → GeodesicSphere n} {z : tangentPlane p}
    (h : sphericalLift p f z = sphericalAffine p r z) :
    f (gnomonicPoint p z) = mapEquiv r (gnomonicPoint p z) := by
  apply GeodesicSphere.ext
  apply smul_right_injective _ (gnomonicScale_pos p z).ne'
  exact h.trans (sphericalLift_eq_affine_of_eq p r (f := mapEquiv r) rfl).symm

/-- Transport an affine cover of the normalized graph back to actual
hemispherical polyhedra. -/
theorem sphericalPLOn_of_chart_cover {ι : Type*}
    (r : ι → EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (f : GeodesicSphere n → GeodesicSphere n) (p : GeodesicSphere n)
    (V : Finset (GeodesicSphere n)) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (C : Finset (Finset (tangentPlane p)))
    (hcover : convexHull ℝ (projectVertices p V hp : Set (tangentPlane p)) =
      ⋃ W ∈ C, convexHull ℝ (W : Set (tangentPlane p)))
    (hpieces : ∀ W ∈ C, ∃ i, Set.EqOn (sphericalLift p f) (sphericalAffine p (r i))
      (convexHull ℝ (W : Set (tangentPlane p)))) :
    SphericalPLOn (sphericalCell V) f := by
  classical
  have himage : sphericalCell V =
      gnomonicPoint p '' convexHull ℝ (projectVertices p V hp : Set (tangentPlane p)) := by
    simpa only [chartVertices_projectVertices] using
      sphericalCell_chartVertices_eq_image p (projectVertices p V hp)
  refine ⟨C.image (chartVertices p), ?_, ?_⟩
  · rw [himage, hcover]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨W, hW, hzW⟩ := Set.mem_iUnion₂.mp hz
      apply Set.mem_iUnion₂.mpr
      refine ⟨chartVertices p W, Finset.mem_image.mpr ⟨W, hW, rfl⟩, ?_⟩
      rw [sphericalCell_chartVertices_eq_image]
      exact ⟨z, hzW, rfl⟩
    · intro hx
      obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hD
      rw [sphericalCell_chartVertices_eq_image] at hxD
      obtain ⟨z, hzW, rfl⟩ := hxD
      exact ⟨z, Set.mem_iUnion₂.mpr ⟨W, hW, hzW⟩, rfl⟩
  · intro D hD
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨i, hi⟩ := hpieces W hW
    refine ⟨chartVertices_hemisphere p W, r i, ?_⟩
    intro x hx
    rw [sphericalCell_chartVertices_eq_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact eq_of_sphericalLift_eq_affine p (r i) (hi hz)

/-- A continuous finite selection of orthogonal motions has finite genuine
spherical pieces on every hemispherical polytope. -/
theorem locallySphericalPL_of_finite_orthogonal_selection
    {ι : Type*} [Finite ι]
    (r : ι → EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {f : GeodesicSphere n → GeodesicSphere n} (hf : Continuous f)
    (hselect : ∀ x, ∃ i, f x = mapEquiv (r i) x) : LocallySphericalPL f := by
  intro V hV
  obtain ⟨p, hp⟩ := hV
  have hsel : ∀ z ∈ convexHull ℝ (projectVertices p V hp : Set (tangentPlane p)),
      ∃ i, sphericalLift p f z = sphericalAffine p (r i) z := by
    intro z _
    obtain ⟨i, hi⟩ := hselect (gnomonicPoint p z)
    exact ⟨i, sphericalLift_eq_affine_of_eq p (r i) hi⟩
  obtain ⟨C, hC, hpieces⟩ := finite_selection_affine_polytope_cover
    (projectVertices p V hp) (fun i => sphericalAffine p (r i))
    (continuous_sphericalLift p hf).continuousOn hsel
  exact sphericalPLOn_of_chart_cover r f p V hp C hC hpieces

/-- The same criterion with the finite motions supplied as a finite set. -/
theorem locallySphericalPL_of_finset_orthogonal_selection
    {f : GeodesicSphere n → GeodesicSphere n} (hf : Continuous f)
    (S : Finset (EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1))))
    (hselect : ∀ x, ∃ r ∈ S, f x = mapEquiv r x) : LocallySphericalPL f := by
  apply locallySphericalPL_of_finite_orthogonal_selection (fun r : S => r.val) hf
  intro x
  obtain ⟨r, hr, hx⟩ := hselect x
  exact ⟨⟨r, hr⟩, hx⟩

end BrehmApprox
