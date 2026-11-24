module

public import BrehmApprox.SphericalOrthogonalProjection

/-!
# Naturality of spherical local flattening

The central chart and its normal flattening commute with actual ambient linear
isometric embeddings, including embeddings between different dimensions. Thus
local constructions agree when a common face is represented inside different
incident simplices, provided the intrinsic cut-off radius agrees on that face.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma radialFlatten_map_linearIsometry (f : E →ₗᵢ[ℝ] F) (α R : ℝ) (x : E) :
    f (radialFlatten α R x) = radialFlatten α R (f x) := by
  simp only [radialFlatten, map_smul, f.norm_map]

lemma normalFlatten_map_linearIsometry (f : E →ₗᵢ[ℝ] F)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    [(K.map f.toLinearMap).HasOrthogonalProjection] (α R : ℝ) (x : E) :
    f (normalFlatten K α R x) = normalFlatten (K.map f.toLinearMap) α R (f x) := by
  simp only [normalFlatten, map_add, radialFlatten_map_linearIsometry, map_sub,
    f.map_starProjection]

lemma taperedNormalFlatten_map_linearIsometry (f : E →ₗᵢ[ℝ] F)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    [(K.map f.toLinearMap).HasOrthogonalProjection]
    (α : ℝ) (R : E → ℝ) (S : F → ℝ)
    (hRS : ∀ z ∈ K, S (f z) = R z) (x : E) :
    f (taperedNormalFlatten K α R x) =
      taperedNormalFlatten (K.map f.toLinearMap) α S (f x) := by
  unfold taperedNormalFlatten
  rw [← f.map_starProjection K x, hRS _ (K.starProjection_apply_mem x)]
  exact normalFlatten_map_linearIsometry f K α _ x

end BrehmApprox

namespace GeodesicSphere

open BrehmApprox

variable {n m : ℕ}

/-- The restriction of a spherical isometric embedding to a hemisphere. -/
def mapHemisphere
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (p : GeodesicSphere n) (x : openHemisphere p) : openHemisphere (map f p) :=
  ⟨map f x.val, by
    change 0 < inner ℝ (f p.val) (f x.val.val)
    rw [f.inner_map_map]
    exact x.property⟩

@[simp]
lemma mapHemisphere_val
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (p : GeodesicSphere n) (x : openHemisphere p) :
    (mapHemisphere f p x).val = map f x.val := rfl

lemma isometry_mapHemisphere
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (p : GeodesicSphere n) : Isometry (mapHemisphere f p) := by
  apply Isometry.of_dist_eq
  intro x y
  exact (isometry_map f).dist_eq x.val y.val

/-- The actual linear isometry induced on the tangent spaces. -/
def tangentMap
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (p : GeodesicSphere n) : tangentPlane p →ₗᵢ[ℝ] tangentPlane (map f p) where
  toFun z := ⟨f z.val, by
    change inner ℝ (f p.val) (f z.val) = 0
    rw [f.inner_map_map, inner_tangentPlane]⟩
  map_add' z w := Subtype.ext (f.map_add z.val w.val)
  map_smul' c z := Subtype.ext (f.map_smul c z.val)
  norm_map' z := f.norm_map z.val

@[simp]
lemma tangentMap_val
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (p : GeodesicSphere n) (z : tangentPlane p) : (tangentMap f p z).val = f z.val := rfl

/-- The central chart commutes with ambient isometric embeddings. -/
lemma gnomonic_natural
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (p : GeodesicSphere n) (x : openHemisphere p) :
    tangentMap f p (gnomonic p x) = gnomonic (map f p) (mapHemisphere f p x) := by
  apply Subtype.ext
  change f ((inner ℝ p.val x.val.val)⁻¹ • x.val.val - p.val) =
    (inner ℝ (f p.val) (f x.val.val))⁻¹ • f x.val.val - f p.val
  rw [map_sub, map_smul, f.inner_map_map]

lemma gnomonicInverse_natural
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (p : GeodesicSphere n) (z : tangentPlane p) :
    mapHemisphere f p (gnomonicInverse p z) =
      gnomonicInverse (map f p) (tangentMap f p z) := by
  apply Subtype.ext
  apply GeodesicSphere.ext
  change f (NormedSpace.normalize (p.val + z.val)) =
    NormedSpace.normalize (f p.val + f z.val)
  simp only [NormedSpace.normalize, map_smul, ← map_add, f.norm_map]

/-- Exact agreement of the constructed spherical flattenings in compatible
isometric charts, including restriction from a larger simplex to a face. -/
theorem sphericalNormalFlatten_natural
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (p : GeodesicSphere n) (K : Submodule ℝ (tangentPlane p)) (α : ℝ)
    (R : tangentPlane p → ℝ) (S : tangentPlane (map f p) → ℝ)
    (hRS : ∀ z ∈ K, S (tangentMap f p z) = R z) (x : openHemisphere p) :
    mapHemisphere f p (sphericalNormalFlatten p K α R x) =
      sphericalNormalFlatten (map f p) (K.map (tangentMap f p).toLinearMap) α S
        (mapHemisphere f p x) := by
  unfold sphericalNormalFlatten
  rw [gnomonicInverse_natural,
    taperedNormalFlatten_map_linearIsometry (tangentMap f p) K α R S hRS,
    gnomonic_natural]

end GeodesicSphere
