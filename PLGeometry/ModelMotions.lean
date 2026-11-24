module

public import PLGeometry.Dimension
public import BrehmApprox.HyperbolicIsometryClassification
public import BrehmApprox.HyperbolicAffineProjection

/-!
# Ambient motions preserve model simplices

Euclidean affine motions, orthogonal spherical motions, and arbitrary
hyperbolic isometries preserve genuine simplex hulls and nondegeneracy.
-/

@[expose] public section
noncomputable section

open BrehmApprox
open scoped InnerProductSpace

namespace ArchivePLGeometry

variable {n : ℕ}

local instance modelMotionsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance modelMotionsEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance modelMotionsSDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance modelMotionsHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _

def euclideanMotionEmbedding
    (r : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ModelEmbedding .euclidean n n where
  toFun := r
  isometry := r.isometry
  image_hull V := by
    change r '' convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))) =
      convexHull ℝ (V.image r : Set (EuclideanSpace ℝ (Fin n)))
    rw [Finset.coe_image]
    exact r.toAffineMap.image_convexHull (V : Set (EuclideanSpace ℝ (Fin n)))
  simplex_image V hV := by
    have hV' : AffineIndepOn ℝ id (V : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa only [simplexVertices, AffineIndepOn, id_eq] using hV
    have hmap := hV'.map' r.toAffineMap r.injective
    dsimp only [simplexVertices]
    rw [@Finset.coe_image _ _ (Classical.decEq _) r V]
    exact hmap.id_image

def sphericalMotionEmbedding
    (r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ModelEmbedding .spherical n n where
  toFun := GeodesicSphere.mapEquiv r
  isometry := (GeodesicSphere.mapEquiv r).isometry
  image_hull V := CoordinateCellCharts.map_sphericalCell_image r.toLinearIsometry V
  simplex_image V hV := by
    obtain ⟨⟨p, hp⟩, hlin⟩ := hV
    constructor
    · refine ⟨GeodesicSphere.mapEquiv r p, ?_⟩
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      change 0 < ⟪r p.val, r x.val⟫_ℝ
      rw [r.inner_map_map]
      exact hp x hx
    · change LinearIndepOn ℝ GeodesicSphere.val
        (↑(V.image (GeodesicSphere.mapEquiv r)) : Set (GeodesicSphere n))
      rw [Finset.coe_image]
      have hmap : LinearIndepOn ℝ (GeodesicSphere.val ∘ GeodesicSphere.mapEquiv r)
          (V : Set (GeodesicSphere n)) :=
        hlin.map_injOn r.toLinearMap r.injective.injOn
      exact hmap.image_of_comp (GeodesicSphere.mapEquiv r) GeodesicSphere.val

theorem hyperbolic_isometry_image_cell (r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    (V : Finset (HyperbolicSpace n)) : r '' hyperbolicCell V = hyperbolicCell (V.image r) := by
  obtain ⟨L, hL⟩ := HyperbolicSpace.exists_lorentz_linear_lift r
  obtain ⟨L', hL'⟩ := HyperbolicSpace.exists_lorentz_linear_lift r.symm
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_hyperbolicCell_image_of_linear_lift r L hL V hx
  · intro y hy
    have hx := mem_hyperbolicCell_image_of_linear_lift r.symm L' hL' (V.image r) hy
    have him : (V.image r).image r.symm = V := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨u, ⟨v, hv, rfl⟩, h⟩
        rw [r.symm_apply_apply] at h
        exact h ▸ hv
      · intro hx
        exact ⟨r x, ⟨x, hx, rfl⟩, r.symm_apply_apply x⟩
    rw [him] at hx
    exact ⟨r.symm y, hx, r.apply_symm_apply y⟩

def hyperbolicMotionEmbedding (r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n) :
    ModelEmbedding .hyperbolic n n where
  toFun := r
  isometry := r.isometry
  image_hull := hyperbolic_isometry_image_cell r
  simplex_image V hV := by
    obtain ⟨L, hLin, hL⟩ := HyperbolicSpace.exists_injective_lorentz_linear_lift r
    change LinearIndepOn ℝ HyperbolicSpace.lift
      (↑(V.image r) : Set (HyperbolicSpace n))
    rw [Finset.coe_image]
    have hmap : LinearIndepOn ℝ (HyperbolicSpace.lift ∘ r) (V : Set (HyperbolicSpace n)) := by
      have h := hV.map_injOn L hLin.injOn
      simpa only [LinearIndepOn, Function.comp_def, hL] using h
    exact hmap.image_of_comp r HyperbolicSpace.lift

end ArchivePLGeometry
