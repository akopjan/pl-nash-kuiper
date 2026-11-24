module

public import BrehmApprox.SphericalFlattening
public import BrehmApprox.SphericalPolytopeNeighborhoods

/-!
# Spherical orthogonal projection in a central chart

For a great subsphere through the chart's pole, Euclidean orthogonal projection
in the tangent chart agrees exactly with normalization of the ambient
orthogonal projection. It is therefore the actual spherical nearest-point
projection. The constructed normal flattening preserves this projection.
-/

@[expose] public section

noncomputable section

namespace GeodesicSphere

open BrehmApprox

variable {n : ℕ}

/-- The tangent part of an ambient linear subspace at a chosen pole. -/
def tangentSubspace (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) : Submodule ℝ (tangentPlane p) :=
  L.comap (tangentPlane p).subtype

lemma tangentSubspace_mono (p : GeodesicSphere n)
    {F L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))} (hFL : F ≤ L) :
    tangentSubspace p F ≤ tangentSubspace p L := by
  intro z hz
  exact hFL hz

lemma starProjection_mem_tangentPlane (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hp : p.val ∈ L)
    (z : tangentPlane p) : L.starProjection z.val ∈ tangentPlane p := by
  change inner ℝ p.val (L.starProjection z.val) = 0
  have h := L.inner_starProjection_left_eq_right p.val z.val
  rw [L.starProjection_eq_self_iff.mpr hp, inner_tangentPlane] at h
  exact h.symm

/-- Orthogonal projection in the tangent plane is the restriction of the
ambient orthogonal projection whenever the ambient subspace contains the pole. -/
lemma coe_tangentSubspace_starProjection (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hp : p.val ∈ L)
    (z : tangentPlane p) :
    ((tangentSubspace p L).starProjection z).val = L.starProjection z.val := by
  let v : tangentPlane p := ⟨L.starProjection z.val, starProjection_mem_tangentPlane p L hp z⟩
  have hv : v ∈ tangentSubspace p L := L.starProjection_apply_mem z.val
  have horth : ∀ w ∈ tangentSubspace p L, inner ℝ (z - v) w = 0 := by
    intro w hw
    change inner ℝ (z.val - L.starProjection z.val) w.val = 0
    exact L.starProjection_inner_eq_zero z.val w.val hw
  have h := (tangentSubspace p L).eq_starProjection_of_mem_of_inner_eq_zero hv horth
  exact congrArg Subtype.val h

/-- Projection onto the great subsphere, expressed in the central chart. -/
def greatSphereProjection (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (x : openHemisphere p) : openHemisphere p :=
  gnomonicInverse p ((tangentSubspace p L).starProjection (gnomonic p x))

lemma greatSphereProjection_val (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hp : p.val ∈ L)
    (x : openHemisphere p) :
    (greatSphereProjection p L x).val.val = NormedSpace.normalize (L.starProjection x.val.val) := by
  change NormedSpace.normalize
    (p.val + ((tangentSubspace p L).starProjection (gnomonic p x)).val) = _
  rw [coe_tangentSubspace_starProjection p L hp, gnomonic_val, map_sub, map_smul,
    L.starProjection_eq_self_iff.mpr hp]
  have heq : p.val + ((inner ℝ p.val x.val.val)⁻¹ • L.starProjection x.val.val - p.val) =
      (inner ℝ p.val x.val.val)⁻¹ • L.starProjection x.val.val := by abel
  rw [heq, NormedSpace.normalize_smul_of_pos (inv_pos.mpr x.property)]

lemma ambientProjection_ne_zero (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hp : p.val ∈ L)
    (x : openHemisphere p) : L.starProjection x.val.val ≠ 0 := by
  intro hz
  have h := L.inner_starProjection_left_eq_right p.val x.val.val
  rw [L.starProjection_eq_self_iff.mpr hp, hz, inner_zero_right] at h
  exact (ne_of_gt x.property) h

lemma greatSphereProjection_mem (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hp : p.val ∈ L)
    (x : openHemisphere p) : (greatSphereProjection p L x).val.val ∈ L := by
  rw [greatSphereProjection_val p L hp, NormedSpace.normalize]
  exact L.smul_mem _ (L.starProjection_apply_mem _)

lemma inner_greatSphereProjection (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hp : p.val ∈ L)
    (x : openHemisphere p) :
    inner ℝ x.val.val (greatSphereProjection p L x).val.val = ‖L.starProjection x.val.val‖ := by
  have horth := L.starProjection_inner_eq_zero x.val.val (L.starProjection x.val.val)
    (L.starProjection_apply_mem _)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at horth
  have hinner : inner ℝ x.val.val (L.starProjection x.val.val) = ‖L.starProjection x.val.val‖ ^ 2 :=
    sub_eq_zero.mp horth
  rw [greatSphereProjection_val p L hp, NormedSpace.normalize, inner_smul_right, hinner]
  field_simp [norm_ne_zero_iff.mpr (ambientProjection_ne_zero p L hp x)]

/-- This chart projection is the actual nearest-point projection for the
spherical metric onto the great subsphere. -/
theorem greatSphereProjection_nearest (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hp : p.val ∈ L)
    (x : openHemisphere p) {v : GeodesicSphere n} (hv : v.val ∈ L) :
    dist x.val (greatSphereProjection p L x).val ≤ dist x.val v := by
  have horth := L.starProjection_inner_eq_zero x.val.val v.val hv
  rw [inner_sub_left] at horth
  have hinner : inner ℝ x.val.val v.val = inner ℝ (L.starProjection x.val.val) v.val :=
    sub_eq_zero.mp horth
  have hcs := real_inner_le_norm (L.starProjection x.val.val) v.val
  rw [v.norm_val, mul_one, ← hinner] at hcs
  rw [dist_eq_arccos_inner, dist_eq_arccos_inner, inner_greatSphereProjection p L hp]
  exact Real.arccos_le_arccos hcs

/-- The spherical normal flattening preserves the genuine orthogonal projection. -/
theorem greatSphereProjection_sphericalNormalFlatten (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (α : ℝ)
    (R : tangentPlane p → ℝ) (x : openHemisphere p) :
    greatSphereProjection p L (sphericalNormalFlatten p (tangentSubspace p L) α R x) =
      greatSphereProjection p L x := by
  unfold greatSphereProjection
  rw [sphericalNormalFlatten_projection]

/-- Nearest projections to nested great subspheres through the common pole
compose exactly. -/
theorem greatSphereProjection_nested (p : GeodesicSphere n)
    {F L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))} (hFL : F ≤ L)
    (x : openHemisphere p) :
    greatSphereProjection p F (greatSphereProjection p L x) = greatSphereProjection p F x := by
  unfold greatSphereProjection
  rw [gnomonic_gnomonicInverse]
  congr 1
  have h := Submodule.starProjection_comp_starProjection_of_le (tangentSubspace_mono p hFL)
  exact congrArg (fun f => f (gnomonic p x)) h

/-- Flattening toward one face preserves every orthogonal projection to a
subface through the same pole. -/
theorem greatSphereProjection_sphericalNormalFlatten_of_le (p : GeodesicSphere n)
    {F L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))} (hFL : F ≤ L)
    (α : ℝ) (R : tangentPlane p → ℝ) (x : openHemisphere p) :
    greatSphereProjection p F (sphericalNormalFlatten p (tangentSubspace p L) α R x) =
      greatSphereProjection p F x := by
  rw [← greatSphereProjection_nested p hFL
    (sphericalNormalFlatten p (tangentSubspace p L) α R x),
    greatSphereProjection_sphericalNormalFlatten, greatSphereProjection_nested p hFL]

/-- On the inner tube the actual flattening agrees with the actual nearest
projection onto the great subsphere. -/
theorem sphericalNormalFlatten_eq_greatSphereProjection (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) {α : ℝ}
    (hα1 : α < 1) (R : tangentPlane p → ℝ) {x : openHemisphere p}
    (hin : ‖gnomonic p x - (tangentSubspace p L).starProjection (gnomonic p x)‖ ≤
      α * R ((tangentSubspace p L).starProjection (gnomonic p x))) :
    sphericalNormalFlatten p (tangentSubspace p L) α R x = greatSphereProjection p L x :=
  sphericalNormalFlatten_inner p (tangentSubspace p L) hα1 R hin

/-- A spherical cell is preserved whenever it contains the point and its
normal projection. This is the geometric simplex-preservation step. -/
theorem sphericalNormalFlatten_mem_cell (p : GeodesicSphere n)
    (V : Finset (GeodesicSphere n)) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (K : Submodule ℝ (tangentPlane p)) (α : ℝ) (R : tangentPlane p → ℝ)
    (x : openHemisphere p) (hx : x.val ∈ sphericalCell V)
    (hPx : (gnomonicInverse p (K.starProjection (gnomonic p x))).val ∈ sphericalCell V) :
    (sphericalNormalFlatten p K α R x).val ∈ sphericalCell V := by
  have hxchart := (gnomonic_mem_convexHull_iff p V hp x).mpr hx
  have hPchart := (gnomonicInverse_mem_cell_iff p V hp _).mp hPx
  have hflat := normalFlatten_mem_convex K α (R (K.starProjection (gnomonic p x)))
    (convex_convexHull ℝ (projectVertices p V hp : Set (tangentPlane p))) hxchart hPchart
  apply (gnomonicInverse_mem_cell_iff p V hp _).mpr
  exact hflat

end GeodesicSphere
