module

public import Compatibility.Original
public import PLGeometry.Definitions
public import BrehmApprox.HyperbolicStrictification

/-!
# Exact transport between the two concrete constant-curvature models

The original Challenge uses a subtype of the Klein ball and a subtype of the
unit sphere. The completed proof uses hyperboloid spatial coordinates and an
angular-metric sphere wrapper. These explicit equivalences preserve the
Challenge's model distances and finite geodesic hulls.
-/

@[expose] public section
noncomputable section

open scoped BigOperators InnerProductSpace

namespace PLGeometry

local instance modelBridgeDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

abbrev Geometry.toArchive : Geometry → ArchivePLGeometry.Geometry
  | .euclidean => .euclidean
  | .hyperbolic => .hyperbolic
  | .spherical => .spherical

abbrev modelEquiv (κ : Geometry) (n : ℕ) :
    Model κ n ≃ ArchivePLGeometry.Model κ.toArchive n :=
  match κ with
  | .euclidean => Equiv.refl _
  | .hyperbolic => BrehmApprox.HyperbolicSpace.kleinEquiv.symm
  | .spherical => GeodesicSphere.unitSphereEquiv n

def modelHomeomorph (κ : Geometry) (n : ℕ) :
    Model κ n ≃ₜ ArchivePLGeometry.Model κ.toArchive n :=
  match κ with
  | .euclidean => Homeomorph.refl _
  | .hyperbolic => BrehmApprox.HyperbolicSpace.kleinHomeomorph.symm
  | .spherical => GeodesicSphere.unitSphereHomeomorph n

@[simp]
theorem modelHomeomorph_toEquiv (κ : Geometry) (n : ℕ) :
    (modelHomeomorph κ n).toEquiv = modelEquiv κ n := by
  cases κ <;> rfl

theorem continuous_modelEquiv (κ : Geometry) (n : ℕ) :
    Continuous (modelEquiv κ n) := by
  rw [← modelHomeomorph_toEquiv]
  exact (modelHomeomorph κ n).continuous

theorem continuous_modelEquiv_symm (κ : Geometry) (n : ℕ) :
    Continuous (modelEquiv κ n).symm := by
  rw [← modelHomeomorph_toEquiv]
  exact (modelHomeomorph κ n).symm.continuous

@[simp]
theorem modelEquiv_dist (κ : Geometry) (n : ℕ) (x y : Model κ n) :
    dist (modelEquiv κ n x) (modelEquiv κ n y) = modelDist κ n x y := by
  cases κ with
  | euclidean => rfl
  | spherical => rfl
  | hyperbolic =>
    change BrehmApprox.Hyperboloid.distance
      (BrehmApprox.HyperbolicSpace.fromKlein x.val).point
      (BrehmApprox.HyperbolicSpace.fromKlein y.val).point = _
    rw [BrehmApprox.Hyperboloid.distance,
      BrehmApprox.HyperbolicSpace.coshDist_fromKlein
        (by simpa only [Metric.mem_ball, dist_zero_right] using x.property)
        (by simpa only [Metric.mem_ball, dist_zero_right] using y.property)]
    rfl

@[simp]
theorem modelDist_modelEquiv_symm (κ : Geometry) (n : ℕ)
    (x y : ArchivePLGeometry.Model κ.toArchive n) :
    modelDist κ n ((modelEquiv κ n).symm x) ((modelEquiv κ n).symm y) = dist x y := by
  rw [← modelEquiv_dist, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp]
theorem klein_modelEquiv {n : ℕ} (x : Model .hyperbolic n) :
    BrehmApprox.HyperbolicSpace.klein (modelEquiv .hyperbolic n x) = x.val := by
  exact congrArg Subtype.val (BrehmApprox.HyperbolicSpace.kleinEquiv.apply_symm_apply x)

@[simp]
theorem val_modelEquiv_spherical {n : ℕ} (x : Model .spherical n) :
    (modelEquiv .spherical n x).val = x.val := rfl

/-- The positive spherical hull is the positive radial saturation of the
ordinary convex hull of its unit-vector vertices. No hemisphere assumption
is needed for this equality. -/
theorem sphericalCell_mem_iff_convexHull {n : ℕ}
    (V : Finset (GeodesicSphere n)) (x : GeodesicSphere n) :
    x ∈ BrehmApprox.sphericalCell V ↔
      ∃ y ∈ convexHull ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere n))),
        ∃ t : ℝ, 0 < t ∧ x.val = t • y := by
  classical
  constructor
  · rintro ⟨w, hw, a, ha, hrep⟩
    let s : ℝ := ∑ v ∈ V, w v
    have hs0 : 0 ≤ s := Finset.sum_nonneg hw
    have hs : 0 < s := by
      by_contra! h
      have he : s = 0 := le_antisymm h hs0
      have hz : ∀ v ∈ V, w v = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hw).mp he
      have hv : a • x.val = 0 := by
        rw [← hrep]
        exact Finset.sum_eq_zero (fun v hv => by rw [hz v hv, zero_smul])
      exact smul_ne_zero ha.ne' x.val_ne_zero hv
    let b : GeodesicSphere n → ℝ := fun v => w v / s
    have hb : ∀ v ∈ V, 0 ≤ b v := fun v hv => div_nonneg (hw v hv) hs.le
    have hbs : ∑ v ∈ V, b v = 1 := by
      simp only [b, ← Finset.sum_div]
      exact div_self hs.ne'
    have hvec : ∑ v ∈ V, b v • v.val = (a / s) • x.val := by
      calc
        _ = s⁻¹ • ∑ v ∈ V, w v • v.val := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro v _
          simp only [b, div_eq_mul_inv, smul_smul, mul_comm]
        _ = (a / s) • x.val := by
          rw [hrep, smul_smul]
          congr 1
          ring
    have hm := V.centerMass_mem_convexHull
      (s := GeodesicSphere.val '' (V : Set (GeodesicSphere n)))
      (z := GeodesicSphere.val) hb (by rw [hbs]; exact zero_lt_one)
      (fun v hv => ⟨v, hv, rfl⟩)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hbs, hvec] at hm
    refine ⟨(a / s) • x.val, hm, s / a, div_pos hs ha, ?_⟩
    rw [smul_smul]
    have he : s / a * (a / s) = 1 := by field_simp
    rw [he, one_smul]
  · rintro ⟨y, hy, t, ht, hxy⟩
    have hy' : y ∈ convexHull ℝ
        ((V.image GeodesicSphere.val : Finset (E (n + 1))) : Set (E (n + 1))) := by
      simpa only [Finset.coe_image] using hy
    obtain ⟨b, hb, _, hvec⟩ := Finset.mem_convexHull'.mp hy'
    have hinj : ∀ u ∈ V, ∀ v ∈ V,
        GeodesicSphere.val u = GeodesicSphere.val v → u = v :=
      fun _ _ _ _ h => GeodesicSphere.ext h
    rw [Finset.sum_image hinj] at hvec
    refine ⟨fun v => b v.val, ?_, t⁻¹, inv_pos.mpr ht, ?_⟩
    · intro v hv
      exact hb _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    · rw [hvec, hxy, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

theorem modelEquiv_mem_hull_iff (κ : Geometry) (n : ℕ)
    (V : Finset (Model κ n)) (x : Model κ n) :
    modelEquiv κ n x ∈ ArchivePLGeometry.hull κ.toArchive n
      (V.image (modelEquiv κ n)) ↔ x ∈ hull κ n (V : Set (Model κ n)) := by
  classical
  cases κ with
  | euclidean =>
    simp only [modelEquiv, Geometry.toArchive, ArchivePLGeometry.hull, hull,
      Equiv.coe_refl, id_eq, Finset.image_id]
  | hyperbolic =>
    change modelEquiv .hyperbolic n x ∈ BrehmApprox.hyperbolicCell
      (V.image (modelEquiv .hyperbolic n)) ↔
      x.val ∈ convexHull ℝ (Subtype.val '' (V : Set (Model .hyperbolic n)))
    rw [BrehmApprox.mem_hyperbolicCell_iff_klein_mem_convexHull, klein_modelEquiv]
    have he :
        (((V.image (modelEquiv .hyperbolic n)).image
          BrehmApprox.HyperbolicSpace.klein : Finset (E n)) : Set (E n)) =
        Subtype.val '' (V : Set (Model .hyperbolic n)) := by
      rw [Finset.coe_image, Finset.coe_image, Set.image_image]
      congr 1
      funext z
      exact klein_modelEquiv z
    rw [he]
  | spherical =>
    change modelEquiv .spherical n x ∈ BrehmApprox.sphericalCell
      (V.image (modelEquiv .spherical n)) ↔
      ∃ y ∈ convexHull ℝ (Subtype.val '' (V : Set (Model .spherical n))),
        ∃ t : ℝ, 0 < t ∧ x.val = t • y
    rw [sphericalCell_mem_iff_convexHull]
    simp only [Finset.coe_image, Set.image_image]
    rfl

theorem modelEquiv_image_hull (κ : Geometry) (n : ℕ)
    (V : Finset (Model κ n)) :
    modelEquiv κ n '' hull κ n (V : Set (Model κ n)) =
      ArchivePLGeometry.hull κ.toArchive n (V.image (modelEquiv κ n)) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (modelEquiv_mem_hull_iff κ n V x).mpr hx
  · intro hy
    refine ⟨(modelEquiv κ n).symm y, ?_, (modelEquiv κ n).apply_symm_apply y⟩
    apply (modelEquiv_mem_hull_iff κ n V _).mp
    simpa only [Equiv.apply_symm_apply] using hy

end PLGeometry
