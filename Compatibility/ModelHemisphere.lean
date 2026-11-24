module

public import Compatibility.Models
public import BrehmApprox.SphericalActiveProjection
public import BrehmApprox.SphericalGnomonic

/-! # Spherical simplex charts lie in an open hemisphere

The original chart axiom preserves the hull of every finite subset. In
particular it excludes antipodal image points: the hull of an antipodal pair
has only two points, whereas the source segment contains its distinct midpoint.
A positive dependence of the vertices would produce such an antipodal pair.
Strict separation of their convex hull from the origin then supplies a pole.
-/

@[expose] public section
noncomputable section

open scoped BigOperators InnerProductSpace

namespace PLGeometry

local instance modelHemisphereDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem spherical_val_ne_neg_self {n : ℕ} (u : GeodesicSphere n) : u.val ≠ -u.val := by
  intro h
  have hz : (2 : ℝ) • u.val = 0 := by
    rw [two_smul]
    calc
      u.val + u.val = -u.val + u.val := congrArg (fun z => z + u.val) h
      _ = 0 := neg_add_cancel u.val
  exact u.val_ne_zero ((smul_eq_zero.mp hz).resolve_left (by norm_num))

theorem sphericalCell_pair_antipodal {n : ℕ} (u v z : GeodesicSphere n)
    (hv : v.val = -u.val) (hz : z ∈ BrehmApprox.sphericalCell {u, v}) :
    z = u ∨ z = v := by
  classical
  have huv : u ≠ v := by
    intro he
    exact spherical_val_ne_neg_self u (by simpa only [← he] using hv)
  obtain ⟨w, _, a, ha, hrep⟩ := hz
  rw [Finset.sum_pair huv, hv, smul_neg, ← sub_eq_add_neg, ← sub_smul] at hrep
  let c : ℝ := (w u - w v) / a
  have hzrep : z.val = c • u.val := by
    calc
      z.val = a⁻¹ • (a • z.val) := by
        rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
      _ = a⁻¹ • ((w u - w v) • u.val) := congrArg (fun r => a⁻¹ • r) hrep.symm
      _ = c • u.val := by
        rw [smul_smul]
        congr 1
        dsimp [c]
        ring
  have hc : |c| = 1 := by
    have hnorm := congrArg norm hzrep
    simpa only [z.norm_val, norm_smul, u.norm_val, Real.norm_eq_abs, mul_one] using hnorm.symm
  have hsq : c ^ 2 = 1 := by nlinarith [sq_abs c]
  have hp : (c - 1) * (c + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with hp | hp
  · left
    apply GeodesicSphere.ext
    have hc1 : c = 1 := by linarith
    simpa only [hc1, one_smul] using hzrep
  · right
    apply GeodesicSphere.ext
    have hcm : c = -1 := by linarith
    simpa only [hcm, neg_one_smul, hv] using hzrep

namespace Simplex

variable {κ : Geometry} {d m : ℕ} {σ : Finset (E m)}

theorem archive_image_hull (S : Simplex κ d m σ)
    (V : Finset (E m)) (hV : (V : Set (E m)) ⊆ cell σ) :
    (fun x => modelEquiv κ d (S.toModel x)) '' convexHull ℝ (V : Set (E m)) =
      ArchivePLGeometry.hull κ.toArchive d
        (V.image (fun x => modelEquiv κ d (S.toModel x))) := by
  classical
  rw [← Set.image_image, S.convex V hV]
  rw [← Finset.coe_image, modelEquiv_image_hull, Finset.image_image]
  rfl

theorem archive_not_antipodal (S : Simplex .spherical d m σ)
    {x y : E m} (hx : x ∈ cell σ) (hy : y ∈ cell σ) :
    (modelEquiv .spherical d (S.toModel x)).val ≠
      -(modelEquiv .spherical d (S.toModel y)).val := by
  classical
  let F : E m → GeodesicSphere d := fun x => modelEquiv .spherical d (S.toModel x)
  have hF : Set.InjOn F (cell σ) := fun _ hx _ hy h =>
    S.injective hx hy ((modelEquiv .spherical d).injective h)
  intro hanti
  have hxy : x ≠ y := by
    intro he
    subst y
    exact spherical_val_ne_neg_self (F x) hanti
  have hpair : ({x, y} : Set (E m)) ⊆ cell σ := by
    intro z hz
    rcases hz with rfl | hz
    · exact hx
    · exact Set.mem_singleton_iff.mp hz ▸ hy
  have hmid : midpoint ℝ x y ∈ convexHull ℝ ({x, y} : Set (E m)) := by
    rw [convexHull_pair]
    exact midpoint_mem_segment x y
  have hmidσ : midpoint ℝ x y ∈ cell σ :=
    convexHull_min hpair (convex_convexHull ℝ _) hmid
  have himg := S.archive_image_hull {x, y} (by simpa using hpair)
  have himg' : F '' convexHull ℝ ({x, y} : Set (E m)) =
      BrehmApprox.sphericalCell {F x, F y} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, Finset.image_insert,
      Finset.image_singleton, ArchivePLGeometry.hull, Geometry.toArchive] using himg
  have hz : F (midpoint ℝ x y) ∈ BrehmApprox.sphericalCell {F x, F y} := by
    rw [← himg']
    exact ⟨midpoint ℝ x y, hmid, rfl⟩
  have hanti' : (F y).val = -(F x).val := by
    change (F x).val = -(F y).val at hanti
    rw [hanti, neg_neg]
  rcases sphericalCell_pair_antipodal (F x) (F y) (F (midpoint ℝ x y)) hanti' hz with he | he
  · exact hxy ((midpoint_eq_left_iff (R := ℝ)).mp (hF hmidσ hx he))
  · exact hxy ((midpoint_eq_right_iff (R := ℝ)).mp (hF hmidσ hy he))

theorem spherical_zero_not_mem_convexHull (S : Simplex .spherical d m σ) :
    (0 : E (d + 1)) ∉ convexHull ℝ
      (GeodesicSphere.val ''
        ((σ.image (fun x => modelEquiv .spherical d (S.toModel x))) :
          Set (GeodesicSphere d))) := by
  classical
  let F : E m → GeodesicSphere d := fun x => modelEquiv .spherical d (S.toModel x)
  let V : Finset (GeodesicSphere d) := σ.image F
  intro hzero
  have hzero' : (0 : E (d + 1)) ∈ convexHull ℝ
      ((V.image GeodesicSphere.val : Finset (E (d + 1))) : Set (E (d + 1))) := by
    simpa only [V, F, Finset.coe_image] using hzero
  obtain ⟨b, hb, hsum, hvec⟩ := Finset.mem_convexHull'.mp hzero'
  have hinj : ∀ u ∈ V, ∀ v ∈ V,
      GeodesicSphere.val u = GeodesicSphere.val v → u = v :=
    fun _ _ _ _ h => GeodesicSphere.ext h
  rw [Finset.sum_image hinj] at hsum hvec
  have hb' : ∀ v ∈ V, 0 ≤ b v.val := fun v hv =>
    hb _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  have hpos : ∃ v ∈ V, 0 < b v.val := by
    by_contra! h
    have hle := Finset.sum_nonpos h
    rw [hsum] at hle
    norm_num at hle
  obtain ⟨v, hv, hvpos⟩ := hpos
  have herase : ∑ u ∈ V.erase v, b u.val • u.val = -(b v.val • v.val) := by
    have hs := Finset.sum_erase_add V (fun u : GeodesicSphere d => b u.val • u.val) hv
    rw [hvec] at hs
    exact eq_neg_of_add_eq_zero_left hs
  have hanti : GeodesicSphere.antipode v ∈ BrehmApprox.sphericalCell (V.erase v) := by
    refine ⟨fun u => b u.val, fun u hu => hb' u (Finset.mem_of_mem_erase hu),
      b v.val, hvpos, ?_⟩
    change (∑ u ∈ V.erase v, b u.val • u.val) = b v.val • (-v.val)
    rw [herase, smul_neg]
  have hantiV : GeodesicSphere.antipode v ∈ BrehmApprox.sphericalCell V :=
    BrehmApprox.sphericalCell_mono (Finset.erase_subset v V) hanti
  have himg := S.archive_image_hull σ (subset_convexHull ℝ (σ : Set (E m)))
  have himg' : F '' cell σ = BrehmApprox.sphericalCell V := himg
  have hantiImage : GeodesicSphere.antipode v ∈ F '' cell σ := by
    rw [himg']
    exact hantiV
  obtain ⟨y, hy, hFy⟩ := hantiImage
  obtain ⟨x, hx, hFx⟩ := Finset.mem_image.mp hv
  have hxσ : x ∈ cell σ := subset_convexHull ℝ _ hx
  apply S.archive_not_antipodal hy hxσ
  change (F y).val = -(F x).val
  rw [hFy, hFx]
  rfl

theorem spherical_hemisphere (S : Simplex .spherical d m σ) :
    BrehmApprox.InOpenHemisphere
      (σ.image (fun x => modelEquiv .spherical d (S.toModel x))) := by
  classical
  let V : Finset (GeodesicSphere d) :=
    σ.image (fun x => modelEquiv .spherical d (S.toModel x))
  by_cases hV : V.Nonempty
  · have hcompact : IsCompact
        (convexHull ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere d)))) := by
      simpa only [Finset.coe_image] using
        (V.image GeodesicSphere.val).finite_toSet.isCompact_convexHull ℝ
    obtain ⟨f, a, hfa, haf⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere d))))
      hcompact.isClosed S.spherical_zero_not_mem_convexHull
    have ha : 0 < a := by simpa only [map_zero] using hfa
    let z : E (d + 1) := (InnerProductSpace.toDual ℝ (E (d + 1))).symm f
    have hzv (v : GeodesicSphere d) (hv : v ∈ V) : 0 < inner ℝ z v.val := by
      rw [InnerProductSpace.toDual_symm_apply]
      exact ha.trans (haf v.val (subset_convexHull ℝ _ ⟨v, hv, rfl⟩))
    have hz : z ≠ 0 := by
      obtain ⟨v, hv⟩ := hV
      intro he
      have hp := hzv v hv
      rw [he, inner_zero_left] at hp
      exact lt_irrefl _ hp
    refine ⟨GeodesicSphere.normalizeVector z hz, ?_⟩
    intro v hv
    change 0 < inner ℝ (NormedSpace.normalize z) v.val
    rw [NormedSpace.normalize, inner_smul_left]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hz)) (hzv v hv)
  · refine ⟨GeodesicSphere.northPole d, ?_⟩
    intro v hv
    exact False.elim (hV ⟨v, hv⟩)

theorem spherical_cell_hemisphere (S : Simplex .spherical d m σ) :
    ∃ p : GeodesicSphere d, ∀ x ∈ cell σ,
      0 < inner ℝ p.val (modelEquiv .spherical d (S.toModel x)).val := by
  classical
  obtain ⟨p, hp⟩ := S.spherical_hemisphere
  refine ⟨p, ?_⟩
  intro x hx
  apply BrehmApprox.sphericalCell_inner_pos _ p hp
  have himg := S.archive_image_hull σ (subset_convexHull ℝ (σ : Set (E m)))
  have himg' :
      (fun y => modelEquiv .spherical d (S.toModel y)) '' convexHull ℝ (σ : Set (E m)) =
      BrehmApprox.sphericalCell
        (σ.image (fun y => modelEquiv .spherical d (S.toModel y))) := himg
  rw [← himg']
  exact ⟨x, hx, rfl⟩

end Simplex
end PLGeometry
