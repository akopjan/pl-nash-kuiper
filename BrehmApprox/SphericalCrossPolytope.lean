module

public import BrehmApprox.CoordinateSphericalCells
public import BrehmApprox.PullingPolytopeFamily

/-!
# A polyhedral radial section of the sphere

The boundary of the coordinate crosspolytope meets every positive ray once.
Its finite signed facets provide a common affine model in which spherical
finite-motion arrangements can be triangulated compatibly.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.CrossPolytope

open GeodesicSphere CoordinateSphericalCells

variable {n : ℕ}

local instance sphericalCrossPolytopeLocalInstance1 : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
local instance sphericalCrossPolytopeLocalInstance2 : DecidableEq (GeodesicSphere n) := Classical.decEq _

def facetVertices (σ : Fin (n + 1) → Bool) : Finset (EuclideanSpace ℝ (Fin (n + 1))) :=
  Finset.univ.image (fun i => (signedPole σ i).val)

def facet (σ : Fin (n + 1) → Bool) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  convexHull ℝ (facetVertices σ : Set _)

def gauge (z : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := ∑ i, |z i|

def facetLinear (σ : Fin (n + 1) → Bool) : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ where
  toFun z := ∑ i, sign (σ i) * z i
  map_add' z w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a z := by simp [mul_left_comm, Finset.mul_sum]

theorem signedPole_apply (σ : Fin (n + 1) → Bool) (i j : Fin (n + 1)) :
    (signedPole σ i).val j = if i = j then sign (σ i) else 0 := by
  rw [signedPole_val]
  simp only [PiLp.smul_apply, smul_eq_mul, coordinatePole_val, PiLp.single_apply]
  split_ifs <;> simp_all

theorem weighted_signedPole_apply (σ : Fin (n + 1) → Bool)
    (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    Pulling.barycenter (fun i => (signedPole σ i).val) w j = w j * sign (σ j) := by
  have h := weighted_inner Finset.univ σ w j
  simpa only [Pulling.barycenter, Finset.mem_univ, ite_true, coordinatePole_val,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial] using h

theorem facet_mem_iff (σ : Fin (n + 1) → Bool) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    z ∈ facet σ ↔ (∀ i, 0 ≤ sign (σ i) * z i) ∧ facetLinear σ z = 1 := by
  change z ∈ convexHull ℝ (Finset.univ.image (fun i => (signedPole σ i).val) : Set _) ↔ _
  rw [Pulling.convexHull_eq_barycenter_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hcoord (i : Fin (n + 1)) :
        sign (σ i) * Pulling.barycenter (fun j => (signedPole σ j).val) w i = w i := by
      rw [weighted_signedPole_apply]
      calc
        sign (σ i) * (w i * sign (σ i)) = w i * (sign (σ i) * sign (σ i)) := by ring
        _ = w i := by rw [sign_sq, mul_one]
    refine ⟨fun i => by rw [hcoord]; exact hw.1.1 i, ?_⟩
    change (∑ i, sign (σ i) * Pulling.barycenter (fun j => (signedPole σ j).val) w i) = 1
    simpa only [hcoord] using hw.1.2
  · rintro ⟨hpos, hsum⟩
    let w : Fin (n + 1) → ℝ := fun i => sign (σ i) * z i
    refine ⟨w, ⟨⟨hpos, hsum⟩, by simp⟩, ?_⟩
    apply PiLp.ext
    intro i
    rw [weighted_signedPole_apply]
    dsimp [w]
    calc
      (sign (σ i) * z i) * sign (σ i) = z i * (sign (σ i) * sign (σ i)) := by ring
      _ = z i := by rw [sign_sq, mul_one]

theorem abs_eq_sign_mul {b : Bool} {a : ℝ} (h : 0 ≤ sign b * a) : |a| = sign b * a := by
  cases b <;> simp only [sign, Bool.false_eq_true, ite_false, ite_true, one_mul, neg_mul] at h ⊢
  · exact (abs_of_nonpos (by linarith)).trans (by ring)
  · exact abs_of_nonneg h

theorem gauge_eq_one_of_mem_facet {σ : Fin (n + 1) → Bool}
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ facet σ) : gauge z = 1 := by
  obtain ⟨hpos, hsum⟩ := (facet_mem_iff σ z).mp hz
  calc
    gauge z = facetLinear σ z := Finset.sum_congr rfl (fun i _ => abs_eq_sign_mul (hpos i))
    _ = 1 := hsum

theorem nonzero_of_mem_facet {σ : Fin (n + 1) → Bool}
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ facet σ) : z ≠ 0 := by
  intro heq
  have hg := gauge_eq_one_of_mem_facet hz
  simp [heq, gauge] at hg

theorem gauge_nonneg (z : EuclideanSpace ℝ (Fin (n + 1))) : 0 ≤ gauge z :=
  Finset.sum_nonneg (fun _i _ => abs_nonneg _)

theorem gauge_pos {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ≠ 0) : 0 < gauge z := by
  apply lt_of_le_of_ne (gauge_nonneg z)
  intro heq
  apply hz
  apply PiLp.ext
  intro i
  have hi : |z i| ≤ gauge z := by
    change |z i| ≤ ∑ j, |z j|
    exact Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i)
  have hzi : z i = 0 := abs_eq_zero.mp (le_antisymm (by simpa only [← heq] using hi) (abs_nonneg _))
  exact hzi

theorem gauge_smul (a : ℝ) (z : EuclideanSpace ℝ (Fin (n + 1))) : gauge (a • z) = |a| * gauge z := by
  simp [gauge, PiLp.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem exists_facet_of_gauge_eq_one {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : gauge z = 1) : ∃ σ, z ∈ facet σ := by
  let σ : Fin (n + 1) → Bool := fun i => decide (0 ≤ z i)
  have hcoord (i : Fin (n + 1)) : sign (σ i) * z i = |z i| := by
    by_cases hi : 0 ≤ z i
    · simp [σ, sign, hi, abs_of_nonneg hi]
    · simp [σ, sign, hi, abs_of_neg (lt_of_not_ge hi)]
  refine ⟨σ, (facet_mem_iff σ z).mpr ⟨fun i => by rw [hcoord]; exact abs_nonneg _, ?_⟩⟩
  change (∑ i, sign (σ i) * z i) = 1
  simpa only [hcoord, gauge] using hz

theorem facet_isFinitePolytope (σ : Fin (n + 1) → Bool) : IsFinitePolytope (facet σ) :=
  ⟨facetVertices σ, rfl⟩

theorem facet_face_inter (σ τ : Fin (n + 1) → Bool) :
    _root_.IsExtreme ℝ (facet σ) (facet σ ∩ facet τ) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  refine ⟨hx, (facet_mem_iff τ x).mpr ?_⟩
  have hx' := (facet_mem_iff σ x).mp hx
  have hy' := (facet_mem_iff σ y).mp hy
  have hz' := (facet_mem_iff τ (a • x + b • y)).mp hz.2
  have hpos (i : Fin (n + 1)) : 0 ≤ sign (τ i) * x i := by
    have hxi := hx'.1 i
    have hyi := hy'.1 i
    have hzi := hz'.1 i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hzi
    cases hσ : σ i <;> cases hτ : τ i <;>
      simp only [hσ, hτ, sign, Bool.false_eq_true, ite_false, ite_true,
        one_mul, neg_one_mul] at hxi hyi hzi ⊢ <;> nlinarith
  refine ⟨hpos, ?_⟩
  calc
    facetLinear τ x = gauge x := by
      change (∑ i, sign (τ i) * x i) = ∑ i, |x i|
      exact (Finset.sum_congr rfl (fun i _ => abs_eq_sign_mul (hpos i))).symm
    _ = 1 := gauge_eq_one_of_mem_facet hx

def sphereNormalize (z : EuclideanSpace ℝ (Fin (n + 1))) : GeodesicSphere n :=
  if hz : z = 0 then northPole n else normalizeVector z hz

theorem sphereNormalize_val {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ≠ 0) :
    (sphereNormalize z).val = NormedSpace.normalize z := by
  simp only [sphereNormalize, dite_eq_right hz, normalizeVector_val]

def radialSection (x : GeodesicSphere n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (gauge x.val)⁻¹ • x.val

theorem gauge_radialSection (x : GeodesicSphere n) : gauge (radialSection x) = 1 := by
  rw [radialSection, gauge_smul, abs_of_pos (inv_pos.mpr (gauge_pos x.val_ne_zero)),
    inv_mul_cancel₀ (gauge_pos x.val_ne_zero).ne']

theorem sphereNormalize_radialSection (x : GeodesicSphere n) : sphereNormalize (radialSection x) = x := by
  have hg := gauge_pos x.val_ne_zero
  have hnon : radialSection x ≠ 0 := smul_ne_zero (inv_ne_zero hg.ne') x.val_ne_zero
  apply GeodesicSphere.ext
  rw [sphereNormalize_val hnon, radialSection, NormedSpace.normalize_smul_of_pos (inv_pos.mpr hg),
    NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val]

theorem radialSection_sphereNormalize {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : gauge z = 1) : radialSection (sphereNormalize z) = z := by
  have hnon : z ≠ 0 := by intro h; simp [h, gauge] at hz
  rw [radialSection, sphereNormalize_val hnon, NormedSpace.normalize, gauge_smul,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hnon)), hz, mul_one, inv_inv,
    smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnon), one_smul]

theorem sphereNormalize_injOn : Set.InjOn (sphereNormalize (n := n)) {z | gauge z = 1} := by
  intro z hz w hw heq
  have h := congrArg radialSection heq
  simpa only [radialSection_sphereNormalize hz, radialSection_sphereNormalize hw] using h

end BrehmApprox.CrossPolytope
