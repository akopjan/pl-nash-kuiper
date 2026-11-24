module

public import BrehmApprox.HyperbolicFaceSpan
public import BrehmApprox.HyperbolicSimplicialCharts

/-!
# Radial links of hyperbolic simplices

The boosted Klein chart converts radial distance to `sinh r / cosh r`.
Consequently a small metric sphere meets a simplex exactly in its angular link.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.HyperbolicLink

open HyperbolicSpace CrossPolytope

variable {n : ℕ}

local instance hyperbolicSimplexLinkDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def frame (p x : HyperbolicSpace (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  klein (boostBy p.point x)

theorem frame_injective (p : HyperbolicSpace (n + 1)) : Function.Injective (frame p) :=
  klein_injective.comp (boostEquiv p.point).injective

@[simp] theorem frame_self (p : HyperbolicSpace (n + 1)) : frame p p = 0 := by
  rw [frame, boostBy_self]
  simp only [klein, smul_zero]

def frameVertices (p : HyperbolicSpace (n + 1)) (V : Finset (HyperbolicSpace (n + 1))) :
    Finset (EuclideanSpace ℝ (Fin (n + 1))) := V.image (frame p)

theorem frame_image_cell (p : HyperbolicSpace (n + 1)) (V : Finset (HyperbolicSpace (n + 1))) :
    frame p '' hyperbolicCell V =
      convexHull ℝ (frameVertices p V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hV : (V.image (boostBy p.point)).image klein = frameVertices p V := by
    ext z
    simp only [frameVertices, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨boostBy p.point v, ⟨v, hv, rfl⟩, rfl⟩
  calc
    frame p '' hyperbolicCell V = klein '' (boostBy p.point '' hyperbolicCell V) := by
      rw [Set.image_image]
      rfl
    _ = convexHull ℝ (frameVertices p V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
      rw [hyperbolicCell_image_boost, klein_image_cell, hV]

theorem mem_cell_iff_frame_mem_hull (p x : HyperbolicSpace (n + 1))
    (V : Finset (HyperbolicSpace (n + 1))) :
    x ∈ hyperbolicCell V ↔
      frame p x ∈ convexHull ℝ (frameVertices p V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  rw [← frame_image_cell p V]
  constructor
  · intro hx
    exact Set.mem_image_of_mem (frame p) hx
  · rintro ⟨y, hy, heq⟩
    exact (frame_injective p heq) ▸ hy

theorem frameVertices_independent (p : HyperbolicSpace (n + 1))
    {V : Finset (HyperbolicSpace (n + 1))}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val)) :
    AffineIndependent ℝ ((↑) : frameVertices p V → EuclideanSpace ℝ (Fin (n + 1))) := by
  have hL := hV.map_injOn (Hyperboloid.boostLinearEquiv p.point).toLinearMap
    (Hyperboloid.boostLinearEquiv p.point).injective.injOn
  have hb : LinearIndependent ℝ (fun v : V => lift (boostBy p.point v.val)) := by
    convert hL using 1
    funext v
    exact lift_boostBy p.point v.val
  have ha := (linearIndependent_lift_iff_affineIndependent_klein
    (fun v : V => boostBy p.point v.val)).mp hb
  have hset : Set.range (fun v : V => klein (boostBy p.point v.val)) =
      (frameVertices p V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    ext z
    simp only [frameVertices, Finset.mem_coe, Finset.mem_image, Set.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hr := ha.range
  change AffineIndependent ℝ
    ((↑) : Set.range (fun v : V => klein (boostBy p.point v.val)) →
      EuclideanSpace ℝ (Fin (n + 1))) at hr
  rw [hset] at hr
  exact hr

def linkVertices (V : Finset (HyperbolicSpace (n + 1))) (p : HyperbolicSpace (n + 1)) :
    Finset (GeodesicSphere n) := RadialLink.linkVertices (frameVertices p V) 0

theorem frameVertices_erase (V : Finset (HyperbolicSpace (n + 1)))
    (p : HyperbolicSpace (n + 1)) :
    frameVertices p (V.erase p) = (frameVertices p V).erase 0 := by
  ext z
  simp only [frameVertices, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨v, ⟨hvp, hv⟩, rfl⟩
    refine ⟨?_, v, hv, rfl⟩
    intro he
    exact hvp (frame_injective p (he.trans (frame_self p).symm))
  · rintro ⟨hz, v, hv, rfl⟩
    refine ⟨v, ⟨?_, hv⟩, rfl⟩
    intro hvp
    exact hz (hvp ▸ frame_self p)

theorem sphereNormalize_frame_of_ne (p v : HyperbolicSpace (n + 1)) (hvp : v ≠ p) :
    sphereNormalize (frame p v) = sphereNormalize (radialVector p v) := by
  have hvec : radialVector p v ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_radialVector]
    exact Real.sinh_pos_iff.mpr (dist_pos.mpr hvp.symm)
  have hpos : 0 < (Hyperboloid.height (boostBy p.point v).point)⁻¹ :=
    inv_pos.mpr (Hyperboloid.height_pos _)
  apply GeodesicSphere.ext
  change (sphereNormalize ((Hyperboloid.height (boostBy p.point v).point)⁻¹ •
    radialVector p v)).val = _
  rw [sphereNormalize_val (smul_ne_zero hpos.ne' hvec), sphereNormalize_val hvec,
    NormedSpace.normalize_smul_of_pos hpos]

/-- The Klein construction gives precisely the normalized boosted edge directions. -/
theorem linkVertices_eq_radial (V : Finset (HyperbolicSpace (n + 1)))
    (p : HyperbolicSpace (n + 1)) :
    linkVertices V p = (V.erase p).image (fun v => sphereNormalize (radialVector p v)) := by
  have he : RadialLink.edgeVectors (frameVertices p V) 0 = frameVertices p (V.erase p) := by
    rw [frameVertices_erase]
    ext z
    simp only [RadialLink.edgeVectors, Finset.mem_image, sub_zero]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  unfold linkVertices RadialLink.linkVertices CrossPolytope.radialVertices
  rw [he]
  ext u
  constructor
  · intro hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨v, hv, (sphereNormalize_frame_of_ne p v
      (Finset.ne_of_mem_erase hv)).symm⟩
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_image.mpr ⟨frame p v,
      Finset.mem_image.mpr ⟨v, hv, rfl⟩,
      sphereNormalize_frame_of_ne p v (Finset.ne_of_mem_erase hv)⟩

theorem linkVertices_simplex {V : Finset (HyperbolicSpace (n + 1))}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val))
    {p : HyperbolicSpace (n + 1)} (hp : p ∈ V) :
    InOpenHemisphere (linkVertices V p) ∧
      LinearIndependent ℝ (fun u : linkVertices V p => u.val.val) := by
  apply RadialLink.linkVertices_simplex (frameVertices_independent p hV)
  exact Finset.mem_image.mpr ⟨p, hp, frame_self p⟩

/-- The point at signed radial distance `r` in the unit direction `u`. -/
def radialPoint (p : HyperbolicSpace (n + 1)) (u : GeodesicSphere n) (r : ℝ) :
    HyperbolicSpace (n + 1) := boostBy (-p.point) (radialLine u.val r)

theorem boost_radialPoint (p : HyperbolicSpace (n + 1)) (u : GeodesicSphere n) (r : ℝ) :
    boostBy p.point (radialPoint p u r) = radialLine u.val r := by
  simpa only [radialPoint, neg_neg] using
    boostBy_neg_inverse (-p.point) (radialLine u.val r)

theorem frame_radialPoint (p : HyperbolicSpace (n + 1)) (u : GeodesicSphere n) (r : ℝ) :
    frame p (radialPoint p u r) = (Real.sinh r / Real.cosh r) • u.val := by
  rw [frame, boost_radialPoint, klein, height_radialLine u.norm_val]
  change (Real.cosh r)⁻¹ • (Real.sinh r • u.val) = _
  rw [smul_smul, div_eq_mul_inv, mul_comm]

theorem radialPoint_dist (p : HyperbolicSpace (n + 1)) (u : GeodesicSphere n)
    {r : ℝ} (hr : 0 ≤ r) : dist (radialPoint p u r) p = r := by
  have h := (isometry_boostBy p.point).dist_eq (radialPoint p u r) p
  rw [boost_radialPoint, boostBy_self] at h
  have hzero : radialLine u.val 0 = (⟨0⟩ : HyperbolicSpace (n + 1)) := by
    apply HyperbolicSpace.ext
    simp only [radialLine, Real.sinh_zero, zero_smul]
  rw [← hzero, radialLine_dist u.norm_val, sub_zero, abs_of_nonneg hr] at h
  exact h.symm

/-- One positive radius works for every smaller concentric sphere. -/
theorem exists_radial_link_radius
    {V : Finset (HyperbolicSpace (n + 1))}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val))
    {p : HyperbolicSpace (n + 1)} (hp : p ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ u : GeodesicSphere n,
      radialPoint p u r ∈ hyperbolicCell V ↔ u ∈ sphericalCell (linkVertices V p) := by
  have hp0 : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ frameVertices p V :=
    Finset.mem_image.mpr ⟨p, hp, frame_self p⟩
  obtain ⟨R, hR, hlink⟩ := RadialLink.exists_radial_link_radius
    (frameVertices_independent p hV) hp0
  have hc : Continuous (fun r : ℝ => Real.sinh r / Real.cosh r) :=
    Real.continuous_sinh.div Real.continuous_cosh (fun r => (Real.cosh_pos r).ne')
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0)) R hR
  refine ⟨δ / 2, by positivity, ?_⟩
  intro r hr hrδ u
  have hratio : 0 < Real.sinh r / Real.cosh r :=
    div_pos (Real.sinh_pos_iff.mpr hr) (Real.cosh_pos r)
  have hbound : Real.sinh r / Real.cosh r ≤ R := by
    have hd : dist r 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; linarith
    have h := hsmall hd
    simpa only [Real.sinh_zero, Real.cosh_zero, zero_div, dist_zero_right,
      Real.norm_eq_abs, abs_of_pos hratio] using h.le
  rw [mem_cell_iff_frame_mem_hull p, frame_radialPoint]
  simpa only [zero_add, linkVertices] using hlink _ hratio hbound u

theorem vertex_not_mem_opposite_face
    {V : Finset (HyperbolicSpace (n + 1))}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val))
    {p : HyperbolicSpace (n + 1)} (hp : p ∈ V) :
    p ∉ hyperbolicCell (V.erase p) := by
  obtain ⟨ℓ, hℓ⟩ := RadialLink.exists_functional_values hV
    (fun v : V => if v.val = p then 1 else 0)
  have hℓp : ℓ (lift p) = 1 := by simpa using hℓ ⟨p, hp⟩
  have hℓv (v : HyperbolicSpace (n + 1)) (hv : v ∈ V.erase p) : ℓ (lift v) = 0 := by
    simpa only [ite_eq_right (Finset.ne_of_mem_erase hv)] using hℓ ⟨v, Finset.mem_of_mem_erase hv⟩
  rintro ⟨w, _, a, ha, hrep⟩
  have h := congrArg ℓ hrep
  rw [map_sum, map_smul, hℓp, smul_eq_mul, mul_one] at h
  have hsum : ∑ v ∈ V.erase p, ℓ (w v • lift v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [map_smul, hℓv v hv, smul_zero]
  rw [hsum] at h
  exact ha.ne' h.symm

/-- The slice radius may also be chosen strictly below the entire opposite face. -/
theorem exists_radial_link_radius_with_boundary
    {V : Finset (HyperbolicSpace (n + 1))}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val))
    {p : HyperbolicSpace (n + 1)} (hp : p ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ x ∈ hyperbolicCell (V.erase p), ρ < dist x p) ∧
      ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ u : GeodesicSphere n,
        radialPoint p u r ∈ hyperbolicCell V ↔ u ∈ sphericalCell (linkVertices V p) := by
  obtain ⟨R, hR, hlink⟩ := exists_radial_link_radius hV hp
  have hclosed : IsClosed (hyperbolicCell (V.erase p)) := (isCompact_hyperbolicCell _).isClosed
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hclosed.isOpen_compl.mem_nhds (vertex_not_mem_opposite_face hV hp))
  refine ⟨min R (δ / 2), lt_min hR (by positivity), ?_, ?_⟩
  · intro x hx
    by_contra hn
    have hd : dist x p < δ := lt_of_le_of_lt
      ((not_lt.mp hn).trans (min_le_right _ _)) (by linarith)
    exact hball hd hx
  · intro r hr hrρ u
    exact hlink r hr (hrρ.trans (min_le_left _ _)) u

end BrehmApprox.HyperbolicLink
