module

public import BrehmApprox.SphericalGnomonic

/-!
# Spherical polytope neighborhoods from gnomonic coordinates

This file identifies finite positive spherical hulls with Euclidean convex
hulls in a genuine gnomonic chart, then transports the finite-dimensional
polytope neighborhood theorem back to the round sphere.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace GeodesicSphere

variable {n : ℕ}

/-- The point of the hemisphere represented by a tangent coordinate. -/
def gnomonicPoint (p : GeodesicSphere n) (z : tangentPlane p) : GeodesicSphere n :=
  (gnomonicInverse p z).val

@[simp]
lemma gnomonicPoint_val (p : GeodesicSphere n) (z : tangentPlane p) :
    (gnomonicPoint p z).val = NormedSpace.normalize (p.val + z.val) := rfl

lemma gnomonicPoint_mem (p : GeodesicSphere n) (z : tangentPlane p) :
    gnomonicPoint p z ∈ openHemisphere p := (gnomonicInverse p z).property

lemma gnomonicPoint_injective (p : GeodesicSphere n) : Function.Injective (gnomonicPoint p) := by
  intro z w h
  apply (gnomonicHomeomorph p).symm.injective
  exact Subtype.ext h

lemma continuous_gnomonicPoint (p : GeodesicSphere n) : Continuous (gnomonicPoint p) :=
  continuous_subtype_val.comp (continuous_gnomonicInverse p)

lemma isOpenMap_gnomonicPoint (p : GeodesicSphere n) : IsOpenMap (gnomonicPoint p) :=
  (isOpen_openHemisphere p).isOpenMap_subtype_val.comp (gnomonicHomeomorph p).symm.isOpenMap

/-- The positive normalizing scale of a tangent affine point. -/
def gnomonicScale (p : GeodesicSphere n) (z : tangentPlane p) : ℝ := ‖p.val + z.val‖

lemma gnomonicScale_pos (p : GeodesicSphere n) (z : tangentPlane p) :
    0 < gnomonicScale p z := norm_pos_iff.mpr (pole_add_tangent_ne_zero p z)

@[simp]
lemma gnomonicScale_smul_point (p : GeodesicSphere n) (z : tangentPlane p) :
    gnomonicScale p z • (gnomonicPoint p z).val = p.val + z.val :=
  NormedSpace.norm_smul_normalize _

end GeodesicSphere

namespace BrehmApprox

open GeodesicSphere

variable {n : ℕ}

/-- Lift a finite set of gnomonic coordinates to spherical vertices. -/
def chartVertices (p : GeodesicSphere n) (Q : Finset (tangentPlane p)) :
    Finset (GeodesicSphere n) := by
  classical
  exact Q.image (gnomonicPoint p)

lemma chartVertices_hemisphere (p : GeodesicSphere n) (Q : Finset (tangentPlane p)) :
    InOpenHemisphere (chartVertices p Q) := by
  classical
  refine ⟨p, ?_⟩
  intro v hv
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  exact gnomonicPoint_mem p z

/-- Central projection takes positive spherical hulls to ordinary convex hulls. -/
lemma gnomonicPoint_mem_cell_iff (p : GeodesicSphere n) (Q : Finset (tangentPlane p))
    (z : tangentPlane p) :
    gnomonicPoint p z ∈ sphericalCell (chartVertices p Q) ↔
      z ∈ convexHull ℝ (Q : Set (tangentPlane p)) := by
  classical
  constructor
  · intro hx
    obtain ⟨w, hw, a, ha, hrep⟩ := hx
    rw [chartVertices, Finset.sum_image (gnomonicPoint_injective p).injOn] at hrep
    let α : tangentPlane p → ℝ := fun q => w (gnomonicPoint p q) * (gnomonicScale p q)⁻¹
    let c : ℝ := a * (gnomonicScale p z)⁻¹
    have hc : 0 < c := mul_pos ha (inv_pos.mpr (gnomonicScale_pos p z))
    have hα : ∀ q ∈ Q, 0 ≤ α q := by
      intro q hq
      exact mul_nonneg (hw _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
        (inv_nonneg.mpr (gnomonicScale_pos p q).le)
    have hvec : ∑ q ∈ Q, α q • (p.val + q.val) = c • (p.val + z.val) := by
      simpa only [α, c, gnomonicScale, gnomonicPoint_val,
        NormedSpace.normalize, smul_smul] using hrep
    have hsum : ∑ q ∈ Q, α q = c := by
      have hi := congrArg (fun v => inner ℝ p.val v) hvec
      simpa only [inner_sum, inner_smul_right, inner_pole_add_tangent, mul_one] using hi
    have hzsum : ∑ q ∈ Q, α q • q.val = c • z.val := by
      have hi := hvec
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum] at hi
      exact add_left_cancel hi
    apply Finset.mem_convexHull'.mpr
    refine ⟨fun q => α q / c, fun q hq => div_nonneg (hα q hq) hc.le, ?_, ?_⟩
    · simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, hsum, mul_inv_cancel₀ hc.ne']
    · apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      calc
        (∑ q ∈ Q, (α q / c) • q.val) = c⁻¹ • ∑ q ∈ Q, α q • q.val := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro q _
          simp only [div_eq_mul_inv, smul_smul, mul_comm]
        _ = c⁻¹ • (c • z.val) := congrArg (fun v => c⁻¹ • v) hzsum
        _ = z.val := by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  · intro hz
    obtain ⟨μ, hμ, hsum, hvec⟩ := Finset.mem_convexHull'.mp hz
    let w : GeodesicSphere n → ℝ := fun x =>
      if hx : x ∈ openHemisphere p then
        μ (gnomonic p ⟨x, hx⟩) * gnomonicScale p (gnomonic p ⟨x, hx⟩)
      else 0
    have hwpoint (q : tangentPlane p) :
        w (gnomonicPoint p q) = μ q * gnomonicScale p q := by
      dsimp [w]
      rw [dite_eq_left (gnomonicPoint_mem p q)]
      change μ (gnomonic p (gnomonicInverse p q)) *
        gnomonicScale p (gnomonic p (gnomonicInverse p q)) = _
      rw [gnomonic_gnomonicInverse]
    have hw : ∀ v ∈ chartVertices p Q, 0 ≤ w v := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      rw [hwpoint]
      exact mul_nonneg (hμ q hq) (gnomonicScale_pos p q).le
    refine ⟨w, hw, gnomonicScale p z, gnomonicScale_pos p z, ?_⟩
    rw [chartVertices, Finset.sum_image (gnomonicPoint_injective p).injOn]
    simp_rw [hwpoint, mul_smul, gnomonicScale_smul_point, smul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
    have hvec' := congrArg (fun q : tangentPlane p => q.val) hvec
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hvec'
    rw [hvec']

lemma sphericalCell_chartVertices_eq_image (p : GeodesicSphere n)
    (Q : Finset (tangentPlane p)) :
    sphericalCell (chartVertices p Q) =
      gnomonicPoint p '' convexHull ℝ (Q : Set (tangentPlane p)) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hp : ∀ v ∈ chartVertices p Q, 0 < inner ℝ p.val v.val := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      exact gnomonicPoint_mem p q
    have hxin : x ∈ openHemisphere p := sphericalCell_inner_pos _ p hp hx
    let z : tangentPlane p := gnomonic p ⟨x, hxin⟩
    have heq : gnomonicPoint p z = x :=
      congrArg Subtype.val (gnomonicInverse_gnomonic p ⟨x, hxin⟩)
    exact ⟨z, (gnomonicPoint_mem_cell_iff p Q z).mp (heq.symm ▸ hx), heq⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (gnomonicPoint_mem_cell_iff p Q z).mpr hz

/-- Project a finite hemispherical vertex set into tangent coordinates. -/
def projectVertices (p : GeodesicSphere n) (V : Finset (GeodesicSphere n))
    (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val) : Finset (tangentPlane p) := by
  classical
  exact V.attach.image (fun v => gnomonic p ⟨v.val, hp v.val v.property⟩)

@[simp]
lemma chartVertices_projectVertices (p : GeodesicSphere n) (V : Finset (GeodesicSphere n))
    (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val) :
    chartVertices p (projectVertices p V hp) = V := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    have heq : gnomonicPoint p (gnomonic p ⟨u.val, hp u.val u.property⟩) = u.val :=
      congrArg Subtype.val (gnomonicInverse_gnomonic p ⟨u.val, hp u.val u.property⟩)
    rw [heq]
    exact u.property
  · intro hv
    refine Finset.mem_image.mpr ⟨gnomonic p ⟨v, hp v hv⟩, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_attach _ _, rfl⟩
    · exact congrArg Subtype.val (gnomonicInverse_gnomonic p ⟨v, hp v hv⟩)

/-- Membership in an arbitrary hemispherical cell in its actual central chart. -/
lemma gnomonicInverse_mem_cell_iff (p : GeodesicSphere n) (V : Finset (GeodesicSphere n))
    (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val) (z : tangentPlane p) :
    (gnomonicInverse p z).val ∈ sphericalCell V ↔
      z ∈ convexHull ℝ (projectVertices p V hp : Set (tangentPlane p)) := by
  simpa only [chartVertices_projectVertices, gnomonicPoint] using
    gnomonicPoint_mem_cell_iff p (projectVertices p V hp) z

lemma gnomonic_mem_convexHull_iff (p : GeodesicSphere n) (V : Finset (GeodesicSphere n))
    (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val) (x : openHemisphere p) :
    gnomonic p x ∈ convexHull ℝ (projectVertices p V hp : Set (tangentPlane p)) ↔
      x.val ∈ sphericalCell V := by
  simpa only [gnomonicInverse_gnomonic] using
    (gnomonicInverse_mem_cell_iff p V hp (gnomonic p x)).symm

/-- Every open neighborhood of a compact hemispherical spherical polytope
contains a slightly larger hemispherical spherical polytope whose interior
contains the original one. -/
theorem exists_sphericalCell_neighborhood (V : Finset (GeodesicSphere n))
    (hV : InOpenHemisphere V) {U : Set (GeodesicSphere n)}
    (hU : IsOpen U) (hVU : sphericalCell V ⊆ U) :
    ∃ W : Finset (GeodesicSphere n), InOpenHemisphere W ∧
      sphericalCell V ⊆ interior (sphericalCell W) ∧ sphericalCell W ⊆ U := by
  classical
  obtain ⟨p, hp⟩ := hV
  let Q : Finset (tangentPlane p) := projectVertices p V hp
  let K : Set (tangentPlane p) := convexHull ℝ (Q : Set (tangentPlane p))
  let T : Set (tangentPlane p) := (gnomonicPoint p) ⁻¹' U
  have hKcompact : IsCompact K := Q.finite_toSet.isCompact_convexHull ℝ
  have hKconvex : Convex ℝ K := convex_convexHull ℝ _
  have hTopen : IsOpen T := hU.preimage (continuous_gnomonicPoint p)
  have hKT : K ⊆ T := by
    intro z hz
    apply hVU
    have hcell := (gnomonicPoint_mem_cell_iff p Q z).mpr hz
    simpa only [Q, chartVertices_projectVertices] using hcell
  obtain ⟨R, hKR, hRT⟩ :=
    hKconvex.exists_subset_interior_convexHull_finset_of_isCompact hKcompact
      (hTopen.mem_nhdsSet.mpr hKT)
  refine ⟨chartVertices p R, chartVertices_hemisphere p R, ?_, ?_⟩
  · have hO : IsOpen (gnomonicPoint p '' interior (convexHull ℝ (R : Set (tangentPlane p)))) :=
      isOpenMap_gnomonicPoint p _ isOpen_interior
    have hsub : gnomonicPoint p '' interior (convexHull ℝ (R : Set (tangentPlane p))) ⊆
        sphericalCell (chartVertices p R) := by
      rintro _ ⟨z, hz, rfl⟩
      exact (gnomonicPoint_mem_cell_iff p R z).mpr (interior_subset hz)
    have hVimage : sphericalCell V = gnomonicPoint p '' K := by
      have h := sphericalCell_chartVertices_eq_image p Q
      simpa only [Q, chartVertices_projectVertices] using h
    rw [hVimage]
    exact (Set.image_mono hKR).trans (hO.subset_interior_iff.mpr hsub)
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := (sphericalCell_chartVertices_eq_image p R) ▸ hx
    exact hRT hz

end BrehmApprox
