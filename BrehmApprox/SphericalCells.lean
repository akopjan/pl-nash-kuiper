module

public import BrehmApprox.SphericalRigidity
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# Compact hemispherical cells

A finite hemispherical spherical cell is the continuous image of an ordinary
finite-dimensional standard simplex under normalization of its barycenter.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeodesicSphere

variable {n : ℕ}

/-- Normalize a nonzero ambient vector to a point of the round sphere. -/
def normalizeVector (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ≠ 0) :
    GeodesicSphere n :=
  ⟨NormedSpace.normalize v, NormedSpace.norm_normalize hv⟩

@[simp]
theorem normalizeVector_val (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ≠ 0) :
    (normalizeVector v hv).val = NormedSpace.normalize v := rfl

/-- Normalization is continuous for a continuous family of nonzero vectors. -/
theorem continuous_normalizeVector {T : Type*} [TopologicalSpace T]
    (f : T → EuclideanSpace ℝ (Fin (n + 1))) (hf : Continuous f)
    (hn : ∀ x, f x ≠ 0) : Continuous (fun x => normalizeVector (f x) (hn x)) := by
  have hv : Continuous (fun x => NormedSpace.normalize (f x)) :=
    (hf.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hn x))).smul hf
  have hc : Continuous (fun x =>
      (⟨NormedSpace.normalize (f x), by
        simpa using NormedSpace.norm_normalize (hn x)⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    hv.subtype_mk _
  exact (continuous_unitSphereEquiv n).comp hc

end GeodesicSphere

namespace BrehmApprox

variable {n : ℕ}

/-- The Euclidean barycenter of finitely many spherical vertices. -/
def sphericalBaryVector (V : Finset (GeodesicSphere n))
    (t : Convexity.StdSimplex ℝ V) : EuclideanSpace ℝ (Fin (n + 1)) :=
  ∑ v : V, t.weights v • v.val.val

lemma continuous_sphericalBaryVector (V : Finset (GeodesicSphere n)) :
    Continuous (sphericalBaryVector V) := by
  unfold sphericalBaryVector
  exact continuous_finsetSum _ (fun v _ =>
    (Convexity.StdSimplex.continuous_weights_apply ℝ v).smul continuous_const)

lemma inner_sphericalBaryVector_pos (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (t : Convexity.StdSimplex ℝ V) :
    0 < inner ℝ p.val (sphericalBaryVector V t) := by
  have ht : ∃ v : V, 0 < t.weights v := by
    by_contra! h
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun v _ => h v)
    rw [t.total_of_fintype] at hs
    norm_num at hs
  obtain ⟨v, hv⟩ := ht
  unfold sphericalBaryVector
  rw [inner_sum]
  simp_rw [inner_smul_right]
  apply Finset.sum_pos'
  · intro u _
    exact mul_nonneg (t.weights_nonneg u) (hp u.val u.property).le
  · exact ⟨v, Finset.mem_univ v, mul_pos hv (hp v.val v.property)⟩

lemma sphericalBaryVector_ne_zero (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (t : Convexity.StdSimplex ℝ V) : sphericalBaryVector V t ≠ 0 := by
  intro hzero
  have hpos := inner_sphericalBaryVector_pos V p hp t
  rw [hzero, inner_zero_right] at hpos
  exact lt_irrefl _ hpos

/-- The normalization map from a finite standard simplex onto a spherical cell. -/
def sphericalBarycenter (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (t : Convexity.StdSimplex ℝ V) : GeodesicSphere n :=
  GeodesicSphere.normalizeVector (sphericalBaryVector V t)
    (sphericalBaryVector_ne_zero V p hp t)

lemma continuous_sphericalBarycenter (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val) :
    Continuous (sphericalBarycenter V p hp) :=
  GeodesicSphere.continuous_normalizeVector _ (continuous_sphericalBaryVector V) _

lemma sphericalBarycenter_mem (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (t : Convexity.StdSimplex ℝ V) : sphericalBarycenter V p hp t ∈ sphericalCell V := by
  classical
  let w : GeodesicSphere n → ℝ :=
    fun v => if hv : v ∈ V then t.weights ⟨v, hv⟩ else 0
  have hw : ∀ v ∈ V, 0 ≤ w v := by
    intro v hv
    simp only [w, dite_eq_left hv]
    exact t.weights_nonneg ⟨v, hv⟩
  have hsum : ∑ v ∈ V, w v • v.val = sphericalBaryVector V t := by
    rw [← Finset.sum_coe_sort]
    unfold sphericalBaryVector
    apply Finset.sum_congr rfl
    intro v _
    simp only [w, dite_eq_left v.property]
  refine ⟨w, hw, ‖sphericalBaryVector V t‖,
    norm_pos_iff.mpr (sphericalBaryVector_ne_zero V p hp t), ?_⟩
  rw [hsum]
  exact (NormedSpace.norm_smul_normalize (sphericalBaryVector V t)).symm

lemma sphericalCell_subset_range_barycenter (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val) :
    sphericalCell V ⊆ Set.range (sphericalBarycenter V p hp) := by
  classical
  intro x hx
  obtain ⟨w, hw, a, ha, hrep⟩ := hx
  let s : ℝ := ∑ v ∈ V, w v
  have hnorm : ‖∑ v ∈ V, w v • v.val‖ ≤ s := by
    calc
      _ ≤ ∑ v ∈ V, ‖w v • v.val‖ := norm_sum_le _ _
      _ = s := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [norm_smul, v.norm_val, Real.norm_eq_abs, abs_of_nonneg (hw v hv), mul_one]
  rw [hrep, norm_smul, x.norm_val, Real.norm_eq_abs, abs_of_pos ha, mul_one] at hnorm
  have hs : 0 < s := ha.trans_le hnorm
  let t : Convexity.StdSimplex ℝ V :=
    { weights := Finsupp.equivFunOnFinite.symm (fun v : V => w v.val / s)
      nonneg := by
        intro v
        exact div_nonneg (hw v.val v.property) hs.le
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        change ∑ v : V, w v.val / s = 1
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_coe_sort]
        exact mul_inv_cancel₀ hs.ne' }
  have hb : sphericalBaryVector V t = (a / s) • x.val := by
    change (∑ v : V, (w v.val / s) • v.val.val) = (a / s) • x.val
    calc
      _ = s⁻¹ • ∑ v : V, w v.val • v.val.val := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro v _
        simp only [div_eq_mul_inv, smul_smul, mul_comm]
      _ = s⁻¹ • (a • x.val) := by
        have heq : (∑ v : V, w v.val • v.val.val) = a • x.val :=
          (Finset.sum_coe_sort V (fun v => w v • v.val)).trans hrep
        exact congrArg (fun z => s⁻¹ • z) heq
      _ = (a / s) • x.val := by rw [smul_smul]; congr 1; ring
  refine ⟨t, ?_⟩
  apply GeodesicSphere.ext
  change NormedSpace.normalize (sphericalBaryVector V t) = x.val
  rw [hb, NormedSpace.normalize_smul_of_pos (div_pos ha hs),
    NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val]

lemma sphericalCell_eq_range_barycenter (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val) :
    sphericalCell V = Set.range (sphericalBarycenter V p hp) := by
  apply Set.Subset.antisymm (sphericalCell_subset_range_barycenter V p hp)
  rintro _ ⟨t, rfl⟩
  exact sphericalBarycenter_mem V p hp t

/-- A finite spherical cell contained in an open hemisphere is compact. -/
theorem isCompact_sphericalCell (V : Finset (GeodesicSphere n)) (hV : InOpenHemisphere V) :
    IsCompact (sphericalCell V) := by
  obtain ⟨p, hp⟩ := hV
  rw [sphericalCell_eq_range_barycenter V p hp]
  exact isCompact_range (continuous_sphericalBarycenter V p hp)

theorem isClosed_sphericalCell (V : Finset (GeodesicSphere n)) (hV : InOpenHemisphere V) :
    IsClosed (sphericalCell V) :=
  (isCompact_sphericalCell V hV).isClosed

/-- Every point of the spherical cell stays in the same open hemisphere as
its vertices. -/
theorem sphericalCell_inner_pos (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    {x : GeodesicSphere n} (hx : x ∈ sphericalCell V) :
    0 < inner ℝ p.val x.val := by
  obtain ⟨t, rfl⟩ := sphericalCell_subset_range_barycenter V p hp hx
  change 0 < inner ℝ p.val (NormedSpace.normalize (sphericalBaryVector V t))
  rw [NormedSpace.normalize, inner_smul_right]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (sphericalBaryVector_ne_zero V p hp t)))
    (inner_sphericalBaryVector_pos V p hp t)

/-- The domain of a finite spherical piecewise isometry is compact. -/
theorem SphericalPLOn.isCompact {A : Set (GeodesicSphere n)}
    {f : GeodesicSphere n → GeodesicSphere n} (hf : SphericalPLOn A f) : IsCompact A := by
  obtain ⟨C, hA, hC⟩ := hf
  rw [hA]
  exact C.isCompact_biUnion (fun V hV => isCompact_sphericalCell V (hC V hV).1)

end BrehmApprox
