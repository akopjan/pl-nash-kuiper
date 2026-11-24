module

public import BrehmApprox.SphericalCells
public import BrehmApprox.LexicographicTriangulation
public import BrehmApprox.FiniteGramIsometry

/-!
# Barycentric realization of a spherical simplex

Normalized positive barycentric coordinates give a homeomorphism from the
standard simplex to the spherical hull of an independent unit-vector family.
Gram matrices determine the metric in these coordinates.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.SphericalBarycentric

variable {ι : Type*} [Fintype ι] {n : ℕ}

local instance sphericalBarycentricDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

abbrev Weights (ι : Type*) [Fintype ι] := Pulling.simplexWeights ι

def vector (v : ι → GeodesicSphere n) (w : ι → ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  ∑ i, w i • (v i).val

theorem continuous_vector (v : ι → GeodesicSphere n) : Continuous (vector v) := by
  unfold vector
  fun_prop

theorem vector_ne_zero (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) (w : Weights ι) : vector v w.val ≠ 0 := by
  intro hz
  have hzero : ∀ i, w.val i = 0 := (Fintype.linearIndependent_iff.mp hv) w.val hz
  have hs := w.property.2
  simp only [hzero, Finset.sum_const_zero] at hs
  norm_num at hs

def point (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) (w : Weights ι) : GeodesicSphere n :=
  GeodesicSphere.normalizeVector (vector v w.val) (vector_ne_zero v hv w)

@[simp] theorem point_val (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) (w : Weights ι) :
    (point v hv w).val = NormedSpace.normalize (vector v w.val) := rfl

theorem continuous_point (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) : Continuous (point v hv) :=
  GeodesicSphere.continuous_normalizeVector _
    ((continuous_vector v).comp continuous_subtype_val) (vector_ne_zero v hv)

theorem vertex_injective (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) : Function.Injective v := by
  intro i j hij
  exact hv.injective (congrArg GeodesicSphere.val hij)

theorem point_injective (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) : Function.Injective (point v hv) := by
  intro w z heq
  have he := congrArg GeodesicSphere.val heq
  change ‖vector v w.val‖⁻¹ • vector v w.val = ‖vector v z.val‖⁻¹ • vector v z.val at he
  have he' : (∑ i, (‖vector v w.val‖⁻¹ * w.val i) • (v i).val) =
      ∑ i, (‖vector v z.val‖⁻¹ * z.val i) • (v i).val := by
    simpa only [vector, Finset.smul_sum, smul_smul] using he
  have hcoeff : (fun i => ‖vector v w.val‖⁻¹ * w.val i) =
      (fun i => ‖vector v z.val‖⁻¹ * z.val i) :=
    hv.fintypeLinearCombination_injective he'
  have hs : ‖vector v w.val‖⁻¹ = ‖vector v z.val‖⁻¹ := by
    have hh := congrArg (fun a : ι → ℝ => ∑ i, a i) hcoeff
    simpa only [← Finset.mul_sum, w.property.2, z.property.2, mul_one] using hh
  apply Subtype.ext
  funext i
  have hh := congrFun hcoeff i
  rw [← hs] at hh
  exact mul_left_cancel₀ (inv_ne_zero (norm_ne_zero_iff.mpr (vector_ne_zero v hv w))) hh

theorem point_mem (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) (w : Weights ι) :
    point v hv w ∈ sphericalCell (Finset.univ.image v) := by
  let a : GeodesicSphere n → ℝ := fun x => if h : ∃ i, v i = x then w.val h.choose else 0
  have ha (i : ι) : a (v i) = w.val i := by
    have hi : ∃ j, v j = v i := ⟨i, rfl⟩
    simp only [a, dite_eq_left hi]
    exact congrArg w.val (vertex_injective v hv hi.choose_spec)
  refine ⟨a, ?_, ‖vector v w.val‖, norm_pos_iff.mpr (vector_ne_zero v hv w), ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [ha]
    exact w.property.1 i
  · rw [Finset.sum_image (fun i _ j _ hij => vertex_injective v hv hij)]
    simp only [ha]
    exact (NormedSpace.norm_smul_normalize (vector v w.val)).symm

theorem range_point (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) :
    Set.range (point v hv) = sphericalCell (Finset.univ.image v) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨w, rfl⟩
    exact point_mem v hv w
  · intro x hx
    obtain ⟨a, ha, c, hc, hrep⟩ := hx
    rw [Finset.sum_image (fun i _ j _ hij => vertex_injective v hv hij)] at hrep
    have hai (i : ι) : 0 ≤ a (v i) := ha _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    let s : ℝ := ∑ i, a (v i)
    have hs : 0 < s := by
      have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => hai i)
      apply lt_of_le_of_ne hs0
      intro heq
      have hz : ∀ i, a (v i) = 0 := by
        have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hai i)).mp heq.symm
        exact fun i => hh i (Finset.mem_univ i)
      have hzero : c • x.val = 0 := by
        rw [← hrep]
        simp only [hz, zero_smul, Finset.sum_const_zero]
      exact smul_ne_zero hc.ne' x.val_ne_zero hzero
    let w : Weights ι := ⟨fun i => a (v i) / s,
      ⟨fun i => div_nonneg (hai i) hs.le, by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        exact mul_inv_cancel₀ hs.ne'⟩⟩
    have hw : vector v w.val = (c / s) • x.val := by
      calc
        vector v w.val = s⁻¹ • ∑ i, a (v i) • (v i).val := by
          simp only [vector, w, div_eq_mul_inv, Finset.smul_sum, smul_smul, mul_comm]
        _ = (c / s) • x.val := by rw [hrep, smul_smul]; congr 1; ring
    refine ⟨w, ?_⟩
    apply GeodesicSphere.ext
    rw [point_val, hw, NormedSpace.normalize_smul_of_pos (div_pos hc hs),
      NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val]

/-- The usual barycentric simplex and its spherical realization are homeomorphic. -/
def homeomorph (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) :
    Weights ι ≃ₜ sphericalCell (Finset.univ.image v) := by
  let : CompactSpace (Weights ι) := isCompact_iff_compactSpace.mp Pulling.isCompact_simplexWeights
  let f : Weights ι → sphericalCell (Finset.univ.image v) :=
    fun w => ⟨point v hv w, point_mem v hv w⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      exact point_injective v hv (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ Set.range (point v hv) := by
        rw [range_point]
        exact x.property
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, Subtype.ext hw⟩
  let e := Equiv.ofBijective f hbij
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) ((continuous_point v hv).subtype_mk _)

@[simp] theorem homeomorph_apply (v : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val)) (w : Weights ι) :
    (homeomorph v hv w).val = point v hv w := rfl

/-- Equal Gram matrices give the same spherical metric in barycentric coordinates. -/
theorem point_dist_eq_of_gram (v u : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val))
    (hu : LinearIndependent ℝ (fun i => (u i).val))
    (hgram : ∀ i j, ⟪(v i).val, (v j).val⟫_ℝ = ⟪(u i).val, (u j).val⟫_ℝ)
    (w z : Weights ι) :
    dist (point v hv w) (point v hv z) = dist (point u hu w) (point u hu z) := by
  obtain ⟨r, hr⟩ := exists_ambient_gram_isometry (fun i => (v i).val)
    (fun i => (u i).val) hv hgram
  have hp (a : Weights ι) : GeodesicSphere.mapEquiv r (point v hv a) = point u hu a := by
    apply GeodesicSphere.ext
    change r (NormedSpace.normalize (vector v a.val)) = NormedSpace.normalize (vector u a.val)
    have hvect : r (vector v a.val) = vector u a.val := by
      simp only [vector, map_sum, map_smul, hr]
    rw [NormedSpace.normalize, map_smul, ← r.norm_map (vector v a.val), hvect]
    rfl
  rw [← hp w, ← hp z, (GeodesicSphere.mapEquiv r).dist_eq]

end BrehmApprox.SphericalBarycentric
