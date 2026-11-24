module

public import BrehmApprox.SphericalFaceSpan

/-! # Positive tangent combinations detect every old spherical face -/

@[expose] public section
noncomputable section

open scoped BigOperators InnerProductSpace

namespace BrehmApprox.SphericalLink

variable {n : ℕ} {J : Type*} [Fintype J]

local instance sphericalRadialSupportDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem linear_zero_on_cell (ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    {V : Finset (GeodesicSphere n)} (hV : ∀ v ∈ V, ℓ v.val = 0)
    {x : GeodesicSphere n} (hx : x ∈ sphericalCell V) : ℓ x.val = 0 := by
  obtain ⟨w, _, c, hc, he⟩ := hx
  have hh := congrArg ℓ he
  rw [map_sum, map_smul] at hh
  have hs : (∑ v ∈ V, ℓ (w v • v.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [map_smul, hV v hv, smul_zero]
  rw [hs] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left hc.ne'

/-- A strictly positive tangent coefficient cannot disappear into a face
which contains both the radial center and the resulting radial point. -/
theorem mem_face_of_positive_tangent_combination
    (V U : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (hUV : U ⊆ V)
    (p q : GeodesicSphere n) (hp : p ∈ sphericalCell U) (hq : q ∈ sphericalCell U)
    (v : J → GeodesicSphere n) (hv : ∀ j, v j ∈ V)
    (w : J → ℝ) (hw : ∀ j, 0 < w j) (a b : ℝ) (hb : 0 < b)
    (hrep : q.val = a • p.val + b • ∑ j, w j • tangentLinear p (v j).val) :
    ∀ j, v j ∈ U := by
  intro j
  by_contra hj
  obtain ⟨ℓ, hℓ⟩ := RadialLink.exists_functional_values hV
    (fun z : V => if z.val = v j then 1 else 0)
  have hℓV (z : GeodesicSphere n) (hz : z ∈ V) :
      ℓ z.val = if z = v j then 1 else 0 := hℓ ⟨z, hz⟩
  have hℓU (z : GeodesicSphere n) (hz : z ∈ U) : ℓ z.val = 0 := by
    have hne : z ≠ v j := fun he => hj (he ▸ hz)
    rw [hℓV z (hUV hz), ite_eq_right hne]
  have hℓp := linear_zero_on_cell ℓ hℓU hp
  have hℓq := linear_zero_on_cell ℓ hℓU hq
  have ht (i : J) : ℓ (tangentLinear p (v i).val) = if v i = v j then 1 else 0 := by
    rw [tangentLinear_apply, map_sub, map_smul, hℓp, smul_zero, sub_zero, hℓV _ (hv i)]
  have hpos : 0 < ∑ i, w i * (if v i = v j then 1 else 0) := by
    apply Finset.sum_pos'
    · intro i _
      split_ifs
      · simpa only [mul_one] using (hw i).le
      · simp only [mul_zero, le_refl]
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      simpa only [ite_true, mul_one] using hw j
  have hh := congrArg ℓ hrep
  simp only [map_add, map_smul, map_sum, hℓp, hℓq, smul_zero, zero_add,
    ht, smul_eq_mul, mul_zero, zero_add] at hh
  exact (mul_pos hb hpos).ne' hh.symm

end BrehmApprox.SphericalLink
