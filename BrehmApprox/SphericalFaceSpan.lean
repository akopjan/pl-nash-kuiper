module

public import BrehmApprox.SphericalSimplexLink

/-!
# Supporting spans of spherical simplex faces

Within a nondegenerate spherical simplex, the linear span of a face cuts out
exactly that face. An apex outside the face therefore remains independent
of its vertices after tangent projection.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.SphericalLink

open GeodesicSphere CrossPolytope RadialLink

variable {n : ℕ}

local instance sphericalFaceSpanDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem mem_sphericalCell_of_mem_span_subface
    {V W : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (hWV : W ⊆ V)
    {p : GeodesicSphere n} (hp : p ∈ sphericalCell V)
    (hspan : p.val ∈ Submodule.span ℝ (GeodesicSphere.val '' (W : Set (GeodesicSphere n)))) :
    p ∈ sphericalCell W := by
  obtain ⟨w, hw, a, ha, hrep⟩ := hp
  have hzero (b : GeodesicSphere n) (hb : b ∈ V) (hbW : b ∉ W) : w b = 0 := by
    obtain ⟨ℓ, hℓ⟩ := exists_functional_values hV (fun v : V => if v.val = b then 1 else 0)
    have hℓV (v : GeodesicSphere n) (hv : v ∈ V) :
        ℓ v.val = if v = b then 1 else 0 := hℓ ⟨v, hv⟩
    have hker : Submodule.span ℝ (GeodesicSphere.val '' (W : Set (GeodesicSphere n))) ≤
        LinearMap.ker ℓ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change ℓ v.val = 0
      have hvb : v ≠ b := by
        intro h
        exact hbW (h ▸ hv)
      rw [hℓV v (hWV hv), ite_eq_right hvb]
    have hℓp : ℓ p.val = 0 := hker hspan
    have hsum : ℓ (∑ v ∈ V, w v • v.val) = w b := by
      rw [map_sum]
      calc
        _ = ∑ v ∈ V, if v = b then w v else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [map_smul, hℓV v hv]
          by_cases hvb : v = b <;> simp [hvb]
        _ = w b := by simp [hb]
    have hh := congrArg ℓ hrep
    rw [hsum, map_smul, hℓp, smul_zero] at hh
    exact hh
  refine ⟨w, fun v hv => hw v (hWV hv), a, ha, ?_⟩
  calc
    ∑ v ∈ W, w v • v.val = ∑ v ∈ V, w v • v.val :=
      Finset.sum_subset hWV (fun v hv hvW => by rw [hzero v hv hvW, zero_smul])
    _ = a • p.val := hrep

theorem not_mem_span_subface
    {V W : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (hWV : W ⊆ V)
    {p : GeodesicSphere n} (hp : p ∈ sphericalCell V) (hpW : p ∉ sphericalCell W) :
    p.val ∉ Submodule.span ℝ (GeodesicSphere.val '' (W : Set (GeodesicSphere n))) :=
  fun h => hpW (mem_sphericalCell_of_mem_span_subface hV hWV hp h)

/-- Tangent vectors from any point of a simplex to an opposite old face are independent. -/
theorem tangent_subface_independent
    {V W : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (hWV : W ⊆ V)
    {p : GeodesicSphere n} (hp : p ∈ sphericalCell V) (hpW : p ∉ sphericalCell W) :
    LinearIndependent ℝ (fun v : W => tangentLinear p v.val.val) := by
  let e : W ↪ V :=
    { toFun := fun v => ⟨v.val, hWV v.property⟩
      inj' := by intro v w h; exact Subtype.ext (congrArg (fun z : V => z.val) h) }
  have hW : LinearIndependent ℝ (fun v : W => v.val.val) := hV.comp e e.injective
  have hset : Set.range (fun v : W => v.val.val) =
      GeodesicSphere.val '' (W : Set (GeodesicSphere n)) := by
    ext z
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  apply linearIndependent_sub_smul_of_notMem_span (fun v : W => v.val.val) p.val
    (fun v => inner ℝ p.val v.val.val) hW
  rw [hset]
  exact not_mem_span_subface hV hWV hp hpW


/-- Coning an opposite face to any point of the original simplex remains
nondegenerate. -/
theorem insert_independent_of_face_avoidance
    {V W : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (hWV : W ⊆ V)
    {p : GeodesicSphere n} (hp : p ∈ sphericalCell V) (hpW : p ∉ sphericalCell W) :
    LinearIndependent ℝ (fun v : (insert p W : Finset (GeodesicSphere n)) => v.val.val) := by
  have hpW' : p ∉ (W : Set (GeodesicSphere n)) := fun h => hpW (mem_sphericalCell_of_mem h)
  have hW : LinearIndepOn ℝ GeodesicSphere.val (W : Set (GeodesicSphere n)) :=
    (show LinearIndepOn ℝ GeodesicSphere.val (V : Set (GeodesicSphere n)) from hV).mono hWV
  change LinearIndepOn ℝ GeodesicSphere.val ((insert p W : Finset (GeodesicSphere n)) : Set (GeodesicSphere n))
  rw [Finset.coe_insert, linearIndepOn_insert hpW']
  exact ⟨hW, not_mem_span_subface hV hWV hp hpW⟩

end BrehmApprox.SphericalLink
