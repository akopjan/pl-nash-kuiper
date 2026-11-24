module

public import BrehmApprox.HyperbolicAngularSimplex
public import BrehmApprox.SimplexRadialLink

/-! # Supporting spans and angular faces of hyperbolic simplices -/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.HyperbolicSpace

open RadialLink

variable {n : ℕ}

local instance hyperbolicFaceSpanDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem mem_hyperbolicCell_of_mem_span_subface
    {V W : Finset (HyperbolicSpace n)}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val)) (hWV : W ⊆ V)
    {p : HyperbolicSpace n} (hp : p ∈ hyperbolicCell V)
    (hspan : lift p ∈ Submodule.span ℝ (lift '' (W : Set (HyperbolicSpace n)))) :
    p ∈ hyperbolicCell W := by
  obtain ⟨w, hw, a, ha, hrep⟩ := hp
  have hzero (b : HyperbolicSpace n) (hb : b ∈ V) (hbW : b ∉ W) : w b = 0 := by
    obtain ⟨ℓ, hℓ⟩ := exists_functional_values hV (fun v : V => if v.val = b then 1 else 0)
    have hℓV (v : HyperbolicSpace n) (hv : v ∈ V) :
        ℓ (lift v) = if v = b then 1 else 0 := hℓ ⟨v, hv⟩
    have hker : Submodule.span ℝ (lift '' (W : Set (HyperbolicSpace n))) ≤
        LinearMap.ker ℓ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change ℓ (lift v) = 0
      have hvb : v ≠ b := by
        intro h
        exact hbW (h ▸ hv)
      rw [hℓV v (hWV hv), ite_eq_right hvb]
    have hℓp : ℓ (lift p) = 0 := hker hspan
    have hsum : ℓ (∑ v ∈ V, w v • lift v) = w b := by
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
    ∑ v ∈ W, w v • lift v = ∑ v ∈ V, w v • lift v :=
      Finset.sum_subset hWV (fun v hv hvW => by rw [hzero v hv hvW, zero_smul])
    _ = a • lift p := hrep

theorem not_mem_span_subface
    {V W : Finset (HyperbolicSpace n)}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val)) (hWV : W ⊆ V)
    {p : HyperbolicSpace n} (hp : p ∈ hyperbolicCell V) (hpW : p ∉ hyperbolicCell W) :
    lift p ∉ Submodule.span ℝ (lift '' (W : Set (HyperbolicSpace n))) :=
  fun h => hpW (mem_hyperbolicCell_of_mem_span_subface hV hWV hp h)

/-- Boosted spatial directions from a point to an opposite face are independent. -/
theorem radial_subface_independent
    {V W : Finset (HyperbolicSpace n)}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val)) (hWV : W ⊆ V)
    {p : HyperbolicSpace n} (hp : p ∈ hyperbolicCell V) (hpW : p ∉ hyperbolicCell W) :
    LinearIndependent ℝ (fun v : W => radialVector p v.val) := by
  let e : W ↪ V :=
    { toFun := fun v => ⟨v.val, hWV v.property⟩
      inj' := by intro v w h; exact Subtype.ext (congrArg (fun z : V => z.val) h) }
  have hW : LinearIndependent ℝ (fun v : W => lift v.val) := hV.comp e e.injective
  have hset : Set.range (fun v : W => lift v.val) =
      lift '' (W : Set (HyperbolicSpace n)) := by
    ext z
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  apply linearIndependent_radialVector p ((↑) : W → HyperbolicSpace n) hW
  rw [hset]
  exact not_mem_span_subface hV hWV hp hpW

/-- Coning an opposite face to a point of the original simplex is nondegenerate. -/
theorem insert_independent_of_face_avoidance
    {V W : Finset (HyperbolicSpace n)}
    (hV : LinearIndependent ℝ (fun v : V => lift v.val)) (hWV : W ⊆ V)
    {p : HyperbolicSpace n} (hp : p ∈ hyperbolicCell V) (hpW : p ∉ hyperbolicCell W) :
    LinearIndependent ℝ (fun v : (insert p W : Finset (HyperbolicSpace n)) => lift v.val) := by
  have hpW' : p ∉ (W : Set (HyperbolicSpace n)) := fun h => hpW (mem_hyperbolicCell_of_mem h)
  have hW : LinearIndepOn ℝ lift (W : Set (HyperbolicSpace n)) :=
    (show LinearIndepOn ℝ lift (V : Set (HyperbolicSpace n)) from hV).mono hWV
  change LinearIndepOn ℝ lift ((insert p W : Finset (HyperbolicSpace n)) : Set (HyperbolicSpace n))
  rw [Finset.coe_insert, linearIndepOn_insert hpW']
  exact ⟨hW, not_mem_span_subface hV hWV hp hpW⟩

end BrehmApprox.HyperbolicSpace
