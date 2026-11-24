module

public import PLGeometry.ModelBarycentric
public import BrehmApprox.HyperbolicFoldingGeometry

/-! # Distance comparisons are affine cuts in normalized barycentric coordinates -/

@[expose] public section
noncomputable section

open BrehmApprox
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.ModelBarycentric

variable {ι : Type*} [Fintype ι] {n : ℕ}

def weightedLinearForm (c : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ i, w i * c i
  map_add' w z := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem euclidean_distance_cut (v : ι → EuclideanSpace ℝ (Fin n))
    (a b : EuclideanSpace ℝ (Fin n)) :
    ∃ ℓ : (ι → ℝ) →ₗ[ℝ] ℝ, ∃ c : ℝ, ∀ w x,
      Represents .euclidean n v w x →
      (dist x a ≤ dist x b ↔ ℓ w ≤ c) ∧ (dist x a = dist x b ↔ ℓ w = c) := by
  let ℓ := weightedLinearForm (fun i => 2 * inner ℝ (v i) (b - a))
  refine ⟨ℓ, ‖b‖ ^ 2 - ‖a‖ ^ 2, ?_⟩
  intro w x hrep
  have hlin : ℓ w = 2 * inner ℝ x (b - a) := by
    change ∑ i, w i * (2 * inner ℝ (v i) (b - a)) = _
    change ∑ i, w i • v i = x at hrep
    rw [← hrep, sum_inner, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_left]
    ring
  have ha := norm_sub_sq_real x a
  have hb := norm_sub_sq_real x b
  rw [hlin, inner_sub_right]
  simp only [dist_eq_norm]
  constructor
  · constructor
    · intro h
      nlinarith [sq_le_sq₀ (norm_nonneg (x - a)) (norm_nonneg (x - b)) |>.mpr h]
    · intro h
      apply (sq_le_sq₀ (norm_nonneg (x - a)) (norm_nonneg (x - b))).mp
      nlinarith
  · constructor
    · intro h
      rw [h] at ha
      linarith
    · intro h
      nlinarith [norm_nonneg (x - a), norm_nonneg (x - b)]

theorem spherical_distance_cut (v : ι → GeodesicSphere n) (a b : GeodesicSphere n) :
    ∃ ℓ : (ι → ℝ) →ₗ[ℝ] ℝ, ∃ c : ℝ, ∀ w x,
      Represents .spherical n v w x →
      (dist x a ≤ dist x b ↔ ℓ w ≤ c) ∧ (dist x a = dist x b ↔ ℓ w = c) := by
  let ℓ := weightedLinearForm (fun i => inner ℝ (v i).val (b.val - a.val))
  refine ⟨ℓ, 0, ?_⟩
  intro w x hrep
  obtain ⟨s, hs, hrep⟩ := hrep
  have hlin : ℓ w = s * (inner ℝ x.val b.val - inner ℝ x.val a.val) := by
    change ∑ i, w i * inner ℝ (v i).val (b.val - a.val) = _
    calc
      _ = inner ℝ (∑ i, w i • (v i).val) (b.val - a.val) := by
        simp only [sum_inner, real_inner_smul_left]
      _ = _ := by rw [hrep, real_inner_smul_left, inner_sub_right]
  have hle : dist x a ≤ dist x b ↔ inner ℝ x.val b.val ≤ inner ℝ x.val a.val := by
    have h := Real.strictAntiOn_cos.le_iff_ge
      (show dist x b ∈ Set.Icc 0 Real.pi from ⟨dist_nonneg, GeodesicSphere.dist_le_pi x b⟩)
      (show dist x a ∈ Set.Icc 0 Real.pi from ⟨dist_nonneg, GeodesicSphere.dist_le_pi x a⟩)
    simpa only [GeodesicSphere.cos_dist] using h.symm
  have heq : dist x a = dist x b ↔ inner ℝ x.val a.val = inner ℝ x.val b.val := by
    constructor
    · intro h
      simpa only [GeodesicSphere.cos_dist] using congrArg Real.cos h
    · intro h
      apply Real.strictAntiOn_cos.injOn
        ⟨dist_nonneg, GeodesicSphere.dist_le_pi x a⟩
        ⟨dist_nonneg, GeodesicSphere.dist_le_pi x b⟩
      simpa only [GeodesicSphere.cos_dist] using h
  rw [hlin, hle, heq]
  constructor <;> constructor <;> intro h <;> nlinarith

theorem hyperbolic_distance_cut (v : ι → HyperbolicSpace n) (a b : HyperbolicSpace n) :
    ∃ ℓ : (ι → ℝ) →ₗ[ℝ] ℝ, ∃ c : ℝ, ∀ w x,
      Represents .hyperbolic n v w x →
      (dist x a ≤ dist x b ↔ ℓ w ≤ c) ∧ (dist x a = dist x b ↔ ℓ w = c) := by
  let F := HyperbolicSpace.coshFunctional a - HyperbolicSpace.coshFunctional b
  let ℓ := weightedLinearForm (fun i => F (HyperbolicSpace.lift (v i)))
  refine ⟨ℓ, 0, ?_⟩
  intro w x hrep
  obtain ⟨s, hs, hrep⟩ := hrep
  have hlin : ℓ w = s * (Real.cosh (dist x a) - Real.cosh (dist x b)) := by
    change ∑ i, w i * F (HyperbolicSpace.lift (v i)) = _
    calc
      _ = F (∑ i, w i • HyperbolicSpace.lift (v i)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = _ := by
        rw [hrep, map_smul]
        simp only [F, LinearMap.sub_apply, smul_eq_mul,
          HyperbolicSpace.coshFunctional_lift, dist_comm]
  have hle : dist x a ≤ dist x b ↔ Real.cosh (dist x a) ≤ Real.cosh (dist x b) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]
  have heq : dist x a = dist x b ↔ Real.cosh (dist x a) = Real.cosh (dist x b) :=
    ⟨congrArg Real.cosh, Real.cosh_injOn dist_nonneg dist_nonneg⟩
  rw [hlin, hle, heq]
  constructor <;> constructor <;> intro h <;> nlinarith

/-- The same linear cut records both the closed halfspace and its bisector. -/
theorem exists_distance_cut (κ : Geometry) (n : ℕ) (v : ι → Model κ n)
    (a b : Model κ n) :
    ∃ ℓ : (ι → ℝ) →ₗ[ℝ] ℝ, ∃ c : ℝ, ∀ w x,
      Represents κ n v w x →
      (dist x a ≤ dist x b ↔ ℓ w ≤ c) ∧ (dist x a = dist x b ↔ ℓ w = c) := by
  cases κ with
  | euclidean => exact euclidean_distance_cut v a b
  | spherical => exact spherical_distance_cut v a b
  | hyperbolic => exact hyperbolic_distance_cut v a b

end ArchivePLGeometry.ModelBarycentric
