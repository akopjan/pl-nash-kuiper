module

public import BrehmApprox.EuclideanBarycentricSimplex
public import BrehmApprox.HyperbolicSimplicialCharts

/-!
# Projective geometry in normalized positive coordinates

An injective linear map on homogeneous coordinates preserves positive
cones. On the affine hyperplane of coefficient sum one, this identifies
positive projective hulls with ordinary convex hulls.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox.PositiveBarycentric

variable {ι J V : Type*} [Fintype ι] [Fintype J]
    [AddCommGroup V] [Module ℝ V]

local instance positiveBarycentricDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def mass : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ i, w i
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' _ _ := by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

theorem linearIndependent_of_mass_one (w : J → (ι → ℝ))
    (hw : ∀ j, mass (w j) = 1) (hi : AffineIndependent ℝ w) : LinearIndependent ℝ w := by
  rw [linearIndependent_iff']
  intro s a ha
  have hsum : ∑ j ∈ s, a j = 0 := by
    have hh := congrArg (mass : (ι → ℝ) →ₗ[ℝ] ℝ) ha
    simpa only [map_sum, map_smul, hw, smul_eq_mul, mul_one, map_zero] using hh
  exact hi.eq_zero_of_sum_eq_zero hsum ha

theorem lift_independent (L : (ι → ℝ) →ₗ[ℝ] V) (hL : Function.Injective L)
    (w : J → (ι → ℝ)) (hw : ∀ j, mass (w j) = 1) (hi : AffineIndependent ℝ w)
    (z : J → V) (c : J → ℝ) (hc : ∀ j, c j ≠ 0) (hrep : ∀ j, L (w j) = c j • z j) :
    LinearIndependent ℝ z := by
  have hwi := linearIndependent_of_mass_one w hw hi
  have him := hwi.map' L (LinearMap.ker_eq_bot.mpr hL)
  let a : J → ℝˣ := fun j => Units.mk0 (c j) (hc j)
  have he : (fun j => L (w j)) = a • z := by funext j; exact hrep j
  change LinearIndependent ℝ (fun j => L (w j)) at him
  rw [he, LinearIndependent.units_smul_iff] at him
  exact him

theorem convexHull_iff_positive_lifts
    (L : (ι → ℝ) →ₗ[ℝ] V) (hL : Function.Injective L)
    (w : J → EuclideanBarycentric.Weights ι) (z : J → V)
    (c : J → ℝ) (hc : ∀ j, 0 < c j) (hrep : ∀ j, L (w j).val = c j • z j)
    (a : EuclideanBarycentric.Weights ι) (x : V) (d : ℝ) (hd : 0 < d)
    (hax : L a.val = d • x) :
    a.val ∈ convexHull ℝ (Set.range (fun j => (w j).val)) ↔
      ∃ b : J → ℝ, (∀ j, 0 ≤ b j) ∧ ∃ t : ℝ, 0 < t ∧ ∑ j, b j • z j = t • x := by
  constructor
  · intro ha
    have ha' : a.val ∈ Set.range (EuclideanBarycentric.point (fun j => (w j).val)) := by
      rw [EuclideanBarycentric.range_point]
      exact ha
    obtain ⟨b, hb⟩ := ha'
    refine ⟨fun j => b.val j * c j, fun j => mul_nonneg (b.property.1 j) (hc j).le, d, hd, ?_⟩
    have hh := congrArg L hb
    simpa only [EuclideanBarycentric.point, map_sum, map_smul, hrep, smul_smul, hax] using hh
  · rintro ⟨b, hb, t, ht, hbx⟩
    let e : J → ℝ := fun j => (d / t) * (b j / c j)
    have he0 (j : J) : 0 ≤ e j :=
      mul_nonneg (div_pos hd ht).le (div_nonneg (hb j) (hc j).le)
    have hevec : (∑ j, e j • (w j).val) = a.val := by
      apply hL
      rw [map_sum]
      calc
        ∑ j, L (e j • (w j).val) = (d / t) • ∑ j, b j • z j := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [map_smul, hrep, smul_smul, smul_smul]
          congr 1
          dsimp [e]
          field_simp [(hc j).ne']
        _ = d • x := by rw [hbx, smul_smul, div_mul_cancel₀ _ ht.ne']
        _ = L a.val := hax.symm
    have hesum : ∑ j, e j = 1 := by
      have hh := congrArg (mass : (ι → ℝ) →ₗ[ℝ] ℝ) hevec
      have hm (j : J) : mass (w j).val = 1 := (w j).property.2
      have hma : mass a.val = 1 := a.property.2
      simpa only [map_sum, map_smul, hm, hma, smul_eq_mul, mul_one] using hh
    rw [← EuclideanBarycentric.range_point]
    exact ⟨⟨e, ⟨he0, hesum⟩⟩, hevec⟩

theorem rayCombination_image_iff {X : Type*} (u : J → X) (hu : Function.Injective u)
    (lift : X → V) (x : X) :
    (∃ b : X → ℝ, (∀ z ∈ Finset.univ.image u, 0 ≤ b z) ∧
      ∃ t : ℝ, 0 < t ∧ ∑ z ∈ Finset.univ.image u, b z • lift z = t • lift x) ↔
    (∃ b : J → ℝ, (∀ j, 0 ≤ b j) ∧ ∃ t : ℝ, 0 < t ∧ ∑ j, b j • lift (u j) = t • lift x) := by
  constructor
  · rintro ⟨b, hb, t, ht, he⟩
    refine ⟨fun j => b (u j), fun j => hb _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩), t, ht, ?_⟩
    rw [Finset.sum_image (fun i _ j _ hij => hu hij)] at he
    exact he
  · rintro ⟨b, hb, t, ht, he⟩
    let a : X → ℝ := fun z => if h : ∃ j, u j = z then b h.choose else 0
    have ha (j : J) : a (u j) = b j := by
      have hj : ∃ i, u i = u j := ⟨j, rfl⟩
      simp only [a, dite_eq_left hj]
      exact congrArg b (hu hj.choose_spec)
    refine ⟨a, ?_, t, ht, ?_⟩
    · intro z hz
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
      rw [ha]
      exact hb j
    · rw [Finset.sum_image (fun i _ j _ hij => hu hij)]
      simpa only [ha] using he

theorem homogeneous_mem_convexHull_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : J → E) (x : E) :
    x ∈ convexHull ℝ (Set.range u) ↔
      ∃ b : J → ℝ, (∀ j, 0 ≤ b j) ∧ ∃ t : ℝ, 0 < t ∧
        ∑ j, b j • ((1 : ℝ), u j) = t • ((1 : ℝ), x) := by
  constructor
  · intro hx
    rw [← EuclideanBarycentric.range_point] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨w.val, w.property.1, 1, zero_lt_one, ?_⟩
    rw [one_smul]
    apply Prod.ext
    · change (LinearMap.fst ℝ ℝ E) (∑ j, w.val j • ((1 : ℝ), u j)) = (1 : ℝ)
      simpa only [map_sum, map_smul, LinearMap.fst_apply, smul_eq_mul, mul_one] using w.property.2
    · change (LinearMap.snd ℝ ℝ E) (∑ j, w.val j • ((1 : ℝ), u j)) = x
      simpa only [EuclideanBarycentric.point, map_sum, map_smul, LinearMap.snd_apply] using hw
  · rintro ⟨b, hb, t, ht, he⟩
    have hs := congrArg (LinearMap.fst ℝ ℝ E) he
    have hv := congrArg (LinearMap.snd ℝ ℝ E) he
    simp only [map_sum, map_smul, LinearMap.fst_apply, smul_eq_mul, mul_one] at hs
    simp only [map_sum, map_smul, LinearMap.snd_apply] at hv
    let w : EuclideanBarycentric.Weights J := ⟨fun j => b j / t,
      ⟨fun j => div_nonneg (hb j) ht.le, by rw [← Finset.sum_div, hs, div_self ht.ne']⟩⟩
    rw [← EuclideanBarycentric.range_point]
    refine ⟨w, ?_⟩
    change (∑ j, (b j / t) • u j) = x
    calc
      _ = t⁻¹ • ∑ j, b j • u j := by
        simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv, mul_comm]
      _ = x := by rw [hv, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

end BrehmApprox.PositiveBarycentric
