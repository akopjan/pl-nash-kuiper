module

public import BrehmApprox.AffineArrangement

/-!
# The first face met by a segment

A segment leaving a finite intersection of affine halfspaces first meets
one of their bounding hyperplanes. The proof takes a minimum of the
explicit intersection parameters, and records the whole initial segment.
-/

@[expose] public section
noncomputable section

open Set Classical

namespace BrehmApprox

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

local instance firstAffineHitDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem exists_first_affine_halfspace_hit (L : ι → E →ₗ[ℝ] ℝ) (c : ι → ℝ)
    (p q : E) (hp : ∀ i, L i p < c i) (hq : ∃ i, c i < L i q) :
    ∃ y ∈ segment ℝ p q, (∀ i, L i y ≤ c i) ∧ (∃ i, L i y = c i) ∧
      ∀ x ∈ segment ℝ p q, (∀ i, L i x ≤ c i) → x ∈ segment ℝ p y := by
  let J : Finset ι := Finset.univ.filter (fun i => c i < L i q)
  have hJ : J.Nonempty := by
    obtain ⟨i, hi⟩ := hq
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let t : ι → ℝ := fun i => (c i - L i p) / (L i q - L i p)
  obtain ⟨i, hi, hmin⟩ := J.exists_min_image t hJ
  have hiq := (Finset.mem_filter.mp hi).2
  have hden : 0 < L i q - L i p := by linarith [hp i]
  have ht0 : 0 < t i := div_pos (sub_pos.mpr (hp i)) hden
  have ht1 : t i < 1 := by
    dsimp [t]
    rw [div_lt_one hden]
    linarith
  let y : E := (1 - t i) • p + t i • q
  have hyseg : y ∈ segment ℝ p q :=
    ⟨1 - t i, t i, (sub_pos.mpr ht1).le, ht0.le, by ring, rfl⟩
  have hy (j : ι) : L j y ≤ c j := by
    change L j ((1 - t i) • p + t i • q) ≤ c j
    rw [map_add, map_smul, map_smul]
    change (1 - t i) * L j p + t i * L j q ≤ c j
    by_cases hjq : c j < L j q
    · have hdenj : 0 < L j q - L j p := by linarith [hp j]
      have hm := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjq⟩)
      have hm' := (le_div_iff₀ hdenj).mp hm
      nlinarith
    · have hqle : L j q ≤ c j := le_of_not_gt hjq
      have h₁ := mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hp j).le)
      have h₂ := mul_nonneg ht0.le (sub_nonneg.mpr hqle)
      nlinarith
  have hye : L i y = c i := by
    change L i ((1 - t i) • p + t i • q) = c i
    rw [map_add, map_smul, map_smul]
    change (1 - t i) * L i p + t i * L i q = c i
    have htden : t i * (L i q - L i p) = c i - L i p :=
      div_mul_cancel₀ _ hden.ne'
    nlinarith
  refine ⟨y, hyseg, hy, ⟨i, hye⟩, ?_⟩
  intro x hx hcuts
  obtain ⟨a, b, ha, hb, hab, hrep⟩ := hx
  have hbx : b ≤ t i := by
    apply (le_div_iff₀ hden).mpr
    have hlin := congrArg (L i) hrep
    simp only [map_add, map_smul, smul_eq_mul] at hlin
    have hsum := congrArg (fun z : ℝ => z * L i p) hab
    nlinarith [hcuts i]
  have hbr0 : 0 ≤ b / t i := div_nonneg hb ht0.le
  have hbr1 : b / t i ≤ 1 := (div_le_one ht0).mpr hbx
  refine ⟨1 - b / t i, b / t i, sub_nonneg.mpr hbr1, hbr0, by ring, ?_⟩
  have hcoeff : (1 - b / t i) + (b / t i) * (1 - t i) = a := by
    have hcancel : b / t i * t i = b := div_mul_cancel₀ _ ht0.ne'
    nlinarith
  calc
    (1 - b / t i) • p + (b / t i) • y =
        ((1 - b / t i) + (b / t i) * (1 - t i)) • p + ((b / t i) * t i) • q := by
      dsimp [y]
      module
    _ = a • p + b • q := by rw [hcoeff, div_mul_cancel₀ _ ht0.ne']
    _ = x := hrep

end BrehmApprox
