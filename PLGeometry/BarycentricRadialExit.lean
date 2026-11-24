module

public import PLGeometry.BarycentricPolytopes

/-!
# A radial endpoint in an opposite face

In standard barycentric coordinates, the minimum ratio of the two weight
vectors finds a face beyond a given point which does not contain the apex.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators

namespace ArchivePLGeometry.Barycentric

variable {ι : Type*} [Fintype ι]

local instance barycentricRadialExitDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem exists_radial_endpoint {σ : Finset ι} {a x : ι → ℝ}
    (ha : a ∈ weightsOn σ) (hx : x ∈ weightsOn σ) (hxa : x ≠ a) :
    ∃ i ∈ σ, 0 < a i ∧ ∃ y ∈ weightsOn (σ.erase i), x ∈ segment ℝ a y := by
  let J : Finset ι := σ.filter (fun i => 0 < a i)
  have hJ : J.Nonempty := by
    have hs : 0 < ∑ i, a i := by rw [ha.1.2]; norm_num
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => ha.1.1 i)).mp hs
    have hiσ : i ∈ σ := by
      by_contra hh
      rw [ha.2 i hh] at hi
      exact lt_irrefl 0 hi
    exact ⟨i, Finset.mem_filter.mpr ⟨hiσ, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := J.exists_min_image (fun i => x i / a i) hJ
  obtain ⟨hiσ, hai⟩ := Finset.mem_filter.mp hi
  let r : ℝ := x i / a i
  let k : ι → ℝ := fun j => x j - r * a j
  have hr0 : 0 ≤ r := div_nonneg (hx.1.1 i) hai.le
  have hk (j : ι) : 0 ≤ k j := by
    by_cases haj : 0 < a j
    · have hjσ : j ∈ σ := by
        by_contra hh
        rw [ha.2 j hh] at haj
        exact lt_irrefl 0 haj
      exact sub_nonneg.mpr ((le_div_iff₀ haj).mp
        (hmin j (Finset.mem_filter.mpr ⟨hjσ, haj⟩)))
    · have haj0 : a j = 0 := le_antisymm (le_of_not_gt haj) (ha.1.1 j)
      simpa only [k, haj0, mul_zero, sub_zero] using hx.1.1 j
  have hki : k i = 0 := by simp [k, r, hai.ne']
  have hksum : ∑ j, k j = 1 - r := by
    simp only [k, Finset.sum_sub_distrib, ← Finset.mul_sum, ha.1.2, hx.1.2, mul_one]
  have hr1 : r ≤ 1 := by
    have hsum : 0 ≤ ∑ j, k j := Finset.sum_nonneg (fun j _ => hk j)
    rw [hksum] at hsum
    linarith
  have hrne : r ≠ 1 := by
    intro hr
    apply hxa
    funext j
    have hle : k j ≤ ∑ l, k l := Finset.single_le_sum (fun l _ => hk l) (Finset.mem_univ j)
    rw [hksum, hr, sub_self] at hle
    have hzero := le_antisymm hle (hk j)
    simpa only [k, hr, one_mul, sub_eq_zero] using hzero
  have hden : 0 < 1 - r := sub_pos.mpr (lt_of_le_of_ne hr1 hrne)
  let y : ι → ℝ := fun j => k j / (1 - r)
  have hy : y ∈ weightsOn (σ.erase i) := by
    refine ⟨⟨fun j => div_nonneg (hk j) hden.le, ?_⟩, ?_⟩
    · dsimp [y]
      rw [← Finset.sum_div, hksum, div_self hden.ne']
    · intro j hj
      by_cases hji : j = i
      · subst j
        simp only [y, hki, zero_div]
      · have hjσ : j ∉ σ := fun h => hj (Finset.mem_erase.mpr ⟨hji, h⟩)
        simp only [y, k, ha.2 j hjσ, hx.2 j hjσ, mul_zero, sub_self, zero_div]
  refine ⟨i, hiσ, hai, y, hy, r, 1 - r, hr0, hden.le, by ring, ?_⟩
  funext j
  change r * a j + (1 - r) * (k j / (1 - r)) = x j
  rw [mul_div_cancel₀ _ hden.ne']
  dsimp [k]
  ring

end ArchivePLGeometry.Barycentric
