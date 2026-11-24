module

public import BrehmApprox.PiecewiseConsequences
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Preservation of the lengths of continuous curves

A short map which locally preserves distance from each fixed point preserves
the extended variation of every continuous curve on an interval. The proof
uses continuous induction and the signed variation of the image curve. Thus
it also applies to curves of infinite length, and no finite subdivision of the
curve by polyhedral pieces is assumed.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace BrehmApprox

universe u v
variable {P : Type u} [MetricSpace P] {X : Type v} [MetricSpace X]
variable {f : P → X}

/-- Local radial distance preservation bounds endpoint distance by the actual
extended variation of the image curve. -/
theorem edist_le_image_variation_of_locally_dist_eq
    (hf : Continuous f)
    (hlocal : ∀ p : P, ∀ᶠ q in 𝓝 p, dist (f q) (f p) = dist q p)
    (γ : ℝ → P) {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b)) :
    edist (γ a) (γ b) ≤ eVariationOn (f ∘ γ) (Icc a b) := by
  by_cases htop : eVariationOn (f ∘ γ) (Icc a b) = ∞
  · simp [htop]
  have hvar : BoundedVariationOn (f ∘ γ) (Icc a b) := htop
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hfg : ContinuousOn (f ∘ γ) (Icc a b) := hf.comp_continuousOn hγ
  let v : ℝ → ℝ := variationOnFromTo (f ∘ γ) (Icc a b) a
  have hvc : ContinuousOn v (Icc a b) := by
    intro t ht
    exact (hvar.continuousWithinAt_variationOnFromTo_iff ha ht).mpr (hfg t ht)
  let S : Set ℝ := {t | dist (γ a) (γ t) ≤ v t}
  have hclosed : IsClosed (S ∩ Icc a b) := by
    convert isClosed_Icc.isClosed_le
      (continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ)) hvc using 1
    ext t
    simp only [S, Set.mem_inter_iff, Set.mem_ofPred_eq, Function.comp_apply]
    exact and_comm
  have haS : a ∈ S := by
    simp [S, v, variationOnFromTo.self]
  have hbS : b ∈ S := by
    apply hclosed.mem_of_ge_of_forall_exists_gt haS hab
    intro t ht
    have htmem : t ∈ Icc a b := ⟨ht.2.1, ht.2.2.le⟩
    have hrad : ∀ᶠ s in 𝓝[>] t, dist (f (γ s)) (f (γ t)) = dist (γ s) (γ t) := by
      rw [← nhdsWithin_Ioc_eq_nhdsGT ht.2.2]
      exact ((hγ t htmem).eventually (hlocal (γ t))).filter_mono
        (nhdsWithin_mono t (show Ioc t b ⊆ Icc a b from
          fun s hs => ⟨ht.2.1.trans hs.1.le, hs.2⟩))
    have hright : ∀ᶠ s in 𝓝[>] t, s ∈ Ioc t b := Ioc_mem_nhdsGT ht.2.2
    obtain ⟨s, hs, heq⟩ := (hright.and hrad).exists
    have hsmem : s ∈ Icc a b := ⟨ht.2.1.trans hs.1.le, hs.2⟩
    have hstep : dist (γ t) (γ s) ≤ variationOnFromTo (f ∘ γ) (Icc a b) t s := by
      rw [variationOnFromTo.eq_of_le _ _ hs.1.le]
      have hd := (hvar.mono (inter_subset_left (s := Icc a b) (t := Icc t s))).dist_le
        (show t ∈ Icc a b ∩ Icc t s from ⟨htmem, le_rfl, hs.1.le⟩)
        (show s ∈ Icc a b ∩ Icc t s from ⟨hsmem, hs.1.le, le_rfl⟩)
      calc
        dist (γ t) (γ s) = dist (γ s) (γ t) := dist_comm _ _
        _ = dist (f (γ s)) (f (γ t)) := heq.symm
        _ = dist (f (γ t)) (f (γ s)) := dist_comm _ _
        _ ≤ _ := hd
    have hadd := variationOnFromTo.add hvar.locallyBoundedVariationOn ha htmem hsmem
    have htri := dist_triangle (γ a) (γ t) (γ s)
    have htS : dist (γ a) (γ t) ≤ v t := ht.1
    refine ⟨s, ?_, hs⟩
    change dist (γ a) (γ s) ≤ v s
    dsimp only [v] at htS ⊢
    linarith
  have hdist : dist (γ a) (γ b) ≤ (eVariationOn (f ∘ γ) (Icc a b)).toReal := by
    simpa only [S, Set.mem_ofPred_eq, v, variationOnFromTo.eq_of_le _ _ hab,
      inter_self] using hbS
  rw [edist_dist, ← ENNReal.ofReal_toReal hvar]
  exact ENNReal.ofReal_le_ofReal hdist

/-- Local radial isometry and global shortness preserve the full extended
variation on every order-convex parameter set, including infinite variation. -/
theorem eVariationOn_comp_eq_of_locally_dist_eq
    (hf : LipschitzWith 1 f)
    (hlocal : ∀ p : P, ∀ᶠ q in 𝓝 p, dist (f q) (f p) = dist q p)
    (γ : ℝ → P) {s : Set ℝ} (hs : OrdConnected s) (hγ : ContinuousOn γ s) :
    eVariationOn (f ∘ γ) s = eVariationOn γ s := by
  apply le_antisymm
  · simpa using hf.lipschitzOnWith.comp_eVariationOn_le (mapsTo_univ γ s)
  · apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    calc
      (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
          ∑ i ∈ Finset.range n,
            eVariationOn (f ∘ γ) (Icc (u i) (u (i + 1))) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [edist_comm]
        exact edist_le_image_variation_of_locally_dist_eq hf.continuous hlocal γ
          (hu (Nat.le_succ i)) (hγ.mono (hs.out (hus i) (hus (i + 1))))
      _ = eVariationOn (f ∘ γ) (Icc (u 0) (u n)) := eVariationOn.sum' _ hu
      _ ≤ eVariationOn (f ∘ γ) s := eVariationOn.mono _ (hs.out (hus 0) (hus n))

namespace PolyhedralPiecewiseIsometry

variable {Good : (X → X) → Prop} {M : PolytopeModel X Good} {q : P → X}

/-- Every constructed short polyhedral piecewise isometry preserves lengths
of all continuous curves, with length expressed by `eVariationOn`. -/
theorem eVariationOn_comp_eq (hPL : PolyhedralPiecewiseIsometry M q f)
    (hf : LipschitzWith 1 f) (γ : ℝ → P) {s : Set ℝ}
    (hs : OrdConnected s) (hγ : ContinuousOn γ s) :
    eVariationOn (f ∘ γ) s = eVariationOn γ s :=
  eVariationOn_comp_eq_of_locally_dist_eq hf hPL.eventually_dist_eq γ hs hγ

/-- The usual closed-interval formulation of preservation of curve length. -/
theorem eVariationOn_comp_Icc_eq (hPL : PolyhedralPiecewiseIsometry M q f)
    (hf : LipschitzWith 1 f) (γ : ℝ → P) (a b : ℝ)
    (hγ : ContinuousOn γ (Icc a b)) :
    eVariationOn (f ∘ γ) (Icc a b) = eVariationOn γ (Icc a b) :=
  hPL.eVariationOn_comp_eq hf γ ordConnected_Icc hγ

end PolyhedralPiecewiseIsometry
end BrehmApprox
