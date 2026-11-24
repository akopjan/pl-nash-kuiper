module

public import BrehmApprox.Core
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# A continuous finite selection of short maps

The nearest projection to a polytope is locally a selection among projections
to its finitely many faces.  No analytic subdivision of a geodesic is needed:
continuity eliminates, near a point, every candidate having a different value
there.  A one-sided mean-value argument then gives the global metric estimate.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace BrehmApprox

universe u v w
variable {X : Type u} {Y : Type v} {ι : Type w}
variable [MetricSpace X] [MetricSpace Y] [Finite ι]

/-- Near a point of a continuous finite selection, every selected candidate
agrees with the selection at that point as well. -/
theorem finite_selection_eventually_matches
    {s : Set X} {f : X → Y} {F : ι → X → Y} {x : X}
    (hf : ContinuousWithinAt f s x)
    (hF : ∀ i, ContinuousWithinAt (F i) s x) :
    ∀ᶠ y in 𝓝[s] x, ∀ i, f y = F i y → f x = F i x := by
  classical
  apply Filter.eventually_all.2
  intro i
  by_cases h : f x = F i x
  · exact Filter.Eventually.of_forall (fun _ _ => h)
  · have he : ∀ᶠ y in 𝓝[s] x, f y ≠ F i y :=
      (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds h |>
        (hf.prodMk (hF i))
    exact he.mono (fun _ hy heq => (hy heq).elim)

/-- A finite continuous selection of `C`-Lipschitz maps satisfies the sharp
radial estimate in a neighborhood of each point. -/
theorem finite_selection_eventually_dist_le
    {s : Set X} {f : X → Y} {F : ι → X → Y} {C : NNReal} {x : X}
    (hf : ContinuousWithinAt f s x) (hx : x ∈ s)
    (hF : ∀ i, LipschitzOnWith C (F i) s)
    (hsel : ∀ y ∈ s, ∃ i, f y = F i y) :
    ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ C * dist y x := by
  have he := finite_selection_eventually_matches hf
    (fun i => (hF i).continuousOn x hx)
  filter_upwards [he, self_mem_nhdsWithin] with y hy hys
  obtain ⟨i, hi⟩ := hsel y hys
  rw [hi, hy i hi]
  exact (hF i).dist_le_mul y hys x hx

/-- The sharp local radial estimate on a real interval implies the endpoint
estimate.  This remains valid when the active finite piece changes infinitely
often along the interval. -/
theorem dist_endpoints_le_of_local_radial
    {f : ℝ → Y} {a b C : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hloc : ∀ x ∈ Icc a b, ∀ᶠ y in 𝓝[Icc a b] x,
      dist (f y) (f x) ≤ C * dist y x) :
    dist (f b) (f a) ≤ C * (b - a) := by
  let v : ℝ → ℝ := fun t => dist (f t) (f a)
  let B : ℝ → ℝ := fun t => C * (t - a)
  have hv : ContinuousOn v (Icc a b) :=
    continuous_dist.comp_continuousOn (hf.prodMk continuousOn_const)
  have hBa : v a ≤ B a := by simp [v, B]
  have hBc : ContinuousOn B (Icc a b) := by fun_prop
  have hBd : ∀ x ∈ Ico a b, HasDerivWithinAt B C (Ici x) x := by
    intro x _
    simpa only [B, id_eq, mul_one] using
      (((hasDerivAt_id x).sub_const a).const_mul C).hasDerivWithinAt (s := Ici x)
  have hbound : ∀ x ∈ Ico a b, ∀ r, C < r →
      ∃ᶠ y in 𝓝[>] x, slope v x y < r := by
    intro x hx r hr
    have he : ∀ᶠ y in 𝓝[>] x, dist (f y) (f x) ≤ C * dist y x :=
      nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx) (hloc x (Ico_subset_Icc_self hx))
    have hs : ∀ᶠ y in 𝓝[>] x, slope v x y < r := by
      filter_upwards [he, self_mem_nhdsWithin] with y hy hxy
      have hpos : 0 < y - x := sub_pos.mpr hxy
      have hd : dist y x = y - x := by
        rw [Real.dist_eq, abs_of_pos hpos]
      have htri : v y - v x ≤ dist (f y) (f x) := by
        dsimp [v]
        linarith [dist_triangle (f y) (f x) (f a)]
      have hle : slope v x y ≤ C := by
        rw [slope_def_field]
        exact (div_le_iff₀ hpos).2 (by simpa only [hd] using htri.trans hy)
      exact hle.trans_lt hr
    exact hs.frequently
  exact image_le_of_liminf_slope_right_le_deriv_boundary hv hBa hBc hBd hbound
    ⟨hab, le_rfl⟩

/-- Sharp Lipschitz control for a continuous finite selection along a real
interval. -/
theorem finite_selection_lipschitzOn_interval
    {f : ℝ → Y} {F : ι → ℝ → Y} {a b : ℝ} {C : NNReal}
    (hf : ContinuousOn f (Icc a b))
    (hF : ∀ i, LipschitzOnWith C (F i) (Icc a b))
    (hsel : ∀ y ∈ Icc a b, ∃ i, f y = F i y) :
    LipschitzOnWith C f (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this y hy x hx (le_of_not_ge hxy)
  have hsub : Icc x y ⊆ Icc a b :=
    fun z hz => ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
  have h := dist_endpoints_le_of_local_radial hxy (hf.mono hsub) (by
    intro z hz
    exact (finite_selection_eventually_dist_le
      (hf z (hsub hz)) (hsub hz) hF hsel).filter_mono (nhdsWithin_mono z hsub))
  calc
    dist (f x) (f y) = dist (f y) (f x) := dist_comm _ _
    _ ≤ C * (y - x) := h
    _ = C * dist x y := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]

/-- A metric formulation of the global conclusion.  The path hypothesis is
the usual existence of constant-speed shortest paths, written explicitly
rather than postulated as an additional geometric axiom. -/
theorem finite_selection_lipschitz_of_paths
    {f : X → Y} {F : ι → X → Y} {C : NNReal}
    (hpaths : ∀ x y : X, ∃ γ : ℝ → X,
      γ 0 = x ∧ γ 1 = y ∧
      LipschitzOnWith (nndist x y) γ (Icc 0 1))
    (hf : Continuous f) (hF : ∀ i, LipschitzWith C (F i))
    (hsel : ∀ x, ∃ i, f x = F i x) : LipschitzWith C f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := hpaths x y
  have h := finite_selection_lipschitzOn_interval
    (hf.comp_continuousOn hγ.continuousOn)
    (fun i => (hF i).comp_lipschitzOnWith hγ)
    (fun t _ => hsel (γ t))
  have hd := h.dist_le_mul 0 (by norm_num) 1 (by norm_num)
  simpa only [Function.comp_apply, hγ0, hγ1, NNReal.coe_mul,
    coe_nndist, Real.dist_eq, zero_sub, abs_neg, abs_one, mul_one] using hd

/-- In particular, a continuous finite selection on a real normed space has
the very same Lipschitz constant as its candidates. -/
theorem finite_selection_lipschitz_normed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Y} {F : ι → E → Y} {C : NNReal}
    (hf : Continuous f) (hF : ∀ i, LipschitzWith C (F i))
    (hsel : ∀ x, ∃ i, f x = F i x) : LipschitzWith C f := by
  apply finite_selection_lipschitz_of_paths ?_ hf hF hsel
  intro x y
  exact ⟨AffineMap.lineMap x y, AffineMap.lineMap_apply_zero _ _,
    AffineMap.lineMap_apply_one _ _, (lipschitzWith_lineMap x y).lipschitzOnWith⟩

end BrehmApprox
