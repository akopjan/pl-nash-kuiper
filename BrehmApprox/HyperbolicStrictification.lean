module

public import BrehmApprox.HyperbolicCoordinates

/-!
# Strict approximation of the identity on hyperbolic compact sets

The maps are radial homotheties in genuine Klein coordinates.  Their metric
contraction on bounded sets is proved algebraically, followed by the ordinary
one variable mean value theorem.  No Riemannian or extension axiom is used.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

namespace BrehmApprox

lemma exists_linear_bound_arsinh_mul_sinh {t R : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ L < 1 ∧
      ∀ r ∈ Set.Icc 0 R, Real.arsinh (t * Real.sinh r) ≤ L * r := by
  let D : ℝ → ℝ := fun r => t * Real.cosh r / Real.sqrt (1 + (t * Real.sinh r) ^ 2)
  have hD0 : ∀ r, 0 ≤ D r := by
    intro r
    dsimp [D]
    exact div_nonneg (mul_nonneg ht0 (Real.cosh_pos r).le) (Real.sqrt_nonneg _)
  have hD1 : ∀ r, D r < 1 := by
    intro r
    have hs : 0 < Real.sqrt (1 + (t * Real.sinh r) ^ 2) := by positivity
    have hsq : (Real.sqrt (1 + (t * Real.sinh r) ^ 2)) ^ 2 =
        1 + (t * Real.sinh r) ^ 2 := Real.sq_sqrt (by positivity)
    have ht2 : t ^ 2 < 1 := by nlinarith
    have hdiff : (Real.sqrt (1 + (t * Real.sinh r) ^ 2)) ^ 2 -
        (t * Real.cosh r) ^ 2 = 1 - t ^ 2 := by
      rw [hsq, mul_pow, mul_pow, Real.cosh_sq]
      ring
    have hnum : 0 ≤ t * Real.cosh r := mul_nonneg ht0 (Real.cosh_pos r).le
    dsimp [D]
    apply (div_lt_one hs).mpr
    nlinarith
  have hDc : Continuous D := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro r
      positivity
  obtain ⟨r₀, hr₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hR) hDc.continuousOn
  refine ⟨D r₀, hD0 r₀, hD1 r₀, ?_⟩
  have hderiv : ∀ r ∈ Set.Icc 0 R,
      HasDerivWithinAt (fun s => Real.arsinh (t * Real.sinh s)) (D r) (Set.Icc 0 R) r := by
    intro r hr
    have hh := (Real.hasDerivAt_arsinh (t * Real.sinh r)).comp r
      ((Real.hasDerivAt_sinh r).const_mul t)
    convert hh.hasDerivWithinAt using 1 <;> simp only [D, Function.comp_def, div_eq_mul_inv]; ring
  have hbound : ∀ r ∈ Set.Ico 0 R, ‖D r‖ ≤ D r₀ := by
    intro r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hD0 r)]
    exact hmax ⟨hr.1, hr.2.le⟩
  intro r hr
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound r hr
  have hg0 : 0 ≤ Real.arsinh (t * Real.sinh r) :=
    Real.arsinh_nonneg_iff.mpr (mul_nonneg ht0 (Real.sinh_nonneg_iff.mpr hr.1))
  simpa only [Real.sinh_zero, mul_zero, Real.arsinh_zero, sub_zero,
    Real.norm_eq_abs, abs_of_nonneg hg0] using hh

namespace HyperbolicSpace

variable {n : ℕ}

lemma coshDist_fromKlein {p q : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    Hyperboloid.coshDist (fromKlein p).point (fromKlein q).point =
      (1 - ⟪p, q⟫_ℝ) /
        (Real.sqrt (1 - ‖p‖ ^ 2) * Real.sqrt (1 - ‖q‖ ^ 2)) := by
  rw [Hyperboloid.coshDist, height_fromKlein hp, height_fromKlein hq]
  simp only [fromKlein, real_inner_smul_left, real_inner_smul_right]
  field_simp

lemma coshDist_eq_klein (x y : HyperbolicSpace n) :
    Hyperboloid.coshDist x.point y.point =
      (1 - ⟪klein x, klein y⟫_ℝ) /
        (Real.sqrt (1 - ‖klein x‖ ^ 2) * Real.sqrt (1 - ‖klein y‖ ^ 2)) := by
  have h := coshDist_fromKlein (norm_klein_lt_one x) (norm_klein_lt_one y)
  simpa only [fromKlein_klein] using h

/-- A radial homothety in Klein coordinates. -/
def shrink (t : ℝ) (x : HyperbolicSpace n) : HyperbolicSpace n :=
  fromKlein (t • klein x)

lemma norm_smul_klein_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : HyperbolicSpace n) : ‖t • klein x‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  calc
    t * ‖klein x‖ ≤ 1 * ‖klein x‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
    _ = ‖klein x‖ := one_mul _
    _ < 1 := norm_klein_lt_one x

private lemma mean_product_le {s u a b d e : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hd2 : d ^ 2 = s + u * a ^ 2) (he2 : e ^ 2 = s + u * b ^ 2) :
    s + u * a * b ≤ d * e := by
  have hl : 0 ≤ s + u * a * b := by positivity
  have hr : 0 ≤ d * e := by positivity
  have hsq : (d * e) ^ 2 - (s + u * a * b) ^ 2 = s * u * (a - b) ^ 2 := by
    rw [mul_pow, hd2, he2]
    ring
  have hnon : 0 ≤ s * u * (a - b) ^ 2 := by positivity
  nlinarith

private lemma scaled_fraction_le {s u a b d e c : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    (hsu : s + u = 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b ≤ 1)
    (hd : 0 < d) (he : 0 < e) (hc : 1 ≤ c)
    (hd2 : d ^ 2 = s + u * a ^ 2) (he2 : e ^ 2 = s + u * b ^ 2) :
    (s + u * a * b * c) / (d * e) ≤ s + u * c := by
  apply (div_le_iff₀ (mul_pos hd he)).mpr
  have hm := mean_product_le hs hu ha hb hd.le he.le hd2 he2
  have hsc : 0 ≤ s + u * c := by positivity
  have hmul := mul_le_mul_of_nonneg_left hm hsc
  have hgap : (s + u * c) * (s + u * a * b) - (s + u * a * b * c) =
      s * u * (c - 1) * (1 - a * b) := by
    have hs' : s = 1 - u := by linarith
    rw [hs']
    ring
  have hn : 0 ≤ s * u * (c - 1) * (1 - a * b) := by positivity
  nlinarith

lemma coshDist_shrink_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x y : HyperbolicSpace n) :
    Hyperboloid.coshDist (shrink t x).point (shrink t y).point - 1 ≤
      t ^ 2 * (Hyperboloid.coshDist x.point y.point - 1) := by
  let a : ℝ := Real.sqrt (1 - ‖klein x‖ ^ 2)
  let b : ℝ := Real.sqrt (1 - ‖klein y‖ ^ 2)
  let d : ℝ := Real.sqrt (1 - ‖t • klein x‖ ^ 2)
  let e : ℝ := Real.sqrt (1 - ‖t • klein y‖ ^ 2)
  let c : ℝ := Hyperboloid.coshDist x.point y.point
  have ha : 0 < a := klein_denominator_pos (norm_klein_lt_one x)
  have hb : 0 < b := klein_denominator_pos (norm_klein_lt_one y)
  have hd : 0 < d := klein_denominator_pos (norm_smul_klein_lt_one ht0 ht1 x)
  have he : 0 < e := klein_denominator_pos (norm_smul_klein_lt_one ht0 ht1 y)
  have ha2 : a ^ 2 = 1 - ‖klein x‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_klein_lt_one x, norm_nonneg (klein x)])
  have hb2 : b ^ 2 = 1 - ‖klein y‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_klein_lt_one y, norm_nonneg (klein y)])
  have hab : a * b ≤ 1 := by
    have ha1 : a ≤ 1 := by nlinarith [sq_nonneg ‖klein x‖]
    have hb1 : b ≤ 1 := by nlinarith [sq_nonneg ‖klein y‖]
    calc
      a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha1 hb.le
      _ = b := one_mul _
      _ ≤ 1 := hb1
  have hd2 : d ^ 2 = (1 - t ^ 2) + t ^ 2 * a ^ 2 := by
    dsimp [d]
    rw [Real.sq_sqrt (by nlinarith [norm_smul_klein_lt_one ht0 ht1 x, norm_nonneg (t • klein x)])]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha2]
    ring
  have he2 : e ^ 2 = (1 - t ^ 2) + t ^ 2 * b ^ 2 := by
    dsimp [e]
    rw [Real.sq_sqrt (by nlinarith [norm_smul_klein_lt_one ht0 ht1 y, norm_nonneg (t • klein y)])]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hb2]
    ring
  have hc : 1 ≤ c := Hyperboloid.one_le_coshDist x.point y.point
  have hcp : 1 - ⟪klein x, klein y⟫_ℝ = a * b * c := by
    dsimp [c]
    rw [coshDist_eq_klein]
    change _ = (a * b) * ((1 - ⟪klein x, klein y⟫_ℝ) / (a * b))
    field_simp [ne_of_gt ha, ne_of_gt hb]
  have hf := scaled_fraction_le (s := 1 - t ^ 2) (u := t ^ 2)
    (a := a) (b := b) (d := d) (e := e) (c := c)
    (by nlinarith) (sq_nonneg t) (by ring) ha.le hb.le hab hd he hc hd2 he2
  have heq : Hyperboloid.coshDist (shrink t x).point (shrink t y).point =
      ((1 - t ^ 2) + t ^ 2 * a * b * c) / (d * e) := by
    rw [shrink, shrink, coshDist_fromKlein
      (norm_smul_klein_lt_one ht0 ht1 x) (norm_smul_klein_lt_one ht0 ht1 y)]
    change (1 - ⟪t • klein x, t • klein y⟫_ℝ) / (d * e) = _
    congr 1
    rw [real_inner_smul_left, real_inner_smul_right]
    nlinarith [hcp]
  rw [heq]
  change _ ≤ t ^ 2 * (c - 1)
  nlinarith

lemma dist_shrink_le_arsinh {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x y : HyperbolicSpace n) :
    dist (shrink t x) (shrink t y) ≤
      2 * Real.arsinh (t * Real.sinh (dist x y / 2)) := by
  have hhalf (r : ℝ) : Real.cosh r - 1 = 2 * Real.sinh (r / 2) ^ 2 := by
    have hh := Real.cosh_two_mul (r / 2)
    rw [show 2 * (r / 2) = r by ring, Real.cosh_sq] at hh
    linarith
  have hc := coshDist_shrink_le ht0 ht1 x y
  rw [← cosh_dist, ← cosh_dist, hhalf, hhalf] at hc
  have hs0 : 0 ≤ Real.sinh (dist (shrink t x) (shrink t y) / 2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hs1 : 0 ≤ t * Real.sinh (dist x y / 2) :=
    mul_nonneg ht0 (Real.sinh_nonneg_iff.mpr (by positivity))
  have hs : Real.sinh (dist (shrink t x) (shrink t y) / 2) ≤
      t * Real.sinh (dist x y / 2) := by nlinarith
  have hh := Real.arsinh_le_arsinh.mpr hs
  rw [Real.arsinh_sinh] at hh
  linarith

lemma shrink_short {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Short (shrink (n := n) t) := by
  intro x y
  have hs : t * Real.sinh (dist x y / 2) ≤ Real.sinh (dist x y / 2) := by
    have hnon : 0 ≤ Real.sinh (dist x y / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
    nlinarith
  have ha := Real.arsinh_le_arsinh.mpr hs
  rw [Real.arsinh_sinh] at ha
  have hd := dist_shrink_le_arsinh ht0 ht1 x y
  linarith

lemma shrink_strict_on_bounded {A : Set (HyperbolicSpace n)} (hA : Bornology.IsBounded A)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ L < 1 ∧
      ∀ x ∈ A, ∀ y ∈ A, dist (shrink t x) (shrink t y) ≤ L * dist x y := by
  obtain ⟨R, hR, hAR⟩ := (Metric.isBounded_iff_exists_ge 0).mp hA
  obtain ⟨L, hL0, hL1, hL⟩ := exists_linear_bound_arsinh_mul_sinh ht0 ht1
    (show 0 ≤ R / 2 by positivity)
  refine ⟨L, hL0, hL1, ?_⟩
  intro x hx y hy
  have hr : dist x y / 2 ∈ Set.Icc 0 (R / 2) := by
    constructor
    · positivity
    · linarith [hAR hx hy]
  have hh := hL (dist x y / 2) hr
  have hd := dist_shrink_le_arsinh ht0 ht1.le x y
  nlinarith

lemma shrink_uniform_approximation {A : Set (HyperbolicSpace n)} (hA : IsCompact A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ x ∈ A, dist (shrink t x) x < ε := by
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun p : ℝ × HyperbolicSpace n => p.1 • klein p.2) '' (Set.Icc 0 1 ×ˢ A)
  have hK : IsCompact K := (isCompact_Icc.prod hA).image
    (continuous_fst.fun_smul (continuous_klein.comp continuous_snd))
  have hKb : K ⊆ Metric.ball 0 1 := by
    rintro p ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right] using norm_smul_klein_lt_one ht.1 ht.2 x
  have hu := hK.uniformContinuousOn_of_continuous (continuousOn_fromKlein.mono hKb)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let s : ℝ := min (δ / 2) (1 / 2)
  let t : ℝ := 1 - s
  have hs : 0 < s := lt_min (by linarith) (by norm_num)
  have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs1 : s ≤ (1 : ℝ) / 2 := min_le_right _ _
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  refine ⟨t, ht0, ht1, ?_⟩
  intro x hx
  have htx : t • klein x ∈ K := ⟨(t, x), ⟨⟨ht0, ht1.le⟩, hx⟩, rfl⟩
  have hxK : klein x ∈ K := by
    refine ⟨(1, x), ⟨⟨zero_le_one, le_rfl⟩, hx⟩, ?_⟩
    simp
  have hdist : dist (t • klein x) (klein x) < δ := by
    have heq : dist (t • klein x) (klein x) = s * ‖klein x‖ := by
      rw [dist_eq_norm]
      rw [show t • klein x - klein x = (t - 1) • klein x by
        simpa only [one_smul] using (sub_smul t (1 : ℝ) (klein x)).symm]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      dsimp [t]
      ring
    rw [heq]
    have hle : s * ‖klein x‖ ≤ s := by
      have hh := mul_le_mul_of_nonneg_left (norm_klein_lt_one x).le hs.le
      simpa using hh
    exact hle.trans_lt hsδ
  have hh := hδu (t • klein x) htx (klein x) hxK hdist
  simpa only [shrink, fromKlein_klein] using hh

/-- Every compact subset of genuine hyperbolic space admits strict contractions
arbitrarily close to its inclusion.  The displayed Lipschitz constant is uniform
on the compact set; the ambient map is also globally short. -/
theorem compact_strictification {A : Set (HyperbolicSpace n)} (hA : IsCompact A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : HyperbolicSpace n → HyperbolicSpace n, ∃ L : ℝ,
      Short g ∧ 0 ≤ L ∧ L < 1 ∧
      (∀ x ∈ A, ∀ y ∈ A, dist (g x) (g y) ≤ L * dist x y) ∧
      ∀ x ∈ A, dist (g x) x < ε := by
  obtain ⟨t, ht0, ht1, hclose⟩ := shrink_uniform_approximation hA hε
  obtain ⟨L, hL0, hL1, hshort⟩ := shrink_strict_on_bounded hA.isBounded ht0 ht1
  exact ⟨shrink t, L, shrink_short ht0 ht1.le, hL0, hL1, hshort, hclose⟩

end HyperbolicSpace
end BrehmApprox
