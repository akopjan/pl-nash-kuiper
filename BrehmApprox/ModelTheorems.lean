module

public import BrehmApprox.Relative
public import BrehmApprox.EuclideanBrehm
public import BrehmApprox.SphericalBrehm
public import BrehmApprox.HyperbolicFiniteSelection
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Concrete approximation theorems in the three model geometries

The finite extension theorems are proved in all three constant-curvature
models. Their kernel dependencies are the standard logical axioms of mathlib.

The metric spaces, their metrics, the geometric polyhedral pieces and finite
determination are defined and proved in the imported files. The conclusions
below concern subsets of the indicated model space. They do not, by themselves,
assert the approximation theorem for an arbitrary abstract polyhedral source.
-/

@[expose] public section

namespace BrehmApprox

/-- Brehm's finite Euclidean extension theorem, with genuine affine-isometric
polyhedral pieces. -/
theorem euclideanBrehm (n : ℕ) :
    FiniteExtension (LocallyEuclideanPL (E := EuclideanSpace ℝ (Fin n))) :=
  euclideanBrehm_proved n

/-- Finite spherical extension, with angular geodesic distance and genuine
orthogonal polyhedral pieces. -/
theorem sphericalBrehm (n : ℕ) :
    FiniteExtension (LocallySphericalPL (n := n)) :=
  sphericalBrehm_proved n

/-- The Akopyan–Tarasov finite extension theorem in hyperbolic space. -/
theorem hyperbolicBrehm (n : ℕ) :
    FiniteExtension (LocallyHyperbolicPL (n := n)) :=
  hyperbolic_finite_extension n

/-- Uniform Euclidean PL approximation on a compact model-space subset,
with exact interpolation of any specified finite set. -/
theorem euclidean_compact_approximation {n : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsCompact W)
    (V : Finset (EuclideanSpace ℝ (Fin n)))
    {u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : ShortOn u (W ∪ (V : Set (EuclideanSpace ℝ (Fin n)))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Short H ∧ LocallyEuclideanPL H ∧
      (∀ v ∈ V, H v = u v) ∧ ∀ x ∈ W, dist (H x) (u x) < ε :=
  compact_model_approximation (euclideanBrehm n) hW V hu hε

/-- Uniform spherical PL approximation on a compact subset of the round
sphere, with exact interpolation of a finite set. -/
theorem spherical_compact_approximation {n : ℕ}
    {W : Set (GeodesicSphere n)} (hW : IsCompact W)
    (V : Finset (GeodesicSphere n)) {u : GeodesicSphere n → GeodesicSphere n}
    (hu : ShortOn u (W ∪ (V : Set (GeodesicSphere n)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : GeodesicSphere n → GeodesicSphere n,
      Short H ∧ LocallySphericalPL H ∧
      (∀ v ∈ V, H v = u v) ∧ ∀ x ∈ W, dist (H x) (u x) < ε :=
  compact_model_approximation (sphericalBrehm n) hW V hu hε

/-- Uniform hyperbolic PL approximation on a compact model-space subset,
with exact interpolation of a finite set. -/
theorem hyperbolic_compact_approximation {n : ℕ}
    {W : Set (HyperbolicSpace n)} (hW : IsCompact W)
    (V : Finset (HyperbolicSpace n)) {u : HyperbolicSpace n → HyperbolicSpace n}
    (hu : ShortOn u (W ∪ (V : Set (HyperbolicSpace n)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : HyperbolicSpace n → HyperbolicSpace n,
      Short H ∧ LocallyHyperbolicPL H ∧
      (∀ v ∈ V, H v = u v) ∧ ∀ x ∈ W, dist (H x) (u x) < ε :=
  compact_model_approximation (hyperbolicBrehm n) hW V hu hε

/-- Relative Euclidean approximation preserving an actual finite Euclidean
piecewise isometry on the whole prescribed polyhedral subset. -/
theorem euclidean_relative_approximation {n : ℕ}
    {A W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsCompact W)
    {g u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hgPL : EuclideanPLOn A g) (hg : ShortOn g A)
    {L δ ρ : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hu : ∀ x ∈ A ∪ W, ∀ y ∈ A ∪ W,
      dist (u x) (u y) ≤ L * dist x y)
    (hδ0 : 0 ≤ δ) (herr : ∀ a ∈ A, dist (g a) (u a) ≤ δ) (hρ : 0 < ρ) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Short H ∧ LocallyEuclideanPL H ∧ (∀ a ∈ A, H a = g a) ∧
      ∀ x ∈ W, dist (H x) (u x) < 2 * δ / (1 - L) + ρ :=
  relative_approximation_linear (euclideanBrehm n) hW
    (determinedOn_euclideanPL hgPL) hg hL0 hL1 hu hδ0 herr hρ

/-- Relative spherical approximation preserving an actual finite piecewise
orthogonal map on a union of hemispherical polyhedral cells. -/
theorem spherical_relative_approximation {n : ℕ}
    {A W : Set (GeodesicSphere n)} (hW : IsCompact W)
    {g u : GeodesicSphere n → GeodesicSphere n}
    (hgPL : SphericalPLOn A g) (hg : ShortOn g A)
    {L δ ρ : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hu : ∀ x ∈ A ∪ W, ∀ y ∈ A ∪ W,
      dist (u x) (u y) ≤ L * dist x y)
    (hδ0 : 0 ≤ δ) (herr : ∀ a ∈ A, dist (g a) (u a) ≤ δ) (hρ : 0 < ρ) :
    ∃ H : GeodesicSphere n → GeodesicSphere n,
      Short H ∧ LocallySphericalPL H ∧ (∀ a ∈ A, H a = g a) ∧
      ∀ x ∈ W, dist (H x) (u x) < 2 * δ / (1 - L) + ρ :=
  relative_approximation_linear (sphericalBrehm n) hW
    (determinedOn_sphericalPL hgPL) hg hL0 hL1 hu hδ0 herr hρ

/-- Relative hyperbolic approximation preserving an actual finite piecewise
hyperbolic isometry on a union of geodesic polyhedral cells. -/
theorem hyperbolic_relative_approximation {n : ℕ}
    {A W : Set (HyperbolicSpace n)} (hW : IsCompact W)
    {g u : HyperbolicSpace n → HyperbolicSpace n}
    (hgPL : HyperbolicPLOn A g) (hg : ShortOn g A)
    {L δ ρ : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hu : ∀ x ∈ A ∪ W, ∀ y ∈ A ∪ W,
      dist (u x) (u y) ≤ L * dist x y)
    (hδ0 : 0 ≤ δ) (herr : ∀ a ∈ A, dist (g a) (u a) ≤ δ) (hρ : 0 < ρ) :
    ∃ H : HyperbolicSpace n → HyperbolicSpace n,
      Short H ∧ LocallyHyperbolicPL H ∧ (∀ a ∈ A, H a = g a) ∧
      ∀ x ∈ W, dist (H x) (u x) < 2 * δ / (1 - L) + ρ :=
  relative_approximation_linear (hyperbolicBrehm n) hW
    (determinedOn_hyperbolicPL hgPL) hg hL0 hL1 hu hδ0 herr hρ

/-- A compact set admits a strict homothety arbitrarily close to the identity.
This proof includes empty and zero-diameter sets and imposes no upper bound on
the requested error. It uses no Brehm axiom. -/
theorem compact_strict_homothety
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ x ∈ K, dist (t • x) x < ε := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let s : ℝ := min (1 / 2) (ε / (2 * R))
  have hs : 0 < s := by dsimp [s]; positivity
  have hs_half : s ≤ 1 / 2 := min_le_left _ _
  have hs_error : s * R ≤ ε / 2 := by
    have hlim : s ≤ ε / (2 * R) := min_le_right _ _
    have hprod := (le_div_iff₀ (show 0 < 2 * R by positivity)).mp hlim
    nlinarith
  refine ⟨1 - s, by linarith, by linarith, ?_⟩
  intro x hx
  have hscale : (1 - s) - 1 = -s := by ring
  calc
    dist ((1 - s) • x) x = ‖(1 - s) • x - (1 : ℝ) • x‖ := by
      simp only [one_smul, dist_eq_norm]
    _ = |(1 - s) - 1| * ‖x‖ := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    _ = s * ‖x‖ := by rw [hscale, abs_neg, abs_of_nonneg hs.le]
    _ ≤ s * R := mul_le_mul_of_nonneg_left (hbound x hx) hs.le
    _ ≤ ε / 2 := hs_error
    _ < ε := by linarith

/-- Strictification of a short map into Euclidean space on a compact source
subset. The source may be any metric space. The construction and its estimates
are proved directly and depend on no geometric axiom. -/
theorem euclidean_strictification_on_compact
    {P : Type*} [MetricSpace P] {n : ℕ} {K : Set P} (hK : IsCompact K)
    {f : P → EuclideanSpace ℝ (Fin n)} (hf : LipschitzWith 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ L < 1 ∧
      ∃ u : P → EuclideanSpace ℝ (Fin n),
        (∀ x y, dist (u x) (u y) ≤ L * dist x y) ∧
        ∀ x ∈ K, dist (u x) (f x) < ε := by
  obtain ⟨t, ht0, ht1, hclose⟩ :=
    compact_strict_homothety (hK.image hf.continuous) hε
  refine ⟨t, ht0, ht1, (fun x => t • f x), ?_, ?_⟩
  · intro x y
    have hdist : dist (f x) (f y) ≤ dist x y := by simpa using hf.dist_le_mul x y
    calc
      dist (t • f x) (t • f y) = t * dist (f x) (f y) := by
        simp only [dist_eq_norm, ← smul_sub, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg ht0]
      _ ≤ t * dist x y := mul_le_mul_of_nonneg_left hdist ht0
  · intro x hx
    exact hclose (f x) (Set.mem_image_of_mem f hx)

end BrehmApprox
