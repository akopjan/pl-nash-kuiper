module

public import BrehmApprox.Core
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Convex.Hull

/-!
# Finite determination on actual Euclidean polyhedra

Pieces are convex hulls of finite sets of points.  On every piece the map
agrees with an ambient affine isometry.  In particular, this is geometric
data, not an assumption that a desired approximation already exists.
-/

@[expose] public section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weighted_variance_two (x y z : E) (a b : ℝ) (hab : a + b = 1) :
    a * ‖z - x‖ ^ 2 + b * ‖z - y‖ ^ 2 =
      ‖z - (a • x + b • y)‖ ^ 2 + a * b * ‖x - y‖ ^ 2 := by
  have ha : a = 1 - b := by linarith
  subst a
  simp only [norm_sub_sq_real, norm_add_sq_real, norm_smul,
    real_inner_smul_left, inner_smul_right, inner_add_right,
    Real.norm_eq_abs, sq_abs, mul_pow]
  ring

/-- The fixed point set of a short self-map of a real inner product space is
convex.  The proof is the two-point weighted variance identity. -/
lemma convex_fixedPoints_of_short {f : E → E} (hf : Short f) :
    Convex ℝ {x : E | f x = x} := by
  intro x hx y hy a b ha hb hab
  change f x = x at hx
  change f y = y at hy
  let z : E := a • x + b • y
  have hx' : ‖f z - x‖ ≤ ‖z - x‖ := by
    simpa only [dist_eq_norm, hx] using hf z x
  have hy' : ‖f z - y‖ ≤ ‖z - y‖ := by
    simpa only [dist_eq_norm, hy] using hf z y
  have hx2 : ‖f z - x‖ ^ 2 ≤ ‖z - x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hx' 2
  have hy2 : ‖f z - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hy' 2
  have hle := add_le_add (mul_le_mul_of_nonneg_left hx2 ha)
    (mul_le_mul_of_nonneg_left hy2 hb)
  have h₁ := weighted_variance_two x y (f z) a b hab
  have h₂ := weighted_variance_two x y z a b hab
  change f z = z
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hzero : ‖z - (a • x + b • y)‖ = 0 := by simp [z]
  have hn : 0 ≤ ‖f z - z‖ := norm_nonneg _
  change a * ‖f z - x‖ ^ 2 + b * ‖f z - y‖ ^ 2 =
    ‖f z - z‖ ^ 2 + a * b * ‖x - y‖ ^ 2 at h₁
  nlinarith

lemma short_eq_on_convexHull_of_fixed {f : E → E} (hf : Short f)
    (s : Set E) (hs : ∀ x ∈ s, f x = x) :
    ∀ x ∈ convexHull ℝ s, f x = x := by
  intro x hx
  exact convexHull_min (show s ⊆ {y : E | f y = y} by
    intro y hy
    exact hs y hy) (convex_fixedPoints_of_short hf) hx

/-- A finite Euclidean piecewise isometry on the set `A`. -/
def EuclideanPLOn (A : Set E) (f : E → E) : Prop :=
  ∃ C : Finset (Finset E),
    A = ⋃ V ∈ C, convexHull ℝ (V : Set E) ∧
    ∀ V ∈ C, ∃ r : E ≃ᵃⁱ[ℝ] E,
      ∀ x ∈ convexHull ℝ (V : Set E), f x = r x

/-- Local finiteness expressed by finite isometric subdivisions on every
compact Euclidean polytope. -/
def LocallyEuclideanPL (f : E → E) : Prop :=
  ∀ V : Finset E, EuclideanPLOn (convexHull ℝ (V : Set E)) f

lemma determinedOn_euclideanPL {A : Set E} {g : E → E}
    (hg : EuclideanPLOn A g) : DeterminedOn A g := by
  classical
  obtain ⟨C, hA, hg⟩ := hg
  let V : Finset E := C.biUnion id
  have hVC (D : Finset E) (hD : D ∈ C) : (D : Set E) ⊆ (V : Set E) := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨D, hD, hv⟩
  refine ⟨V, ?_, ?_⟩
  · intro v hv
    obtain ⟨D, hD, hvD⟩ := Finset.mem_biUnion.mp hv
    rw [hA]
    exact Set.mem_iUnion.mpr ⟨D, Set.mem_iUnion.mpr ⟨hD,
      subset_convexHull ℝ (D : Set E) hvD⟩⟩
  · intro h hh hV x hx
    rw [hA] at hx
    obtain ⟨D, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hD, hxD⟩ := Set.mem_iUnion.mp hx
    obtain ⟨r, hr⟩ := hg D hD
    let k : E → E := fun y => r.symm (h y)
    have hk : Short k := by
      intro y z
      simpa only [k, r.symm.isometry.dist_eq] using hh y z
    have hfix : ∀ v ∈ (D : Set E), k v = v := by
      intro v hv
      change r.symm (h v) = v
      rw [hV v (hVC D hD hv), hr v (subset_convexHull ℝ (D : Set E) hv)]
      exact r.symm_apply_apply v
    have hxfix := short_eq_on_convexHull_of_fixed hk (D : Set E) hfix x hxD
    calc
      h x = r (r.symm (h x)) := (r.apply_symm_apply (h x)).symm
      _ = r x := congrArg r hxfix
      _ = g x := (hr x hxD).symm

end BrehmApprox
