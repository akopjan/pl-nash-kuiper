module

public import BrehmApprox.Core
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Tactic.Abel

/-!
# Euclidean nearest-point projection and contracting reference maps

The nearest-point map to a nonempty complete convex subset is constructed from
the Hilbert projection theorem already proved in mathlib. Its nonexpansiveness,
fixed-point property, uniqueness and compatibility with ambient affine
projection are proved below. No extension or approximation axiom is used.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two variational projection inequalities imply the nonexpansive estimate.
This is the elementary inner-product part of the projection argument. -/
lemma variational_distance_le (x y p q : E)
    (hp : inner ℝ (x - p) (q - p) ≤ 0)
    (hq : inner ℝ (y - q) (p - q) ≤ 0) : dist p q ≤ dist x y := by
  have hidentity : inner ℝ (x - y) (p - q) - inner ℝ (p - q) (p - q) =
      -inner ℝ (x - p) (q - p) - inner ℝ (y - q) (p - q) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [real_inner_self_eq_norm_sq] at hidentity
  have hfirm : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by linarith
  have hcs := real_inner_le_norm (x - y) (p - q)
  simp only [dist_eq_norm]
  nlinarith [norm_nonneg (p - q), norm_nonneg (x - y)]

/-- Nearest-point projection to a nonempty complete convex set. -/
def convexProjection (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C)
    (hconvex : Convex ℝ C) (x : E) : E :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose

lemma convexProjection_mem (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C)
    (hconvex : Convex ℝ C) (x : E) : convexProjection C hne hcomplete hconvex x ∈ C :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose_spec.1

lemma convexProjection_minimizes (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hconvex : Convex ℝ C) (x : E) :
    ‖x - convexProjection C hne hcomplete hconvex x‖ = ⨅ y : C, ‖x - y‖ :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose_spec.2

lemma convexProjection_variational (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hconvex : Convex ℝ C) (x : E) :
    ∀ y ∈ C, inner ℝ (x - convexProjection C hne hcomplete hconvex x)
      (y - convexProjection C hne hcomplete hconvex x) ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconvex
    (convexProjection_mem C hne hcomplete hconvex x)).mp
      (convexProjection_minimizes C hne hcomplete hconvex x)

theorem convexProjection_short (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hconvex : Convex ℝ C) :
    Short (convexProjection C hne hcomplete hconvex) := by
  intro x y
  exact variational_distance_le x y _ _
    (convexProjection_variational C hne hcomplete hconvex x _
      (convexProjection_mem C hne hcomplete hconvex y))
    (convexProjection_variational C hne hcomplete hconvex y _
      (convexProjection_mem C hne hcomplete hconvex x))

lemma convexProjection_eq_of_variational (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hconvex : Convex ℝ C) {x p : E} (hp : p ∈ C)
    (hvar : ∀ y ∈ C, inner ℝ (x - p) (y - p) ≤ 0) :
    convexProjection C hne hcomplete hconvex x = p := by
  have hd := variational_distance_le x x
    (convexProjection C hne hcomplete hconvex x) p
    (convexProjection_variational C hne hcomplete hconvex x p hp)
    (hvar _ (convexProjection_mem C hne hcomplete hconvex x))
  simpa only [dist_self, dist_le_zero] using hd

lemma convexProjection_fix (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hconvex : Convex ℝ C) {x : E} (hx : x ∈ C) :
    convexProjection C hne hcomplete hconvex x = x := by
  apply convexProjection_eq_of_variational C hne hcomplete hconvex hx
  intro y hy
  simp only [sub_self, inner_zero_left, le_refl]

theorem convexProjection_continuous (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hconvex : Convex ℝ C) :
    Continuous (convexProjection C hne hcomplete hconvex) :=
  (convexProjection_short C hne hcomplete hconvex).continuous

/-- A contracting map on a convex face extends to a contracting reference
map on the ambient Euclidean space by composition with nearest projection. -/
theorem contracting_reference_via_projection
    {Y : Type*} [MetricSpace Y] (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hconvex : Convex ℝ C) (f : E → Y)
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) ≤ L * dist x y) :
    ∀ x y : E,
      dist (f (convexProjection C hne hcomplete hconvex x))
        (f (convexProjection C hne hcomplete hconvex y)) ≤ L * dist x y := by
  intro x y
  exact (hf _ (convexProjection_mem C hne hcomplete hconvex x)
    _ (convexProjection_mem C hne hcomplete hconvex y)).trans
      (mul_le_mul_of_nonneg_left (convexProjection_short C hne hcomplete hconvex x y) hL)

/-- Moving towards the nearest point along its normal ray does not change
the nearest point. -/
lemma convexProjection_normal_ray (C : Set E) (hne : C.Nonempty)
    (hcomplete : IsComplete C) (hconvex : Convex ℝ C) (x : E)
    {t : ℝ} (ht : 0 ≤ t) :
    let p := convexProjection C hne hcomplete hconvex x
    convexProjection C hne hcomplete hconvex (p + t • (x - p)) = p := by
  dsimp only
  let p := convexProjection C hne hcomplete hconvex x
  apply convexProjection_eq_of_variational C hne hcomplete hconvex
    (convexProjection_mem C hne hcomplete hconvex x)
  intro y hy
  have heq : p + t • (x - p) - p = t • (x - p) := by abel
  change inner ℝ (p + t • (x - p) - p) (y - p) ≤ 0
  rw [heq, real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos ht
    (convexProjection_variational C hne hcomplete hconvex x y hy)

/-- Nested affine orthogonal projections commute in the required order. This
is a specialization of the proved affine projection theorem in mathlib. -/
lemma affine_projection_nested {F G : AffineSubspace ℝ E}
    [Nonempty F] [Nonempty G]
    [F.direction.HasOrthogonalProjection] [G.direction.HasOrthogonalProjection]
    (hFG : F ≤ G) (x : E) :
    EuclideanGeometry.orthogonalProjection F (EuclideanGeometry.orthogonalProjection G x) =
      EuclideanGeometry.orthogonalProjection F x :=
  EuclideanGeometry.orthogonalProjection_orthogonalProjection_of_le hFG x

/-- Nearest projection to a convex subset of an affine subspace is unchanged
if one first projects to that affine subspace. This does not assert the reverse
composition identity for two arbitrary nested convex sets. -/
lemma convexProjection_after_affine_projection
    (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C) (hconvex : Convex ℝ C)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (hCF : C ⊆ F) (x : E) :
    convexProjection C hne hcomplete hconvex (EuclideanGeometry.orthogonalProjection F x) =
      convexProjection C hne hcomplete hconvex x := by
  let p := convexProjection C hne hcomplete hconvex x
  let z : E := EuclideanGeometry.orthogonalProjection F x
  have hpC : p ∈ C := convexProjection_mem C hne hcomplete hconvex x
  apply convexProjection_eq_of_variational C hne hcomplete hconvex hpC
  intro y hy
  have hdir : y - p ∈ F.direction := by
    exact AffineSubspace.vsub_mem_direction (hCF hy) (hCF hpC)
  have horth : inner ℝ (x - z) (y - p) = 0 := by
    exact (F.direction.mem_orthogonal' _).mp
      (EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal F x) _ hdir
  have hvar := convexProjection_variational C hne hcomplete hconvex x y hy
  change inner ℝ (z - p) (y - p) ≤ 0
  have heq : z - p = (x - p) - (x - z) := by abel
  rw [heq, inner_sub_left, horth, sub_zero]
  exact hvar

end BrehmApprox
