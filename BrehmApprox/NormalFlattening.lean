module

public import BrehmApprox.RadialFlattening
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic.Abel

/-!
# Continuous normal flattening along a Euclidean subspace

The construction fixes the orthogonal projection and applies the radial
flattening only to the normal component. The Lipschitz estimate uses the
Pythagorean identity in the original inner product space. A varying cut-off
radius produces the bound `(1 + α c) / (1 - α)`, which tends to one with `α`.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normal flattening with constant outer radius. -/
def normalFlatten (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (α R : ℝ) (x : E) : E :=
  K.starProjection x + radialFlatten α R (x - K.starProjection x)

lemma normalFlatten_projection (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (α R : ℝ) (x : E) :
    K.starProjection (normalFlatten K α R x) = K.starProjection x := by
  have hPP : K.starProjection (K.starProjection x) = K.starProjection x :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
  simp only [normalFlatten, radialFlatten, map_add, map_smul, map_sub, hPP,
    sub_self, smul_zero, add_zero]

lemma normalFlatten_inner (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α R : ℝ} (hα1 : α < 1) {x : E}
    (hin : ‖x - K.starProjection x‖ ≤ α * R) :
    normalFlatten K α R x = K.starProjection x := by
  rw [normalFlatten, radialFlatten_inner hα1 hin, add_zero]

lemma normalFlatten_outer (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {x : E}
    (hout : R ≤ ‖x - K.starProjection x‖) : normalFlatten K α R x = x := by
  rw [normalFlatten, radialFlatten_outer hα0 hα1 hout]
  abel

lemma normalFlatten_zero_radius (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : E) :
    normalFlatten K α 0 x = x :=
  normalFlatten_outer K hα0 hα1 (norm_nonneg _)

lemma normalFlatten_displacement (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hR : 0 ≤ R) (x : E) :
    dist (normalFlatten K α R x) x ≤ α * R := by
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  calc
    dist (normalFlatten K α R x) x =
        dist (normalFlatten K α R x) (K.starProjection x + (x - K.starProjection x)) :=
      congrArg (dist (normalFlatten K α R x)) hx
    _ = dist (radialFlatten α R (x - K.starProjection x)) (x - K.starProjection x) := by
      simp only [normalFlatten, dist_add_left]
    _ ≤ α * R := radialFlatten_displacement hα0 hα1 hR _

/-- The normal map stays on the segment joining the original point to its
projection. Consequently it preserves any convex set containing both. -/
lemma normalFlatten_mem_convex (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (α R : ℝ) {C : Set E} (hC : Convex ℝ C) {x : E}
    (hx : x ∈ C) (hPx : K.starProjection x ∈ C) : normalFlatten K α R x ∈ C := by
  let v := x - K.starProjection x
  let c := radialProfile α R ‖v‖ / ‖v‖
  have hc0 : 0 ≤ c := radial_coefficient_nonneg α R v
  have hc1 : c ≤ 1 := radial_coefficient_le_one α R v
  have hmem : (1 - c) • K.starProjection x + c • x ∈ C :=
    hC hPx hx (by linarith) hc0 (by ring)
  have heq : normalFlatten K α R x = (1 - c) • K.starProjection x + c • x := by
    simp only [normalFlatten, radialFlatten, c, v, sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  exact hmem

/-- Constant-radius normal flattening has the same sharp Lipschitz constant
as its normal radial part. The tangential component introduces no `√2` loss. -/
theorem normalFlatten_lipschitz (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hR : 0 ≤ R) (x y : E) :
    dist (normalFlatten K α R x) (normalFlatten K α R y) ≤
      (1 / (1 - α)) * dist x y := by
  let p : E := K.starProjection x - K.starProjection y
  let v : E := x - K.starProjection x
  let w : E := y - K.starProjection y
  let L : ℝ := 1 / (1 - α)
  have hβ : 0 < 1 - α := by linarith
  have hL : 1 ≤ L := by
    apply (le_div_iff₀ hβ).2
    linarith
  have hp : p ∈ K := K.sub_mem (K.starProjection_apply_mem x) (K.starProjection_apply_mem y)
  have hv : v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
  have hw : w ∈ Kᗮ := K.sub_starProjection_mem_orthogonal y
  have hnormal : radialFlatten α R v - radialFlatten α R w ∈ Kᗮ :=
    Kᗮ.sub_mem
      (Kᗮ.smul_mem _ hv)
      (Kᗮ.smul_mem _ hw)
  have horth_out : inner ℝ p (radialFlatten α R v - radialFlatten α R w) = 0 :=
    (K.mem_orthogonal _).mp hnormal p hp
  have horth_in : inner ℝ p (v - w) = 0 :=
    (K.mem_orthogonal _).mp (Kᗮ.sub_mem hv hw) p hp
  have hdecomp : x - y = p + (v - w) := by dsimp [p, v, w]; abel
  have hdecomp_out : normalFlatten K α R x - normalFlatten K α R y =
      p + (radialFlatten α R v - radialFlatten α R w) := by
    dsimp [normalFlatten, p, v, w]
    abel
  have hsource : ‖x - y‖ ^ 2 = ‖p‖ ^ 2 + ‖v - w‖ ^ 2 := by
    rw [hdecomp]
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth_in
  have houtput : ‖normalFlatten K α R x - normalFlatten K α R y‖ ^ 2 =
      ‖p‖ ^ 2 + ‖radialFlatten α R v - radialFlatten α R w‖ ^ 2 := by
    rw [hdecomp_out]
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth_out
  have hrad : ‖radialFlatten α R v - radialFlatten α R w‖ ≤ L * ‖v - w‖ := by
    simpa only [dist_eq_norm] using radialFlatten_lipschitz hα0 hα1 hR v w
  have hrad2 := pow_le_pow_left₀ (norm_nonneg _) hrad 2
  simp only [mul_pow] at hrad2
  have hp2 : ‖p‖ ^ 2 ≤ L ^ 2 * ‖p‖ ^ 2 := by
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL2 (sq_nonneg ‖p‖)
  have hsq : ‖normalFlatten K α R x - normalFlatten K α R y‖ ^ 2 ≤
      (L * ‖x - y‖) ^ 2 := by
    rw [houtput, mul_pow, hsource, mul_add]
    exact add_le_add hp2 hrad2
  simp only [dist_eq_norm]
  change ‖normalFlatten K α R x - normalFlatten K α R y‖ ≤ L * ‖x - y‖
  have hright : 0 ≤ L * ‖x - y‖ := mul_nonneg (by linarith) (norm_nonneg _)
  nlinarith [norm_nonneg (normalFlatten K α R x - normalFlatten K α R y)]

lemma normalFlatten_parameter (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α R S : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : E) :
    dist (normalFlatten K α R x) (normalFlatten K α S x) ≤
      (α / (1 - α)) * |R - S| := by
  simpa only [normalFlatten, dist_add_left] using
    radialFlatten_parameter hα0 hα1 (R := R) (S := S) (x - K.starProjection x)

/-- A variable cut-off radius depending only on the projected point. -/
def taperedNormalFlatten (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (α : ℝ) (R : E → ℝ) (x : E) : E :=
  normalFlatten K α (R (K.starProjection x)) x

lemma taperedNormalFlatten_projection (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (α : ℝ) (R : E → ℝ) (x : E) :
    K.starProjection (taperedNormalFlatten K α R x) = K.starProjection x :=
  normalFlatten_projection K α _ x

lemma taperedNormalFlatten_inner (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α : ℝ} (hα1 : α < 1) (R : E → ℝ) {x : E}
    (hin : ‖x - K.starProjection x‖ ≤ α * R (K.starProjection x)) :
    taperedNormalFlatten K α R x = K.starProjection x :=
  normalFlatten_inner K hα1 hin

lemma taperedNormalFlatten_outer (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (R : E → ℝ) {x : E}
    (hout : R (K.starProjection x) ≤ ‖x - K.starProjection x‖) :
    taperedNormalFlatten K α R x = x :=
  normalFlatten_outer K hα0 hα1 hout

lemma taperedNormalFlatten_displacement (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (R : E → ℝ)
    (hR : ∀ z ∈ K, 0 ≤ R z) (x : E) :
    dist (taperedNormalFlatten K α R x) x ≤ α * R (K.starProjection x) :=
  normalFlatten_displacement K hα0 hα1 (hR _ (K.starProjection_apply_mem x)) x

theorem taperedNormalFlatten_lipschitz (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : E → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    (hRlip : ∀ z ∈ K, ∀ w ∈ K, |R z - R w| ≤ c * dist z w) (x y : E) :
    dist (taperedNormalFlatten K α R x) (taperedNormalFlatten K α R y) ≤
      ((1 + α * c) / (1 - α)) * dist x y := by
  have hβ : 0 < 1 - α := by linarith
  have hcoef : 0 ≤ α / (1 - α) := div_nonneg hα0 hβ.le
  have hproj : dist (K.starProjection x) (K.starProjection y) ≤ dist x y := by
    simpa using K.lipschitzWith_starProjection.dist_le_mul x y
  have hRdist : |R (K.starProjection x) - R (K.starProjection y)| ≤ c * dist x y :=
    (hRlip _ (K.starProjection_apply_mem x) _ (K.starProjection_apply_mem y)).trans
      (mul_le_mul_of_nonneg_left hproj hc)
  calc
    dist (taperedNormalFlatten K α R x) (taperedNormalFlatten K α R y) ≤
        dist (normalFlatten K α (R (K.starProjection x)) x)
          (normalFlatten K α (R (K.starProjection x)) y) +
        dist (normalFlatten K α (R (K.starProjection x)) y)
          (normalFlatten K α (R (K.starProjection y)) y) := dist_triangle _ _ _
    _ ≤ (1 / (1 - α)) * dist x y +
        (α / (1 - α)) * |R (K.starProjection x) - R (K.starProjection y)| :=
      add_le_add (normalFlatten_lipschitz K hα0 hα1
        (hR _ (K.starProjection_apply_mem x)) x y)
        (normalFlatten_parameter K hα0 hα1 y)
    _ ≤ (1 / (1 - α)) * dist x y + (α / (1 - α)) * (c * dist x y) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hRdist hcoef)
    _ = ((1 + α * c) / (1 - α)) * dist x y := by ring

theorem taperedNormalFlatten_continuous (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : E → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    (hRlip : ∀ z ∈ K, ∀ w ∈ K, |R z - R w| ≤ c * dist z w) :
    Continuous (taperedNormalFlatten K α R) := by
  have hconst : 0 ≤ (1 + α * c) / (1 - α) := by positivity
  exact (LipschitzWith.of_dist_le_mul (K := ⟨(1 + α * c) / (1 - α), hconst⟩)
    (taperedNormalFlatten_lipschitz K hα0 hα1 hc R hR hRlip)).continuous

end BrehmApprox
