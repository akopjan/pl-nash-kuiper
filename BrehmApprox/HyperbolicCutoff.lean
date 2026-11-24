module

public import BrehmApprox.HyperbolicFlattening
public import BrehmApprox.DistanceCutoff

/-!
# Actual distance cut-offs in hyperbolic normal charts

The bad set is a closed Euclidean set in the actual Klein chart.  It can
include all nonincident cofacial cells and the complement of the chosen face
inside its plane.  The resulting map has true local collapse, local identity
off the face, support control and metric activity bounds needed by the
dimension-by-dimension source construction.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

instance nonempty_submodule_toAffineSubspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) : Nonempty K.toAffineSubspace :=
  ⟨⟨0, K.zero_mem⟩⟩

instance orthogonalProjection_submodule_toAffineSubspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    K.toAffineSubspace.direction.HasOrthogonalProjection := by
  simpa only [Submodule.toAffineSubspace_direction] using
    (inferInstance : K.HasOrthogonalProjection)

lemma affineProjection_toAffineSubspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) :
    affineProjection K.toAffineSubspace x = K.starProjection x := by
  simpa using affineProjection_eq_shift K.toAffineSubspace 0 K.zero_mem x

lemma cutoffAffineFlatten_toAffineSubspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (Bad : Set E) (b c α : ℝ) (x : E) :
    cutoffAffineFlatten K.toAffineSubspace Bad b c α x =
      taperedNormalFlatten K α (distanceCutoff Bad b c) x := by
  simp only [cutoffAffineFlatten, affineNormalFlatten, affineProjection_toAffineSubspace,
    taperedNormalFlatten, normalFlatten]

namespace HyperbolicSpace

variable {n : ℕ}

def cutoffKleinFlatten (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n))) (b c α : ℝ) : HyperbolicSpace n → HyperbolicSpace n :=
  kleinNormalFlatten K α (distanceCutoff Bad b c)

lemma klein_cutoffKleinFlatten (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n))) (b c α : ℝ) (x : HyperbolicSpace n) :
    klein (cutoffKleinFlatten K Bad b c α x) =
      cutoffAffineFlatten K.toAffineSubspace Bad b c α (klein x) := by
  rw [cutoffAffineFlatten_toAffineSubspace]
  exact klein_kleinNormalFlatten K α _ x

lemma cutoffKleinFlatten_active_iff (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n))) (b c α : ℝ) (x : HyperbolicSpace n) :
    cutoffKleinFlatten K Bad b c α x ≠ x ↔
      cutoffAffineFlatten K.toAffineSubspace Bad b c α (klein x) ≠ klein x := by
  rw [← klein_cutoffKleinFlatten]
  exact klein_injective.ne_iff.symm

theorem cutoffKleinFlatten_lipschitz_on_chart
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (Bad : Set (EuclideanSpace ℝ (Fin n)))
    {ρ b c α : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    {x y : HyperbolicSpace n} (hx : ‖klein x‖ ≤ ρ) (hy : ‖klein y‖ ≤ ρ) :
    dist (cutoffKleinFlatten K Bad b c α x) (cutoffKleinFlatten K Bad b c α y) ≤
      ((1 - ρ ^ 2)⁻¹ * ((1 + α * c) / (1 - α))) * dist x y :=
  kleinNormalFlatten_lipschitz_on_chart K hρ0 hρ1 hα0 hα1 hc _
    (fun z _ => distanceCutoff_nonneg Bad hb hc z)
    (fun z _ w _ => distanceCutoff_lipschitz Bad b hc z w) hx hy

theorem cutoffKleinFlatten_local_collapse
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n))) (hBad : IsClosed Bad)
    {b c α : ℝ} (hb : 0 < b) (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1)
    {p : HyperbolicSpace n} (hp : p ∈ geodesicPlane K) (hpBad : klein p ∉ Bad) :
    ∃ U : Set (HyperbolicSpace n), IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, cutoffKleinFlatten K Bad b c α x = geodesicProjection K x := by
  obtain ⟨U, hU, hpU, hcollapse⟩ := cutoffAffineFlatten_local_collapse K.toAffineSubspace
    Bad hBad hb hc hα0 hα1 ((klein_mem_iff K p).mpr hp) hpBad
  refine ⟨klein ⁻¹' U, hU.preimage continuous_klein, hpU, ?_⟩
  intro x hx
  apply klein_injective
  rw [klein_cutoffKleinFlatten, klein_geodesicProjection, hcollapse (klein x) hx,
    affineProjection_toAffineSubspace]

theorem cutoffKleinFlatten_local_identity
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n))) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsClosed A) (hbad : (K : Set (EuclideanSpace ℝ (Fin n))) \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc1 : c < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {p : HyperbolicSpace n} (hpBad : klein p ∈ Bad) (hpA : klein p ∉ A) :
    ∃ U : Set (HyperbolicSpace n), IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, cutoffKleinFlatten K Bad b c α x = x := by
  obtain ⟨U, hU, hpU, hidentity⟩ := cutoffAffineFlatten_local_identity K.toAffineSubspace
    Bad hA hbad hb hc0 hc1 hα0 hα1 hpBad hpA
  refine ⟨klein ⁻¹' U, hU.preimage continuous_klein, hpU, ?_⟩
  intro x hx
  apply klein_injective
  rw [klein_cutoffKleinFlatten, hidentity (klein x) hx]

theorem cutoffKleinFlatten_projection_mem_of_active
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n))) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hbad : (K : Set (EuclideanSpace ℝ (Fin n))) \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {x : HyperbolicSpace n} (hx : cutoffKleinFlatten K Bad b c α x ≠ x) :
    klein (geodesicProjection K x) ∈ A := by
  have h := cutoffAffineFlatten_projection_mem_of_ne K.toAffineSubspace Bad hbad hb hα0 hα1
    ((cutoffKleinFlatten_active_iff K Bad b c α x).mp hx)
  simpa only [klein_geodesicProjection, affineProjection_toAffineSubspace] using h

theorem cutoffKleinFlatten_support_inter_bad
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n))) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsClosed A) (hbad : (K : Set (EuclideanSpace ℝ (Fin n))) \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc1 : c < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    closure {x | cutoffKleinFlatten K Bad b c α x ≠ x} ∩ klein ⁻¹' Bad ⊆
      klein ⁻¹' (A ∩ Bad) := by
  let M : Set (EuclideanSpace ℝ (Fin n)) :=
    {v | cutoffAffineFlatten K.toAffineSubspace Bad b c α v ≠ v}
  have hclosed : IsClosed (klein ⁻¹' closure M) := isClosed_closure.preimage continuous_klein
  have hsub : {x | cutoffKleinFlatten K Bad b c α x ≠ x} ⊆ klein ⁻¹' closure M := by
    intro x hx
    exact subset_closure ((cutoffKleinFlatten_active_iff K Bad b c α x).mp hx)
  intro x hx
  have hcl : klein x ∈ closure M := closure_minimal hsub hclosed hx.1
  exact cutoffAffineFlatten_support_inter_bad K.toAffineSubspace Bad hA hbad hb hc0 hc1 hα0 hα1
    ⟨hcl, hx.2⟩

theorem cutoffKleinFlatten_mapsTo_hyperbolicCell
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n))) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hbad : (K : Set (EuclideanSpace ℝ (Fin n))) \ A ⊆ Bad)
    (V : Finset (HyperbolicSpace n))
    (hA : ∀ p ∈ A, fromKlein p ∈ hyperbolicCell V)
    {b c α : ℝ} (hb : 0 ≤ b) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Set.MapsTo (cutoffKleinFlatten K Bad b c α) (hyperbolicCell V) (hyperbolicCell V) := by
  intro x hx
  by_cases hfix : cutoffKleinFlatten K Bad b c α x = x
  · simpa only [hfix] using hx
  · apply kleinNormalFlatten_mem_hyperbolicCell K α _ V hx
    have hpA := cutoffKleinFlatten_projection_mem_of_active K Bad hbad hb hα0 hα1 hfix
    simpa only [fromKlein_klein] using hA _ hpA

/-- The actual hyperbolic normal distance at an active point is bounded by
the distance to every bad point, with the sharp chart distortion factor.
Choosing `c / (1-ρ²) ≤ 1/2` makes activities of incomparable cofacial collapses
disjoint by the elementary two-foot triangle argument. -/
theorem cutoffKleinFlatten_active_distance_bound
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (Bad : Set (EuclideanSpace ℝ (Fin n)))
    {ρ b c α : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 ≤ c)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    {x y : HyperbolicSpace n} (hxρ : ‖klein x‖ ≤ ρ)
    (hactive : cutoffKleinFlatten K Bad b c α x ≠ x) (hy : klein y ∈ Bad) :
    dist x (geodesicProjection K x) <
      ((1 - ρ ^ 2)⁻¹ * c) * dist (geodesicProjection K x) y := by
  have hnormal : ‖klein x - K.starProjection (klein x)‖ <
      distanceCutoff Bad b c (K.starProjection (klein x)) := by
    by_contra h
    exact hactive (kleinNormalFlatten_outer K hα0 hα1 _ (le_of_not_gt h))
  have hcut := distanceCutoff_le_dist Bad b hc (K.starProjection (klein x)) hy
  have hPnorm : ‖K.starProjection (klein x)‖ ≤ ρ :=
    (K.norm_starProjection_apply_le _).trans hxρ
  have hmetric := dist_fromKlein_le hρ0 hρ1 hxρ hPnorm
  rw [fromKlein_klein] at hmetric
  change dist x (geodesicProjection K x) ≤
    (1 - ρ ^ 2)⁻¹ * ‖klein x - K.starProjection (klein x)‖ at hmetric
  have hD : 0 < (1 - ρ ^ 2)⁻¹ := by
    apply inv_pos.mpr
    nlinarith
  have hcoord : dist (K.starProjection (klein x)) (klein y) ≤ dist (geodesicProjection K x) y := by
    simpa only [klein_geodesicProjection] using klein_dist_le (geodesicProjection K x) y
  calc
    _ ≤ _ := hmetric
    _ < (1 - ρ ^ 2)⁻¹ * distanceCutoff Bad b c (K.starProjection (klein x)) :=
      mul_lt_mul_of_pos_left hnormal hD
    _ ≤ (1 - ρ ^ 2)⁻¹ * (c * dist (K.starProjection (klein x)) (klein y)) :=
      mul_le_mul_of_nonneg_left hcut hD.le
    _ ≤ (1 - ρ ^ 2)⁻¹ * (c * dist (geodesicProjection K x) y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcoord hc) hD.le
    _ = _ := by ring

end HyperbolicSpace
end BrehmApprox
