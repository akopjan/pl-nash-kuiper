module

public import BrehmApprox.DistanceCutoff
public import BrehmApprox.DisjointStages

/-!+# Disjoint stages from actual distance cut-offs

The bad set for one face contains every other face in the stage. With radius
coefficient at most `1/2`, two maps cannot move the same point. A moved image is
either still in the same active region or has reached that face; this proves
the stability hypothesis used in the cardinality-independent stage estimate.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

lemma radialProfile_lt {α R t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ht : 0 < t) (hR : t < R) : radialProfile α R t < t := by
  have hβ : 0 < 1 - α := by linarith
  have hq : (t - α * R) / (1 - α) < t := by
    apply (div_lt_iff₀ hβ).2
    nlinarith [mul_pos hα0 (sub_pos.mpr hR)]
  exact (min_le_right _ _).trans_lt (max_lt ht hq)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma affineNormalFlatten_ne_of_near (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (R : E → ℝ) {x : E} (hx : x ≠ affineProjection F x)
    (hnear : ‖x - affineProjection F x‖ < R (affineProjection F x)) :
    affineNormalFlatten F α R x ≠ x := by
  have hpos : 0 < ‖x - affineProjection F x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hnorm : ‖affineNormalFlatten F α R x - affineProjection F x‖ =
      radialProfile α (R (affineProjection F x)) ‖x - affineProjection F x‖ := by
    rw [affineNormalFlatten, add_sub_cancel_left]
    exact radialFlatten_norm hα0.le hα1 (hpos.le.trans hnear.le) _
  intro heq
  rw [heq] at hnorm
  have hlt := radialProfile_lt hα0 hα1 hpos hnear
  linarith

lemma cutoffAffineFlatten_normal_lt_of_ne (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {b c α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) {x : E}
    (hx : cutoffAffineFlatten F Bad b c α x ≠ x) :
    ‖x - affineProjection F x‖ < distanceCutoff Bad b c (affineProjection F x) := by
  apply lt_of_not_ge
  intro h
  exact hx (affineNormalFlatten_outer F hα0 hα1 _ h)

/-- Pairwise activity is disjoint as soon as each bad set contains the other
face and the common distance coefficient is at most one half. -/
theorem cutoffAffineFlatten_disjoint_activity
    (F G : AffineSubspace ℝ E) [Nonempty F] [Nonempty G]
    [F.direction.HasOrthogonalProjection] [G.direction.HasOrthogonalProjection]
    (BadF BadG : Set E) {A B : Set E}
    (hbadF : (F : Set E) \ A ⊆ BadF) (hbadG : (G : Set E) \ B ⊆ BadG)
    (hAB : A ⊆ BadG) (hBA : B ⊆ BadF) {bF bG c α : ℝ}
    (hbF : 0 ≤ bF) (hbG : 0 ≤ bG) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (hα0 : 0 ≤ α) (hα1 : α < 1) {x : E}
    (hFx : cutoffAffineFlatten F BadF bF c α x ≠ x) :
    cutoffAffineFlatten G BadG bG c α x = x := by
  by_contra hGx
  have hFA := cutoffAffineFlatten_projection_mem_of_ne F BadF hbadF hbF hα0 hα1 hFx
  have hGB := cutoffAffineFlatten_projection_mem_of_ne G BadG hbadG hbG hα0 hα1 hGx
  have hFn := cutoffAffineFlatten_normal_lt_of_ne F BadF hα0 hα1 hFx
  have hGn := cutoffAffineFlatten_normal_lt_of_ne G BadG hα0 hα1 hGx
  have hFc := distanceCutoff_le_dist BadF bF hc0 (affineProjection F x) (hBA hGB)
  have hGc := distanceCutoff_le_dist BadG bG hc0 (affineProjection G x) (hAB hFA)
  rw [dist_comm (affineProjection G x) (affineProjection F x)] at hGc
  have htri := dist_triangle (affineProjection F x) x (affineProjection G x)
  rw [dist_comm (affineProjection F x) x, dist_eq_norm x (affineProjection F x),
    dist_eq_norm x (affineProjection G x)] at htri
  have hcoeff : 2 * c * dist (affineProjection F x) (affineProjection G x) ≤
      dist (affineProjection F x) (affineProjection G x) :=
    mul_le_of_le_one_left dist_nonneg (by linarith)
  linarith

/-- The image of an active point either remains active for the same map or
lies on its projected face. -/
theorem cutoffAffineFlatten_image_active_or_face
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (Bad : Set E) {A : Set E} (hbad : (F : Set E) \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hα0 : 0 < α) (hα1 : α < 1) {x : E}
    (hx : cutoffAffineFlatten F Bad b c α x ≠ x) :
    cutoffAffineFlatten F Bad b c α (cutoffAffineFlatten F Bad b c α x) ≠
        cutoffAffineFlatten F Bad b c α x ∨ cutoffAffineFlatten F Bad b c α x ∈ A := by
  let q := cutoffAffineFlatten F Bad b c α x
  have hproj : affineProjection F q = affineProjection F x :=
    affineNormalFlatten_projection F α _ x
  have hPx := cutoffAffineFlatten_projection_mem_of_ne F Bad hbad hb hα0.le hα1 hx
  by_cases hq : q = affineProjection F x
  · apply Or.inr
    change q ∈ A
    rw [hq]
    exact hPx
  · apply Or.inl
    change affineNormalFlatten F α (distanceCutoff Bad b c) q ≠ q
    apply affineNormalFlatten_ne_of_near F hα0 hα1 _
    · simpa only [hproj] using hq
    · have hbound := affineNormalFlatten_dist_to_mem F α (distanceCutoff Bad b c) x
        (affineProjection_mem F x)
      change dist q (affineProjection F x) ≤ dist x (affineProjection F x) at hbound
      rw [dist_eq_norm, dist_eq_norm] at hbound
      rw [hproj]
      exact hbound.trans_lt (cutoffAffineFlatten_normal_lt_of_ne F Bad hα0.le hα1 hx)

theorem cutoffAffineFlatten_stable_activity
    (F G : AffineSubspace ℝ E) [Nonempty F] [Nonempty G]
    [F.direction.HasOrthogonalProjection] [G.direction.HasOrthogonalProjection]
    (BadF BadG : Set E) {A B : Set E}
    (hbadF : (F : Set E) \ A ⊆ BadF) (hbadG : (G : Set E) \ B ⊆ BadG)
    (hAB : A ⊆ BadG) (hBA : B ⊆ BadF) {bF bG c α : ℝ}
    (hbF : 0 ≤ bF) (hbG : 0 ≤ bG) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (hα0 : 0 < α) (hα1 : α < 1) {x : E}
    (hFx : cutoffAffineFlatten F BadF bF c α x ≠ x) :
    cutoffAffineFlatten G BadG bG c α (cutoffAffineFlatten F BadF bF c α x) =
      cutoffAffineFlatten F BadF bF c α x := by
  rcases cutoffAffineFlatten_image_active_or_face F BadF hbadF hbF hα0 hα1 hFx with
    hactive | hface
  · exact cutoffAffineFlatten_disjoint_activity F G BadF BadG hbadF hbadG hAB hBA
      hbF hbG hc0 hc1 hα0.le hα1 hactive
  · exact cutoffAffineFlatten_fix_on_bad G BadG hc0 (by linarith) hα0.le hα1 (hAB hface)

section Family

variable {ι : Type*} (I : Finset ι) (F : ι → AffineSubspace ℝ E)
  [∀ i, Nonempty (F i)] [∀ i, (F i).direction.HasOrthogonalProjection]
  (Bad A : ι → Set E) (b : ι → ℝ) {c α : ℝ}

theorem cutoffAffineFlatten_family_disjoint
    (hbad : ∀ i ∈ I, (F i : Set E) \ A i ⊆ Bad i)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → A i ⊆ Bad j)
    (hb : ∀ i ∈ I, 0 ≤ b i) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    DisjointActivity I (fun i => cutoffAffineFlatten (F i) (Bad i) (b i) c α) := by
  intro i hi j hj hij x hx
  exact cutoffAffineFlatten_disjoint_activity (F i) (F j) (Bad i) (Bad j)
    (hbad i hi) (hbad j hj) (hcross i hi j hj hij)
    (hcross j hj i hi (fun h => hij h.symm))
    (hb i hi) (hb j hj) hc0 hc1 hα0 hα1 hx

theorem cutoffAffineFlatten_family_stable
    (hbad : ∀ i ∈ I, (F i : Set E) \ A i ⊆ Bad i)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → A i ⊆ Bad j)
    (hb : ∀ i ∈ I, 0 ≤ b i) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (hα0 : 0 < α) (hα1 : α < 1) :
    StableActivity I (fun i => cutoffAffineFlatten (F i) (Bad i) (b i) c α) := by
  intro i hi j hj hij x hx
  exact cutoffAffineFlatten_stable_activity (F i) (F j) (Bad i) (Bad j)
    (hbad i hi) (hbad j hj) (hcross i hi j hj hij)
    (hcross j hj i hi (fun h => hij h.symm))
    (hb i hi) (hb j hj) hc0 hc1 hα0 hα1 hx

/-- A simultaneous family of genuine Euclidean face collapses has a bound
depending on the common parameters, but not on the number of faces. -/
theorem cutoffAffineFlatten_stage_lipschitz
    (hbad : ∀ i ∈ I, (F i : Set E) \ A i ⊆ Bad i)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → A i ⊆ Bad j)
    (hb : ∀ i ∈ I, 0 ≤ b i) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (hα0 : 0 < α) (hα1 : α < 1) (x y : E) :
    dist (disjointStage I (fun i => cutoffAffineFlatten (F i) (Bad i) (b i) c α) x)
      (disjointStage I (fun i => cutoffAffineFlatten (F i) (Bad i) (b i) c α) y) ≤
      ((1 + α * c) / (1 - α)) ^ 2 * dist x y := by
  have hL : 1 ≤ (1 + α * c) / (1 - α) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - α)).2
    nlinarith [mul_nonneg hα0.le hc0]
  let L : NNReal := ⟨(1 + α * c) / (1 - α), le_trans zero_le_one hL⟩
  have hLip : ∀ i ∈ I,
      LipschitzWith L (cutoffAffineFlatten (F i) (Bad i) (b i) c α) := by
    intro i hi
    exact LipschitzWith.of_dist_le_mul
      (cutoffAffineFlatten_lipschitz (F i) (Bad i) (hb i hi) hc0 hα0.le hα1)
  have hstage := disjointStage_lipschitz I _
    (cutoffAffineFlatten_family_disjoint I F Bad A b hbad hcross hb hc0 hc1 hα0.le hα1)
    (cutoffAffineFlatten_family_stable I F Bad A b hbad hcross hb hc0 hc1 hα0 hα1)
    (show 1 ≤ L from hL) hLip
  have hd := hstage.dist_le_mul x y
  rw [NNReal.coe_mul] at hd
  change _ ≤ ((1 + α * c) / (1 - α)) * ((1 + α * c) / (1 - α)) * dist x y at hd
  simpa only [pow_two] using hd

end Family

end BrehmApprox
