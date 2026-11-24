module

public import BrehmApprox.AffineNormalFlattening
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Distance cut-offs and the support of an actual face collapse

The radius is `c * min b (dist (x, Bad))`, with the constant value `c * b`
when `Bad` is empty. This convention handles zero-dimensional faces without
inventing a real distance to the empty set. The resulting affine normal map
fixes `Bad`, preserves incident convex cells, and has support closure meeting
`Bad` only along the face itself.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

section Metric

variable {X : Type*} [MetricSpace X]

def distanceCutoff (Bad : Set X) (b c : ℝ) (x : X) : ℝ := by
  classical
  exact if Bad.Nonempty then c * min b (Metric.infDist x Bad) else c * b

lemma distanceCutoff_nonneg (Bad : Set X) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (x : X) : 0 ≤ distanceCutoff Bad b c x := by
  classical
  unfold distanceCutoff
  split_ifs
  · exact mul_nonneg hc (le_min hb Metric.infDist_nonneg)
  · exact mul_nonneg hc hb

lemma distanceCutoff_le (Bad : Set X) (b : ℝ) {c : ℝ} (hc : 0 ≤ c) (x : X) :
    distanceCutoff Bad b c x ≤ c * b := by
  classical
  unfold distanceCutoff
  split_ifs
  · exact mul_le_mul_of_nonneg_left (min_le_left _ _) hc
  · exact le_rfl

lemma distanceCutoff_zero_of_mem (Bad : Set X) {b c : ℝ} (hb : 0 ≤ b)
    {x : X} (hx : x ∈ Bad) : distanceCutoff Bad b c x = 0 := by
  classical
  simp only [distanceCutoff, ite_eq_left (show Bad.Nonempty from ⟨x, hx⟩),
    Metric.infDist_zero_of_mem hx, min_eq_right hb, mul_zero]

lemma distanceCutoff_pos (Bad : Set X) (hBad : IsClosed Bad) {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) {x : X} (hx : x ∉ Bad) :
    0 < distanceCutoff Bad b c x := by
  classical
  unfold distanceCutoff
  split_ifs with hne
  · exact mul_pos hc (lt_min hb ((hBad.notMem_iff_infDist_pos hne).mp hx))
  · exact mul_pos hc hb

lemma distanceCutoff_le_dist (Bad : Set X) (b : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (x : X) {y : X} (hy : y ∈ Bad) : distanceCutoff Bad b c x ≤ c * dist x y := by
  classical
  simp only [distanceCutoff, ite_eq_left (show Bad.Nonempty from ⟨y, hy⟩)]
  exact mul_le_mul_of_nonneg_left
    ((min_le_right _ _).trans (Metric.infDist_le_dist_of_mem hy)) hc

lemma distanceCutoff_lipschitz (Bad : Set X) (b : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (x y : X) : |distanceCutoff Bad b c x - distanceCutoff Bad b c y| ≤ c * dist x y := by
  classical
  by_cases hne : Bad.Nonempty
  · simp only [distanceCutoff, ite_eq_left hne, ← mul_sub, abs_mul, abs_of_nonneg hc]
    have habs : (0 : ℝ) ≤ |Metric.infDist x Bad - Metric.infDist y Bad| := abs_nonneg _
    have hmin : |min b (Metric.infDist x Bad) - min b (Metric.infDist y Bad)| ≤
        |Metric.infDist x Bad - Metric.infDist y Bad| := by
      simpa only [sub_self, abs_zero, max_eq_right habs] using
        abs_min_sub_min_le_max b (Metric.infDist x Bad) b (Metric.infDist y Bad)
    have hd : |Metric.infDist x Bad - Metric.infDist y Bad| ≤ dist x y := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (Metric.lipschitz_infDist_pt Bad).dist_le_mul x y
    exact mul_le_mul_of_nonneg_left (hmin.trans hd) hc
  · simp only [distanceCutoff, ite_eq_right hne, sub_self, abs_zero]
    exact mul_nonneg hc dist_nonneg

lemma distanceCutoff_continuous (Bad : Set X) (b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (distanceCutoff Bad b c) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨c, hc⟩) ?_).continuous
  intro x y
  rw [Real.dist_eq]
  exact distanceCutoff_lipschitz Bad b hc x y

end Metric

section Affine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine affine face collapse with bounded distance cut-off. -/
def cutoffAffineFlatten (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) (b c α : ℝ) : E → E :=
  affineNormalFlatten F α (distanceCutoff Bad b c)

theorem cutoffAffineFlatten_lipschitz (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {b c α : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α < 1) (x y : E) :
    dist (cutoffAffineFlatten F Bad b c α x) (cutoffAffineFlatten F Bad b c α y) ≤
      ((1 + α * c) / (1 - α)) * dist x y :=
  affineNormalFlatten_lipschitz F hα0 hα1 hc _
    (fun z _ => distanceCutoff_nonneg Bad hb hc z)
    (fun z _ w _ => distanceCutoff_lipschitz Bad b hc z w) x y

lemma cutoffAffineFlatten_displacement (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {b c α : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α < 1) (x : E) :
    dist (cutoffAffineFlatten F Bad b c α x) x ≤ α * (c * b) :=
  (affineNormalFlatten_displacement F hα0 hα1 _
    (fun z _ => distanceCutoff_nonneg Bad hb hc z) x).trans
      (mul_le_mul_of_nonneg_left (distanceCutoff_le Bad b hc _) hα0)

lemma cutoffAffineFlatten_fix_on_bad (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {b c α : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {x : E} (hx : x ∈ Bad) : cutoffAffineFlatten F Bad b c α x = x := by
  apply affineNormalFlatten_outer F hα0 hα1
  have hbound := distanceCutoff_le_dist Bad b hc0 (affineProjection F x) hx
  have heq : dist (affineProjection F x) x = ‖x - affineProjection F x‖ := by
    rw [dist_comm, dist_eq_norm]
  rw [heq] at hbound
  exact hbound.trans (by nlinarith [norm_nonneg (x - affineProjection F x)])

/-- If the bad set contains the complement of the face within its affine
span, every point moved by the map projects into the face. -/
lemma cutoffAffineFlatten_projection_mem_of_ne (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {A : Set E}
    (hbad : (F : Set E) \ A ⊆ Bad) {b c α : ℝ} (hb : 0 ≤ b)
    (hα0 : 0 ≤ α) (hα1 : α < 1) {x : E}
    (hx : cutoffAffineFlatten F Bad b c α x ≠ x) : affineProjection F x ∈ A := by
  by_contra hp
  have hPBad := hbad ⟨affineProjection_mem F x, hp⟩
  have hzero : distanceCutoff Bad b c (affineProjection F x) = 0 :=
    distanceCutoff_zero_of_mem Bad hb hPBad
  apply hx
  apply affineNormalFlatten_outer F hα0 hα1
  rw [hzero]
  exact norm_nonneg _

/-- Every incident convex cell is preserved. This is proved from the actual
formula, not assumed as preparation data. -/
lemma cutoffAffineFlatten_mapsTo_convex (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {A C : Set E}
    (hbad : (F : Set E) \ A ⊆ Bad) (hAC : A ⊆ C) (hC : Convex ℝ C)
    {b c α : ℝ} (hb : 0 ≤ b) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Set.MapsTo (cutoffAffineFlatten F Bad b c α) C C := by
  intro x hxC
  by_cases hx : cutoffAffineFlatten F Bad b c α x = x
  · simpa only [hx] using hxC
  · exact affineNormalFlatten_mem_convex F α _ hC hxC
      (hAC (cutoffAffineFlatten_projection_mem_of_ne F Bad hbad hb hα0 hα1 hx))

/-- The support closure still satisfies the outer-radius inequality. -/
lemma cutoffAffineFlatten_normal_bound_on_closure (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {b c α : ℝ}
    (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α < 1) {x : E}
    (hx : x ∈ closure {y | cutoffAffineFlatten F Bad b c α y ≠ y}) :
    ‖x - affineProjection F x‖ ≤ distanceCutoff Bad b c (affineProjection F x) := by
  let S : Set E := {y | ‖y - affineProjection F y‖ ≤
    distanceCutoff Bad b c (affineProjection F y)}
  have hS : IsClosed S := isClosed_le
    (continuous_id.sub (affineProjection_short F).continuous).norm
    ((distanceCutoff_continuous Bad b hc).comp (affineProjection_short F).continuous)
  have hsub : {y | cutoffAffineFlatten F Bad b c α y ≠ y} ⊆ S := by
    intro y hy
    by_contra hnot
    have hout : distanceCutoff Bad b c (affineProjection F y) ≤ ‖y - affineProjection F y‖ :=
      (lt_of_not_ge hnot).le
    exact hy (affineNormalFlatten_outer F hα0 hα1 _ hout)
  exact closure_minimal hsub hS hx

/-- Support can approach a nonincident bad cell only through the face itself.
The strict factor `c < 1` is what forces the limiting normal vector to vanish. -/
theorem cutoffAffineFlatten_support_inter_bad (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {A : Set E} (hA : IsClosed A)
    (hbad : (F : Set E) \ A ⊆ Bad) {b c α : ℝ} (hb : 0 ≤ b)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    closure {y | cutoffAffineFlatten F Bad b c α y ≠ y} ∩ Bad ⊆ A ∩ Bad := by
  intro x hx
  have hnormal := cutoffAffineFlatten_normal_bound_on_closure F Bad hc0 hα0 hα1 hx.1
  have hcut := distanceCutoff_le_dist Bad b hc0 (affineProjection F x) hx.2
  have heqdist : dist (affineProjection F x) x = ‖x - affineProjection F x‖ := by
    rw [dist_comm, dist_eq_norm]
  rw [heqdist] at hcut
  have hzero : ‖x - affineProjection F x‖ = 0 := by
    nlinarith [norm_nonneg (x - affineProjection F x)]
  have hfix : x = affineProjection F x := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hclosed : IsClosed {y | affineProjection F y ∈ A} :=
    hA.preimage (affineProjection_short F).continuous
  have hsub : {y | cutoffAffineFlatten F Bad b c α y ≠ y} ⊆
      {y | affineProjection F y ∈ A} := by
    intro y hy
    exact cutoffAffineFlatten_projection_mem_of_ne F Bad hbad hb hα0 hα1 hy
  have hPx : affineProjection F x ∈ A := closure_minimal hsub hclosed hx.1
  exact ⟨hfix.symm ▸ hPx, hx.2⟩

/-- At a point of a nonincident cell outside the collapsed face, the map is
the identity on a whole ambient neighborhood. This supplies the preceding
identity factors in the descending face-composition argument. -/
theorem cutoffAffineFlatten_local_identity (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) {A : Set E} (hA : IsClosed A)
    (hbad : (F : Set E) \ A ⊆ Bad) {b c α : ℝ} (hb : 0 ≤ b)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {p : E} (hpBad : p ∈ Bad) (hpA : p ∉ A) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, cutoffAffineFlatten F Bad b c α x = x := by
  let M : Set E := {y | cutoffAffineFlatten F Bad b c α y ≠ y}
  have hpcl : p ∉ closure M := by
    intro h
    exact hpA ((cutoffAffineFlatten_support_inter_bad F Bad hA hbad hb hc0 hc1 hα0 hα1
      ⟨h, hpBad⟩).1)
  refine ⟨(closure M)ᶜ, isClosed_closure.isOpen_compl, hpcl, ?_⟩
  intro x hx
  by_contra hmove
  exact hx (subset_closure hmove)

/-- Positive distance from the closed bad set gives an actual open region of
normal collapse at every interior point of the face. -/
theorem cutoffAffineFlatten_local_collapse (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (Bad : Set E) (hBad : IsClosed Bad)
    {b c α : ℝ} (hb : 0 < b) (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1)
    {p : E} (hp : p ∈ F) (hpBad : p ∉ Bad) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, cutoffAffineFlatten F Bad b c α x = affineProjection F x :=
  affineNormalFlatten_local_collapse F hα0 hα1 hc.le _
    (fun z _ w _ => distanceCutoff_lipschitz Bad b hc.le z w) hp
    (distanceCutoff_pos Bad hBad hb hc hpBad)

end Affine
end BrehmApprox
