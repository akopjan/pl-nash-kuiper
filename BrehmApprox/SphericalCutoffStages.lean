module

public import BrehmApprox.SphericalOrthogonalProjection
public import BrehmApprox.CutoffStages
public import BrehmApprox.MetricSupport

/-!
# Spherical distance cut-offs with different chart poles

The cut-off radius is measured by actual spherical distance to the bad set,
then pulled back to the tangent chart. This gives disjoint and stable active
regions even when two faces use different gnomonic poles. The maps are
defined on the whole round sphere by the identity outside their respective
open hemispheres. Quantitative Lipschitz estimates are asserted on small
caps or invariant cells, not on the entire sphere.
-/

@[expose] public section

noncomputable section

open scoped Topology NNReal

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normalFlatten_ne_of_near (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α R : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {z : E}
    (hz : z ≠ K.starProjection z) (hnear : ‖z - K.starProjection z‖ < R) :
    normalFlatten K α R z ≠ z := by
  have hpos : 0 < ‖z - K.starProjection z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hnorm : ‖normalFlatten K α R z - K.starProjection z‖ =
      radialProfile α R ‖z - K.starProjection z‖ := by
    rw [normalFlatten, add_sub_cancel_left]
    exact radialFlatten_norm hα0.le hα1 (hpos.le.trans hnear.le) _
  intro heq
  rw [heq] at hnorm
  have hlt := radialProfile_lt hα0 hα1 hpos hnear
  linarith

lemma normalFlatten_normal_norm_le (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {α R : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hR : 0 ≤ R) (z : E) :
    ‖normalFlatten K α R z - K.starProjection z‖ ≤ ‖z - K.starProjection z‖ := by
  rw [normalFlatten, add_sub_cancel_left, radialFlatten_norm hα0 hα1 hR]
  exact radialProfile_le _ _ _

end BrehmApprox

namespace GeodesicSphere

open BrehmApprox

variable {n : ℕ}

/-- A global bound for the inverse chart in angular distance. -/
lemma gnomonicInverse_dist_le_global (p : GeodesicSphere n) (z w : tangentPlane p) :
    dist (gnomonicInverse p z).val (gnomonicInverse p w).val ≤
      (Real.pi / 2) * dist z w :=
  (dist_le_pi_div_two_mul_chord _ _).trans
    (mul_le_mul_of_nonneg_left (gnomonicInverse_chord_le p z w) (by positivity))

/-- The cut-off is measured in spherical distance, independently of chart
coordinates, so it can be compared across different poles. -/
def sphericalDistanceCutoff (p : GeodesicSphere n) (Bad : Set (GeodesicSphere n))
    (b c : ℝ) (z : tangentPlane p) : ℝ :=
  distanceCutoff Bad b c (gnomonicInverse p z).val

lemma sphericalDistanceCutoff_nonneg (p : GeodesicSphere n) (Bad : Set (GeodesicSphere n))
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (z : tangentPlane p) :
    0 ≤ sphericalDistanceCutoff p Bad b c z := distanceCutoff_nonneg Bad hb hc _

lemma sphericalDistanceCutoff_lipschitz (p : GeodesicSphere n) (Bad : Set (GeodesicSphere n))
    (b : ℝ) {c : ℝ} (hc : 0 ≤ c) (z w : tangentPlane p) :
    |sphericalDistanceCutoff p Bad b c z - sphericalDistanceCutoff p Bad b c w| ≤
      (c * (Real.pi / 2)) * dist z w := by
  calc
    _ ≤ c * dist (gnomonicInverse p z).val (gnomonicInverse p w).val :=
      distanceCutoff_lipschitz Bad b hc _ _
    _ ≤ c * ((Real.pi / 2) * dist z w) :=
      mul_le_mul_of_nonneg_left (gnomonicInverse_dist_le_global p z w) hc
    _ = _ := by ring

/-- The actual spherical face collapse, totalized by the identity outside
its chart hemisphere. -/
def cutoffSphericalFlatten (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (Bad : Set (GeodesicSphere n)) (b c α : ℝ) (x : GeodesicSphere n) : GeodesicSphere n := by
  classical
  exact if hx : x ∈ openHemisphere p then
    (sphericalNormalFlatten p (tangentSubspace p L) α
      (sphericalDistanceCutoff p Bad b c) ⟨x, hx⟩).val else x

lemma cutoffSphericalFlatten_in (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (Bad : Set (GeodesicSphere n)) (b c α : ℝ) {x : GeodesicSphere n}
    (hx : x ∈ openHemisphere p) :
    cutoffSphericalFlatten p L Bad b c α x =
      (sphericalNormalFlatten p (tangentSubspace p L) α
        (sphericalDistanceCutoff p Bad b c) ⟨x, hx⟩).val := by
  classical
  simp only [cutoffSphericalFlatten, dite_eq_left hx]

lemma cutoffSphericalFlatten_active_in_hemisphere (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (Bad : Set (GeodesicSphere n)) (b c α : ℝ) {x : GeodesicSphere n}
    (hx : cutoffSphericalFlatten p L Bad b c α x ≠ x) : x ∈ openHemisphere p := by
  classical
  by_contra hnot
  exact hx (by simp only [cutoffSphericalFlatten, dite_eq_right hnot])

lemma cutoffSphericalFlatten_normal_lt_of_ne (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (Bad : Set (GeodesicSphere n)) (b c : ℝ) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) {x : GeodesicSphere n}
    (hxp : x ∈ openHemisphere p) (hx : cutoffSphericalFlatten p L Bad b c α x ≠ x) :
    ‖gnomonic p ⟨x, hxp⟩ - (tangentSubspace p L).starProjection (gnomonic p ⟨x, hxp⟩)‖ <
      sphericalDistanceCutoff p Bad b c ((tangentSubspace p L).starProjection (gnomonic p ⟨x, hxp⟩)) := by
  apply lt_of_not_ge
  intro hout
  apply hx
  rw [cutoffSphericalFlatten_in p L Bad b c α hxp,
    sphericalNormalFlatten_outer p (tangentSubspace p L) hα0 hα1 _ hout]

/-- Every active point is closer to its genuine great-sphere foot than a
fixed small multiple of the distance from that foot to any bad point. -/
lemma cutoffSphericalFlatten_active_dist_bound (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (Bad : Set (GeodesicSphere n)) (b : ℝ) {c α : ℝ} (hc : 0 ≤ c)
    (hα0 : 0 ≤ α) (hα1 : α < 1) {x : GeodesicSphere n}
    (hxp : x ∈ openHemisphere p) (hx : cutoffSphericalFlatten p L Bad b c α x ≠ x)
    {y : GeodesicSphere n} (hy : y ∈ Bad) :
    dist x (greatSphereProjection p L ⟨x, hxp⟩).val <
      ((Real.pi / 2) * c) * dist (greatSphereProjection p L ⟨x, hxp⟩).val y := by
  let z := gnomonic p ⟨x, hxp⟩
  let K := tangentSubspace p L
  have hnear := cutoffSphericalFlatten_normal_lt_of_ne p L Bad b c hα0 hα1 hxp hx
  have hdist := gnomonicInverse_dist_le_global p z (K.starProjection z)
  rw [gnomonicInverse_gnomonic] at hdist
  change dist x (greatSphereProjection p L ⟨x, hxp⟩).val ≤ (Real.pi / 2) * dist z (K.starProjection z) at hdist
  rw [dist_eq_norm] at hdist
  calc
    _ ≤ (Real.pi / 2) * ‖z - K.starProjection z‖ := hdist
    _ < (Real.pi / 2) * sphericalDistanceCutoff p Bad b c (K.starProjection z) :=
      mul_lt_mul_of_pos_left hnear (by positivity)
    _ ≤ (Real.pi / 2) * (c * dist (greatSphereProjection p L ⟨x, hxp⟩).val y) :=
      mul_le_mul_of_nonneg_left (distanceCutoff_le_dist Bad b hc _ hy) (by positivity)
    _ = _ := by ring

/-- Activity forces the foot into the actual prescribed face, when the bad
set contains the rest of its supporting great subsphere. -/
lemma cutoffSphericalFlatten_foot_mem_of_ne (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hpL : p.val ∈ L)
    (Bad : Set (GeodesicSphere n)) {A : Set (GeodesicSphere n)}
    (hbad : {x : GeodesicSphere n | x.val ∈ L} \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {x : GeodesicSphere n} (hxp : x ∈ openHemisphere p)
    (hx : cutoffSphericalFlatten p L Bad b c α x ≠ x) :
    (greatSphereProjection p L ⟨x, hxp⟩).val ∈ A := by
  by_contra hnot
  have hBad := hbad ⟨greatSphereProjection_mem p L hpL ⟨x, hxp⟩, hnot⟩
  have hnear := cutoffSphericalFlatten_normal_lt_of_ne p L Bad b c hα0 hα1 hxp hx
  change _ < distanceCutoff Bad b c (greatSphereProjection p L ⟨x, hxp⟩).val at hnear
  rw [distanceCutoff_zero_of_mem Bad hb hBad] at hnear
  exact (norm_nonneg _).not_gt hnear

theorem cutoffSphericalFlatten_active_foot (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hpL : p.val ∈ L)
    (Bad : Set (GeodesicSphere n)) {A : Set (GeodesicSphere n)}
    (hbad : {x : GeodesicSphere n | x.val ∈ L} \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {x : GeodesicSphere n} (hx : cutoffSphericalFlatten p L Bad b c α x ≠ x) :
    ∃ t ∈ A, ∀ y ∈ Bad, dist x t < ((Real.pi / 2) * c) * dist t y := by
  have hxp := cutoffSphericalFlatten_active_in_hemisphere p L Bad b c α hx
  refine ⟨(greatSphereProjection p L ⟨x, hxp⟩).val,
    cutoffSphericalFlatten_foot_mem_of_ne p L hpL Bad hbad hb hα0 hα1 hxp hx, ?_⟩
  intro y hy
  exact cutoffSphericalFlatten_active_dist_bound p L Bad b hc hα0 hα1 hxp hx hy

lemma cutoffSphericalFlatten_fix_on_bad (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (Bad : Set (GeodesicSphere n)) (b : ℝ) {c α : ℝ} (hc0 : 0 ≤ c)
    (hc1 : (Real.pi / 2) * c ≤ 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {x : GeodesicSphere n} (hx : x ∈ Bad) : cutoffSphericalFlatten p L Bad b c α x = x := by
  by_contra hactive
  have hxp := cutoffSphericalFlatten_active_in_hemisphere p L Bad b c α hactive
  have h := cutoffSphericalFlatten_active_dist_bound p L Bad b hc0 hα0 hα1 hxp hactive hx
  rw [dist_comm (greatSphereProjection p L ⟨x, hxp⟩).val x] at h
  have hle := mul_le_mul_of_nonneg_right hc1
    (dist_nonneg : 0 ≤ dist x (greatSphereProjection p L ⟨x, hxp⟩).val)
  linarith

/-- The closure of the true spherical support can approach a bad set only
through the closed face itself. This does not assume global continuity of
the totalized chart map. -/
theorem cutoffSphericalFlatten_support_closure_inter_bad (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hpL : p.val ∈ L)
    (Bad : Set (GeodesicSphere n)) {A : Set (GeodesicSphere n)} (hA : IsClosed A)
    (hbad : {x : GeodesicSphere n | x.val ∈ L} \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc1 : (Real.pi / 2) * c < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    closure {x | cutoffSphericalFlatten p L Bad b c α x ≠ x} ∩ Bad ⊆ A := by
  apply closure_inter_bad_subset_of_feet hA (by positivity) hc1
  intro u hu
  obtain ⟨t, ht, hdist⟩ := cutoffSphericalFlatten_active_foot p L hpL Bad hbad hb hc0 hα0 hα1 hu
  exact ⟨t, ht, fun y hy => (hdist y hy).le⟩

theorem cutoffSphericalFlatten_eventually_fixed_on_bad (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hpL : p.val ∈ L)
    (Bad : Set (GeodesicSphere n)) {A : Set (GeodesicSphere n)} (hA : IsClosed A)
    (hbad : {x : GeodesicSphere n | x.val ∈ L} \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hc1 : (Real.pi / 2) * c < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) {x : GeodesicSphere n} (hxBad : x ∈ Bad) (hxA : x ∉ A) :
    ∀ᶠ y in 𝓝 x, cutoffSphericalFlatten p L Bad b c α y = y := by
  apply eventually_fixed_of_metric_feet _ hA (by positivity) hc1 _ hxBad hxA
  intro u hu
  obtain ⟨t, ht, hdist⟩ := cutoffSphericalFlatten_active_foot p L hpL Bad hbad hb hc0 hα0 hα1 hu
  exact ⟨t, ht, fun y hy => (hdist y hy).le⟩

/-- A moved image either remains active for the same collapse or has reached
its actual face. The claim uses the explicit radial profile. -/
theorem cutoffSphericalFlatten_image_active_or_face (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hpL : p.val ∈ L)
    (Bad : Set (GeodesicSphere n)) {A : Set (GeodesicSphere n)}
    (hbad : {x : GeodesicSphere n | x.val ∈ L} \ A ⊆ Bad)
    {b c α : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    {x : GeodesicSphere n} (hx : cutoffSphericalFlatten p L Bad b c α x ≠ x) :
    cutoffSphericalFlatten p L Bad b c α (cutoffSphericalFlatten p L Bad b c α x) ≠
      cutoffSphericalFlatten p L Bad b c α x ∨ cutoffSphericalFlatten p L Bad b c α x ∈ A := by
  have hxp := cutoffSphericalFlatten_active_in_hemisphere p L Bad b c α hx
  let K := tangentSubspace p L
  let R := sphericalDistanceCutoff p Bad b c
  let xH : openHemisphere p := ⟨x, hxp⟩
  let z := gnomonic p xH
  let qH := sphericalNormalFlatten p K α R xH
  have hQx : cutoffSphericalFlatten p L Bad b c α x = qH.val :=
    cutoffSphericalFlatten_in p L Bad b c α hxp
  have hfoot : (greatSphereProjection p L xH).val ∈ A :=
    cutoffSphericalFlatten_foot_mem_of_ne p L hpL Bad hbad hb hα0.le hα1 hxp hx
  have hproj : K.starProjection (gnomonic p qH) = K.starProjection z :=
    sphericalNormalFlatten_projection p K α R xH
  rw [hQx]
  by_cases hq : gnomonic p qH = K.starProjection z
  · apply Or.inr
    have heq : qH = greatSphereProjection p L xH := by
      rw [← gnomonicInverse_gnomonic p qH, hq]
      rfl
    rw [heq]
    exact hfoot
  · apply Or.inl
    have hnear := cutoffSphericalFlatten_normal_lt_of_ne p L Bad b c hα0.le hα1 hxp hx
    have hnorm : ‖gnomonic p qH - K.starProjection z‖ ≤ ‖z - K.starProjection z‖ := by
      simpa only [qH, gnomonic_sphericalNormalFlatten, taperedNormalFlatten] using
        normalFlatten_normal_norm_le K hα0.le hα1
          (sphericalDistanceCutoff_nonneg p Bad hb hc (K.starProjection z)) z
    have hqne : sphericalNormalFlatten p K α R qH ≠ qH := by
      intro heq
      have heqchart := congrArg (gnomonic p) heq
      rw [gnomonic_sphericalNormalFlatten] at heqchart
      have hnearQ : ‖gnomonic p qH - K.starProjection (gnomonic p qH)‖ <
          R (K.starProjection (gnomonic p qH)) := by
        rw [hproj]
        exact hnorm.trans_lt hnear
      have hnot : gnomonic p qH ≠ K.starProjection (gnomonic p qH) := by rwa [hproj]
      exact normalFlatten_ne_of_near K hα0 hα1 hnot hnearQ heqchart
    rw [cutoffSphericalFlatten_in p L Bad b c α qH.property]
    exact fun heq => hqne (Subtype.ext heq)

/-- Two genuine spherical face collapses with different chart poles cannot
both move one point when each bad set contains the other face. -/
theorem cutoffSphericalFlatten_disjoint_activity
    (p q : GeodesicSphere n)
    (L M : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hpL : p.val ∈ L) (hqM : q.val ∈ M)
    (BadL BadM : Set (GeodesicSphere n)) {A B : Set (GeodesicSphere n)}
    (hbadL : {x : GeodesicSphere n | x.val ∈ L} \ A ⊆ BadL)
    (hbadM : {x : GeodesicSphere n | x.val ∈ M} \ B ⊆ BadM)
    (hAB : A ⊆ BadM) (hBA : B ⊆ BadL) {bL bM c α : ℝ}
    (hbL : 0 ≤ bL) (hbM : 0 ≤ bM) (hc0 : 0 ≤ c) (hc1 : (Real.pi / 2) * c ≤ 1 / 2)
    (hα0 : 0 ≤ α) (hα1 : α < 1) {x : GeodesicSphere n}
    (hx : cutoffSphericalFlatten p L BadL bL c α x ≠ x) :
    cutoffSphericalFlatten q M BadM bM c α x = x := by
  by_contra hy
  obtain ⟨u, huA, hu⟩ := cutoffSphericalFlatten_active_foot p L hpL BadL hbadL hbL hc0 hα0 hα1 hx
  obtain ⟨v, hvB, hv⟩ := cutoffSphericalFlatten_active_foot q M hqM BadM hbadM hbM hc0 hα0 hα1 hy
  have h1 := hu v (hBA hvB)
  have h2 := hv u (hAB huA)
  rw [dist_comm v u] at h2
  have htri := dist_triangle u x v
  rw [dist_comm u x] at htri
  have hcoeff : 2 * ((Real.pi / 2) * c) * dist u v ≤ dist u v :=
    mul_le_of_le_one_left dist_nonneg (by linarith)
  linarith

theorem cutoffSphericalFlatten_stable_activity
    (p q : GeodesicSphere n)
    (L M : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hpL : p.val ∈ L) (hqM : q.val ∈ M)
    (BadL BadM : Set (GeodesicSphere n)) {A B : Set (GeodesicSphere n)}
    (hbadL : {x : GeodesicSphere n | x.val ∈ L} \ A ⊆ BadL)
    (hbadM : {x : GeodesicSphere n | x.val ∈ M} \ B ⊆ BadM)
    (hAB : A ⊆ BadM) (hBA : B ⊆ BadL) {bL bM c α : ℝ}
    (hbL : 0 ≤ bL) (hbM : 0 ≤ bM) (hc0 : 0 ≤ c) (hc1 : (Real.pi / 2) * c ≤ 1 / 2)
    (hα0 : 0 < α) (hα1 : α < 1) {x : GeodesicSphere n}
    (hx : cutoffSphericalFlatten p L BadL bL c α x ≠ x) :
    cutoffSphericalFlatten q M BadM bM c α (cutoffSphericalFlatten p L BadL bL c α x) =
      cutoffSphericalFlatten p L BadL bL c α x := by
  rcases cutoffSphericalFlatten_image_active_or_face p L hpL BadL hbadL hbL hc0 hα0 hα1 hx with
    hactive | hface
  · exact cutoffSphericalFlatten_disjoint_activity p q L M hpL hqM BadL BadM
      hbadL hbadM hAB hBA hbL hbM hc0 hc1 hα0.le hα1 hactive
  · exact cutoffSphericalFlatten_fix_on_bad q M BadM bM hc0 (by linarith) hα0.le hα1 (hAB hface)

/-- Every incident hemispherical cell is preserved by the actual cut-off map. -/
theorem cutoffSphericalFlatten_mapsTo_cell (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hpL : p.val ∈ L)
    (Bad : Set (GeodesicSphere n)) {A : Set (GeodesicSphere n)}
    (hbad : {x : GeodesicSphere n | x.val ∈ L} \ A ⊆ Bad)
    (V : Finset (GeodesicSphere n)) (hV : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (hAV : A ⊆ sphericalCell V) {b c α : ℝ}
    (hb : 0 ≤ b) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Set.MapsTo (cutoffSphericalFlatten p L Bad b c α) (sphericalCell V) (sphericalCell V) := by
  intro x hxV
  by_cases hx : cutoffSphericalFlatten p L Bad b c α x = x
  · rwa [hx]
  · have hxp := cutoffSphericalFlatten_active_in_hemisphere p L Bad b c α hx
    rw [cutoffSphericalFlatten_in p L Bad b c α hxp]
    apply sphericalNormalFlatten_mem_cell p V hV (tangentSubspace p L) α
      (sphericalDistanceCutoff p Bad b c) ⟨x, hxp⟩ hxV
    exact hAV (cutoffSphericalFlatten_foot_mem_of_ne p L hpL Bad hbad hb hα0 hα1 hxp hx)

/-- The cap Lipschitz bound uses the spherical cut-off's proved chart
constant. A family may use a different pole for every face. -/
theorem cutoffSphericalFlatten_lipschitz_on_cap (p : GeodesicSphere n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (Bad : Set (GeodesicSphere n)) {b c α ρ : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi / 2)
    (x y : GeodesicSphere n) (hx : dist p x ≤ ρ) (hy : dist p y ≤ ρ) :
    dist (cutoffSphericalFlatten p L Bad b c α x) (cutoffSphericalFlatten p L Bad b c α y) ≤
      sphericalFlattenFactor α (c * (Real.pi / 2)) ρ * dist x y := by
  have hxp : x ∈ openHemisphere p := (dist_lt_pi_div_two_iff p x).mp (hx.trans_lt hρπ)
  have hyp : y ∈ openHemisphere p := (dist_lt_pi_div_two_iff p y).mp (hy.trans_lt hρπ)
  rw [cutoffSphericalFlatten_in p L Bad b c α hxp, cutoffSphericalFlatten_in p L Bad b c α hyp]
  exact sphericalNormalFlatten_lipschitz p (tangentSubspace p L) hα0 hα1 (by positivity) hρ0 hρπ
    (sphericalDistanceCutoff p Bad b c) (fun z _ => sphericalDistanceCutoff_nonneg p Bad hb hc z)
    (fun z _ w _ => sphericalDistanceCutoff_lipschitz p Bad b hc z w) ⟨x, hxp⟩ ⟨y, hyp⟩ hx hy

/-- The simultaneous-stage factor. The square is independent of the number
of faces, and the harmless maximum also covers an empty active family. -/
def sphericalStageFactor (α c ρ : ℝ) : ℝ :=
  (max 1 (sphericalFlattenFactor α (c * (Real.pi / 2)) ρ)) ^ 2

@[simp]
lemma sphericalStageFactor_zero (c : ℝ) : sphericalStageFactor 0 c 0 = 1 := by
  simp [sphericalStageFactor]

lemma continuousAt_sphericalStageFactor (c : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => sphericalStageFactor q.1 c q.2) (0, 0) :=
  (continuousAt_const.max (continuousAt_sphericalFlattenFactor (c * (Real.pi / 2)))).pow 2

/-- Any fixed number of dimension stages has a factor arbitrarily close to
one. This quantifier is independent of how many faces a fine subdivision has. -/
theorem exists_sphericalStageFactor_pow_lt (c : ℝ) (N : ℕ) {K : ℝ} (hK : 1 < K) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < Real.pi / 2 ∧
      ∀ α ρ : ℝ, 0 ≤ α → α ≤ δ → 0 ≤ ρ → ρ ≤ δ →
        (sphericalStageFactor α c ρ) ^ N < K := by
  have hcont := (continuousAt_sphericalStageFactor c).pow N
  obtain ⟨η, hη, hbound⟩ := Metric.continuousAt_iff.mp hcont (K - 1) (by linarith)
  let δ := min (η / 2) (min (1 / 2) (Real.pi / 4))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt
    ((min_le_left _ _).trans_lt (by norm_num))
  have hδπ : δ < Real.pi / 2 := (min_le_right _ _).trans_lt
    ((min_le_right _ _).trans_lt (by linarith [Real.pi_pos]))
  refine ⟨δ, hδ0, hδ1, hδπ, ?_⟩
  intro α ρ hα0 hαδ hρ0 hρδ
  have hd : dist (α, ρ) (0, 0) < η := by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg hα0, abs_of_nonneg hρ0]
    exact max_lt (hαδ.trans_lt hδη) (hρδ.trans_lt hδη)
  have h := hbound hd
  change dist ((sphericalStageFactor α c ρ) ^ N) ((sphericalStageFactor 0 c 0) ^ N) < K - 1 at h
  simp only [sphericalStageFactor_zero, one_pow, Real.dist_eq] at h
  have hu := (abs_lt.mp h).2
  linarith

section Family

variable {ι : Type*} (I : Finset ι) (p : ι → GeodesicSphere n)
  (L : ι → Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
  (Bad A : ι → Set (GeodesicSphere n)) (b : ι → ℝ) {c α : ℝ}

theorem cutoffSphericalFlatten_family_disjoint
    (hp : ∀ i ∈ I, (p i).val ∈ L i)
    (hbad : ∀ i ∈ I, {x : GeodesicSphere n | x.val ∈ L i} \ A i ⊆ Bad i)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → A i ⊆ Bad j)
    (hb : ∀ i ∈ I, 0 ≤ b i) (hc0 : 0 ≤ c) (hc1 : (Real.pi / 2) * c ≤ 1 / 2)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    DisjointActivity I (fun i => cutoffSphericalFlatten (p i) (L i) (Bad i) (b i) c α) := by
  intro i hi j hj hij x hx
  exact cutoffSphericalFlatten_disjoint_activity (p i) (p j) (L i) (L j) (hp i hi) (hp j hj)
    (Bad i) (Bad j) (hbad i hi) (hbad j hj) (hcross i hi j hj hij)
    (hcross j hj i hi hij.symm) (hb i hi) (hb j hj) hc0 hc1 hα0 hα1 hx

theorem cutoffSphericalFlatten_family_stable
    (hp : ∀ i ∈ I, (p i).val ∈ L i)
    (hbad : ∀ i ∈ I, {x : GeodesicSphere n | x.val ∈ L i} \ A i ⊆ Bad i)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → A i ⊆ Bad j)
    (hb : ∀ i ∈ I, 0 ≤ b i) (hc0 : 0 ≤ c) (hc1 : (Real.pi / 2) * c ≤ 1 / 2)
    (hα0 : 0 < α) (hα1 : α < 1) :
    StableActivity I (fun i => cutoffSphericalFlatten (p i) (L i) (Bad i) (b i) c α) := by
  intro i hi j hj hij x hx
  exact cutoffSphericalFlatten_stable_activity (p i) (p j) (L i) (L j) (hp i hi) (hp j hj)
    (Bad i) (Bad j) (hbad i hi) (hbad j hj) (hcross i hi j hj hij)
    (hcross j hj i hi hij.symm) (hb i hi) (hb j hj) hc0 hc1 hα0 hα1 hx

/-- A finite simultaneous family with arbitrary distinct chart poles has a
cardinality-independent bound on every invariant common small cell. -/
theorem cutoffSphericalFlatten_stage_lipschitzOn
    (hp : ∀ i ∈ I, (p i).val ∈ L i)
    (hbad : ∀ i ∈ I, {x : GeodesicSphere n | x.val ∈ L i} \ A i ⊆ Bad i)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → A i ⊆ Bad j)
    (hb : ∀ i ∈ I, 0 ≤ b i) (hc0 : 0 ≤ c) (hc1 : (Real.pi / 2) * c ≤ 1 / 2)
    (hα0 : 0 < α) (hα1 : α < 1) {D : Set (GeodesicSphere n)}
    (hpres : ∀ i ∈ I, Set.MapsTo (cutoffSphericalFlatten (p i) (L i) (Bad i) (b i) c α) D D)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi / 2)
    (hcap : ∀ i ∈ I, ∀ x ∈ D, dist (p i) x ≤ ρ) :
    ∀ x ∈ D, ∀ y ∈ D,
      dist (disjointStage I (fun i => cutoffSphericalFlatten (p i) (L i) (Bad i) (b i) c α) x)
        (disjointStage I (fun i => cutoffSphericalFlatten (p i) (L i) (Bad i) (b i) c α) y) ≤
          sphericalStageFactor α c ρ * dist x y := by
  let F : ℝ≥0 := ⟨max 1 (sphericalFlattenFactor α (c * (Real.pi / 2)) ρ),
    zero_le_one.trans (le_max_left _ _)⟩
  have hLip : ∀ i ∈ I, ∀ x ∈ D, ∀ y ∈ D,
      dist (cutoffSphericalFlatten (p i) (L i) (Bad i) (b i) c α x)
        (cutoffSphericalFlatten (p i) (L i) (Bad i) (b i) c α y) ≤ (F : ℝ) * dist x y := by
    intro i hi x hx y hy
    exact (cutoffSphericalFlatten_lipschitz_on_cap (p i) (L i) (Bad i) (hb i hi) hc0
      hα0.le hα1 hρ0 hρπ x y (hcap i hi x hx) (hcap i hi y hy)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)
  have hstage := disjointStage_lipschitzOn I _
    (cutoffSphericalFlatten_family_disjoint I p L Bad A b hp hbad hcross hb hc0 hc1 hα0.le hα1)
    (cutoffSphericalFlatten_family_stable I p L Bad A b hp hbad hcross hb hc0 hc1 hα0 hα1)
    hpres (show 1 ≤ F from le_max_left _ _) hLip
  intro x hx y hy
  have hd := hstage x hx y hy
  change _ ≤ (max 1 (sphericalFlattenFactor α (c * (Real.pi / 2)) ρ) *
    max 1 (sphericalFlattenFactor α (c * (Real.pi / 2)) ρ)) * dist x y at hd
  simpa only [sphericalStageFactor, pow_two] using hd

end Family

end GeodesicSphere
