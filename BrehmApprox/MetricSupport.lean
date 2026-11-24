module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.Linarith

/-!
# Support closure from metric foot estimates

An active point lies much nearer a foot in the closed core than that foot
lies to a bad point. The closure of the active set therefore meets the bad
set only in the core. The proof needs no continuity of the active map or of
the selected foot.
-/

@[expose] public section

open scoped Topology

namespace BrehmApprox

variable {X : Type*} [MetricSpace X]

/-- The distance-to-core inequality passes to the closure of the active set. -/
lemma infDist_bound_on_closure_of_feet {U A Bad : Set X} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hfeet : ∀ u ∈ U, ∃ t ∈ A, ∀ b ∈ Bad, dist u t ≤ k * dist t b)
    {x b : X} (hx : x ∈ closure U) (hb : b ∈ Bad) :
    (1 - k) * Metric.infDist x A ≤ k * dist x b := by
  let S : Set X := {u | (1 - k) * Metric.infDist u A ≤ k * dist u b}
  have hS : IsClosed S := isClosed_le
    (continuous_const.mul (Metric.lipschitz_infDist_pt A).continuous)
    (continuous_const.mul (continuous_id.dist continuous_const))
  have hUS : U ⊆ S := by
    intro u hu
    obtain ⟨t, ht, hdist⟩ := hfeet u hu
    have h1 := hdist b hb
    have htri := dist_triangle t u b
    rw [dist_comm t u] at htri
    have h2 := mul_le_mul_of_nonneg_left htri hk0
    have h3 := mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem ht :
      Metric.infDist u A ≤ dist u t) (sub_nonneg.mpr hk1.le)
    change (1 - k) * Metric.infDist u A ≤ k * dist u b
    nlinarith
  exact closure_minimal hUS hS hx

theorem closure_inter_bad_subset_of_feet {U A Bad : Set X} (hA : IsClosed A)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hfeet : ∀ u ∈ U, ∃ t ∈ A, ∀ b ∈ Bad, dist u t ≤ k * dist t b) :
    closure U ∩ Bad ⊆ A := by
  rintro x ⟨hx, hxBad⟩
  have hU : U.Nonempty := closure_nonempty_iff.mp ⟨x, hx⟩
  obtain ⟨u, hu⟩ := hU
  obtain ⟨t, ht, _⟩ := hfeet u hu
  have h := infDist_bound_on_closure_of_feet hk0 hk1 hfeet hx hxBad
  rw [dist_self, mul_zero] at h
  apply (hA.mem_iff_infDist_zero ⟨t, ht⟩).mpr
  have hn := Metric.infDist_nonneg (x := x) (s := A)
  nlinarith

/-- Away from the core, a bad point has a whole neighborhood on which the
map is exactly the identity. -/
theorem eventually_fixed_of_metric_feet (Q : X → X) {A Bad : Set X} (hA : IsClosed A)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hfeet : ∀ u, Q u ≠ u → ∃ t ∈ A, ∀ b ∈ Bad, dist u t ≤ k * dist t b)
    {p : X} (hpBad : p ∈ Bad) (hpA : p ∉ A) : ∀ᶠ x in 𝓝 p, Q x = x := by
  have hpcl : p ∉ closure {u | Q u ≠ u} := by
    intro hp
    exact hpA (closure_inter_bad_subset_of_feet hA hk0 hk1 hfeet ⟨hp, hpBad⟩)
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hpcl] with x hx
  by_contra hne
  exact hx (subset_closure hne)

end BrehmApprox
