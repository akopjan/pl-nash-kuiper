module

public import BrehmApprox.ExplicitFourOctantSource

/-!
# An infinite fiber for every sufficiently close short approximation

This strengthens the concrete counterexample without using a predicate for
piecewise isometry: every short map close to the identity on the old sphere
is constant on the nondegenerate attached interval, hence has an infinite
fiber. A finite cover by injective pieces is therefore impossible.
-/

@[expose] public section
noncomputable section

namespace ExplicitFourOctantSource

open GeodesicSphere BrehmApprox

theorem infinite_fiber_of_short_close_on_sphere
    (g : Source → GeodesicSphere 2) (hg : LipschitzWith 1 g)
    (hclose : ∀ x : GeodesicSphere 2, dist (g (sphereEmbedding x)) x < Real.pi / 2) :
    ∃ y : GeodesicSphere 2, (g ⁻¹' {y}).Infinite := by
  have hr : Short (g ∘ sphereEmbedding) := by
    intro x y
    simpa only [Function.comp_apply, NNReal.coe_one, one_mul,
      isometry_sphereEmbedding.dist_eq] using hg.dist_le_mul (sphereEmbedding x) (sphereEmbedding y)
  obtain ⟨U, hU⟩ := orthogonal_of_short_close_to_id hr hclose
  let R := mapEquiv U
  have hanchor (v : GeodesicSphere 2) : R v = g (sphereEmbedding v) := by
    simpa only [R, Function.comp_apply] using (congrFun hU v).symm
  let u : Set.Icc (0 : ℝ) (Real.pi / 2) → GeodesicSphere 2 := fun t => R.symm (g (edge t))
  have hu : Continuous u := R.symm.continuous.comp (hg.continuous.comp isometry_edge.continuous)
  have hucaps : ∀ t : Set.Icc (0 : ℝ) (Real.pi / 2),
      ∀ v ∈ ExplicitBalancedFrame.vertices, dist (u t) v ≤ Real.pi / 2 := by
    intro t v hv
    calc
      dist (u t) v = dist (R.symm (g (edge t))) (R.symm (R v)) := by
        simp only [u, R.symm_apply_apply]
      _ = dist (g (edge t)) (R v) := R.symm.dist_eq _ _
      _ = dist (g (edge t)) (g (sphereEmbedding v)) := by rw [hanchor]
      _ ≤ dist (edge t) (sphereEmbedding v) := by simpa using hg.dist_le_mul (edge t) (sphereEmbedding v)
      _ = Real.pi / 2 := edge_anchor_distance ⟨v, hv⟩ t
  let : PreconnectedSpace (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let t₀ : Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨0, le_rfl, by positivity⟩
  have hconst : ∀ t, g (edge t) = g (edge t₀) := by
    intro t
    apply R.symm.injective
    exact eq_on_preconnected_of_balanced_caps
      ExplicitBalancedFrame.vertices ExplicitBalancedFrame.pole
      ExplicitBalancedFrame.balance ExplicitBalancedFrame.span
      isPreconnected_univ u hu.continuousOn (fun t _ => hucaps t)
      t (Set.mem_univ t) t₀ (Set.mem_univ t₀)
  refine ⟨g (edge t₀), ?_⟩
  intro hfinite
  have hrange : (Set.range edge).Finite := hfinite.subset (by
    rintro x ⟨t, rfl⟩
    exact hconst t)
  let : Fintype (Set.range edge) := hrange.fintype
  let : Finite (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    Finite.of_injective (fun t => (⟨edge t, Set.mem_range_self t⟩ : Set.range edge)) (by
      intro s t hst
      exact isometry_edge.injective (congrArg Subtype.val hst))
  have hi : (Set.Icc (0 : ℝ) (Real.pi / 2)).Infinite := Set.Icc_infinite (by positivity)
  exact hi (Set.toFinite _)

end ExplicitFourOctantSource
