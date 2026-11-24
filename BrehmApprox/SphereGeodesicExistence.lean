module

public import BrehmApprox.SphericalGeodesics
public import BrehmApprox.SphereSurjectiveRigidity
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Actual shortest spherical arcs, including antipodal endpoints. -/

@[expose] public section
noncomputable section

namespace GeodesicSphere

variable {n : ℕ}

theorem exists_unit_tangent (a : GeodesicSphere n) (hn : 0 < n) :
    ∃ u : tangentPlane a, ‖u‖ = 1 := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n a.val_ne_zero
  let i : Fin n := ⟨0, hn⟩
  let v := b i
  have hv : inner ℝ a.val v.val = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property
  refine ⟨⟨v.val, hv⟩, ?_⟩
  exact b.norm_eq_one i

theorem exists_metric_geodesic (a b : GeodesicSphere n) (hn : 0 < n) :
    ∃ γ : ℝ → GeodesicSphere n,
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧ γ 0 = a ∧ γ 1 = b ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = dist a b * dist s t := by
  by_cases hπ : dist a b < Real.pi
  · refine ⟨geodesic a b hπ, (geodesic_lipschitzOn a b hπ).continuousOn,
      geodesic_zero a b hπ, geodesic_one a b hπ, ?_⟩
    intro s hs t ht
    rw [geodesic_dist a b hπ hs ht, Real.dist_eq, mul_comm]
  · have heq : dist a b = Real.pi := le_antisymm (dist_le_pi a b) (le_of_not_gt hπ)
    have hb : b = antipode a := eq_antipode_of_dist_pi heq
    obtain ⟨u, hu⟩ := exists_unit_tangent a hn
    let γ : ℝ → GeodesicSphere n := fun t => radialCircle a u hu (Real.pi * t)
    have hdist {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
        (ht : t ∈ Set.Icc (0 : ℝ) 1) :
        dist (γ s) (γ t) = Real.pi * dist s t := by
      change dist (radialCircle a u hu (Real.pi * s))
        (radialCircle a u hu (Real.pi * t)) = _
      rw [radialCircle_dist]
      · rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos, Real.dist_eq]
      · rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
        have hst : |s - t| ≤ 1 := abs_le.mpr
          ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
        nlinarith [Real.pi_pos]
    have hLip : LipschitzOnWith ⟨Real.pi, Real.pi_pos.le⟩ γ (Set.Icc 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro s hs t ht
      exact (hdist hs ht).le
    refine ⟨γ, hLip.continuousOn, ?_, ?_, ?_⟩
    · apply GeodesicSphere.ext
      simp only [γ, mul_zero, radialCircle_val, Real.cos_zero, Real.sin_zero,
        one_smul, zero_smul, add_zero]
    · rw [hb]
      apply GeodesicSphere.ext
      simp only [γ, mul_one, radialCircle_val, Real.cos_pi, Real.sin_pi,
        neg_smul, one_smul, zero_smul, add_zero, antipode]
    · intro s hs t ht
      rw [heq]
      exact hdist hs ht

end GeodesicSphere
