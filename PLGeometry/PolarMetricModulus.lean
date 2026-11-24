module

public import PLGeometry.ModelCones
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # A uniform radial and angular metric modulus in all model geometries -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry

variable {m : ℕ}

theorem continuous_conePoint (κ : Geometry) (o : Model κ (m + 1)) :
    Continuous (fun z : ℝ × GeodesicSphere m => conePoint κ m o z.2 z.1) := by
  cases κ with
  | euclidean =>
    change Continuous (fun z : ℝ × GeodesicSphere m => o + z.1 • z.2.val)
    exact continuous_const.add (continuous_fst.smul (GeodesicSphere.continuous_val.comp continuous_snd))
  | spherical =>
    apply continuous_iff_continuous_dist.mpr
    have he (z : (ℝ × GeodesicSphere m) × (ℝ × GeodesicSphere m)) :
        dist (conePoint .spherical m o z.1.2 z.1.1) (conePoint .spherical m o z.2.2 z.2.1) =
        Real.arccos (Real.cos z.1.1 * Real.cos z.2.1 +
          Real.sin z.1.1 * Real.sin z.2.1 * Real.cos (dist z.1.2 z.2.2)) := by
      calc
        _ = Real.arccos (Real.cos (dist (conePoint .spherical m o z.1.2 z.1.1)
            (conePoint .spherical m o z.2.2 z.2.1))) :=
          (Real.arccos_cos dist_nonneg (GeodesicSphere.dist_le_pi _ _)).symm
        _ = _ := by rw [spherical_cone_cos_dist]
    simp_rw [he]
    fun_prop
  | hyperbolic =>
    apply continuous_iff_continuous_dist.mpr
    have he (z : (ℝ × GeodesicSphere m) × (ℝ × GeodesicSphere m)) :
        dist (conePoint .hyperbolic m o z.1.2 z.1.1) (conePoint .hyperbolic m o z.2.2 z.2.1) =
        Real.arcosh (Real.cosh z.1.1 * Real.cosh z.2.1 -
          Real.sinh z.1.1 * Real.sinh z.2.1 * Real.cos (dist z.1.2 z.2.2)) := by
      calc
        _ = Real.arcosh (Real.cosh (dist (conePoint .hyperbolic m o z.1.2 z.1.1)
            (conePoint .hyperbolic m o z.2.2 z.2.1))) := (Real.arcosh_cosh dist_nonneg).symm
        _ = _ := by rw [hyperbolic_cone_cosh_dist]
    simp_rw [he]
    apply Real.continuousOn_arcosh.comp_continuous (by fun_prop)
    intro z
    change 1 ≤ Real.cosh z.1.1 * Real.cosh z.2.1 -
      Real.sinh z.1.1 * Real.sinh z.2.1 * Real.cos (dist z.1.2 z.2.2)
    rw [← hyperbolic_cone_cosh_dist o z.1.2 z.2.2 z.1.1 z.2.1]
    exact Real.one_le_cosh _

theorem exists_conePoint_metric_modulus (κ : Geometry) (o : Model κ (m + 1))
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Set.Icc (0 : ℝ) R, ∀ s ∈ Set.Icc (0 : ℝ) R,
      ∀ u v : GeodesicSphere m, |r - s| < δ → dist u v < δ →
        dist (conePoint κ m o u r) (conePoint κ m o v s) < ε := by
  let X := Set.Icc (0 : ℝ) R × GeodesicSphere m
  let : CompactSpace (Set.Icc (0 : ℝ) R) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : X → Model κ (m + 1) := fun z => conePoint κ m o z.2 z.1.val
  have hf : Continuous f := (continuous_conePoint κ o).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have huf : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp huf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr s hs u v hrs huv
  have hd : dist ((⟨r, hr⟩, u) : X) ((⟨s, hs⟩, v) : X) < δ := by
    change max (dist r s) (dist u v) < δ
    exact max_lt (by simpa only [Real.dist_eq] using hrs) huv
  exact hδf hd

end ArchivePLGeometry
