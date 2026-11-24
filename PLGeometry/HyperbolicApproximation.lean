module

public import PLGeometry.FoldedHyperbolicPL
public import BrehmApprox.HyperbolicFoldedTheorem

/-! # Hyperbolic approximation with a compatible source triangulation -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

open BrehmApprox BrehmApprox.HyperbolicSpace

variable {P : Type*} [MetricSpace P] {n N : ℕ}

/-- Approximation from a sufficiently small genuine initial folding.
The resulting PL isometry uses a finite compatible triangulation of the source. -/
theorem hyperbolic_approximation_of_small_folded_geometry
    (G : FoldedGeometry (P := P) (hyperbolicPolytopeModel n) N)
    (T : HyperbolicSimplicialFaceData G.toPolyhedralFaceData)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hV : ∀ i v, v ∈ T.vertices i → ‖klein v‖ ≤ ρ)
    (f : P → HyperbolicSpace n) {C : NNReal} (hf : LipschitzWith C f)
    (hC : (C : ℝ) / (1 - ρ ^ 2) < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → HyperbolicSpace n, LipschitzWith 1 g ∧
      PLIsometry .hyperbolic n g ∧ ∀ x, dist (g x) (f x) < ε := by
  have hden : 0 < 1 - ρ ^ 2 := by
    have hprod : 0 < (1 - ρ) * (1 + ρ) :=
      mul_pos (sub_pos.mpr hρ1) (by linarith)
    nlinarith
  let B : NNReal := ⟨(1 - ρ ^ 2)⁻¹, (inv_pos.mpr hden).le⟩
  have hB : 0 < (B : ℝ) := inv_pos.mpr hden
  have hshort : (C : ℝ) * (1 : NNReal) * B < 1 := by
    change (C : ℝ) * 1 * (1 - ρ ^ 2)⁻¹ < 1
    simpa only [mul_one, div_eq_mul_inv] using hC
  obtain ⟨g, hg, hm, hnear⟩ := G.chart_folded_approximation_with_maps
    T.kleinFaceData T.kleinSimplicialFaceData
    klein Set.univ (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun _ => rfl) isOpen_univ (fun _ => Set.subset_univ _)
    continuous_klein.continuousOn hB
    (fun x _ y _ => by simpa only [NNReal.coe_one, one_mul] using klein_dist_le x y)
    (fun i x hx y hy => (T.core_chart_distortion hρ0 hρ1 hV i i hx hy).2)
    ⟨0⟩ f hf hshort (hyperbolicBrehm n) hε
  exact ⟨g, hg, plIsometry_hyperbolic_of_model_maps G T hg.continuous hm, hnear⟩

/-- Arbitrarily small genuine initial foldings suffice for the full
hyperbolic approximation statement, with an actual source triangulation. -/
theorem hyperbolic_approximation_of_small_foldable
    (hP : HyperbolicSmallFoldable P n)
    (f : P → HyperbolicSpace n) (hf : LipschitzWith 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → HyperbolicSpace n, LipschitzWith 1 g ∧
      PLIsometry .hyperbolic n g ∧ ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨N₀, G₀, _, _⟩ := hP (1 / 2) (by norm_num) (by norm_num)
  let : CompactSpace P := G₀.compactSpace ⟨0⟩
  have hε2 : 0 < ε / 2 := by positivity
  have hcompact : IsCompact (Set.range f) := isCompact_range hf.continuous
  obtain ⟨s, L, _, hL0, hL1, hs, hnear⟩ := compact_strictification hcompact hε2
  let C : NNReal := ⟨L, hL0⟩
  let u : P → HyperbolicSpace n := s ∘ f
  have hu : LipschitzWith C u := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hfxy : dist (f x) (f y) ≤ dist x y := by simpa using hf.dist_le_mul x y
    exact (hs (f x) (Set.mem_range_self x) (f y) (Set.mem_range_self y)).trans
      (mul_le_mul_of_nonneg_left hfxy hL0)
  let ρ : ℝ := (1 - L) / 4
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith
  have hρsmall : ρ ≤ 1 / 4 := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by linarith
  have hden : L < 1 - ρ ^ 2 := by
    have hρsq : ρ ^ 2 ≤ ρ / 4 := by nlinarith
    dsimp [ρ] at *
    nlinarith
  have hC : (C : ℝ) / (1 - ρ ^ 2) < 1 :=
    (div_lt_one (by linarith : 0 < 1 - ρ ^ 2)).mpr hden
  obtain ⟨N, G, T, hV⟩ := hP ρ hρ0 hρ1
  obtain ⟨g, hg, hPL, hgu⟩ := hyperbolic_approximation_of_small_folded_geometry
    G T hρ0.le hρ1 hV u hu hC hε2
  refine ⟨g, hg, hPL, ?_⟩
  intro x
  have h₁ := hgu x
  have h₂ := hnear (f x) (Set.mem_range_self x)
  have htriangle := dist_triangle (g x) (u x) (f x)
  change dist (u x) (f x) < ε / 2 at h₂
  linarith

end ArchivePLGeometry
