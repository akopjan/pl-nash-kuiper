module

public import BrehmApprox.ExplicitFourOctantCompact
public import BrehmApprox.SphereGeodesicExistence

/-!
# Genuine shortest arcs in the coarse cells of the explicit source

These arcs use the intrinsic source metric. The base sphere includes antipodal
endpoints, while each attached octant uses the unique short spherical arc.
-/

@[expose] public section
noncomputable section

namespace ExplicitFourOctantSource

open GeodesicSphere ExplicitSphericalOctants BrehmApprox

theorem exists_cell_geodesic_with_mem (i : Option ExplicitBalancedFrame.vertices)
    (x : Source) (hx : x ∈ cell i) (y : Source) (hy : y ∈ cell i) :
    ∃ γ : ℝ → Source, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = x ∧ γ 1 = y ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = dist x y * dist s t) ∧
      ∀ t, γ t ∈ cell i := by
  cases i with
  | none =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have hax : sphereEmbedding a = x := Source.ext ha
    have hby : sphereEmbedding b = y := Source.ext hb
    obtain ⟨γ, hc, h0, h1, hd⟩ := exists_metric_geodesic a b (by norm_num)
    refine ⟨sphereEmbedding ∘ γ, isometry_sphereEmbedding.continuous.comp_continuousOn hc,
      ?_, ?_, ?_, ?_⟩
    · simpa only [Function.comp_apply, h0] using hax
    · simpa only [Function.comp_apply, h1] using hby
    · intro s hs t ht
      change dist (sphereEmbedding (γ s)) (sphereEmbedding (γ t)) = _
      rw [isometry_sphereEmbedding.dist_eq, hd s hs t ht, ← hax, ← hby,
        isometry_sphereEmbedding.dist_eq]
    · intro t
      exact Set.mem_range_self (γ t)
  | some v =>
    obtain ⟨p, hp⟩ := octant_inOpenHemisphere v
    have hpx : dist p x.val < Real.pi / 2 :=
      (dist_lt_pi_div_two_iff p x.val).mpr
        (sphericalCell_inner_pos _ p hp hx)
    have hpy : dist p y.val < Real.pi / 2 :=
      (dist_lt_pi_div_two_iff p y.val).mpr
        (sphericalCell_inner_pos _ p hp hy)
    have hπ : dist x.val y.val < Real.pi := by
      have hh := dist_triangle x.val p y.val
      rw [dist_comm x.val p] at hh
      linarith
    let clip : ℝ → ℝ := fun t => max 0 (min 1 t)
    have hclip0 (t : ℝ) : 0 ≤ clip t := le_max_left _ _
    have hclip1 (t : ℝ) : clip t ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    have hclip (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : clip t = t := by
      dsimp [clip]
      rw [min_eq_right ht.2, max_eq_right ht.1]
    have hclipcont : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
    have hmem (t : ℝ) : geodesic x.val y.val hπ (clip t) ∈ octant v :=
      geodesic_mem_sphericalCell hx hy hπ (hclip0 t) (hclip1 t)
    let γoctant : ℝ → octant v := fun t => ⟨geodesic x.val y.val hπ (clip t), hmem t⟩
    have hcont : Continuous γoctant :=
      ((geodesic_lipschitzOn x.val y.val hπ).continuousOn.comp_continuous
        hclipcont (fun t => ⟨hclip0 t, hclip1 t⟩)).subtype_mk hmem
    let γ := octantEmbedding v ∘ γoctant
    refine ⟨γ, ((isometry_octantEmbedding v).continuous.comp hcont).continuousOn,
      ?_, ?_, ?_, ?_⟩
    · apply Source.ext
      change geodesic x.val y.val hπ (clip 0) = x.val
      simp [clip]
    · apply Source.ext
      change geodesic x.val y.val hπ (clip 1) = y.val
      simp [clip]
    · intro s hs t ht
      change dist (octantEmbedding v (γoctant s)) (octantEmbedding v (γoctant t)) = _
      rw [(isometry_octantEmbedding v).dist_eq]
      change dist (geodesic x.val y.val hπ (clip s))
        (geodesic x.val y.val hπ (clip t)) = _
      rw [hclip s hs, hclip t ht, geodesic_dist _ _ _ hs ht,
        cell_dist (some v) x hx y hy, Real.dist_eq]
      ring
    · intro t
      exact hmem t

theorem exists_cell_geodesic (i : Option ExplicitBalancedFrame.vertices)
    (x : Source) (hx : x ∈ cell i) (y : Source) (hy : y ∈ cell i) :
    ∃ γ : ℝ → Source, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = dist x y * dist s t := by
  obtain ⟨γ, hc, h0, h1, hd, _⟩ := exists_cell_geodesic_with_mem i x hx y hy
  exact ⟨γ, hc, h0, h1, hd⟩

end ExplicitFourOctantSource

