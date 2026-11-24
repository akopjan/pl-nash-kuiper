module

public import BrehmApprox.SphericalGeodesics
public import BrehmApprox.FiniteClosedRefinement

/-!
# Intrinsic metric preservation under finite closed spherical refinements

Hemispherical cells contain the actual shortest spherical segments. Lifting
those segments through the original cell charts proves that a finite closed
covering refinement generates the original intrinsic metric. Construction of
a compatible simplicial subdivision is a separate combinatorial step.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox.FoldedGeometry

open GeodesicSphere

universe u v
variable {P : Type u} [MetricSpace P] {n N : ℕ}

theorem exists_spherical_cell_geodesic
    (G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N)
    (i : Fin N) (x : P) (hx : x ∈ G.cell i) (y : P) (hy : y ∈ G.cell i) :
    ∃ γ : ℝ → P, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧ γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = dist x y * dist s t := by
  let S := G.constantSource (northPole n)
  have hqx : G.fold x ∈ G.core i := S.fold_mem_core hx
  have hqy : G.fold y ∈ G.core i := S.fold_mem_core hy
  obtain ⟨V, ⟨p, hp⟩, hV⟩ := G.polytope_core i
  have hpx : dist p (G.fold x) < Real.pi / 2 :=
    (dist_lt_pi_div_two_iff p (G.fold x)).mpr
      (sphericalCell_inner_pos V p hp (hV ▸ hqx))
  have hpy : dist p (G.fold y) < Real.pi / 2 :=
    (dist_lt_pi_div_two_iff p (G.fold y)).mpr
      (sphericalCell_inner_pos V p hp (hV ▸ hqy))
  have hπ : dist (G.fold x) (G.fold y) < Real.pi := by
    have hh := dist_triangle (G.fold x) p (G.fold y)
    rw [dist_comm (G.fold x) p] at hh
    linarith
  let clip : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclip0 (t : ℝ) : 0 ≤ clip t := le_max_left _ _
  have hclip1 (t : ℝ) : clip t ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hclip (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : clip t = t := by
    dsimp [clip]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hclipcont : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hmem (t : ℝ) : geodesic (G.fold x) (G.fold y) hπ (clip t) ∈ G.core i := by
    rw [hV]
    exact geodesic_mem_sphericalCell (hV ▸ hqx) (hV ▸ hqy) hπ (hclip0 t) (hclip1 t)
  let γcore : ℝ → G.core i :=
    fun t => ⟨geodesic (G.fold x) (G.fold y) hπ (clip t), hmem t⟩
  let e : G.cell i ≃ᵢ G.core i := S.cellChart i
  let γ : ℝ → P := fun t => (e.symm (γcore t) : P)
  have hcorecont : Continuous γcore :=
    ((geodesic_lipschitzOn (G.fold x) (G.fold y) hπ).continuousOn.comp_continuous
      hclipcont (fun t => ⟨hclip0 t, hclip1 t⟩)).subtype_mk hmem
  have hγ : Continuous γ := continuous_subtype_val.comp
    (e.symm.continuous.comp hcorecont)
  refine ⟨γ, hγ.continuousOn, ?_, ?_, ?_⟩
  · have hc0 : γcore 0 = e ⟨x, hx⟩ := by
      apply Subtype.ext
      change geodesic (G.fold x) (G.fold y) hπ (clip 0) = G.fold x
      simp [clip]
    change (e.symm (γcore 0) : P) = x
    rw [hc0, e.symm_apply_apply]
  · have hc1 : γcore 1 = e ⟨y, hy⟩ := by
      apply Subtype.ext
      change geodesic (G.fold x) (G.fold y) hπ (clip 1) = G.fold y
      simp [clip]
    change (e.symm (γcore 1) : P) = y
    rw [hc1, e.symm_apply_apply]
  · intro s hs t ht
    change dist (e.symm (γcore s)) (e.symm (γcore t)) = _
    rw [e.symm.dist_eq]
    change dist (geodesic (G.fold x) (G.fold y) hπ (clip s))
      (geodesic (G.fold x) (G.fold y) hπ (clip t)) = _
    rw [hclip s hs, hclip t ht, geodesic_dist _ _ _ hs ht,
      G.isometry_cell i x hx y hy, Real.dist_eq]
    ring

/-- This conclusion uses the original intrinsic metric, and assumes only a
finite closed cover rather than intrinsicness of that refined cover. -/
theorem spherical_chainGenerated_closed_refinement
    (G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N)
    {κ : Type v} [Fintype κ] (new : κ → Set P)
    (hclosed : ∀ k, IsClosed (new k)) (hcover : ∀ x : P, ∃ k, x ∈ new k) :
    ChainGenerated new :=
  chainGenerated_finite_closed_cover new G.intrinsic hclosed hcover
    (fun i x hx y hy => G.exists_spherical_cell_geodesic i x hx y hy)

end BrehmApprox.FoldedGeometry
