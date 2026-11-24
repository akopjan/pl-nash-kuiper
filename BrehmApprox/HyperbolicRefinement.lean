module

public import BrehmApprox.HyperbolicGeodesics
public import BrehmApprox.FiniteClosedRefinement

/-!
# Intrinsic metric preservation under finite closed hyperbolic refinements

Every cell of an actual folded hyperbolic source has an actual geodesic,
obtained by lifting the explicit model segment through its inverse isometric
chart. Therefore every finite closed covering refinement generates the same
original intrinsic chain metric. The combinatorial construction of a common
simplicial subdivision is a separate problem.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox.FoldedGeometry

open HyperbolicSpace

universe u v
variable {P : Type u} [MetricSpace P] {n N : ℕ}

/-- The real hyperbolic geodesic inside a core, lifted by the inverse source
chart. Clamping gives a continuous total parameter map without choosing any
extension outside the unit interval. -/
theorem exists_hyperbolic_cell_geodesic
    (G : FoldedGeometry (P := P) (hyperbolicPolytopeModel n) N)
    (i : Fin N) (x : P) (hx : x ∈ G.cell i) (y : P) (hy : y ∈ G.cell i) :
    ∃ γ : ℝ → P, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧ γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = dist x y * dist s t := by
  let S := G.constantSource (⟨0⟩ : HyperbolicSpace n)
  have hqx : G.fold x ∈ G.core i := S.fold_mem_core hx
  have hqy : G.fold y ∈ G.core i := S.fold_mem_core hy
  obtain ⟨V, hV⟩ := G.polytope_core i
  let clip : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclip0 (t : ℝ) : 0 ≤ clip t := le_max_left _ _
  have hclip1 (t : ℝ) : clip t ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hclip (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : clip t = t := by
    dsimp [clip]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hclipcont : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hmem (t : ℝ) : geodesic (G.fold x) (G.fold y) (clip t) ∈ G.core i := by
    rw [hV]
    exact geodesic_mem_hyperbolicCell (hV ▸ hqx) (hV ▸ hqy) (hclip0 t) (hclip1 t)
  let γcore : ℝ → G.core i := fun t => ⟨geodesic (G.fold x) (G.fold y) (clip t), hmem t⟩
  let e : G.cell i ≃ᵢ G.core i := S.cellChart i
  let γ : ℝ → P := fun t => (e.symm (γcore t) : P)
  have hcorecont : Continuous γcore :=
    ((continuous_geodesic (G.fold x) (G.fold y)).comp hclipcont).subtype_mk hmem
  have hγ : Continuous γ := continuous_subtype_val.comp
    (e.symm.continuous.comp hcorecont)
  refine ⟨γ, hγ.continuousOn, ?_, ?_, ?_⟩
  · have hc0 : γcore 0 = e ⟨x, hx⟩ := by
      apply Subtype.ext
      change geodesic (G.fold x) (G.fold y) (clip 0) = G.fold x
      simp [clip]
    change (e.symm (γcore 0) : P) = x
    rw [hc0, e.symm_apply_apply]
  · have hc1 : γcore 1 = e ⟨y, hy⟩ := by
      apply Subtype.ext
      change geodesic (G.fold x) (G.fold y) (clip 1) = G.fold y
      simp [clip]
    change (e.symm (γcore 1) : P) = y
    rw [hc1, e.symm_apply_apply]
  · intro s hs t ht
    change dist (e.symm (γcore s)) (e.symm (γcore t)) = _
    rw [e.symm.dist_eq]
    change dist (geodesic (G.fold x) (G.fold y) (clip s))
      (geodesic (G.fold x) (G.fold y) (clip t)) = _
    rw [hclip s hs, hclip t ht, geodesic_dist, G.isometry_cell i x hx y hy, Real.dist_eq]
    ring

/-- Finite closed refinements preserve the actual original hyperbolic source
metric. No intrinsic-chain hypothesis on the refined cover is assumed. -/
theorem hyperbolic_chainGenerated_closed_refinement
    (G : FoldedGeometry (P := P) (hyperbolicPolytopeModel n) N)
    {κ : Type v} [Fintype κ] (new : κ → Set P)
    (hclosed : ∀ k, IsClosed (new k)) (hcover : ∀ x : P, ∃ k, x ∈ new k) :
    ChainGenerated new :=
  chainGenerated_finite_closed_cover new G.intrinsic hclosed hcover
    (fun i x hx y hy => G.exists_hyperbolic_cell_geodesic i x hx y hy)

end BrehmApprox.FoldedGeometry
