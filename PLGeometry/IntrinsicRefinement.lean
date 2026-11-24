module

public import PLGeometry.Basic
public import BrehmApprox.SphericalGeodesics
public import BrehmApprox.HyperbolicGeodesics
public import BrehmApprox.FiniteClosedRefinement

/-!
# Intrinsic metrics under finite refinements

Every model simplex contains a shortest segment. An isometric simplex chart
therefore supplies a shortest segment in the source. A finite closed cover
cuts such a segment into a chain of exactly the same length. Consequently,
any finite geodesic triangulation of an intrinsic polyhedron generates its
original metric.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry

universe u v

private theorem clamped_geodesic_in_set {X : Type u} [MetricSpace X]
    (C : Set X) (x y : C) (γ : ℝ → X)
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ C)
    (h0 : γ 0 = x.val) (h1 : γ 1 = y.val)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = dist x y * dist s t) :
    ∃ δ : ℝ → C, Continuous δ ∧ δ 0 = x ∧ δ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (δ s) (δ t) = dist x y * dist s t := by
  let clip : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclip (t : ℝ) : clip t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hfix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : clip t = t := by
    simp only [clip, min_eq_right ht.2, max_eq_right ht.1]
  have hcont : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  let δ : ℝ → C := fun t => ⟨γ (clip t), hm _ (hclip t)⟩
  refine ⟨δ, (hc.comp_continuous hcont hclip).subtype_mk _, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change γ (clip 0) = x.val
    simpa only [hfix 0 (by constructor <;> norm_num)] using h0
  · apply Subtype.ext
    change γ (clip 1) = y.val
    simpa only [hfix 1 (by constructor <;> norm_num)] using h1
  · intro s hs t ht
    change dist (γ (clip s)) (γ (clip t)) = _
    rw [hfix s hs, hfix t ht]
    exact hd s hs t ht

/-- The shortest segment in a model simplex, with a continuous total
parameterization obtained by clamping to the unit interval. -/
theorem exists_hull_geodesic (κ : Geometry) (n : ℕ)
    (V : Finset (Model κ n)) (hV : simplexVertices κ n V)
    (x y : hull κ n V) :
    ∃ γ : ℝ → hull κ n V, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = dist x y * dist s t := by
  cases κ with
  | euclidean =>
    apply clamped_geodesic_in_set _ x y (AffineMap.lineMap x.val y.val)
    · exact (lipschitzWith_lineMap x.val y.val).continuous.continuousOn
    · intro t ht
      exact (convex_convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))).lineMap_mem
        x.property y.property ht
    · exact AffineMap.lineMap_apply_zero _ _
    · exact AffineMap.lineMap_apply_one _ _
    · intro s _ t _
      rw [dist_lineMap_lineMap]
      exact mul_comm _ _
  | spherical =>
    obtain ⟨p, hp⟩ := hV.1
    have hpx : dist p x.val < Real.pi / 2 :=
      (GeodesicSphere.dist_lt_pi_div_two_iff p x.val).mpr
        (sphericalCell_inner_pos V p hp x.property)
    have hpy : dist p y.val < Real.pi / 2 :=
      (GeodesicSphere.dist_lt_pi_div_two_iff p y.val).mpr
        (sphericalCell_inner_pos V p hp y.property)
    have hπ : dist x.val y.val < Real.pi := by
      have ht := dist_triangle x.val p y.val
      rw [dist_comm x.val p] at ht
      linarith
    apply clamped_geodesic_in_set _ x y (GeodesicSphere.geodesic x.val y.val hπ)
    · exact (GeodesicSphere.geodesic_lipschitzOn _ _ _).continuousOn
    · intro t ht
      exact geodesic_mem_sphericalCell x.property y.property hπ ht.1 ht.2
    · exact GeodesicSphere.geodesic_zero _ _ _
    · exact GeodesicSphere.geodesic_one _ _ _
    · intro s hs t ht
      rw [GeodesicSphere.geodesic_dist _ _ _ hs ht, Real.dist_eq]
      exact mul_comm _ _
  | hyperbolic =>
    apply clamped_geodesic_in_set _ x y (HyperbolicSpace.geodesic x.val y.val)
    · exact (HyperbolicSpace.continuous_geodesic _ _).continuousOn
    · intro t ht
      exact geodesic_mem_hyperbolicCell x.property y.property ht.1 ht.2
    · exact HyperbolicSpace.geodesic_zero _ _
    · exact HyperbolicSpace.geodesic_one _ _
    · intro s _ t _
      rw [HyperbolicSpace.geodesic_dist, Real.dist_eq]
      exact mul_comm _ _

namespace Triangulation

variable {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]
    (T : Triangulation κ n P)

/-- A shortest segment in a source cell, constructed through its chart. -/
theorem exists_cell_geodesic (σ : Finset P) (hσ : σ ∈ T.simplices)
    (x : P) (hx : x ∈ T.cell σ) (y : P) (hy : y ∈ T.cell σ) :
    ∃ γ : ℝ → P, Continuous γ ∧ γ 0 = x ∧ γ 1 = y ∧
      (∀ t, γ t ∈ T.cell σ) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = dist x y * dist s t := by
  let e := T.cellChart σ hσ
  let a : T.cell σ := ⟨x, hx⟩
  let b : T.cell σ := ⟨y, hy⟩
  obtain ⟨δ, hδ, h0, h1, hd⟩ :=
    exists_hull_geodesic κ n _ (T.simplex σ hσ) (e a) (e b)
  let γ : ℝ → P := fun t => (e.symm (δ t)).val
  refine ⟨γ, continuous_subtype_val.comp (e.symm.continuous.comp hδ), ?_, ?_,
    fun t => (e.symm (δ t)).property, ?_⟩
  · change (e.symm (δ 0)).val = x
    rw [h0, e.symm_apply_apply]
  · change (e.symm (δ 1)).val = y
    rw [h1, e.symm_apply_apply]
  · intro s hs t ht
    change dist (e.symm (δ s)) (e.symm (δ t)) = _
    rw [e.symm.dist_eq, hd s hs t ht, e.dist_eq]
    rfl

/-- Every finite closed covering of this polyhedron generates its metric.
The construction produces the chains, rather than assuming that the new
cover has the intrinsic-metric property. -/
theorem chainGenerated_finite_cover {I : Type v} [Fintype I]
    (hT : Intrinsic T) (C : I → Set P)
    (hc : ∀ i, IsClosed (C i)) (hcover : ∀ x, ∃ i, x ∈ C i) :
    ChainGenerated C := by
  apply chainGenerated_finite_closed_cover C (T.intrinsic_iff_chainGenerated.mp hT) hc hcover
  intro σ x hx y hy
  obtain ⟨γ, hγ, h0, h1, _, hd⟩ := T.exists_cell_geodesic σ.val σ.property x hx y hy
  exact ⟨γ, hγ.continuousOn, h0, h1, hd⟩

/-- Intrinsicness is independent of the chosen finite geodesic triangulation. -/
theorem intrinsic_of_finite_triangulation {κ' : Geometry} {m : ℕ}
    (hT : Intrinsic T) (U : Triangulation κ' m P) (hU : U.simplices.Finite) :
    Intrinsic U := by
  letI : Fintype U.simplices := hU.fintype
  apply U.intrinsic_iff_chainGenerated.mpr
  exact T.chainGenerated_finite_cover hT (fun σ : U.simplices => U.cell σ.val)
    (fun σ => U.closed_cell σ.val σ.property)
    (fun x => by obtain ⟨σ, hσ, hx⟩ := U.cover x; exact ⟨⟨σ, hσ⟩, hx⟩)

end Triangulation
end ArchivePLGeometry
