module

public import BrehmApprox.ChainRemetricization
public import BrehmApprox.FoldedChartTransport
public import BrehmApprox.EuclideanTargetReferences
public import BrehmApprox.ChartReferences

/-!
# Approximation through one common Euclidean chart

The source chain metric is constructed from actual chart distances. The
Euclidean flattening and reference construction then applies with the original
model as its target. References are pulled back through the chart, and finite
Brehm gives the final map in the original metric. No reference atlas is assumed.
The quantitative condition is precisely the available contraction margin
against the chart and inverse-chart constants.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

universe u v w

variable {X : Type u} [MetricSpace X]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {P : Type w} [mP : MetricSpace P]
variable {GoodX : (X → X) → Prop} {GoodE : (E → E) → Prop}
variable {MX : PolytopeModel X GoodX} {ME : PolytopeModel E GoodE} {N : ℕ}

namespace FoldedGeometry

variable (G : FoldedGeometry (P := P) MX N)

/-- A full approximation theorem from an actual common chart and actual
Euclidean simplex face transport. All collars and reference maps are constructed.
An initial folded source remains an explicit geometric input. -/
theorem chart_folded_approximation_with_maps
    (D : PolyhedralFaceData ME N) (T : SimplicialFaceData D)
    (Φ : X → E) (V : Set X)
    (hface : ∀ i j, D.faceLE i j ↔ G.faceLE i j)
    (hmeet : ∀ i j, D.meet i j = G.meet i j)
    (hcore : ∀ i, D.core i = Φ '' G.core i)
    (hV : IsOpen V) (hcoreV : ∀ i, G.core i ⊆ V) (hΦ : ContinuousOn Φ V)
    {A B κ : NNReal} (hB : 0 < (B : ℝ))
    (hΦLip : ∀ x ∈ V, ∀ y ∈ V, dist (Φ x) (Φ y) ≤ A * dist x y)
    (hinv : ∀ i, ∀ x ∈ G.core i, ∀ y ∈ G.core i,
      dist x y ≤ B * dist (Φ x) (Φ y))
    (o : X) (f : P → X) (hf : LipschitzWith κ f)
    (hshort : (κ : ℝ) * A * B < 1)
    (hBrehm : FiniteExtension GoodX) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → X, LipschitzWith 1 g ∧ G.RealizedByModelMaps g ∧
      ∀ x, dist (g x) (f x) < ε := by
  let cell₀ := G.cell
  let fold₀ := G.fold
  let q : P → E := fun x => Φ (fold₀ x)
  have hc : ChainGenerated cell₀ := G.intrinsic
  have hmem : ∀ i, ∀ x ∈ cell₀ i, fold₀ x ∈ G.core i := by
    intro i x hx
    rw [← G.image_cell i]
    exact Set.mem_image_of_mem G.fold hx
  have hchart : ∀ i, ∀ x ∈ cell₀ i, ∀ y ∈ cell₀ i,
      dist (q x) (q y) ≤ (A : ℝ) * dist x y := by
    intro i x hx y hy
    have h := hΦLip (G.fold x) (hcoreV i (hmem i x hx))
      (G.fold y) (hcoreV i (hmem i y hy))
    simpa only [G.isometry_cell i x hx y hy] using h
  have hinv₀ : ∀ i, ∀ x ∈ cell₀ i, ∀ y ∈ cell₀ i,
      dist x y ≤ (B : ℝ) * dist (q x) (q y) := by
    intro i x hx y hy
    have h := hinv i (G.fold x) (hmem i x hx)
      (G.fold y) (hmem i y hy)
    simpa only [G.isometry_cell i x hx y hy] using h
  have hfdist : ∀ x y, dist (f x) (f y) ≤
      ((κ : ℝ) * B) * chartChainDist cell₀ q x y := by
    intro x y
    have h₁ := hf.dist_le_mul x y
    have h₂ := mul_le_mul_of_nonneg_left
      (ChartChainDist.lower_bound hc hB hinv₀ x y) κ.coe_nonneg
    nlinarith
  let m := ChartChainDist.metricSpace hc A.coe_nonneg hB hchart hinv₀
  let : MetricSpace P := mP
  have hcell : ∀ i, ∀ x ∈ cell₀ i, ∀ y ∈ cell₀ i,
      dist (q x) (q y) = (letI : MetricSpace P := m; dist x y) := by
    intro i x hx y hy
    exact (ChartChainDist.on_cell hc i hx hy).symm
  have hchain : @ChainGenerated P m (Fin N) cell₀ :=
    ChartChainDist.intrinsic hc A.coe_nonneg hB hchart hinv₀
  let GE := G.rechartWithData D Φ hface hmeet hcore m hcell hchain
  let t : ℝ := (κ : ℝ) * A * B
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := hshort
  let β : ℝ := (1 - t) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hε2 : 0 < ε / 2 := by positivity
  have hprepared : ∃ f₀ : P → X, ∃ u : Fin N → E → X,
      (∀ x, dist (f₀ x) (f x) < ε / 2) ∧
      (∀ i x y, dist (u i x) (u i y) ≤
        (((κ : ℝ) * B) * (1 + β)) * dist x y) ∧
      (∀ i, ∀ x ∈ cell₀ i, u i (q x) = f₀ x) ∧
      ∀ i j, D.faceLE i j → ∃ U : Set E, IsOpen U ∧ D.core i ⊆ U ∧
        ∀ z ∈ U, u i z = u j z := by
    let : MetricSpace P := m
    have hfnew : LipschitzWith (κ * B) f := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      exact hfdist x y
    obtain ⟨f₀, u, _, hnear, hu, hexact, hagree⟩ :=
      GE.prepare_euclidean_target_references_with_factor T o f hfnew hβ hε2
    exact ⟨f₀, u, hnear, hu, hexact, hagree⟩
  obtain ⟨f₀, u, hnear, hu, hexact, hagree⟩ := hprepared
  let C : NNReal := ⟨((κ : ℝ) * B) * (1 + β), by positivity⟩
  have huC : ∀ i, LipschitzWith C (u i) :=
    fun i => LipschitzWith.of_dist_le_mul (hu i)
  have hCshort : (C : ℝ) * A < 1 := by
    change (((κ : ℝ) * B) * (1 + β)) * A < 1
    have heq : (((κ : ℝ) * B) * (1 + β)) * A = t * (1 + β) := by
      dsimp [t]
      ring
    rw [heq]
    have htb : t * β < β := by nlinarith
    dsimp [β] at *
    nlinarith
  have hcoremap : ∀ i, Set.MapsTo Φ (G.core i) (D.core i) := by
    intro i x hx
    rw [hcore i]
    exact ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hPL, hgf₀⟩ := G.approximate_from_chart_with_maps D.core Φ V hV hcoreV hΦ
    hΦLip hcoremap u huC (fun i j hij => hagree i j ((hface i j).mpr hij))
    hBrehm hCshort f₀ hexact hε2
  refine ⟨g, hg, hPL, ?_⟩
  intro x
  have ht := dist_triangle (g x) (f₀ x) (f x)
  have h₁ := hgf₀ x
  have h₂ := hnear x
  linarith

/-- The finite-polytope formulation follows by forgetting the retained ambient maps. -/
theorem chart_folded_approximation
    (D : PolyhedralFaceData ME N) (T : SimplicialFaceData D)
    (Φ : X → E) (V : Set X)
    (hface : ∀ i j, D.faceLE i j ↔ G.faceLE i j)
    (hmeet : ∀ i j, D.meet i j = G.meet i j)
    (hcore : ∀ i, D.core i = Φ '' G.core i)
    (hV : IsOpen V) (hcoreV : ∀ i, G.core i ⊆ V) (hΦ : ContinuousOn Φ V)
    {A B κ : NNReal} (hB : 0 < (B : ℝ))
    (hΦLip : ∀ x ∈ V, ∀ y ∈ V, dist (Φ x) (Φ y) ≤ A * dist x y)
    (hinv : ∀ i, ∀ x ∈ G.core i, ∀ y ∈ G.core i,
      dist x y ≤ B * dist (Φ x) (Φ y))
    (o : X) (f : P → X) (hf : LipschitzWith κ f)
    (hshort : (κ : ℝ) * A * B < 1)
    (hBrehm : FiniteExtension GoodX) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → X, LipschitzWith 1 g ∧ PolyhedralPiecewiseIsometry MX G.fold g ∧
      ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨g, hg, hm, hnear⟩ := G.chart_folded_approximation_with_maps D T Φ V
    hface hmeet hcore hV hcoreV hΦ hB hΦLip hinv o f hf hshort hBrehm hε
  exact ⟨g, hg, RealizedByModelMaps.piecewise G hm o, hnear⟩

end FoldedGeometry
end BrehmApprox
