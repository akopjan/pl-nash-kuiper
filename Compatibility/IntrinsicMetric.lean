module

public import BrehmApprox.CommonCenterCellMetric
public import PLGeometry.ChartedComplex

/-!
# Intrinsic metrics on finite compact folded cell covers

A folding need only be injective on each cell. A compact star-boundary cutoff
separates points in the intrinsic chain distance, even when the global folding
identifies them. The constructed metric retains the original topology.
-/

@[expose] public section
noncomputable section
open scoped Topology
open Set BrehmApprox

namespace PLGeometry.Compatibility.FoldedMetric

universe u v w z

variable {P : Type u} [TopologicalSpace P] [T2Space P]
variable {ι : Type v} [Finite ι] (cell : ι → Set P)
variable {E : Type w} [MetricSpace E] (q : P → E)

/-- The star of a point, expressed through a finite closed cover. -/
def star (p : P) : Set P := ⋃ (i : ι) (_ : p ∈ cell i), cell i

/-- The union of cells which do not contain the chosen point. -/
def opposite (p : P) : Set P := ⋃ (i : ι) (_ : p ∉ cell i), cell i

variable (hcompact : ∀ i, IsCompact (cell i))
variable (hcover : ∀ x, ∃ i, x ∈ cell i)
variable (hq : Continuous q) (hinj : ∀ i, Set.InjOn q (cell i))

include hcompact in
theorem compact_star (p : P) : IsCompact (star cell p) := by
  exact isCompact_iUnion fun i => isCompact_iUnion fun _ => hcompact i

include hcompact in
theorem compact_opposite (p : P) : IsCompact (opposite cell p) := by
  exact isCompact_iUnion fun i => isCompact_iUnion fun _ => hcompact i

include hcompact hq hinj in
theorem exists_star_radius (p : P) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ star cell p ∩ opposite cell p,
      R ≤ dist (q p) (q x) := by
  have hc : IsCompact (q '' (star cell p ∩ opposite cell p)) :=
    ((compact_star cell hcompact p).inter_right
      (compact_opposite cell hcompact p).isClosed).image hq
  have hp : q p ∉ q '' (star cell p ∩ opposite cell p) := by
    rintro ⟨x, ⟨hxA, hxB⟩, heq⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
    obtain ⟨hi, hx⟩ := mem_iUnion.mp hxi
    obtain ⟨j, hxj'⟩ := mem_iUnion.mp hxB
    obtain ⟨hj, hxj⟩ := mem_iUnion.mp hxj'
    have he : x = p := hinj i hx hi heq
    exact hj (he ▸ hxj)
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hc.isClosed.isOpen_compl (q p) hp
  refine ⟨R, hR, ?_⟩
  intro x hx
  by_contra h
  have hdist : dist (q x) (q p) < R := by simpa [dist_comm] using (lt_of_not_ge h)
  exact hball hdist ⟨x, hx, rfl⟩

include hcompact hcover hq hinj in
/-- A real-valued cellwise short function which separates any two points. -/
theorem exists_separating_function (p y : P) (hne : p ≠ y) :
    ∃ φ : P → ℝ, φ p = 0 ∧ 0 < φ y ∧
      ∀ i, ∀ x ∈ cell i, ∀ z ∈ cell i,
        dist (φ x) (φ z) ≤ dist (q x) (q z) := by
  classical
  obtain ⟨R, hR, hbound⟩ := exists_star_radius cell q hcompact hq hinj p
  let φ : P → ℝ := fun x => if x ∈ star cell p then min R (dist (q p) (q x)) else R
  have hpA : p ∈ star cell p := by
    obtain ⟨i, hi⟩ := hcover p
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hi⟩⟩
  have hincident (i : ι) (hp : p ∈ cell i) (x : P) (hx : x ∈ cell i) :
      φ x = min R (dist (q p) (q x)) := by
    exact if_pos (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hp, hx⟩⟩)
  have hother (i : ι) (hp : p ∉ cell i) (x : P) (hx : x ∈ cell i) : φ x = R := by
    by_cases hxA : x ∈ star cell p
    · have hxB : x ∈ opposite cell p := mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hp, hx⟩⟩
      exact (if_pos hxA).trans (min_eq_left (hbound x ⟨hxA, hxB⟩))
    · exact if_neg hxA
  refine ⟨φ, ?_, ?_, ?_⟩
  · simp [φ, hpA, le_of_lt hR]
  · by_cases hy : y ∈ star cell p
    · obtain ⟨i, hyi'⟩ := mem_iUnion.mp hy
      obtain ⟨hi, hyi⟩ := mem_iUnion.mp hyi'
      have hd : 0 < dist (q p) (q y) := dist_pos.mpr (fun h => hne (hinj i hi hyi h))
      simpa [φ, hy] using lt_min hR hd
    · simpa [φ, hy] using hR
  · intro i x hx z hz
    by_cases hp : p ∈ cell i
    · rw [hincident i hp x hx, hincident i hp z hz]
      have hclip : LipschitzWith 1 (fun a : E => min R (dist (q p) a)) := by
        apply LipschitzWith.const_min
        apply LipschitzWith.of_dist_le_mul
        intro a b
        simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_comm (q p) a,
          dist_comm (q p) b] using abs_dist_sub_le a b (q p)
      simpa only [NNReal.coe_one, one_mul] using hclip.dist_le_mul (q x) (q z)
    · rw [hother i hp x hx, hother i hp z hz, dist_self]
      exact dist_nonneg

omit [TopologicalSpace P] [T2Space P] [Finite ι] in
theorem dist_le_chain_cost {Y : Type z} [MetricSpace Y]
    (f : P → Y)
    (hf : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i,
      dist (f x) (f y) ≤ dist (q x) (q y))
    {x y : P} (a : CellChain cell x y) : dist (f x) (f y) ≤ a.cost q := by
  induction a with
  | nil x => simp
  | @cons x y z i hx hy tail ih =>
    exact (dist_triangle (f x) (f y) (f z)).trans (add_le_add (hf i x hx y hy) ih)

variable (hc : ConnectedCellMetric.Connected cell)

include hc in
theorem dist_le_chain_dist {Y : Type z} [MetricSpace Y]
    (f : P → Y)
    (hf : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i,
      dist (f x) (f y) ≤ dist (q x) (q y)) (x y : P) :
    dist (f x) (f y) ≤ chartChainDist cell q x y := by
  apply le_csInf (ConnectedCellMetric.costs_nonempty hc x y)
  rintro r ⟨a, rfl⟩
  exact dist_le_chain_cost cell q f hf a

include hcompact hcover hq hinj hc in
theorem eq_of_chain_dist_eq_zero {x y : P} (hzero : chartChainDist cell q x y = 0) : x = y := by
  by_contra hne
  obtain ⟨φ, hp, hy, hφ⟩ := exists_separating_function cell q hcompact hcover hq hinj x y hne
  have h := dist_le_chain_dist cell q hc φ hφ x y
  rw [hzero, hp, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hy] at h
  exact (not_le_of_gt hy) h

/-- A type synonym that keeps the original topology available during transport. -/
structure Point (P : Type u) where
  val : P

@[instance_reducible]
def pointMetricSpace : MetricSpace (Point P) where
  dist x y := chartChainDist cell q x.val y.val
  dist_self x := ConnectedCellMetric.self hc x.val
  dist_comm x y := ConnectedCellMetric.comm hc x.val y.val
  dist_triangle x y z := ConnectedCellMetric.triangle hc x.val y.val z.val
  eq_of_dist_eq_zero := by
    intro x y hxy
    cases x
    cases y
    congr 1
    exact eq_of_chain_dist_eq_zero cell q hcompact hcover hq hinj hc hxy

include hcompact hcover in
theorem source_compactSpace : CompactSpace P := by
  have he : (⋃ i, cell i) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hcover x
  exact isCompact_univ_iff.mp (he ▸ isCompact_iUnion hcompact)

include hcompact hcover hq hinj hc in
theorem continuous_toPoint :
    letI := pointMetricSpace cell q hcompact hcover hq hinj hc
    Continuous (Point.mk : P → Point P) := by
  letI := pointMetricSpace cell q hcompact hcover hq hinj hc
  have he : (⋃ i, cell i) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hcover x
  apply (locallyFinite_of_finite cell).continuous he (fun i => (hcompact i).isClosed)
  intro i
  rw [Metric.continuousOn_iff']
  intro x hx ε hε
  have hevent : ∀ᶠ y in 𝓝[cell i] x, dist (q y) (q x) < ε :=
    Metric.continuousWithinAt_iff'.mp hq.continuousWithinAt ε hε
  filter_upwards [hevent, self_mem_nhdsWithin] with y hy hycell
  change chartChainDist cell q y x < ε
  rw [ConnectedCellMetric.on_cell hc i hycell hx]
  exact hy

include hcompact hcover hq hinj hc in
theorem topology_eq :
    (inferInstance : TopologicalSpace P) =
      TopologicalSpace.induced Point.mk
        (pointMetricSpace cell q hcompact hcover hq hinj hc).toUniformSpace.toTopologicalSpace := by
  letI := pointMetricSpace cell q hcompact hcover hq hinj hc
  letI : CompactSpace P := source_compactSpace cell hcompact hcover
  exact ((continuous_toPoint cell q hcompact hcover hq hinj hc).isClosedEmbedding
    (fun _ _ h => congrArg Point.val h)).isEmbedding.isInducing.eq_induced

/-- The actual chain metric, with the original source topology retained. -/
@[instance_reducible]
def metricSpace : MetricSpace P :=
  (MetricSpace.induced Point.mk (fun _ _ h => congrArg Point.val h)
    (pointMetricSpace cell q hcompact hcover hq hinj hc)).replaceTopology
      (topology_eq cell q hcompact hcover hq hinj hc)

@[simp]
theorem metricSpace_dist (x y : P) :
    @dist P (metricSpace cell q hcompact hcover hq hinj hc).toDist x y =
      chartChainDist cell q x y := rfl

/-- The new metric is generated by the original finite cell chains. -/
theorem intrinsic :
    @ChainGenerated P (metricSpace cell q hcompact hcover hq hinj hc) ι cell := by
  intro x y ε hε
  obtain ⟨a, ha⟩ := ConnectedCellMetric.approx hc (q := q) x y hε
  obtain ⟨n, z, h0, hn, hcells, hcost⟩ := a.exists_sequence q
  refine ⟨n, z, h0, hn, hcells, ?_⟩
  change (∑ j ∈ Finset.range n, chartChainDist cell q (z j) (z (j + 1))) <
    chartChainDist cell q x y + ε
  have heq : (∑ j ∈ Finset.range n, chartChainDist cell q (z j) (z (j + 1))) = a.cost q := by
    rw [← hcost]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨i, hi, hj'⟩ := hcells j (Finset.mem_range.mp hj)
    exact ConnectedCellMetric.on_cell hc i hi hj'
  rwa [heq]

theorem lipschitzWith_of_cellwise {Y : Type z} [MetricSpace Y]
    (f : P → Y) {L : NNReal}
    (hf : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i,
      dist (f x) (f y) ≤ L * dist (q x) (q y)) :
    letI := metricSpace cell q hcompact hcover hq hinj hc
    LipschitzWith L f := by
  letI := metricSpace cell q hcompact hcover hq hinj hc
  apply BrehmApprox.lipschitzWith_of_cellwise (intrinsic cell q hcompact hcover hq hinj hc)
  intro i x hx y hy
  change dist (f x) (f y) ≤ L * chartChainDist cell q x y
  rw [ConnectedCellMetric.on_cell hc i hx hy]
  exact hf i x hx y hy

end PLGeometry.Compatibility.FoldedMetric

namespace ArchivePLGeometry.FiniteChartedComplex

open PLGeometry.Compatibility

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (U : FiniteChartedComplex κ n P) (q : P → Model κ n) (hq : Continuous q)
    (hiso : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (q x) (q y) = dist (U.chart σ x) (U.chart σ y))
    (hc : BrehmApprox.ConnectedCellMetric.Connected (fun σ : U.simplices => U.cell σ.val))

include hiso in
theorem folding_injectiveOn (σ : U.simplices) : Set.InjOn q (U.cell σ.val) := by
  intro x hx y hy hxy
  apply U.chart_injectiveOn σ.val σ.property hx hy
  apply eq_of_dist_eq_zero
  rw [← hiso σ.val σ.property x hx y hy, hxy, dist_self]

/-- Intrinsic metric on a connected finite charted complex carrying a folding. -/
@[instance_reducible]
def foldedIntrinsicMetric : MetricSpace P := by
  letI : Finite U.simplices := U.finite_simplices.to_subtype
  exact FoldedMetric.metricSpace (fun σ : U.simplices => U.cell σ.val) q
    (fun σ => U.compact_cell σ.val σ.property)
    (fun x => by obtain ⟨σ, hσ, hx⟩ := U.cover x; exact ⟨⟨σ, hσ⟩, hx⟩)
    hq (U.folding_injectiveOn q hiso) hc

@[simp]
theorem foldedIntrinsicMetric_dist (x y : P) :
    @dist P (U.foldedIntrinsicMetric q hq hiso hc).toDist x y =
      BrehmApprox.chartChainDist (fun σ : U.simplices => U.cell σ.val) q x y := rfl

/-- Each original cell is isometric for the constructed intrinsic metric. -/
theorem foldedIntrinsicMetric_on_cell (σ : Finset P) (hσ : σ ∈ U.simplices)
    (x : P) (hx : x ∈ U.cell σ) (y : P) (hy : y ∈ U.cell σ) :
    @dist P (U.foldedIntrinsicMetric q hq hiso hc).toDist x y =
      dist (U.chart σ x) (U.chart σ y) := by
  change BrehmApprox.chartChainDist (fun σ : U.simplices => U.cell σ.val) q x y = _
  rw [BrehmApprox.ConnectedCellMetric.on_cell hc ⟨σ, hσ⟩ hx hy]
  exact hiso σ hσ x hx y hy

/-- The connected charted complex, equipped with the constructed metric,
meets the public polyhedron definition from the completed archive. -/
theorem isFinitePolyhedron_foldedIntrinsicMetric :
    letI := U.foldedIntrinsicMetric q hq hiso hc
    IsFinitePolyhedron κ n P := by
  letI := U.foldedIntrinsicMetric q hq hiso hc
  have hm : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (U.chart σ x) (U.chart σ y) = dist x y := by
    intro σ hσ x hx y hy
    exact (U.foldedIntrinsicMetric_on_cell q hq hiso hc σ hσ x hx y hy).symm
  refine ⟨U.toTriangulation hm, U.finite_simplices, ?_⟩
  intro x y ε hε
  letI : Finite U.simplices := U.finite_simplices.to_subtype
  obtain ⟨m, z, h0, hm', hcells, hsum⟩ :=
    FoldedMetric.intrinsic (fun σ : U.simplices => U.cell σ.val) q
      (fun σ => U.compact_cell σ.val σ.property)
      (fun x => by obtain ⟨σ, hσ, hx⟩ := U.cover x; exact ⟨⟨σ, hσ⟩, hx⟩)
      hq (U.folding_injectiveOn q hiso) hc x y ε hε
  refine ⟨m, z, h0, hm', ?_, hsum⟩
  intro j hj
  obtain ⟨σ, hx, hy⟩ := hcells j hj
  exact ⟨σ.val, σ.property, hx, hy⟩

theorem foldedIntrinsicMetric_lipschitzWith_of_cellwise
    {Y : Type*} [MetricSpace Y] (f : P → Y) {L : NNReal}
    (hf : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (f x) (f y) ≤ L * dist (U.chart σ x) (U.chart σ y)) :
    letI := U.foldedIntrinsicMetric q hq hiso hc
    LipschitzWith L f := by
  letI : Finite U.simplices := U.finite_simplices.to_subtype
  apply FoldedMetric.lipschitzWith_of_cellwise
    (fun σ : U.simplices => U.cell σ.val) q
    (fun σ => U.compact_cell σ.val σ.property)
    (fun x => by obtain ⟨σ, hσ, hx⟩ := U.cover x; exact ⟨⟨σ, hσ⟩, hx⟩)
    hq (U.folding_injectiveOn q hiso) hc f
  intro σ x hx y hy
  rw [hiso σ.val σ.property x hx y hy]
  exact hf σ.val σ.property x hx y hy

end ArchivePLGeometry.FiniteChartedComplex
