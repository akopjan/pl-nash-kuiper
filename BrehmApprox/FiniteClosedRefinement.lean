module

public import BrehmApprox.ChainRemetricization
public import BrehmApprox.CellProjections
public import BrehmApprox.FoldedGeometry
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Finite closed refinements and the intrinsic chain metric

A finite closed cover of a real interval admits a monotone finite chain whose
successive endpoints belong to a common member of the cover. No convexity of
the covering sets is assumed. The proof removes a covering set after its last
point in the interval. Applied to a geodesic, this preserves its exact length.
-/

@[expose] public section

open Set

namespace BrehmApprox

universe u v w

/-- A finite closed cover of an interval admits a monotone chain with each
pair of successive endpoints in one covering set. -/
theorem finite_closed_cover_monotone_chain {ι : Type u} (S : Finset ι)
    (C : ι → Set ℝ) (hclosed : ∀ i ∈ S, IsClosed (C i))
    {a b : ℝ} (hab : a ≤ b)
    (hcover : ∀ t ∈ Icc a b, ∃ i ∈ S, t ∈ C i) :
    ∃ n : ℕ, ∃ z : ℕ → ℝ,
      z 0 = a ∧ z n = b ∧ Monotone z ∧
      (∀ j, z j ∈ Icc a b) ∧
      ∀ j < n, ∃ i ∈ S, z j ∈ C i ∧ z (j + 1) ∈ C i := by
  classical
  induction S using Finset.strongInduction generalizing a b with
  | H S ih =>
    obtain ⟨i, hi, hai⟩ := hcover a ⟨le_rfl, hab⟩
    have hcompact : IsCompact (C i ∩ Icc a b) :=
      isCompact_Icc.inter_left (hclosed i hi)
    obtain ⟨t, ht⟩ := hcompact.exists_isGreatest ⟨a, hai, le_rfl, hab⟩
    have hat : a ≤ t := ht.1.2.1
    have htb : t ≤ b := ht.1.2.2
    by_cases hteq : t = b
    · let z : ℕ → ℝ := fun j => if j = 0 then a else b
      refine ⟨1, z, by simp [z], by simp [z], ?_, ?_, ?_⟩
      · apply monotone_nat_of_le_succ
        intro j
        cases j with
        | zero => simpa [z] using hab
        | succ j => simp [z]
      · intro j
        by_cases hj : j = 0
        · simp [z, hj, hab]
        · simp [z, hj, hab]
      · intro j hj
        have hj0 : j = 0 := by omega
        refine ⟨i, hi, ?_, ?_⟩
        · simpa [z, hj0] using hai
        · simpa [z, hj0, ← hteq] using ht.1.1
    · have htb' : t < b := lt_of_le_of_ne htb hteq
      let U : Set ℝ := ⋃ j ∈ S.erase i, C j
      have hU : IsClosed U := isClosed_biUnion_finset fun j hj =>
        hclosed j (Finset.mem_of_mem_erase hj)
      have hIoc : Ioc t b ⊆ U := by
        intro s hs
        obtain ⟨j, hj, hsj⟩ := hcover s ⟨hat.trans hs.1.le, hs.2⟩
        have hji : j ≠ i := by
          intro heq
          have hst := ht.2 (show s ∈ C i ∩ Icc a b from
            ⟨heq ▸ hsj, hat.trans hs.1.le, hs.2⟩)
          exact hs.1.not_ge hst
        exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, hsj⟩
      have hIcc : Icc t b ⊆ U := by
        rw [← closure_Ioc htb'.ne]
        exact closure_minimal hIoc hU
      have hcover' : ∀ s ∈ Icc t b, ∃ j ∈ S.erase i, s ∈ C j := by
        intro s hs
        obtain ⟨j, hj, hsj⟩ := Set.mem_iUnion₂.mp (hIcc hs)
        exact ⟨j, hj, hsj⟩
      obtain ⟨n, v, hv0, hvn, hvm, hvr, hvcell⟩ :=
        ih (S.erase i) (Finset.erase_ssubset hi)
          (fun j hj => hclosed j (Finset.mem_of_mem_erase hj)) htb hcover'
      let z : ℕ → ℝ
        | 0 => a
        | j + 1 => v j
      refine ⟨n + 1, z, rfl, hvn, ?_, ?_, ?_⟩
      · apply monotone_nat_of_le_succ
        intro j
        cases j with
        | zero => change a ≤ v 0; rwa [hv0]
        | succ j => exact hvm (Nat.le_succ j)
      · intro j
        cases j with
        | zero => exact ⟨le_rfl, hab⟩
        | succ j => exact ⟨hat.trans (hvr j).1, (hvr j).2⟩
      · intro j hj
        cases j with
        | zero =>
          refine ⟨i, hi, hai, ?_⟩
          change v 0 ∈ C i
          rw [hv0]
          exact ht.1.1
        | succ j =>
          obtain ⟨k, hk, hkj, hkj'⟩ := hvcell j (by omega)
          exact ⟨k, Finset.mem_of_mem_erase hk, hkj, hkj'⟩


namespace CellChain

/-- Transporting the endpoint indices does not change a chain's cost. -/
theorem cost_cast_endpoints {P : Type v} {ι : Type u} {E : Type w} [MetricSpace E]
    {C : ι → Set P} (q : P → E) {x x' y y' : P}
    (hx : x = x') (hy : y = y') (c : CellChain C x y) :
    (hx ▸ hy ▸ c).cost q = c.cost q := by
  cases hx
  cases hy
  rfl

end CellChain

/-- Pulling a finite closed cover back along an actual constant-speed
geodesic yields an exact-length chain in that cover. -/
theorem finite_closed_cover_geodesic_chain
    {P : Type v} [MetricSpace P] {ι : Type u} (S : Finset ι)
    (C : ι → Set P) (hclosed : ∀ i ∈ S, IsClosed (C i))
    (γ : ℝ → P) (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i ∈ S, γ t ∈ C i)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = dist (γ 0) (γ 1) * dist s t) :
    ∃ c : CellChain C (γ 0) (γ 1), c.cost id = dist (γ 0) (γ 1) := by
  let D : ι → Set ℝ := fun i => Icc (0 : ℝ) 1 ∩ γ ⁻¹' C i
  have hDclosed : ∀ i ∈ S, IsClosed (D i) :=
    fun i hi => hγ.preimage_isClosed_of_isClosed isClosed_Icc (hclosed i hi)
  have hDcover : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i ∈ S, t ∈ D i := by
    intro t ht
    obtain ⟨i, hi, hti⟩ := hcover t ht
    exact ⟨i, hi, ht, hti⟩
  obtain ⟨n, z, hz0, hzn, hzm, hzr, hzc⟩ :=
    finite_closed_cover_monotone_chain S D hDclosed (by norm_num) hDcover
  have hc : ∀ j < n, ∃ i, γ (z j) ∈ C i ∧ γ (z (j + 1)) ∈ C i := by
    intro j hj
    obtain ⟨i, _, hji, hj'i⟩ := hzc j hj
    exact ⟨i, hji.2, hj'i.2⟩
  have hcost : (CellChain.ofSequence n (γ ∘ z) hc).cost id =
      dist (γ 0) (γ 1) := by
    rw [CellChain.cost_ofSequence]
    calc
      (∑ j ∈ Finset.range n, dist (id ((γ ∘ z) j)) (id ((γ ∘ z) (j + 1)))) =
          ∑ j ∈ Finset.range n, dist (γ 0) (γ 1) * (z (j + 1) - z j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [id_eq, Function.comp_apply, hgeo _ (hzr j) _ (hzr (j + 1)),
          Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hzm (Nat.le_succ j))), neg_sub]
      _ = dist (γ 0) (γ 1) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub, hzn, hz0]
        ring
  have he0 : γ (z 0) = γ 0 := congrArg γ hz0
  have hen : γ (z n) = γ 1 := congrArg γ hzn
  refine ⟨he0 ▸ hen ▸ CellChain.ofSequence n (γ ∘ z) hc, ?_⟩
  exact (CellChain.cost_cast_endpoints id he0 hen _).trans hcost

namespace CellChain

/-- Exact-length refinements of individual cells refine every finite chain. -/
theorem refine_cost_eq {P : Type v} [MetricSpace P] {ι : Type u} {κ : Type w}
    {old : ι → Set P} {new : κ → Set P}
    (hlocal : ∀ i, ∀ x ∈ old i, ∀ y ∈ old i,
      ∃ c : CellChain new x y, c.cost id = dist x y)
    {x y : P} (c : CellChain old x y) :
    ∃ d : CellChain new x y, d.cost id = c.cost id := by
  induction c with
  | nil x => exact ⟨.nil x, rfl⟩
  | @cons x y z i hx hy c ih =>
    obtain ⟨a, ha⟩ := hlocal i x hx y hy
    obtain ⟨b, hb⟩ := ih
    exact ⟨a.append b, by simp [ha, hb]⟩

end CellChain

/-- The intrinsic chain property is preserved when every old-cell edge has
an exact-length finite chain in the new cells. -/
theorem chainGenerated_of_cellwise_exact_chains
    {P : Type v} [MetricSpace P] {ι : Type u} {κ : Type w}
    {old : ι → Set P} {new : κ → Set P}
    (hold : ChainGenerated old)
    (hlocal : ∀ i, ∀ x ∈ old i, ∀ y ∈ old i,
      ∃ c : CellChain new x y, c.cost id = dist x y) :
    ChainGenerated new := by
  intro x y ε hε
  obtain ⟨n, z, hz0, hzn, hcell, hcost⟩ := hold x y ε hε
  obtain ⟨d, hd⟩ := (CellChain.ofSequence n z hcell).refine_cost_eq hlocal
  obtain ⟨m, w, hw0, hwm, hwcell, hwcost⟩ := d.exists_sequence id
  refine ⟨m, w, hw0.trans hz0, hwm.trans hzn, hwcell, ?_⟩
  have heq : (∑ j ∈ Finset.range m, dist (w j) (w (j + 1))) =
      ∑ j ∈ Finset.range n, dist (z j) (z (j + 1)) := by
    simpa only [id_eq, hd, CellChain.cost_ofSequence] using hwcost
  exact heq.trans_lt hcost

/-- A finite closed cover generates the original intrinsic metric whenever
the original cells have actual metric geodesics. This theorem constructs
new chains; `ChainGenerated new` is not an input. -/
theorem chainGenerated_finite_closed_cover
    {P : Type v} [MetricSpace P] {ι : Type u} {κ : Type w} [Fintype κ]
    {old : ι → Set P} (new : κ → Set P)
    (hold : ChainGenerated old) (hclosed : ∀ k, IsClosed (new k))
    (hcover : ∀ x : P, ∃ k, x ∈ new k)
    (hgeo : ∀ i, ∀ x ∈ old i, ∀ y ∈ old i,
      ∃ γ : ℝ → P, ContinuousOn γ (Icc (0 : ℝ) 1) ∧ γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = dist x y * dist s t) :
    ChainGenerated new := by
  apply chainGenerated_of_cellwise_exact_chains hold
  intro i x hx y hy
  obtain ⟨γ, hγ, hγ0, hγ1, hγdist⟩ := hgeo i x hx y hy
  have hγcov : ∀ t ∈ Icc (0 : ℝ) 1, ∃ k ∈ (Finset.univ : Finset κ), γ t ∈ new k := by
    intro t _
    obtain ⟨k, hk⟩ := hcover (γ t)
    exact ⟨k, Finset.mem_univ _, hk⟩
  obtain ⟨c, hc⟩ := finite_closed_cover_geodesic_chain Finset.univ new
    (fun k _ => hclosed k) γ hγ hγcov (by simpa only [hγ0, hγ1] using hγdist)
  refine ⟨hγ0 ▸ hγ1 ▸ c, ?_⟩
  exact (CellChain.cost_cast_endpoints id hγ0 hγ1 c).trans (by
    simpa only [hγ0, hγ1] using hc)


namespace FoldedGeometry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : Type v} [MetricSpace P]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good} {N : ℕ}

/-- The actual straight segment in a convex model core, lifted by its
isometric source chart, is a geodesic for the original source metric. -/
theorem exists_cell_geodesic (G : FoldedGeometry (P := P) M N)
    (hconvex : ∀ i, Convex ℝ (G.core i))
    (i : Fin N) (x : P) (hx : x ∈ G.cell i) (y : P) (hy : y ∈ G.cell i) :
    ∃ γ : ℝ → P, ContinuousOn γ (Icc (0 : ℝ) 1) ∧ γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = dist x y * dist s t := by
  let S := G.constantSource (0 : E)
  have hqx : G.fold x ∈ G.core i := S.fold_mem_core hx
  have hqy : G.fold y ∈ G.core i := S.fold_mem_core hy
  have hne : (G.core i).Nonempty := ⟨G.fold x, hqx⟩
  let r := S.convexCoreProjection i hne (hconvex i)
  have hr : ∀ z ∈ G.core i, (r z : E) = z :=
    fun z hz => S.convexCoreProjection_fix i hne (hconvex i) hz
  let γ : ℝ → P := fun t => S.sourceFromCore i r
    (AffineMap.lineMap (G.fold x) (G.fold y) t)
  have hγ : Continuous γ :=
    (S.sourceFromCore_lipschitz i r (S.convexCoreProjection_short i hne
      (hconvex i))).continuous.comp (lipschitzWith_lineMap (G.fold x) (G.fold y)).continuous
  refine ⟨γ, hγ.continuousOn, ?_, ?_, ?_⟩
  · change S.sourceFromCore i r (AffineMap.lineMap (G.fold x) (G.fold y) 0) = x
    rw [AffineMap.lineMap_apply_zero]
    exact S.retractFromCore_fix i r hr hx
  · change S.sourceFromCore i r (AffineMap.lineMap (G.fold x) (G.fold y) 1) = y
    rw [AffineMap.lineMap_apply_one]
    exact S.retractFromCore_fix i r hr hy
  · intro s hs t ht
    change dist (S.sourceFromCore i r _) (S.sourceFromCore i r _) = _
    rw [S.sourceFromCore_dist]
    change dist (r (AffineMap.lineMap (G.fold x) (G.fold y) s) : E)
      (r (AffineMap.lineMap (G.fold x) (G.fold y) t) : E) = _
    rw [hr _ ((hconvex i).lineMap_mem hqx hqy hs),
      hr _ ((hconvex i).lineMap_mem hqx hqy ht), dist_lineMap_lineMap,
      G.isometry_cell i x hx y hy, mul_comm]

/-- Any finite closed cover, in particular a finite polyhedral refinement,
generates the same source metric as genuine convex folded cells. -/
theorem chainGenerated_closed_refinement (G : FoldedGeometry (P := P) M N)
    (hconvex : ∀ i, Convex ℝ (G.core i))
    {κ : Type w} [Fintype κ] (new : κ → Set P)
    (hclosed : ∀ k, IsClosed (new k)) (hcover : ∀ x : P, ∃ k, x ∈ new k) :
    ChainGenerated new :=
  chainGenerated_finite_closed_cover new G.intrinsic hclosed hcover
    (G.exists_cell_geodesic hconvex)

end FoldedGeometry
end BrehmApprox
