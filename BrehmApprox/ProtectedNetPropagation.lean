module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic.Linarith

/-!
# Propagation of protected nearest sites

For a finite closed cell cover, local face protection propagates along any
connected subset of a nearest-site locus. This upgrades cellwise protection
to protection in larger model-embedded regions, without introducing an
intrinsic metric on the entire complex.
-/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox

variable {P : Type*} [TopologicalSpace P] {ι : Type*}

/-- A connected set cannot leave the closed star of `a` if every passage
through a common cell forces the second cell to contain `a`. -/
theorem finite_closed_cover_star_propagation
    (I : Finset ι) (A : ι → Set P)
    (hclosed : ∀ i ∈ I, IsClosed (A i))
    (hcover : ∀ x : P, ∃ i ∈ I, x ∈ A i)
    {C : Set P} (hC : IsPreconnected C) {a : P} (ha : a ∈ C)
    (hpass : ∀ x ∈ C, ∀ i ∈ I, ∀ j ∈ I,
      a ∈ A i → x ∈ A i → x ∈ A j → a ∈ A j) :
    ∀ x ∈ C, ∀ j ∈ I, x ∈ A j → a ∈ A j := by
  classical
  let G := I.filter fun i => a ∈ A i
  let B := I.filter fun i => a ∉ A i
  let U : Set P := ⋃ i ∈ G, A i
  let V : Set P := ⋃ i ∈ B, A i
  have hU : IsClosed U := isClosed_biUnion_finset fun i hi =>
    hclosed i (Finset.mem_filter.mp hi).1
  have hV : IsClosed V := isClosed_biUnion_finset fun i hi =>
    hclosed i (Finset.mem_filter.mp hi).1
  have hall : U ∪ V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hxi⟩ := hcover x
    by_cases hai : a ∈ A i
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩, hxi⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩, hxi⟩)
  have hgood (x : P) (hx : x ∈ C) (hxU : x ∈ U) : x ∉ V := by
    obtain ⟨i, hiG, hxi⟩ := Set.mem_iUnion₂.mp hxU
    obtain ⟨hi, hai⟩ := Finset.mem_filter.mp hiG
    intro hxV
    obtain ⟨j, hjB, hxj⟩ := Set.mem_iUnion₂.mp hxV
    obtain ⟨hj, haj⟩ := Finset.mem_filter.mp hjB
    exact haj (hpass x hx i hi j hj hai hxi hxj)
  have hdis : Disjoint Vᶜ Uᶜ := by
    apply Set.disjoint_left.mpr
    intro x hxV hxU
    have hx : x ∈ U ∪ V := hall ▸ Set.mem_univ x
    exact hx.elim hxU hxV
  have hCcover : C ⊆ Vᶜ ∪ Uᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl (hgood x hx hxU)
    · exact Or.inr hxU
  have haV : a ∉ V := by
    intro h
    obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.mp h
    exact (Finset.mem_filter.mp hi).2 hai
  have hsub : C ⊆ Vᶜ := hC.subset_left_of_subset_union hV.isOpen_compl
    hU.isOpen_compl hdis hCcover ⟨a, ha, haV⟩
  intro x hx j hj hxj
  by_contra haj
  exact hsub hx (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, haj⟩, hxj⟩)

/-- Nearest-site comparisons for an arbitrary real-valued separation
function. Symmetry and the triangle inequality are used only when needed. -/
def IsNearestFor (d : P → P → ℝ) (S : Set P) (x a : P) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, d x a ≤ d x b

omit [TopologicalSpace P] in
theorem IsNearestFor.mono {d : P → P → ℝ} {S U : Set P} {x a : P}
    (h : IsNearestFor d S x a) (hUS : U ⊆ S) (haU : a ∈ U) :
    IsNearestFor d U x a := ⟨haU, fun b hb => h.2 b (hUS hb)⟩

/-- Cellwise protection propagates through connected nearest loci. -/
theorem protected_nearest_of_preconnected_locus
    (I : Finset ι) (A : ι → Set P)
    (hclosed : ∀ i ∈ I, IsClosed (A i))
    (hcover : ∀ x : P, ∃ i ∈ I, x ∈ A i)
    (d : P → P → ℝ) (S : Set P)
    (hprotect : ∀ i ∈ I, ∀ j ∈ I, ∀ x ∈ A i ∩ A j, ∀ a,
      IsNearestFor d (S ∩ A i) x a → a ∈ A j)
    {C : Set P} (hC : IsPreconnected C) {a : P} (ha : a ∈ C)
    (hnearest : ∀ x ∈ C, IsNearestFor d S x a) :
    ∀ x ∈ C, ∀ j ∈ I, x ∈ A j → a ∈ A j := by
  apply finite_closed_cover_star_propagation I A hclosed hcover hC ha
  intro x hx i hi j hj hai hxi hxj
  exact hprotect i hi j hj x ⟨hxi, hxj⟩ a
    ((hnearest x hx).mono Set.inter_subset_left ⟨(hnearest x hx).1, hai⟩)

section Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A nearest site remains nearest at every point on a minimizing segment
from that site to the original point. -/
theorem isNearestFor_dist_along_minimizing
    {S : Set X} {a x y : X} (ha : IsNearestFor dist S x a)
    (hxy : dist x a = dist x y + dist y a) : IsNearestFor dist S y a := by
  refine ⟨ha.1, ?_⟩
  intro b hb
  have ht := dist_triangle x y b
  have hn := ha.2 b hb
  linarith

omit [TopologicalSpace P] in
/-- The same propagation works for distances measured in a model chart. -/
theorem isNearestFor_chart_along_minimizing
    (q : P → X) {S : Set P} {a x y : P}
    (ha : IsNearestFor (fun z w => dist (q z) (q w)) S x a)
    (hxy : dist (q x) (q a) = dist (q x) (q y) + dist (q y) (q a)) :
    IsNearestFor (fun z w => dist (q z) (q w)) S y a := by
  refine ⟨ha.1, ?_⟩
  intro b hb
  have ht := dist_triangle (q x) (q y) (q b)
  have hn := ha.2 b hb
  linarith

end Metric

end BrehmApprox
