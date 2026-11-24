module

public import BrehmApprox.Core
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Metric gluing and the obstruction in the supplied parameter choice

These results use no Brehm assumption. They isolate the compact separation,
local-to-global shortness and finite determination needed in an induction over
polyhedral faces. The last results verify the precise circular-net obstruction
in the supplied proof.
-/

@[expose] public section

namespace BrehmApprox

universe u v
variable {X : Type u} [MetricSpace X]

/-- Finite determination is unchanged if the prescribed maps agree on the
prescribed subset. -/
lemma DeterminedOn.congr {A : Set X} {g f : X → X}
    (hg : DeterminedOn A g) (hgf : ∀ x ∈ A, g x = f x) :
    DeterminedOn A f := by
  obtain ⟨V, hVA, hV⟩ := hg
  refine ⟨V, hVA, ?_⟩
  intro H hH hHV x hx
  have heq : ∀ v ∈ V, H v = g v := by
    intro v hv
    exact (hHV v hv).trans (hgf v (hVA hv)).symm
  exact (hV H hH heq x hx).trans (hgf x hx)

/-- The union of two finitely determined pieces is finitely determined.
Agreement of their maps is encoded by using one prescribed map `g`. -/
lemma DeterminedOn.union {A B : Set X} {g : X → X}
    (hA : DeterminedOn A g) (hB : DeterminedOn B g) :
    DeterminedOn (A ∪ B) g := by
  classical
  obtain ⟨V, hVA, hV⟩ := hA
  obtain ⟨W, hWB, hW⟩ := hB
  refine ⟨V ∪ W, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hv | hw
    · exact Set.mem_union_left _ (hVA hv)
    · exact Set.mem_union_right _ (hWB hw)
  · intro H hH hHV x hx
    rcases hx with hxA | hxB
    · exact hV H hH (fun v hv => hHV v (Finset.mem_union_left W hv)) x hxA
    · exact hW H hH (fun w hw => hHV w (Finset.mem_union_right V hw)) x hxB

lemma determinedOn_finset_iUnion {ι : Type v} (I : Finset ι)
    (A : ι → Set X) (g : X → X)
    (hA : ∀ i ∈ I, DeterminedOn (A i) g) :
    DeterminedOn (⋃ i ∈ I, A i) g := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using determinedOn_empty g
  | @insert i I hi ih =>
      have hiA := hA i (Finset.mem_insert_self i I)
      have hIA := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      have hset : (⋃ j ∈ insert i I, A j) = A i ∪ ⋃ j ∈ I, A j := by
        ext x
        simp
      rw [hset]
      exact hiA.union hIA

/-- A finite family of determining maps may differ away from its pieces. -/
lemma determinedOn_glued_finset {ι : Type v} (I : Finset ι)
    (A : ι → Set X) (g : X → X) (f : ι → X → X)
    (hf : ∀ i ∈ I, DeterminedOn (A i) (f i))
    (hagree : ∀ i ∈ I, ∀ x ∈ A i, f i x = g x) :
    DeterminedOn (⋃ i ∈ I, A i) g :=
  determinedOn_finset_iUnion I A g
    (fun i hi => (hf i hi).congr (hagree i hi))

omit [MetricSpace X] in
/-- Compatible maps on a finite family of sets admit a single global
set-theoretic representative. The identity is used off the union, so no
inhabitedness hypothesis is needed. No shortness is asserted by this lemma. -/
lemma exists_glued_map {ι : Type v} (I : Finset ι)
    (A : ι → Set X) (f : ι → X → X)
    (hagree : ∀ i ∈ I, ∀ j ∈ I, ∀ x ∈ A i ∩ A j, f i x = f j x) :
    ∃ g : X → X, ∀ i ∈ I, ∀ x ∈ A i, g x = f i x := by
  classical
  let g : X → X := fun x =>
    if h : ∃ i ∈ I, x ∈ A i then f h.choose x else x
  refine ⟨g, ?_⟩
  intro i hi x hx
  have hex : ∃ j ∈ I, x ∈ A j := ⟨i, hi, hx⟩
  simp only [g, dite_eq_left hex]
  exact hagree hex.choose hex.choose_spec.1 i hi x ⟨hex.choose_spec.2, hx⟩

/-- Gluing preserves finite determination when each piece has already been
proved finitely determined. The geometric proof of this hypothesis remains
separate from the metric construction. -/
lemma exists_glued_determined_map {ι : Type v} (I : Finset ι)
    (A : ι → Set X) (f : ι → X → X)
    (hagree : ∀ i ∈ I, ∀ j ∈ I, ∀ x ∈ A i ∩ A j, f i x = f j x)
    (hdet : ∀ i ∈ I, DeterminedOn (A i) (f i)) :
    ∃ g : X → X, (∀ i ∈ I, ∀ x ∈ A i, g x = f i x) ∧
      DeterminedOn (⋃ i ∈ I, A i) g := by
  obtain ⟨g, hg⟩ := exists_glued_map I A f hagree
  refine ⟨g, hg, determinedOn_glued_finset I A g f hdet ?_⟩
  intro i hi x hx
  exact (hg i hi x hx).symm

/-- Compact disjoint sets have a positive uniform separation. Empty sets are
included without a special distance-to-the-empty-set convention. -/
lemma compact_separation {A B : Set X} (hA : IsCompact A) (hB : IsClosed B)
    (hdisj : Disjoint A B) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, r < dist x y := by
  obtain ⟨r, hr, hdist⟩ := Metric.exists_pos_forall_lt_edist hA hB hdisj
  refine ⟨(r : ℝ), by exact_mod_cast hr, ?_⟩
  intro x hx y hy
  have h := hdist x hx y hy
  rw [edist_nndist] at h
  have hn : r < nndist x y := ENNReal.coe_lt_coe.mp h
  exact_mod_cast hn

/-- If the intersection of two compact sets lies in an open common region,
then sufficiently close pairs, one from each set, both lie in that region.
This is the geometric buffer used before any approximation errors are chosen. -/
lemma compact_pair_near_intersection {A B U : Set X}
    (hA : IsCompact A) (hB : IsCompact B) (hU : IsOpen U)
    (hinter : A ∩ B ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ B, dist x y < r → x ∈ U ∧ y ∈ U := by
  have hleft : Disjoint (A \ U) B := by
    rw [Set.disjoint_left]
    intro x hx hxB
    exact hx.2 (hinter ⟨hx.1, hxB⟩)
  have hright : Disjoint (B \ U) A := by
    rw [Set.disjoint_left]
    intro x hx hxA
    exact hx.2 (hinter ⟨hxA, hx.1⟩)
  obtain ⟨r, hr, hrdist⟩ :=
    compact_separation (hA.diff hU) hB.isClosed hleft
  obtain ⟨s, hs, hsdist⟩ :=
    compact_separation (hB.diff hU) hA.isClosed hright
  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro x hx y hy hxy
  constructor
  · by_contra hxU
    have hl := hrdist x ⟨hx, hxU⟩ y hy
    have hm := min_le_left r s
    linarith
  · by_contra hyU
    have hl := hsdist y ⟨hy, hyU⟩ x hx
    rw [dist_comm y x] at hl
    have hm := min_le_right r s
    linarith

/-- A finite collection of conditions valid for sufficiently close pairs has
one positive common scale. -/
lemma finite_uniform_near_scale {ι : Type v} (I : Finset ι)
    (P : ι → X → X → Prop)
    (hP : ∀ i ∈ I, ∃ r : ℝ, 0 < r ∧
      ∀ x y : X, dist x y < r → P i x y) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ I, ∀ x y : X, dist x y < r → P i x y := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i I hi ih =>
      obtain ⟨r, hr, hri⟩ := hP i (Finset.mem_insert_self i I)
      obtain ⟨s, hs, hsI⟩ := ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))
      refine ⟨min r s, lt_min hr hs, ?_⟩
      intro j hj x y hxy
      rcases Finset.mem_insert.mp hj with rfl | hjI
      · exact hri x y (hxy.trans_le (min_le_left r s))
      · exact hsI j hjI x y (hxy.trans_le (min_le_right r s))

/-- The common geometric scale for a finite compact family depends only on
the sets and their chosen open buffers, not on any map or later approximation
error. -/
lemma compact_family_near_intersection {ι : Type v} (I : Finset ι)
    (A : ι → Set X) (U : ι → ι → Set X)
    (hA : ∀ i ∈ I, IsCompact (A i))
    (hU : ∀ i ∈ I, ∀ j ∈ I, IsOpen (U i j))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, A i ∩ A j ⊆ U i j) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ I, ∀ j ∈ I,
      ∀ x ∈ A i, ∀ y ∈ A j, dist x y < r → x ∈ U i j ∧ y ∈ U i j := by
  classical
  let P : (ι × ι) → X → X → Prop :=
    fun p x y => x ∈ A p.1 → y ∈ A p.2 → x ∈ U p.1 p.2 ∧ y ∈ U p.1 p.2
  have hP : ∀ p ∈ I.product I, ∃ r : ℝ, 0 < r ∧
      ∀ x y : X, dist x y < r → P p x y := by
    intro p hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
    obtain ⟨r, hr, hnear⟩ := compact_pair_near_intersection
      (hA p.1 hi) (hA p.2 hj) (hU p.1 hi p.2 hj) (hinter p.1 hi p.2 hj)
    exact ⟨r, hr, fun x y hxy hx hy => hnear x hx y hy hxy⟩
  obtain ⟨r, hr, hnear⟩ := finite_uniform_near_scale (I.product I) P hP
  refine ⟨r, hr, ?_⟩
  intro i hi j hj x hx y hy hxy
  exact hnear (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩) x y hxy hx hy

/-- On each selected open buffer, both pieces are represented by one global
short map. The geometric common scale therefore gives local shortness on the
whole finite union. -/
lemma short_near_on_union {ι : Type v} (I : Finset ι)
    (A : ι → Set X) (U : ι → ι → Set X) (g : X → X) (F : ι → ι → X → X)
    {a : ℝ}
    (hnear : ∀ i ∈ I, ∀ j ∈ I, ∀ x ∈ A i, ∀ y ∈ A j,
      dist x y < a → x ∈ U i j ∧ y ∈ U i j)
    (hF : ∀ i ∈ I, ∀ j ∈ I, Short (F i j))
    (hagree : ∀ i ∈ I, ∀ j ∈ I, ∀ z ∈ (A i ∪ A j) ∩ U i j,
      g z = F i j z) :
    ∀ x ∈ ⋃ i ∈ I, A i, ∀ y ∈ ⋃ i ∈ I, A i,
      dist x y < a → dist (g x) (g y) ≤ dist x y := by
  intro x hx y hy hxy
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨hxU, hyU⟩ := hnear i hi j hj x hxi y hyj hxy
  rw [hagree i hi j hj x ⟨Set.mem_union_left _ hxi, hxU⟩,
    hagree i hi j hj y ⟨Set.mem_union_right _ hyj, hyU⟩]
  exact hF i hi j hj x y

/-- A local shortness scale independent of the approximation error, together
with strict contraction of the reference map, gives global shortness. -/
theorem shortOn_of_local_uniform_approximation
    {A : Set X} {g u : X → X} {L δ a : ℝ}
    (hL : L < 1)
    (hlocal : ∀ x ∈ A, ∀ y ∈ A, dist x y < a → dist (g x) (g y) ≤ dist x y)
    (hu : ∀ x ∈ A, ∀ y ∈ A, dist (u x) (u y) ≤ L * dist x y)
    (herr : ∀ x ∈ A, dist (g x) (u x) ≤ δ)
    (hsmall : 2 * δ ≤ (1 - L) * a) : ShortOn g A := by
  intro x hx y hy
  by_cases hxy : dist x y < a
  · exact hlocal x hx y hy hxy
  · have hfar : a ≤ dist x y := le_of_not_gt hxy
    have hmargin : (1 - L) * a ≤ (1 - L) * dist x y :=
      mul_le_mul_of_nonneg_left hfar (by linarith)
    calc
      dist (g x) (g y) ≤ dist (g x) (u x) +
          (dist (u x) (u y) + dist (u y) (g y)) := by
        exact (dist_triangle (g x) (u x) (g y)).trans
          (add_le_add le_rfl (dist_triangle (u x) (u y) (g y)))
      _ ≤ δ + (L * dist x y + δ) :=
        add_le_add (herr x hx) (add_le_add (hu x hx y hy)
          (by simpa [dist_comm] using herr y hy))
      _ ≤ dist x y := by nlinarith

/-- A finite net that reaches the boundary of an old set cannot be separated
from that set by more than its mesh. This is the precise obstruction to the
parameter order in lines 421--424 of the supplied TeX proof. -/
theorem finite_net_separation_le
    {A D : Set X} (N : Finset X) {z : X} (hzA : z ∈ A) (hzD : z ∈ closure D)
    {a η : ℝ} (hnet : ∀ x ∈ D, ∃ p ∈ N, dist x p < η)
    (hsep : ∀ p ∈ N, ∀ q ∈ A, a ≤ dist p q) : a ≤ η := by
  let C : Set X := ⋃ p ∈ N, Metric.closedBall p η
  have hC : IsClosed C := isClosed_biUnion_finset fun _ _ => Metric.isClosed_closedBall
  have hDC : D ⊆ C := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hnet x hx
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hxp.le⟩
  have hzC : z ∈ C := (closure_minimal hDC hC) hzD
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hzC
  exact (hsep p hp z hzA).trans (by simpa [Metric.mem_closedBall, dist_comm] using hzp)

/-- The numerical requirement in the supplied proof is impossible once the
net obstruction `a ≤ η` is taken into account. -/
theorem source_parameter_impossible {a η δ : ℝ} (ha : 0 ≤ a)
    (haη : a ≤ η) (hδ : 0 < δ) :
    ¬ η < a * δ / (2 * (1 + δ)) := by
  have hden : 0 < 2 * (1 + δ) := by positivity
  have hbound : a * δ / (2 * (1 + δ)) ≤ a := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg ha hδ.le]
  exact not_lt_of_ge (hbound.trans haη)

end BrehmApprox
