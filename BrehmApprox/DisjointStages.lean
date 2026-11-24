module

public import BrehmApprox.FiniteFlatteningComposition
public import Mathlib.Order.Filter.Finite

/-!+# Simultaneous maps with disjoint active regions

A stage applies the unique map which moves the point, when there is one.
Pairwise disjoint activity together with preservation of the other fixed-point
sets gives a Lipschitz constant `L²`, independent of the number of maps.
-/

@[expose] public section

noncomputable section

open scoped Topology NNReal
open Filter

namespace BrehmApprox

universe u v

variable {X : Type u} {ι : Type v}

/-- At most one member of the family moves each point. -/
def DisjointActivity (I : Finset ι) (Q : ι → X → X) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ x, Q i x ≠ x → Q j x = x

/-- A moved point remains fixed by every other member after its active map
has been applied. This is stronger than disjointness of active regions alone. -/
def StableActivity (I : Finset ι) (Q : ι → X → X) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ x, Q i x ≠ x → Q j (Q i x) = Q i x

/-- Apply an active member of the finite family, or the identity if every
member fixes the point. Under `DisjointActivity` the choice is unique. -/
def disjointStage (I : Finset ι) (Q : ι → X → X) (x : X) : X := by
  classical
  exact if h : ∃ i ∈ I, Q i x ≠ x then Q h.choose x else x

lemma disjointStage_eq_of_fixed (I : Finset ι) (Q : ι → X → X) (x : X)
    (hfix : ∀ i ∈ I, Q i x = x) : disjointStage I Q x = x := by
  classical
  unfold disjointStage
  split_ifs with h
  · obtain ⟨i, hi, hix⟩ := h
    exact (hix (hfix i hi)).elim
  · rfl

lemma disjointStage_eq_of_other_fixed (I : Finset ι) (Q : ι → X → X)
    {i : ι} (hi : i ∈ I) (x : X)
    (hfix : ∀ j ∈ I, j ≠ i → Q j x = x) : disjointStage I Q x = Q i x := by
  classical
  unfold disjointStage
  split_ifs with h
  · have hk := h.choose_spec
    have heq : h.choose = i := by
      by_contra hne
      exact hk.2 (hfix h.choose hk.1 hne)
    rw [heq]
  · have hiFix : Q i x = x := by
      by_contra hne
      exact h ⟨i, hi, hne⟩
    exact hiFix.symm

lemma disjointStage_eq_of_active (I : Finset ι) (Q : ι → X → X)
    (hdis : DisjointActivity I Q) {i : ι} (hi : i ∈ I) {x : X}
    (hix : Q i x ≠ x) : disjointStage I Q x = Q i x := by
  exact disjointStage_eq_of_other_fixed I Q hi x
    (fun j hj hji => hdis i hi j hj hji.symm x hix)

lemma disjointStage_mapsTo (I : Finset ι) (Q : ι → X → X) {A : Set X}
    (hQ : ∀ i ∈ I, Set.MapsTo (Q i) A A) :
    Set.MapsTo (disjointStage I Q) A A := by
  classical
  intro x hx
  unfold disjointStage
  split_ifs with h
  · exact hQ h.choose h.choose_spec.1 hx
  · exact hx

lemma disjointStage_preserves_projection {Y : Type*} (I : Finset ι)
    (Q : ι → X → X) (π : X → Y) (x : X)
    (hQ : ∀ i ∈ I, π (Q i x) = π x) : π (disjointStage I Q x) = π x := by
  classical
  unfold disjointStage
  split_ifs with h
  · exact hQ h.choose h.choose_spec.1
  · rfl

section Metric

variable [MetricSpace X]

/-- The bound is independent of the cardinality of `I`. Its two factors arise
only when the two points are moved by different members of the family. -/
theorem disjointStage_lipschitz (I : Finset ι) (Q : ι → X → X)
    (hdis : DisjointActivity I Q) (hstable : StableActivity I Q)
    {L : ℝ≥0} (hL : 1 ≤ L) (hQ : ∀ i ∈ I, LipschitzWith L (Q i)) :
    LipschitzWith (L * L) (disjointStage I Q) := by
  classical
  have hLr : (1 : ℝ) ≤ L := hL
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hLL : (L : ℝ) ≤ (L : ℝ) * L := by nlinarith
  have h1LL : (1 : ℝ) ≤ (L : ℝ) * L := hLr.trans hLL
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (disjointStage I Q x) (disjointStage I Q y) ≤
    ((L : ℝ) * L) * dist x y
  by_cases hx : ∃ i ∈ I, Q i x ≠ x
  · obtain ⟨i, hi, hix⟩ := hx
    rw [disjointStage_eq_of_active I Q hdis hi hix]
    by_cases hy : ∃ j ∈ I, Q j y ≠ y
    · obtain ⟨j, hj, hjy⟩ := hy
      rw [disjointStage_eq_of_active I Q hdis hj hjy]
      by_cases hij : i = j
      · subst j
        exact ((hQ i hi).dist_le_mul x y).trans
          (mul_le_mul_of_nonneg_right hLL dist_nonneg)
      · have hjx : Q j x = x := hdis i hi j hj hij x hix
        have hiy : Q i (Q j y) = Q j y := hstable j hj i hi (fun h => hij h.symm) y hjy
        calc
          dist (Q i x) (Q j y) = dist (Q i x) (Q i (Q j y)) := by rw [hiy]
          _ ≤ L * dist x (Q j y) := (hQ i hi).dist_le_mul x (Q j y)
          _ = L * dist (Q j x) (Q j y) := by rw [hjx]
          _ ≤ L * (L * dist x y) :=
            mul_le_mul_of_nonneg_left ((hQ j hj).dist_le_mul x y) hL0
          _ = ((L : ℝ) * L) * dist x y := by ring
    · have hfix : ∀ j ∈ I, Q j y = y := by
        intro j hj
        by_contra hne
        exact hy ⟨j, hj, hne⟩
      rw [disjointStage_eq_of_fixed I Q y hfix]
      calc
        dist (Q i x) y = dist (Q i x) (Q i y) := by rw [hfix i hi]
        _ ≤ L * dist x y := (hQ i hi).dist_le_mul x y
        _ ≤ ((L : ℝ) * L) * dist x y := mul_le_mul_of_nonneg_right hLL dist_nonneg
  · have hfix : ∀ i ∈ I, Q i x = x := by
      intro i hi
      by_contra hne
      exact hx ⟨i, hi, hne⟩
    rw [disjointStage_eq_of_fixed I Q x hfix]
    by_cases hy : ∃ j ∈ I, Q j y ≠ y
    · obtain ⟨j, hj, hjy⟩ := hy
      rw [disjointStage_eq_of_active I Q hdis hj hjy]
      calc
        dist x (Q j y) = dist (Q j x) (Q j y) := by rw [hfix j hj]
        _ ≤ L * dist x y := (hQ j hj).dist_le_mul x y
        _ ≤ ((L : ℝ) * L) * dist x y := mul_le_mul_of_nonneg_right hLL dist_nonneg
    · have hfixY : ∀ j ∈ I, Q j y = y := by
        intro j hj
        by_contra hne
        exact hy ⟨j, hj, hne⟩
      rw [disjointStage_eq_of_fixed I Q y hfixY]
      exact (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right h1LL (dist_nonneg : 0 ≤ dist x y))

lemma disjointStage_displacement (I : Finset ι) (Q : ι → X → X)
    {e : ℝ} (he : 0 ≤ e) (hQ : ∀ i ∈ I, ∀ x, dist (Q i x) x ≤ e) :
    ∀ x, dist (disjointStage I Q x) x ≤ e := by
  classical
  intro x
  unfold disjointStage
  split_ifs with h
  · exact hQ h.choose h.choose_spec.1 x
  · simpa only [dist_self] using he

lemma disjointStage_continuous (I : Finset ι) (Q : ι → X → X)
    (hdis : DisjointActivity I Q) (hstable : StableActivity I Q)
    {L : ℝ≥0} (hL : 1 ≤ L) (hQ : ∀ i ∈ I, LipschitzWith L (Q i)) :
    Continuous (disjointStage I Q) :=
  (disjointStage_lipschitz I Q hdis hstable hL hQ).continuous

/-- The same estimate holds on an invariant subset. In particular, curved
model maps need only satisfy the estimate in one small chart cell. -/
theorem disjointStage_lipschitzOn (I : Finset ι) (Q : ι → X → X)
    (hdis : DisjointActivity I Q) (hstable : StableActivity I Q)
    {D : Set X} (hpres : ∀ i ∈ I, Set.MapsTo (Q i) D D)
    {L : ℝ≥0} (hL : 1 ≤ L)
    (hQ : ∀ i ∈ I, ∀ x ∈ D, ∀ y ∈ D, dist (Q i x) (Q i y) ≤ L * dist x y) :
    ∀ x ∈ D, ∀ y ∈ D,
      dist (disjointStage I Q x) (disjointStage I Q y) ≤ (L * L : ℝ≥0) * dist x y := by
  classical
  let R : ι → D → D := fun i x =>
    if hi : i ∈ I then ⟨Q i x, hpres i hi x.property⟩ else x
  have hRval (i : ι) (hi : i ∈ I) (x : D) : (R i x : X) = Q i x := by
    simp only [R, dite_eq_left hi]
  have hactive (i : ι) (hi : i ∈ I) (x : D) : R i x ≠ x ↔ Q i x ≠ x := by
    constructor
    · intro h hn
      apply h
      apply Subtype.ext
      rw [hRval i hi x, hn]
    · intro h hn
      apply h
      have he := congrArg Subtype.val hn
      rwa [hRval i hi x] at he
  have hdisR : DisjointActivity I R := by
    intro i hi j hj hij x hx
    apply Subtype.ext
    rw [hRval j hj x]
    exact hdis i hi j hj hij x ((hactive i hi x).mp hx)
  have hstableR : StableActivity I R := by
    intro i hi j hj hij x hx
    apply Subtype.ext
    rw [hRval j hj (R i x), hRval i hi x]
    exact hstable i hi j hj hij x ((hactive i hi x).mp hx)
  have hLipR : ∀ i ∈ I, LipschitzWith L (R i) := by
    intro i hi
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (R i x : X) (R i y : X) ≤ (L : ℝ) * dist (x : X) (y : X)
    rw [hRval i hi x, hRval i hi y]
    exact hQ i hi x x.property y y.property
  have hstageVal (x : D) : (disjointStage (X := D) I R x : X) = disjointStage I Q x := by
    by_cases hmove : ∃ i ∈ I, Q i x ≠ x
    · obtain ⟨i, hi, hx⟩ := hmove
      rw [disjointStage_eq_of_active I R hdisR hi ((hactive i hi x).mpr hx),
        disjointStage_eq_of_active I Q hdis hi hx, hRval i hi x]
    · have hfix : ∀ i ∈ I, Q i x = x := by
        intro i hi
        by_contra hn
        exact hmove ⟨i, hi, hn⟩
      have hfixR : ∀ i ∈ I, R i x = x := by
        intro i hi
        apply Subtype.ext
        rw [hRval i hi x, hfix i hi]
      rw [disjointStage_eq_of_fixed I R x hfixR, disjointStage_eq_of_fixed I Q x hfix]
  intro x hx y hy
  have h := (disjointStage_lipschitz I R hdisR hstableR hL hLipR).dist_le_mul
    (⟨x, hx⟩ : D) (⟨y, hy⟩ : D)
  change dist (disjointStage (X := D) I R ⟨x, hx⟩ : X) (disjointStage (X := D) I R ⟨y, hy⟩ : X) ≤
    (L * L : ℝ≥0) * dist x y at h
  rwa [hstageVal ⟨x, hx⟩, hstageVal ⟨y, hy⟩] at h

end Metric

section Topology

variable [TopologicalSpace X]

/-- Local equality with one member follows when all other members are locally
the identity. Finiteness is used only to intersect their neighborhoods. -/
theorem disjointStage_eventuallyEq (I : Finset ι) (Q : ι → X → X)
    {i : ι} (hi : i ∈ I) {p : X}
    (hother : ∀ j ∈ I, j ≠ i → Q j =ᶠ[𝓝 p] id) :
    disjointStage I Q =ᶠ[𝓝 p] Q i := by
  classical
  have hall : ∀ᶠ x in 𝓝 p, ∀ j ∈ I, j ≠ i → Q j x = x := by
    apply (Filter.eventually_all_finset I).2
    intro j hj
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ hne => (hne hji).elim)
    · exact (hother j hj hji).mono (fun _ hx _ => hx)
  filter_upwards [hall] with x hx
  exact disjointStage_eq_of_other_fixed I Q hi x hx

theorem disjointStage_local_collapse (I : Finset ι) (Q : ι → X → X)
    {i : ι} (hi : i ∈ I) {p : X} {π : X → X}
    (hother : ∀ j ∈ I, j ≠ i → Q j =ᶠ[𝓝 p] id)
    (hiπ : Q i =ᶠ[𝓝 p] π) : disjointStage I Q =ᶠ[𝓝 p] π :=
  (disjointStage_eventuallyEq I Q hi hother).trans hiπ

theorem disjointStage_eventually_preserves_projection {Y : Type*} (I : Finset ι)
    (Q : ι → X → X) (π : X → Y) {p : X}
    (hQ : ∀ i ∈ I, (fun x => π (Q i x)) =ᶠ[𝓝 p] π) :
    (fun x => π (disjointStage I Q x)) =ᶠ[𝓝 p] π := by
  have hall : ∀ᶠ x in 𝓝 p, ∀ i ∈ I, π (Q i x) = π x :=
    (Filter.eventually_all_finset I).2 hQ
  filter_upwards [hall] with x hx
  exact disjointStage_preserves_projection I Q π x hx

end Topology

end BrehmApprox
