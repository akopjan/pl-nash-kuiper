module

public import PLGeometry.ChartedComplex
public import Mathlib.Topology.LocallyFinite

/-!
# Radial neighborhoods in finite charted complexes

Each point has an open star and a continuous radial distance on its closed
star. A positive uniform radius in all incident charts lies in the open
star. These facts use only the finite cell atlas and its metric coherence.
-/

@[expose] public section
noncomputable section

open Set

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

/-- The union of all closed cells incident to a point. -/
def closedStar (p : P) : Set P :=
  ⋃ σ : {σ : Finset P // σ ∈ T.simplices ∧ p ∈ T.cell σ}, T.cell σ.val

/-- A point belongs to this open star if every cell containing it also
contains the center. -/
def openStar (p : P) : Set P :=
  {x | ∀ σ ∈ T.simplices, x ∈ T.cell σ → p ∈ T.cell σ}

theorem mem_openStar_self (p : P) : p ∈ T.openStar p := fun _ _ h => h

theorem isOpen_openStar (p : P) : IsOpen (T.openStar p) := by
  have hfin : {σ ∈ T.simplices | p ∉ T.cell σ}.Finite :=
    T.finite_simplices.subset (fun _ h => h.1)
  have he : T.openStar p = (⋃ σ ∈ {σ ∈ T.simplices | p ∉ T.cell σ}, T.cell σ)ᶜ := by
    ext x
    simp only [openStar, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro hx σ hσ hxσ
      exact hσ.2 (hx σ hσ.1 hxσ)
    · intro hx σ hσ hxσ
      by_contra hpσ
      exact hx σ ⟨hσ, hpσ⟩ hxσ
  rw [he]
  exact (hfin.isClosed_biUnion (fun σ hσ => T.closed_cell σ hσ.1)).isOpen_compl

theorem openStar_subset_closedStar (p : P) : T.openStar p ⊆ T.closedStar p := by
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ := T.cover x
  exact Set.mem_iUnion.mpr ⟨⟨σ, hσ, hx σ hσ hxσ⟩, hxσ⟩

/-- The chart distance from the center, independent of the incident chart. -/
def radialDistance (p x : P) : ℝ := by
  classical
  exact if h : ∃ σ ∈ T.simplices, p ∈ T.cell σ ∧ x ∈ T.cell σ then
    dist (T.chart h.choose p) (T.chart h.choose x)
  else 0

theorem radialDistance_eq (p : P) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hp : p ∈ T.cell σ) {x : P} (hx : x ∈ T.cell σ) :
    T.radialDistance p x = dist (T.chart σ p) (T.chart σ x) := by
  have he : ∃ τ ∈ T.simplices, p ∈ T.cell τ ∧ x ∈ T.cell τ := ⟨σ, hσ, hp, hx⟩
  simp only [radialDistance, dite_eq_left he]
  exact T.metric_coherence he.choose he.choose_spec.1 σ hσ
    p ⟨he.choose_spec.2.1, hp⟩ x ⟨he.choose_spec.2.2, hx⟩

@[simp] theorem radialDistance_self (p : P) : T.radialDistance p p = 0 := by
  obtain ⟨σ, hσ, hp⟩ := T.cover p
  rw [T.radialDistance_eq p hσ hp hp, dist_self]

theorem continuousOn_radialDistance (p : P) :
    ContinuousOn (T.radialDistance p) (T.closedStar p) := by
  let J := {σ : Finset P // σ ∈ T.simplices ∧ p ∈ T.cell σ}
  have hfin : {σ ∈ T.simplices | p ∈ T.cell σ}.Finite :=
    T.finite_simplices.subset (fun _ h => h.1)
  let : Finite J := hfin.to_subtype
  apply (locallyFinite_of_finite (fun σ : J => T.cell σ.val)).continuousOn_iUnion
    (fun σ => T.closed_cell σ.val σ.property.1)
  intro σ
  have hc : ContinuousOn (fun x => dist (T.chart σ.val p) (T.chart σ.val x))
      (T.cell σ.val) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_const.dist
      (continuousOn_iff_continuous_domRestrict.mp (T.chart_continuousOn σ.val σ.property.1))
  apply hc.congr
  intro x hx
  exact T.radialDistance_eq p σ.property.1 σ.property.2 hx

/-- An open radial neighborhood contained in the open star. -/
def starBall (p : P) (r : ℝ) : Set P := T.openStar p ∩ T.radialDistance p ⁻¹' Set.Iio r

theorem isOpen_starBall (p : P) (r : ℝ) : IsOpen (T.starBall p r) :=
  ((T.continuousOn_radialDistance p).mono (T.openStar_subset_closedStar p)).isOpen_inter_preimage
    (T.isOpen_openStar p) isOpen_Iio

theorem mem_starBall_self (p : P) {r : ℝ} (hr : 0 < r) : p ∈ T.starBall p r := by
  exact ⟨T.mem_openStar_self p, by simpa only [Set.mem_preimage, Set.mem_Iio, T.radialDistance_self] using hr⟩

/-- The open star contains one positive-radius ball in every incident model
simplex, with a radius independent of that simplex. -/
theorem exists_radial_star_radius (p : P) :
    ∃ r : ℝ, 0 < r ∧ ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < r → x ∈ T.openStar p := by
  classical
  let J := {σ : Finset P // σ ∈ T.simplices ∧ p ∈ T.cell σ}
  have hfin : {σ ∈ T.simplices | p ∈ T.cell σ}.Finite :=
    T.finite_simplices.subset (fun _ h => h.1)
  let : Fintype J := hfin.fintype
  have hJ : Nonempty J := by
    obtain ⟨σ, hσ, hp⟩ := T.cover p
    exact ⟨⟨σ, hσ, hp⟩⟩
  let : Nonempty J := hJ
  have hlocal (σ : J) : ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ T.cell σ.val, dist (T.chart σ.val p) (T.chart σ.val x) < r →
        x ∈ T.openStar p := by
    let e := T.cellHomeomorph σ.val σ.property.1
    let z : hull κ n (σ.val.image (T.chart σ.val)) := e ⟨p, σ.property.2⟩
    have hz : (e.symm z : P) ∈ T.openStar p := by
      simpa only [z, Homeomorph.symm_apply_apply] using T.mem_openStar_self p
    have hopen : IsOpen ((fun y => (e.symm y : P)) ⁻¹' T.openStar p) :=
      (T.isOpen_openStar p).preimage (continuous_subtype_val.comp e.symm.continuous)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z hz
    refine ⟨r, hr, ?_⟩
    intro x hx hdist
    have heq : (e ⟨x, hx⟩ : Model κ n) = T.chart σ.val x :=
      T.cellHomeomorph_apply σ.val σ.property.1 ⟨x, hx⟩
    have heqp : (z : Model κ n) = T.chart σ.val p :=
      T.cellHomeomorph_apply σ.val σ.property.1 ⟨p, σ.property.2⟩
    have hxball : e ⟨x, hx⟩ ∈ Metric.ball z r := by
      change dist (e ⟨x, hx⟩ : Model κ n) (z : Model κ n) < r
      rw [heq, heqp, dist_comm]
      exact hdist
    have hm := hball hxball
    simpa only [Set.mem_preimage, Homeomorph.symm_apply_apply] using hm
  choose r hr hball using hlocal
  let r₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty r
  refine ⟨r₀, ?_, ?_⟩
  · dsimp only [r₀]
    rw [Finset.lt_inf'_iff]
    exact fun σ _ => hr σ
  intro σ hσ hp x hx hdist
  exact hball ⟨σ, hσ, hp⟩ x hx
    (hdist.trans_le (Finset.inf'_le r (Finset.mem_univ (⟨σ, hσ, hp⟩ : J))))

end ArchivePLGeometry.FiniteChartedComplex
