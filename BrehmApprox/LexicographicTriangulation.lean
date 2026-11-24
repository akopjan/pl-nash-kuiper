module

public import Mathlib

/-!
# Pulling triangulations by lexicographic minimization

A compact barycentric fiber has a unique lexicographically least point.
Its positive support is affinely independent. These supports form the
pulling triangulation of a finite set of points.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox
namespace Pulling

open Classical

theorem exists_lexicographic_minimum (m : ℕ) (C : Set (Fin m → ℝ))
    (hC : IsCompact C) (hne : C.Nonempty) :
    ∃ w ∈ C, ∀ v ∈ C, toLex w ≤ toLex v := by
  induction m with
  | zero =>
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw, fun v _ => le_of_eq (congrArg toLex (Subsingleton.elim w v))⟩
  | succ m ih =>
    obtain ⟨w, hw, hwmin⟩ := hC.exists_isMinOn hne
      (continuous_apply (0 : Fin (m + 1))).continuousOn
    let D : Set (Fin (m + 1) → ℝ) := C ∩ {v | v 0 = w 0}
    have hD : IsCompact D := hC.inter_right
      (isClosed_eq (continuous_apply (0 : Fin (m + 1))) continuous_const)
    have hDne : D.Nonempty := ⟨w, hw, rfl⟩
    let tail : (Fin (m + 1) → ℝ) → (Fin m → ℝ) := fun v i => v i.succ
    have htail : Continuous tail := continuous_pi (fun i => continuous_apply i.succ)
    obtain ⟨a, ha, hamin⟩ := ih (tail '' D) (hD.image htail) (hDne.image tail)
    obtain ⟨u, huD, rfl⟩ := ha
    refine ⟨u, huD.1, ?_⟩
    intro v hv
    have hfirst : u 0 ≤ v 0 := by rw [huD.2]; exact hwmin hv
    rcases lt_or_eq_of_le hfirst with hlt | heq
    · exact le_of_lt (show Pi.Lex (· < ·) (· < ·) u v from
        ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, hlt⟩)
    · have hvD : v ∈ D := ⟨hv, heq.symm.trans huD.2⟩
      have ht := hamin (tail v) (mem_image_of_mem tail hvD)
      rcases lt_or_eq_of_le ht with hlt | heqtail
      · obtain ⟨i, hi, hiv⟩ := hlt
        exact le_of_lt (show Pi.Lex (· < ·) (· < ·) u v from
          ⟨i.succ, fun j => by
            refine Fin.cases (fun _ => heq) (fun k hj => ?_) j
            exact hi k (Fin.succ_lt_succ_iff.mp hj), hiv⟩)
      · apply le_of_eq
        apply congrArg toLex
        funext i
        refine Fin.cases heq (fun j => ?_) i
        exact congrFun (congrArg ofLex heqtail) j

theorem lex_comp_orderIso_lt_iff {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃o κ) (u v : κ → ℝ) :
    Pi.Lex (· < ·) (· < ·) (u ∘ e) (v ∘ e) ↔ Pi.Lex (· < ·) (· < ·) u v := by
  constructor
  · rintro ⟨i, hi, hiv⟩
    refine ⟨e i, fun j hj => ?_, hiv⟩
    have hji : e.symm j < i := by simpa using (e.symm.lt_iff_lt).mpr hj
    have hh := hi (e.symm j) hji
    simpa using hh
  · rintro ⟨i, hi, hiv⟩
    refine ⟨e.symm i, fun j hj => ?_, by simpa using hiv⟩
    have hji : e j < i := by simpa using (e.lt_iff_lt).mpr hj
    exact hi (e j) hji

theorem exists_lexicographic_minimum_finite {ι : Type*} [Fintype ι] [LinearOrder ι]
    (C : Set (ι → ℝ)) (hC : IsCompact C) (hne : C.Nonempty) :
    ∃ w ∈ C, ∀ v ∈ C, toLex w ≤ toLex v := by
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  let reindex : (ι → ℝ) → (Fin (Fintype.card ι) → ℝ) := fun w => w ∘ e
  have hr : Continuous reindex := continuous_pi (fun j => continuous_apply (e j))
  obtain ⟨u, hu, hmin⟩ := exists_lexicographic_minimum _ (reindex '' C)
    (hC.image hr) (hne.image reindex)
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨w, hw, ?_⟩
  intro v hv
  by_contra h
  have hlt : toLex v < toLex w := lt_of_not_ge h
  have hlt' : toLex (reindex v) < toLex (reindex w) :=
    (lex_comp_orderIso_lt_iff e v w).mpr hlt
  exact not_lt_of_ge (hmin (reindex v) (mem_image_of_mem reindex hv)) hlt'

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def simplexWeights (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

omit [LinearOrder ι] in
theorem convex_simplexWeights : Convex ℝ (simplexWeights ι) := by
  intro u hu v hv a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hb (hv.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hu.2, hv.2, mul_one]
  exact hab

omit [LinearOrder ι] in
theorem isCompact_simplexWeights : IsCompact (simplexWeights ι) := by
  have hclosed : IsClosed (simplexWeights ι) := by
    have hnon : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
    have hsum : IsClosed {w : ι → ℝ | ∑ i, w i = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    exact hnon.inter hsum
  apply IsCompact.of_isClosed_subset (s := Set.Icc (0 : ι → ℝ) 1) isCompact_Icc hclosed
  intro w hw
  refine ⟨hw.1, fun i => ?_⟩
  have hi := Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
  change w i ≤ 1
  simpa only [hw.2] using hi

theorem single_mem_simplexWeights (i : ι) : Pi.single i 1 ∈ simplexWeights ι := by
  refine ⟨fun j => ?_, by simp⟩
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

omit [Fintype ι] in
theorem lex_smul_lt {a : ℝ} (ha : 0 < a) {u v : ι → ℝ}
    (h : toLex u < toLex v) : toLex (a • u) < toLex (a • v) := by
  obtain ⟨i, hi, hiv⟩ := h
  refine ⟨i, fun j hj => ?_, ?_⟩
  · change a * u j = a * v j
    exact congrArg (a * ·) (hi j hj)
  · change a * u i < a * v i
    exact mul_lt_mul_of_pos_left hiv ha

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def barycenter (p : ι → E) (w : ι → ℝ) : E := ∑ i, w i • p i

omit [LinearOrder ι] in
theorem continuous_barycenter (p : ι → E) : Continuous (barycenter p) := by
  unfold barycenter
  fun_prop

def fiber (p : ι → E) (x : E) : Set (ι → ℝ) :=
  simplexWeights ι ∩ {w | barycenter p w = x}

omit [LinearOrder ι] in
theorem isCompact_fiber (p : ι → E) (x : E) : IsCompact (fiber p x) :=
  isCompact_simplexWeights.inter_right
      (isClosed_eq (continuous_barycenter p) continuous_const)

/-- Least barycentric coordinates for their represented point. -/
def Minimal (p : ι → E) (w : ι → ℝ) : Prop :=
  w ∈ simplexWeights ι ∧
    ∀ v ∈ simplexWeights ι, barycenter p v = barycenter p w → toLex w ≤ toLex v

theorem minimal_unique {p : ι → E} {u v : ι → ℝ}
    (hu : Minimal p u) (hv : Minimal p v) (heq : barycenter p u = barycenter p v) : u = v := by
  exact congrArg ofLex (le_antisymm (hu.2 v hv.1 heq.symm) (hv.2 u hu.1 heq))

theorem exists_minimal {p : ι → E} {x : E}
    (hx : (fiber p x).Nonempty) : ∃ w, Minimal p w ∧ barycenter p w = x := by
  obtain ⟨w, hw, hmin⟩ := exists_lexicographic_minimum_finite (fiber p x) (isCompact_fiber p x) hx
  refine ⟨w, ⟨hw.1, ?_⟩, hw.2⟩
  intro v hv heq
  exact hmin v ⟨hv, heq.trans hw.2⟩

omit [LinearOrder ι] in
theorem exists_positive_perturbation {w z : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, w i = 0 → z i = 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ w i + t * z i ∧ 0 ≤ w i - t * z i := by
  have heach (i : ι) : ∀ᶠ t : ℝ in nhds 0,
      0 ≤ w i + t * z i ∧ 0 ≤ w i - t * z i := by
    by_cases hwi : w i = 0
    · exact Filter.Eventually.of_forall (fun t => by simp [hwi, hz i hwi])
    · have hwi' : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hwi)
      have hp : Continuous (fun t : ℝ => w i + t * z i) := by fun_prop
      have hm : Continuous (fun t : ℝ => w i - t * z i) := by fun_prop
      have hp' : ∀ᶠ t : ℝ in nhds 0, 0 < w i + t * z i :=
        (hp.tendsto 0).eventually (Ioi_mem_nhds (by simpa using hwi'))
      have hm' : ∀ᶠ t : ℝ in nhds 0, 0 < w i - t * z i :=
        (hm.tendsto 0).eventually (Ioi_mem_nhds (by simpa using hwi'))
      filter_upwards [hp', hm'] with t htp htm
      exact ⟨htp.le, htm.le⟩
  have hall : ∀ᶠ t : ℝ in nhds 0, ∀ i, 0 ≤ w i + t * z i ∧ 0 ≤ w i - t * z i :=
    Filter.eventually_all.mpr heach
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ε / 2, by positivity, hball ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ε / 2)]
  linarith

theorem minimal_no_relation {p : ι → E} {w z : ι → ℝ}
    (hw : Minimal p w) (hzsum : ∑ i, z i = 0) (hzbary : barycenter p z = 0)
    (hz : ∀ i, w i = 0 → z i = 0) : z = 0 := by
  obtain ⟨t, ht, hnonneg⟩ := exists_positive_perturbation hw.1.1 hz
  have hplus : w + t • z ∈ simplexWeights ι := by
    refine ⟨fun i => (hnonneg i).1, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hw.1.2, hzsum, mul_zero, add_zero]
  have hminus : w - t • z ∈ simplexWeights ι := by
    refine ⟨fun i => (hnonneg i).2, ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hw.1.2, hzsum, mul_zero, sub_zero]
  have hbplus : barycenter p (w + t • z) = barycenter p w := by
    simp only [barycenter, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
      mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [show (∑ i, z i • p i) = 0 from hzbary, smul_zero, add_zero]
  have hbminus : barycenter p (w - t • z) = barycenter p w := by
    simp only [barycenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul,
      mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
    rw [show (∑ i, z i • p i) = 0 from hzbary, smul_zero, sub_zero]
  have hp := hw.2 (w + t • z) hplus hbplus
  have hm := hw.2 (w - t • z) hminus hbminus
  change toLex w ≤ toLex w + toLex (t • z) at hp
  change toLex w ≤ toLex w - toLex (t • z) at hm
  have hp0 : 0 ≤ toLex (t • z) := (le_add_iff_nonneg_right _).mp hp
  have hm0 : toLex (t • z) ≤ 0 := by
    have hh := (le_sub_iff_add_le).mp hm
    simpa only [add_le_iff_nonpos_right] using hh
  have htz : t • z = 0 := congrArg ofLex (le_antisymm hm0 hp0)
  exact (smul_eq_zero.mp htz).resolve_left ht.ne'

def support (w : ι → ℝ) : Finset (ι) := Finset.univ.filter fun i => w i ≠ 0

omit [LinearOrder ι] in
@[simp] theorem mem_support {w : ι → ℝ} {i : ι} :
    i ∈ support w ↔ w i ≠ 0 := by simp [support]

theorem minimal_support_independent {p : ι → E} {w : ι → ℝ}
    (hw : Minimal p w) : AffineIndependent ℝ (fun i : support w => p i.val) := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro c hcsum hcbary i
  have hcbary' : ∑ j : support w, c j • p j.val = 0 := by
    simpa only [Finset.weightedVSub_eq_linear_combination _ hcsum] using hcbary
  let z : ι → ℝ := fun j => if hj : j ∈ support w then c ⟨j, hj⟩ else 0
  have hzmem (j : support w) : z j.val = c j := by
    simp only [z, dite_eq_left j.property]
  have hzout (j : ι) (hj : j ∉ support w) : z j = 0 := by
    simp only [z, dite_eq_right hj]
  have hzsum : ∑ j, z j = 0 := by
    calc
      ∑ j, z j = ∑ j ∈ support w, z j :=
        (Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hzout j hj)).symm
      _ = ∑ j : support w, z j.val := (Finset.sum_coe_sort _ _).symm
      _ = ∑ j : support w, c j := Finset.sum_congr rfl (fun j _ => hzmem j)
      _ = 0 := hcsum
  have hzbary : barycenter p z = 0 := by
    calc
      barycenter p z = ∑ j ∈ support w, z j • p j :=
        (Finset.sum_subset (Finset.subset_univ _)
          (fun j _ hj => by rw [hzout j hj, zero_smul])).symm
      _ = ∑ j : support w, z j.val • p j.val := (Finset.sum_coe_sort _ _).symm
      _ = ∑ j : support w, c j • p j.val :=
        Finset.sum_congr rfl (fun j _ => by rw [hzmem j])
      _ = 0 := hcbary'
  have hz : ∀ j, w j = 0 → z j = 0 := by
    intro j hj
    simp [z, hj]
  have heq := minimal_no_relation hw hzsum hzbary hz
  have hi := congrFun heq i.val
  simpa only [hzmem i, Pi.zero_apply] using hi

theorem minimal_of_support_subset {p : ι → E} {w v : ι → ℝ}
    (hw : Minimal p w) (hv : v ∈ simplexWeights ι)
    (hsupp : support v ⊆ support w) : Minimal p v := by
  refine ⟨hv, ?_⟩
  intro q hq hqbary
  by_contra hmin
  have hqv : toLex q < toLex v := lt_of_not_ge hmin
  have hz (i : ι) (hi : w i = 0) : v i = 0 := by
    by_contra hiv
    exact (mem_support.mp (hsupp (mem_support.mpr hiv))) hi
  obtain ⟨t, ht, hnonneg⟩ := exists_positive_perturbation hw.1.1 hz
  let u : ι → ℝ := w - t • v + t • q
  have hu : u ∈ simplexWeights ι := by
    refine ⟨fun i => add_nonneg (hnonneg i).2 (mul_nonneg ht.le (hq.1 i)), ?_⟩
    simp only [u, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hw.1.2, hv.2, hq.2, mul_one, sub_add_cancel]
  have hubary : barycenter p u = barycenter p w := by
    change (∑ i, (w i - t * v i + t * q i) • p i) = _
    simp only [add_smul, sub_smul, mul_smul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.smul_sum]
    change barycenter p w - t • barycenter p v + t • barycenter p q = _
    rw [hqbary, sub_add_cancel]
  have hwu := hw.2 u hu hubary
  have huw : toLex u < toLex w := by
    change toLex w - toLex (t • v) + toLex (t • q) < toLex w
    calc
      toLex w - toLex (t • v) + toLex (t • q) <
          toLex w - toLex (t • v) + toLex (t • v) :=
        add_lt_add_of_le_of_lt le_rfl (lex_smul_lt ht hqv)
      _ = toLex w := sub_add_cancel _ _
  exact not_lt_of_ge hwu huw

def barycenterLinear (p : ι → E) : (ι → ℝ) →ₗ[ℝ] E where
  toFun := barycenter p
  map_add' u v := by simp [barycenter, add_smul, Finset.sum_add_distrib]
  map_smul' a u := by simp [barycenter, mul_smul, Finset.smul_sum]

def weightsOn (S : Finset ι) : Set (ι → ℝ) :=
  {w | w ∈ simplexWeights ι ∧ ∀ i ∉ S, w i = 0}

theorem support_subset_iff {S : Finset ι} {w : ι → ℝ} :
    support w ⊆ S ↔ ∀ i ∉ S, w i = 0 := by
  constructor
  · intro h i hi
    by_contra hwi
    exact hi (h (mem_support.mpr hwi))
  · intro h i hi
    by_contra hiS
    exact (mem_support.mp hi) (h i hiS)

omit [LinearOrder ι] in
theorem convex_weightsOn (S : Finset ι) : Convex ℝ (weightsOn S) := by
  intro u hu v hv a b ha hb hab
  refine ⟨convex_simplexWeights (ι := ι) hu.1 hv.1 ha hb hab, ?_⟩
  intro i hi
  simp only [Pi.add_apply, Pi.smul_apply, hu.2 i hi, hv.2 i hi, smul_zero, add_zero]

omit [LinearOrder ι] in
theorem barycenter_mem_convexHull {p : ι → E} {S : Finset ι} {w : ι → ℝ}
    (hw : w ∈ weightsOn S) : barycenter p w ∈ convexHull ℝ (S.image p : Set E) := by
  have hsum : ∑ i ∈ S, w i = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hw.2 i hi)]
    exact hw.1.2
  have hbary : barycenter p w = ∑ i ∈ S, w i • p i :=
    (Finset.sum_subset (Finset.subset_univ S)
      (fun i _ hi => by rw [hw.2 i hi, zero_smul])).symm
  rw [hbary]
  apply (convex_convexHull ℝ (S.image p : Set E)).sum_mem (fun i _ => hw.1.1 i) hsum
  intro i hi
  exact subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem convexHull_eq_barycenter_image (p : ι → E) (S : Finset ι) :
    convexHull ℝ (S.image p : Set E) = barycenter p '' weightsOn S := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨Pi.single i 1, ⟨single_mem_simplexWeights i, ?_⟩, ?_⟩
      · intro j hj
        have hji : j ≠ i := by intro hji; exact hj (hji ▸ hi)
        simp [hji]
      · simp [barycenter]
    · exact (convex_weightsOn S).linear_image (barycenterLinear p)
  · rintro x ⟨w, hw, rfl⟩
    exact barycenter_mem_convexHull hw

/-- A pulling face is a vertex set on which every barycentric vector is
already the lexicographically least representative of its image. -/
def IsFace (p : ι → E) (S : Finset ι) : Prop :=
  ∀ w ∈ weightsOn S, Minimal p w

theorem isFace_mono {p : ι → E} {S T : Finset ι}
    (hS : IsFace p S) (hTS : T ⊆ S) : IsFace p T := by
  intro w hw
  apply hS w
  refine ⟨hw.1, ?_⟩
  intro i hi
  exact hw.2 i (fun hiT => hi (hTS hiT))

theorem isFace_support {p : ι → E} {w : ι → ℝ} (hw : Minimal p w) :
    IsFace p (support w) := by
  intro v hv
  exact minimal_of_support_subset hw hv.1 (support_subset_iff.mpr hv.2)

theorem isFace_independent {p : ι → E} {S : Finset ι} (hS : IsFace p S) :
    AffineIndependent ℝ (fun i : S => p i.val) := by
  by_cases hne : S.Nonempty
  · let w : ι → ℝ := fun i => if i ∈ S then (S.card : ℝ)⁻¹ else 0
    have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hne.card_pos
    have hw : w ∈ weightsOn S := by
      refine ⟨⟨fun i => by dsimp [w]; split_ifs <;> positivity, ?_⟩, ?_⟩
      · simp [w, Finset.sum_ite_mem, hcard.ne']
      · intro i hi
        simp [w, hi]
    have hsupp : support w = S := by
      ext i
      simp [w, hcard.ne']
    rw [← hsupp]
    exact minimal_support_independent (hS w hw)
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    exact affineIndependent_empty_type _ _

theorem isFace_hulls_inter {p : ι → E} {S T : Finset ι}
    (hS : IsFace p S) (hT : IsFace p T) :
    convexHull ℝ (S.image p : Set E) ∩ convexHull ℝ (T.image p : Set E) =
      convexHull ℝ ((S ∩ T).image p : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [convexHull_eq_barycenter_image p S] at hx
    obtain ⟨u, hu, rfl⟩ := hx.1
    have hxT := hx.2
    rw [convexHull_eq_barycenter_image p T] at hxT
    obtain ⟨v, hv, hvbary⟩ := hxT
    have huv : u = v := minimal_unique (hS u hu) (hT v hv) hvbary.symm
    apply barycenter_mem_convexHull
    refine ⟨hu.1, ?_⟩
    intro i hi
    by_cases hiS : i ∈ S
    · rw [huv]
      exact hv.2 i (fun hiT => hi (Finset.mem_inter.mpr ⟨hiS, hiT⟩))
    · exact hu.2 i hiS
  · exact Set.subset_inter
      (convexHull_mono (Finset.coe_subset.mpr (Finset.image_mono p Finset.inter_subset_left)))
      (convexHull_mono (Finset.coe_subset.mpr (Finset.image_mono p Finset.inter_subset_right)))

theorem exists_face_mem_hull (p : ι → E) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range p)) :
    ∃ S : Finset ι, IsFace p S ∧ x ∈ convexHull ℝ (S.image p : Set E) := by
  have hset : (Finset.univ.image p : Set E) = Set.range p := by simp
  rw [← hset, convexHull_eq_barycenter_image p Finset.univ] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  obtain ⟨v, hv, hvx⟩ := exists_minimal (p := p) (x := x) ⟨w, hw.1, hwx⟩
  refine ⟨support v, isFace_support hv, ?_⟩
  rw [← hvx]
  exact barycenter_mem_convexHull ⟨hv.1, support_subset_iff.mp (Finset.Subset.refl _)⟩

end Pulling
end BrehmApprox
