module

public import BrehmApprox.SphericalBarycentricSimplex
public import BrehmApprox.HyperbolicSimplicialCharts

/-!
# Positive barycentric coordinates on a hyperbolic simplex

The coefficients are attached to unit Lorentz lifts. Normalizing their sum
to one makes the coordinates invariant under hyperbolic motions.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.HyperbolicBarycentric

variable {ι : Type*} [Fintype ι] {n : ℕ}

local instance hyperbolicBarycentricDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

abbrev Weights (ι : Type*) [Fintype ι] := Pulling.simplexWeights ι

def vector (v : ι → HyperbolicSpace n) (w : ι → ℝ) : ℝ × EuclideanSpace ℝ (Fin n) :=
  ∑ i, w i • HyperbolicSpace.lift (v i)

theorem vector_fst (v : ι → HyperbolicSpace n) (w : ι → ℝ) :
    (vector v w).1 = ∑ i, w i * Hyperboloid.height (v i).point := by
  change (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))) (vector v w) = _
  simp only [vector, map_sum, map_smul, LinearMap.fst_apply, HyperbolicSpace.lift, smul_eq_mul]

theorem vector_snd (v : ι → HyperbolicSpace n) (w : ι → ℝ) :
    (vector v w).2 = ∑ i, w i • (v i).point := by
  change (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) (vector v w) = _
  simp only [vector, map_sum, map_smul, LinearMap.snd_apply, HyperbolicSpace.lift]

theorem height_pos (v : ι → HyperbolicSpace n) (w : Weights ι) : 0 < (vector v w.val).1 := by
  rw [vector_fst]
  have hs : (0 : ℝ) < ∑ i, w.val i := by rw [w.property.2]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => w.property.1 i)).mp hs
  exact Finset.sum_pos' (fun j _ => mul_nonneg (w.property.1 j)
    (Hyperboloid.height_pos (v j).point).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (Hyperboloid.height_pos (v i).point)⟩

def kleinPoint (v : ι → HyperbolicSpace n) (w : Weights ι) : EuclideanSpace ℝ (Fin n) :=
  (vector v w.val).1⁻¹ • (vector v w.val).2

theorem kleinPoint_mem (v : ι → HyperbolicSpace n) (w : Weights ι) :
    kleinPoint v w ∈ convexHull ℝ (Set.range (fun i => HyperbolicSpace.klein (v i))) := by
  let a : ι → ℝ := fun i => w.val i * Hyperboloid.height (v i).point / (vector v w.val).1
  have ha (i : ι) : 0 ≤ a i := div_nonneg
    (mul_nonneg (w.property.1 i) (Hyperboloid.height_pos (v i).point).le) (height_pos v w).le
  have hs : ∑ i, a i = 1 := by
    simp only [a, ← Finset.sum_div, ← vector_fst]
    exact div_self (height_pos v w).ne'
  have hp : ∑ i, a i • HyperbolicSpace.klein (v i) = kleinPoint v w := by
    rw [kleinPoint, vector_snd, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [HyperbolicSpace.klein, smul_smul, smul_smul]
    congr 1
    dsimp [a]
    field_simp [(Hyperboloid.height_pos (v i).point).ne']
  have hm := Finset.univ.centerMass_mem_convexHull (z := fun i => HyperbolicSpace.klein (v i))
    (s := Set.range (fun i => HyperbolicSpace.klein (v i))) (fun i _ => ha i)
    (by rw [hs]; norm_num) (fun i _ => Set.mem_range_self i)
  rw [Finset.centerMass_eq_of_sum_1 _ _ hs, hp] at hm
  exact hm

theorem norm_kleinPoint_lt_one (v : ι → HyperbolicSpace n) (w : Weights ι) :
    ‖kleinPoint v w‖ < 1 := by
  have hsub : convexHull ℝ (Set.range (fun i => HyperbolicSpace.klein (v i))) ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    convexHull_min (by
      rintro p ⟨i, rfl⟩
      simpa only [Metric.mem_ball, dist_zero_right] using HyperbolicSpace.norm_klein_lt_one (v i))
      (convex_ball 0 1)
  simpa only [Metric.mem_ball, dist_zero_right] using hsub (kleinPoint_mem v w)

def point (v : ι → HyperbolicSpace n) (w : Weights ι) : HyperbolicSpace n :=
  HyperbolicSpace.fromKlein (kleinPoint v w)

theorem continuous_point (v : ι → HyperbolicSpace n) : Continuous (point v) := by
  have hv : Continuous (vector v) := by unfold vector; fun_prop
  have hk : Continuous (kleinPoint v) := by
    exact ((continuous_fst.comp (hv.comp continuous_subtype_val)).inv₀
      (fun w => (height_pos v w).ne')).smul
      (continuous_snd.comp (hv.comp continuous_subtype_val))
  exact HyperbolicSpace.continuousOn_fromKlein.comp_continuous hk
    (fun w => by simpa only [Metric.mem_ball, dist_zero_right] using norm_kleinPoint_lt_one v w)

theorem vector_point (v : ι → HyperbolicSpace n) (w : Weights ι) :
    ∃ c : ℝ, 0 < c ∧ vector v w.val = c • HyperbolicSpace.lift (point v w) := by
  let c := (vector v w.val).1 / Hyperboloid.height (point v w).point
  refine ⟨c, div_pos (height_pos v w) (Hyperboloid.height_pos _), ?_⟩
  have hk : HyperbolicSpace.klein (point v w) = kleinPoint v w :=
    HyperbolicSpace.klein_fromKlein (norm_kleinPoint_lt_one v w)
  apply Prod.ext
  · change (vector v w.val).1 = c * Hyperboloid.height (point v w).point
    exact (div_mul_cancel₀ _ (Hyperboloid.height_pos _).ne').symm
  · change (vector v w.val).2 = c • (point v w).point
    have he := congrArg (fun z => (vector v w.val).1 • z) hk
    simpa only [HyperbolicSpace.klein, kleinPoint, smul_smul,
      mul_inv_cancel₀ (height_pos v w).ne', one_smul, c, div_eq_mul_inv] using he.symm

theorem point_unique (v : ι → HyperbolicSpace n) (w : Weights ι)
    (x : HyperbolicSpace n) {c : ℝ} (hc : 0 < c)
    (he : vector v w.val = c • HyperbolicSpace.lift x) : point v w = x := by
  have ht := congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.1) he
  have hp := congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.2) he
  change (vector v w.val).1 = c * Hyperboloid.height x.point at ht
  change (vector v w.val).2 = c • x.point at hp
  have hk : kleinPoint v w = HyperbolicSpace.klein x := by
    rw [kleinPoint, ht, hp, smul_smul, HyperbolicSpace.klein]
    congr 1
    field_simp [hc.ne', (Hyperboloid.height_pos x.point).ne']
  rw [point, hk, HyperbolicSpace.fromKlein_klein]

theorem point_injective (v : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => HyperbolicSpace.lift (v i))) :
    Function.Injective (point v) := by
  intro w z heq
  obtain ⟨c, hc, hw⟩ := vector_point v w
  obtain ⟨d, hd, hz⟩ := vector_point v z
  have he : d • vector v w.val = c • vector v z.val := by rw [hw, hz, heq, smul_smul, smul_smul, mul_comm]
  have he' : (∑ i, (d * w.val i) • HyperbolicSpace.lift (v i)) =
      ∑ i, (c * z.val i) • HyperbolicSpace.lift (v i) := by
    simpa only [vector, Finset.smul_sum, smul_smul] using he
  have hcoeff : (fun i => d * w.val i) = (fun i => c * z.val i) :=
    hv.fintypeLinearCombination_injective he'
  have hdc : d = c := by
    have hs := congrArg (fun a : ι → ℝ => ∑ i, a i) hcoeff
    simpa only [← Finset.mul_sum, w.property.2, z.property.2, mul_one] using hs
  apply Subtype.ext
  funext i
  have hh := congrFun hcoeff i
  rw [hdc] at hh
  exact mul_left_cancel₀ hc.ne' hh

theorem vertex_injective (v : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => HyperbolicSpace.lift (v i))) : Function.Injective v :=
  fun _ _ h => hv.injective (congrArg HyperbolicSpace.lift h)

theorem point_mem (v : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => HyperbolicSpace.lift (v i))) (w : Weights ι) :
    point v w ∈ hyperbolicCell (Finset.univ.image v) := by
  let a : HyperbolicSpace n → ℝ := fun x => if h : ∃ i, v i = x then w.val h.choose else 0
  have ha (i : ι) : a (v i) = w.val i := by
    have hi : ∃ j, v j = v i := ⟨i, rfl⟩
    simp only [a, dite_eq_left hi]
    exact congrArg w.val (vertex_injective v hv hi.choose_spec)
  obtain ⟨c, hc, he⟩ := vector_point v w
  refine ⟨a, ?_, c, hc, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [ha]
    exact w.property.1 i
  · rw [Finset.sum_image (fun i _ j _ hij => vertex_injective v hv hij)]
    simpa only [ha, vector] using he

theorem range_point (v : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => HyperbolicSpace.lift (v i))) :
    Set.range (point v) = hyperbolicCell (Finset.univ.image v) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨w, rfl⟩
    exact point_mem v hv w
  · intro x hx
    obtain ⟨a, ha, c, hc, hrep⟩ := hx
    rw [Finset.sum_image (fun i _ j _ hij => vertex_injective v hv hij)] at hrep
    have hai (i : ι) : 0 ≤ a (v i) := ha _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    let s : ℝ := ∑ i, a (v i)
    have hs : 0 < s := by
      have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => hai i)
      apply lt_of_le_of_ne hs0
      intro heq
      have hz : ∀ i, a (v i) = 0 := by
        have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hai i)).mp heq.symm
        exact fun i => hh i (Finset.mem_univ i)
      have ht := congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.1) hrep
      simp only [hz, zero_smul, Finset.sum_const_zero, Prod.fst_zero, Prod.fst_smul,
        HyperbolicSpace.lift, smul_eq_mul] at ht
      exact (mul_pos hc (Hyperboloid.height_pos x.point)).ne' ht.symm
    let w : Weights ι := ⟨fun i => a (v i) / s,
      ⟨fun i => div_nonneg (hai i) hs.le, by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        exact mul_inv_cancel₀ hs.ne'⟩⟩
    have hw : vector v w.val = (c / s) • HyperbolicSpace.lift x := by
      calc
        vector v w.val = s⁻¹ • ∑ i, a (v i) • HyperbolicSpace.lift (v i) := by
          simp only [vector, w, div_eq_mul_inv, Finset.smul_sum, smul_smul, mul_comm]
        _ = (c / s) • HyperbolicSpace.lift x := by rw [hrep, smul_smul]; congr 1; ring
    exact ⟨w, point_unique v w x (div_pos hc hs) hw⟩

def homeomorph (v : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => HyperbolicSpace.lift (v i))) :
    Weights ι ≃ₜ hyperbolicCell (Finset.univ.image v) := by
  let : CompactSpace (Weights ι) := isCompact_iff_compactSpace.mp Pulling.isCompact_simplexWeights
  let f : Weights ι → hyperbolicCell (Finset.univ.image v) := fun w => ⟨point v w, point_mem v hv w⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      exact point_injective v hv (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ Set.range (point v) := by rw [range_point v hv]; exact x.property
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, Subtype.ext hw⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    ((continuous_point v).subtype_mk _)

@[simp] theorem homeomorph_apply (v : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => HyperbolicSpace.lift (v i))) (w : Weights ι) :
    (homeomorph v hv w).val = point v w := rfl

end BrehmApprox.HyperbolicBarycentric
