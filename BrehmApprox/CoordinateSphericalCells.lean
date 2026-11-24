module

public import BrehmApprox.SphereShortRigidity
public import BrehmApprox.SphericalCells
public import Mathlib.Tactic.FinCases

/-!
# Genuine spherical cells cut out by signed coordinate axes

The vertices, hemispheres and covering cells below are actual subsets of the
round sphere, rather than an abstract triangulation certificate.
-/

@[expose] public section
noncomputable section

namespace BrehmApprox.CoordinateSphericalCells

open GeodesicSphere
open scoped BigOperators

variable {n : ℕ}

local instance coordinateSphericalCellsLocalInstance1 : DecidableEq (GeodesicSphere n) := Classical.decEq _

def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]
@[simp] lemma sign_ne_zero (b : Bool) : sign b ≠ 0 := by cases b <;> norm_num [sign]

def signedPole (σ : Fin (n + 1) → Bool) (i : Fin (n + 1)) : GeodesicSphere n :=
  if σ i then coordinatePole n i else antipode (coordinatePole n i)

theorem signedPole_val (σ : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    (signedPole σ i).val = sign (σ i) • (coordinatePole n i).val := by
  unfold signedPole sign
  cases σ i <;> simp [antipode]

theorem inner_signedPole_coordinate (σ : Fin (n + 1) → Bool) (i j : Fin (n + 1)) :
    inner ℝ (signedPole σ i).val (coordinatePole n j).val =
      if i = j then sign (σ i) else 0 := by
  rw [signedPole_val, real_inner_smul_left]
  simp [coordinatePole_val, EuclideanSpace.inner_single_left, PiLp.single_apply]

theorem inner_signedPole (σ : Fin (n + 1) → Bool) (i j : Fin (n + 1)) :
    inner ℝ (signedPole σ i).val (signedPole σ j).val = if i = j then 1 else 0 := by
  rw [signedPole_val σ j, inner_smul_right, inner_signedPole_coordinate]
  split_ifs with h
  · subst j
    exact sign_sq _
  · simp

theorem signedPole_injective (σ : Fin (n + 1) → Bool) : Function.Injective (signedPole σ) := by
  intro i j h
  by_contra hij
  have hh := inner_signedPole σ i j
  rw [h] at hh
  simp [hij] at hh

def vertices (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool) :
    Finset (GeodesicSphere n) := by
  classical
  exact I.image (signedPole σ)

theorem weighted_inner (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool)
    (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    inner ℝ (∑ i ∈ I, w i • (signedPole σ i).val) (coordinatePole n j).val =
      if j ∈ I then w j * sign (σ j) else 0 := by
  simp only [sum_inner, real_inner_smul_left, inner_signedPole_coordinate]
  simp [mul_ite, Finset.sum_ite_eq']

theorem weighted_signed_inner (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool)
    (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    inner ℝ (∑ i ∈ I, w i • (signedPole σ i).val) (signedPole σ j).val =
      if j ∈ I then w j else 0 := by
  simp only [sum_inner, real_inner_smul_left, inner_signedPole]
  simp [mul_ite, Finset.sum_ite_eq']

theorem hemispherical (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool) :
    InOpenHemisphere (vertices I σ) := by
  classical
  by_cases hI : I.Nonempty
  · let u : EuclideanSpace ℝ (Fin (n + 1)) := ∑ i ∈ I, (signedPole σ i).val
    have huinner (j : Fin (n + 1)) (hj : j ∈ I) :
        inner ℝ u (signedPole σ j).val = 1 := by
      simpa only [one_smul, u, ite_eq_left hj] using
        weighted_signed_inner I σ (fun _ => 1) j
    have hu : u ≠ 0 := by
      intro hzero
      obtain ⟨j, hj⟩ := hI
      have h := huinner j hj
      rw [hzero, inner_zero_left] at h
      norm_num at h
    refine ⟨normalizeVector u hu, ?_⟩
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    rw [normalizeVector_val, NormedSpace.normalize, real_inner_smul_left, huinner j hj,
      mul_one]
    exact inv_pos.mpr (norm_pos_iff.mpr hu)
  · refine ⟨northPole n, ?_⟩
    simp only [Finset.not_nonempty_iff_eq_empty] at hI
    simp [vertices, hI]

theorem mem_cell_iff (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool)
    (x : GeodesicSphere n) :
    x ∈ sphericalCell (vertices I σ) ↔
      (∀ i ∉ I, x.val i = 0) ∧ ∀ i ∈ I, 0 ≤ sign (σ i) * x.val i := by
  classical
  constructor
  · rintro ⟨w, hw, a, ha, hrep⟩
    have hrep' : ∑ i ∈ I, w (signedPole σ i) • (signedPole σ i).val = a • x.val := by
      simpa only [vertices, Finset.sum_image, (signedPole_injective σ).injOn] using hrep
    have hcoord (j : Fin (n + 1)) :
        (if j ∈ I then w (signedPole σ j) * sign (σ j) else 0) = a * x.val j := by
      have h := congrArg (fun u => inner ℝ u (coordinatePole n j).val) hrep'
      rw [weighted_inner, real_inner_smul_left] at h
      simpa only [coordinatePole_val, EuclideanSpace.inner_single_right, one_mul,
        conj_trivial] using h
    constructor
    · intro i hi
      have h := hcoord i
      rw [ite_eq_right hi] at h
      exact (mul_eq_zero.mp h.symm).resolve_left ha.ne'
    · intro i hi
      have h := hcoord i
      rw [ite_eq_left hi] at h
      have hw' : 0 ≤ w (signedPole σ i) := hw _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have hs := sign_sq (σ i)
      have hh : w (signedPole σ i) = a * (sign (σ i) * x.val i) := by
        calc
          _ = (w (signedPole σ i) * sign (σ i)) * sign (σ i) := by rw [mul_assoc, hs, mul_one]
          _ = _ := by rw [h]; ring
      rw [hh] at hw'
      exact nonneg_of_mul_nonneg_right hw' ha
  · rintro ⟨hzero, hnonneg⟩
    let w : GeodesicSphere n → ℝ := fun v => inner ℝ x.val v.val
    refine ⟨w, ?_, 1, zero_lt_one, ?_⟩
    · intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      change 0 ≤ inner ℝ x.val (signedPole σ i).val
      rw [signedPole_val, inner_smul_right]
      simpa only [coordinatePole_val, EuclideanSpace.inner_single_right, one_mul,
        conj_trivial] using hnonneg i hi
    · rw [one_smul]
      rw [show vertices I σ = I.image (signedPole σ) from rfl,
        Finset.sum_image (fun i _ j _ h => signedPole_injective σ h)]
      apply PiLp.ext
      intro j
      have h := weighted_inner I σ (fun i => w (signedPole σ i)) j
      simp only [coordinatePole_val, EuclideanSpace.inner_single_right, one_mul,
        conj_trivial] at h
      rw [h]
      by_cases hj : j ∈ I
      · rw [ite_eq_left hj]
        dsimp [w]
        rw [signedPole_val, inner_smul_right]
        simp only [coordinatePole_val, EuclideanSpace.inner_single_right, one_mul,
          conj_trivial]
        rw [mul_assoc, mul_comm (x.val j), ← mul_assoc, sign_sq, one_mul]
      · rw [ite_eq_right hj, hzero j hj]

theorem sphere_covered (x : GeodesicSphere n) :
    ∃ σ : Fin (n + 1) → Bool, x ∈ sphericalCell (vertices Finset.univ σ) := by
  classical
  let σ : Fin (n + 1) → Bool := fun i => decide (0 ≤ x.val i)
  refine ⟨σ, (mem_cell_iff Finset.univ σ x).mpr ⟨by simp, ?_⟩⟩
  intro i _
  by_cases hi : 0 ≤ x.val i
  · simp [σ, sign, hi]
  · have hn : x.val i ≤ 0 := le_of_not_ge hi
    simpa [σ, sign, hi] using neg_nonneg.mpr hn

theorem cell_closed (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool) :
    IsClosed (sphericalCell (vertices I σ)) := isClosed_sphericalCell _ (hemispherical I σ)

/-- Common coordinate axes with the same sign. Oppositely signed axes must
have zero coordinate throughout the intersection. -/
def commonIndices (I J : Finset (Fin (n + 1)))
    (σ τ : Fin (n + 1) → Bool) : Finset (Fin (n + 1)) :=
  I.filter fun i => i ∈ J ∧ σ i = τ i

theorem cell_intersection (I J : Finset (Fin (n + 1)))
    (σ τ : Fin (n + 1) → Bool) :
    sphericalCell (vertices I σ) ∩ sphericalCell (vertices J τ) =
      sphericalCell (vertices (commonIndices I J σ τ) σ) := by
  classical
  let K := commonIndices I J σ τ
  have hKI : K ⊆ I := Finset.filter_subset _ _
  have hKJ : K ⊆ J := fun i hi => (Finset.mem_filter.mp hi).2.1
  have hsign (i : Fin (n + 1)) (hi : i ∈ K) : σ i = τ i :=
    (Finset.mem_filter.mp hi).2.2
  ext x
  simp only [Set.mem_inter_iff, mem_cell_iff]
  constructor
  · rintro ⟨⟨hxi, hxs⟩, ⟨hyj, hys⟩⟩
    constructor
    · intro i hi
      by_cases hI : i ∈ I
      · by_cases hJ : i ∈ J
        · have hne : σ i ≠ τ i := fun h => hi (Finset.mem_filter.mpr ⟨hI, hJ, h⟩)
          have h₁ := hxs i hI
          have h₂ := hys i hJ
          cases hs : σ i <;> cases ht : τ i <;> simp_all [sign] <;> linarith
        · exact hyj i hJ
      · exact hxi i hI
    · intro i hi
      exact hxs i (hKI hi)
  · rintro ⟨hzero, hnonneg⟩
    constructor
    · constructor
      · intro i hi
        exact hzero i (fun h => hi (hKI h))
      · intro i _
        by_cases hi : i ∈ K
        · exact hnonneg i hi
        · rw [hzero i hi, mul_zero]
    · constructor
      · intro i hi
        exact hzero i (fun h => hi (hKJ h))
      · intro i _
        by_cases hi : i ∈ K
        · rw [← hsign i hi]
          exact hnonneg i hi
        · rw [hzero i hi, mul_zero]

/-- The displayed common cell is literally the hull of the common vertices. -/
theorem vertices_intersection (I J : Finset (Fin (n + 1)))
    (σ τ : Fin (n + 1) → Bool) :
    vertices I σ ∩ vertices J τ = vertices (commonIndices I J σ τ) σ := by
  classical
  ext v
  simp only [Finset.mem_inter, vertices, Finset.mem_image, commonIndices, Finset.mem_filter]
  constructor
  · rintro ⟨⟨i, hi, hvi⟩, ⟨j, hj, hvj⟩⟩
    have hp : signedPole σ i = signedPole τ j := hvi.trans hvj.symm
    have hij : i = j := by
      by_contra hij
      have h := congrArg (fun x => inner ℝ x.val (coordinatePole n i).val) hp
      rw [inner_signedPole_coordinate, inner_signedPole_coordinate] at h
      simp [Ne.symm hij] at h
    subst j
    have hsign : σ i = τ i := by
      have h := congrArg (fun x => inner ℝ x.val (coordinatePole n i).val) hp
      rw [inner_signedPole_coordinate, inner_signedPole_coordinate] at h
      cases hs : σ i <;> cases ht : τ i <;> simp_all [sign] <;> norm_num at h
    exact ⟨i, ⟨hi, hj, hsign⟩, hvi⟩
  · rintro ⟨i, ⟨hi, hj, hsign⟩, hvi⟩
    refine ⟨⟨i, hi, hvi⟩, ⟨i, hj, ?_⟩⟩
    simpa only [signedPole, hsign] using hvi

theorem cell_intersection_vertices (I J : Finset (Fin (n + 1)))
    (σ τ : Fin (n + 1) → Bool) :
    sphericalCell (vertices I σ) ∩ sphericalCell (vertices J τ) =
      sphericalCell (vertices I σ ∩ vertices J τ) := by
  rw [cell_intersection, vertices_intersection]

theorem vertices_orthonormal (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool) :
    Orthonormal ℝ (fun v : vertices I σ => v.val.val) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro v w
  obtain ⟨i, hi, hvi⟩ := Finset.mem_image.mp v.property
  obtain ⟨j, hj, hwj⟩ := Finset.mem_image.mp w.property
  have hEq : i = j ↔ v = w := by
    constructor
    · intro h
      apply Subtype.ext
      exact hvi.symm.trans ((congrArg (signedPole σ) h).trans hwj)
    · intro h
      apply signedPole_injective σ
      exact hvi.trans ((congrArg Subtype.val h).trans hwj.symm)
  rw [← hvi, ← hwj, inner_signedPole]
  simp only [hEq]

theorem vertices_independent (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool) :
    LinearIndependent ℝ (fun v : vertices I σ => v.val.val) :=
  (vertices_orthonormal I σ).linearIndependent

theorem vertices_card (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool) :
    (vertices I σ).card = I.card := Finset.card_image_of_injective _ (signedPole_injective σ)

/-- Every vertex subface is another actual signed-coordinate cell. -/
theorem subface_coordinates (I : Finset (Fin (n + 1))) (σ : Fin (n + 1) → Bool)
    (W : Finset (GeodesicSphere n)) (hW : W ⊆ vertices I σ) :
    ∃ J : Finset (Fin (n + 1)), J ⊆ I ∧ W = vertices J σ := by
  classical
  let J := I.filter fun i => signedPole σ i ∈ W
  refine ⟨J, Finset.filter_subset _ _, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hW hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩, rfl⟩
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2

def baseAxes : Finset (Fin 4) := {0, 1, 2}

def baseSign (σ : Fin 3 → Bool) : Fin 4 → Bool := Fin.snoc σ true

def baseVertices (σ : Fin 3 → Bool) : Finset (GeodesicSphere 3) :=
  vertices baseAxes (baseSign σ)

def baseCell (σ : Fin 3 → Bool) : Set (GeodesicSphere 3) := sphericalCell (baseVertices σ)

theorem baseCell_hemispherical (σ : Fin 3 → Bool) : InOpenHemisphere (baseVertices σ) :=
  hemispherical baseAxes (baseSign σ)

theorem baseVertices_card (σ : Fin 3 → Bool) : (baseVertices σ).card = 3 := by
  rw [baseVertices, vertices_card]
  norm_num [baseAxes]

theorem baseVertices_independent (σ : Fin 3 → Bool) :
    LinearIndependent ℝ (fun v : baseVertices σ => v.val.val) :=
  vertices_independent baseAxes (baseSign σ)

lemma sign_of_coordinate_nonneg (r : ℝ) : 0 ≤ sign (decide (0 ≤ r)) * r := by
  by_cases hr : 0 ≤ r
  · simp [sign, hr]
  · have h : r ≤ 0 := le_of_not_ge hr
    simpa [sign, hr] using neg_nonneg.mpr h

theorem base_covered_of_last_zero {x : GeodesicSphere 3} (hx : x.val 3 = 0) :
    ∃ σ : Fin 3 → Bool, x ∈ baseCell σ := by
  classical
  let σ : Fin 3 → Bool := fun i => decide (0 ≤ x.val i.castSucc)
  refine ⟨σ, (mem_cell_iff baseAxes (baseSign σ) x).mpr ⟨?_, ?_⟩⟩
  · intro i hi
    fin_cases i <;> simp_all [baseAxes]
  · intro i hi
    fin_cases i
    · change 0 ≤ sign (decide (0 ≤ x.val 0)) * x.val 0
      exact sign_of_coordinate_nonneg _
    · change 0 ≤ sign (decide (0 ≤ x.val 1)) * x.val 1
      exact sign_of_coordinate_nonneg _
    · change 0 ≤ sign (decide (0 ≤ x.val 2)) * x.val 2
      exact sign_of_coordinate_nonneg _
    · norm_num [baseAxes] at hi

theorem last_zero_of_mem_baseCell {σ : Fin 3 → Bool} {x : GeodesicSphere 3}
    (hx : x ∈ baseCell σ) : x.val 3 = 0 :=
  ((mem_cell_iff baseAxes (baseSign σ) x).mp hx).1 3 (by norm_num [baseAxes])

/-- Exactly eight genuine spherical triangles cover the equatorial sphere.
Their cells meet in common signed-coordinate faces. -/
theorem equatorial_cover :
    {x : GeodesicSphere 3 | x.val 3 = 0} = ⋃ σ : Fin 3 → Bool, baseCell σ := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, hσ⟩ := base_covered_of_last_zero hx
    exact Set.mem_iUnion.mpr ⟨σ, hσ⟩
  · intro hx
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hx
    exact last_zero_of_mem_baseCell hσ

theorem number_base_cells : Fintype.card (Fin 3 → Bool) = 8 := by decide

theorem baseCell_closed (σ : Fin 3 → Bool) : IsClosed (baseCell σ) :=
  cell_closed baseAxes (baseSign σ)

end BrehmApprox.CoordinateSphericalCells
