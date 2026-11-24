module

public import BrehmApprox.Core
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Data.Int.Interval

/-!
# A bounded Euclidean folding

The distance to the integer lattice on each coordinate gives a short folding
of Euclidean space into a bounded cube. On every bounded set it is a selection
of finitely many genuine affine isometries.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

/-- The triangular wave with period one and range `[0, 1/2]`. -/
def triangularWave (x : ℝ) : ℝ := |x - round x|

theorem triangularWave_nonneg (x : ℝ) : 0 ≤ triangularWave x := abs_nonneg _

theorem triangularWave_le_half (x : ℝ) : triangularWave x ≤ 1 / 2 :=
  abs_sub_round x

theorem triangularWave_short : Short triangularWave := by
  intro x y
  rw [Real.dist_eq, Real.dist_eq, abs_sub_le_iff]
  have hxy := (round_le x (round y)).trans (abs_sub_le x y (round y : ℝ))
  have hyx := (round_le y (round x)).trans (abs_sub_le y x (round x : ℝ))
  change |x - round x| - |y - round y| ≤ |x - y| ∧
    |y - round y| - |x - round x| ≤ |x - y|
  rw [abs_sub_comm y x] at hyx
  constructor <;> linarith

/-- Fold each Euclidean coordinate to its distance from the nearest integer. -/
def coordinateFolding {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => triangularWave (x i))

@[simp] theorem coordinateFolding_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    coordinateFolding x i = triangularWave (x i) := rfl

theorem coordinateFolding_short (n : ℕ) :
    Short (coordinateFolding (n := n)) := by
  intro x y
  rw [PiLp.dist_eq_of_L2, PiLp.dist_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ dist_nonneg (triangularWave_short (x i) (y i)) 2

theorem coordinateFolding_bounded {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖coordinateFolding x‖ ≤ Real.sqrt n := by
  rw [PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  calc
    ∑ i : Fin n, ‖coordinateFolding x i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h0 := triangularWave_nonneg (x i)
      have h1 := triangularWave_le_half (x i)
      simp only [coordinateFolding_apply, Real.norm_eq_abs, abs_of_nonneg h0]
      nlinarith
    _ = n := by simp

/-- Independent reflections of the coordinate axes. -/
def coordinateReflection {n : ℕ} (s : Fin n → Bool) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if s i then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)

/-- A lattice translation followed by independent coordinate reflections. -/
def latticeMotion {n : ℕ} (s : Fin n → Bool) (z : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n))
    (-WithLp.toLp 2 (fun i => (z i : ℝ)))).trans
      (coordinateReflection s).toAffineIsometryEquiv

theorem latticeMotion_apply {n : ℕ} (s : Fin n → Bool) (z : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    latticeMotion s z x i = if s i then x i - z i else -(x i - z i) := by
  change (if s i then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)
    (-(z i : ℝ) + x i) = _
  split <;> simp [sub_eq_add_neg, add_comm]

theorem coordinateFolding_eq_latticeMotion {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFolding x =
      latticeMotion (fun i => decide (0 ≤ x i - (round (x i) : ℝ)))
        (fun i => round (x i)) x := by
  classical
  ext i
  rw [coordinateFolding_apply, latticeMotion_apply]
  by_cases h : 0 ≤ x i - (round (x i) : ℝ)
  · simp [triangularWave, h, abs_of_nonneg h]
  · simp [triangularWave, h, abs_of_neg (lt_of_not_ge h)]

/-- On each bounded ball, the folding chooses from a finite list of motions. -/
theorem coordinateFolding_finite_motions (n : ℕ) (R : ℝ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)),
      ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R →
        ∃ r ∈ S, coordinateFolding x = r x := by
  classical
  let Z : Finset ℤ := Finset.Icc ⌊-R - 1⌋ ⌈R + 1⌉
  let I := (Fin n → Bool) × (Fin n → {z : ℤ // z ∈ Z})
  let motion : I → EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun p => latticeMotion p.1 (fun i => (p.2 i).val)
  refine ⟨Finset.univ.image motion, ?_⟩
  intro x hx
  have hz (i : Fin n) : round (x i) ∈ Z := by
    have hi : |x i| ≤ R := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx
    have hlo := (abs_le.mp hi).1
    have hhi := (abs_le.mp hi).2
    have hrlo := sub_half_lt_round (x i)
    have hrhi := round_le_add_half (x i)
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (Int.floor_le (-R - 1)).trans
        (show -R - 1 ≤ (round (x i) : ℝ) by linarith)
    · exact_mod_cast (show (round (x i) : ℝ) ≤ R + 1 by linarith).trans
        (Int.le_ceil (R + 1))
  let p : I := ⟨fun i => decide (0 ≤ x i - (round (x i) : ℝ)),
    fun i => ⟨round (x i), hz i⟩⟩
  exact ⟨motion p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩,
    coordinateFolding_eq_latticeMotion x⟩

end BrehmApprox
