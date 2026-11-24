module

public import BrehmApprox.AffineArrangement
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Int.Interval

/-!
# A locally finite polyhedral tiling by integer cubes

The closed unit cubes cover a finite Cartesian power of the real line, are
finite convex hulls, and meet along extreme subsets. These elementary facts
allow a finite affine arrangement to be triangulated globally.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace BrehmApprox

variable {ι : Type*} [Fintype ι]

def integerCube (k : ι → ℤ) : Set (ι → ℝ) :=
  {x | ∀ i, (k i : ℝ) ≤ x i ∧ x i ≤ k i + 1}

def integerCubeVertices (k : ι → ℤ) : Finset (ι → ℝ) := by
  classical
  exact Fintype.piFinset fun i => {(k i : ℝ), (k i : ℝ) + 1}

theorem integerCube_eq_convexHull (k : ι → ℤ) :
    integerCube k = convexHull ℝ (integerCubeVertices k : Set (ι → ℝ)) := by
  classical
  unfold integerCubeVertices
  rw [Fintype.coe_piFinset, convexHull_pi]
  have h (i : ι) : convexHull ℝ ({(k i : ℝ), (k i : ℝ) + 1} : Set ℝ) =
      Set.Icc (k i : ℝ) ((k i : ℝ) + 1) := by
    rw [convexHull_pair, segment_eq_Icc (by linarith : (k i : ℝ) ≤ k i + 1)]
  simp only [Finset.coe_insert, Finset.coe_singleton, h]
  ext x
  simp [integerCube, Pi.le_def, forall_and]

theorem integerCube_compact (k : ι → ℤ) : IsCompact (integerCube k) := by
  rw [integerCube_eq_convexHull]
  exact (integerCubeVertices k).finite_toSet.isCompact_convexHull ℝ

theorem integerCube_convex (k : ι → ℤ) : Convex ℝ (integerCube k) := by
  rw [integerCube_eq_convexHull]
  exact convex_convexHull ℝ _

theorem integerCube_cover (x : ι → ℝ) : ∃ k, x ∈ integerCube k := by
  refine ⟨fun i => ⌊x i⌋, fun i => ⟨Int.floor_le (x i), ?_⟩⟩
  exact (Int.lt_floor_add_one (x i)).le

theorem locallyFinite_integerIntervals :
    LocallyFinite (fun k : ℤ => Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
  intro x
  refine ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (Set.finite_Icc (⌊x⌋ - 2) (⌊x⌋ + 2)).subset
  intro k hk
  obtain ⟨y, ⟨hyk0, hyk1⟩, ⟨hyx0, hyx1⟩⟩ := hk
  have hlo : ((⌊x⌋ - 2 : ℤ) : ℝ) ≤ k := by
    push_cast
    linarith [Int.floor_le x]
  have hhi : (k : ℝ) ≤ ((⌊x⌋ + 2 : ℤ) : ℝ) := by
    push_cast
    linarith [Int.lt_floor_add_one x]
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem locallyFinite_integerCubes : LocallyFinite (integerCube (ι := ι)) := by
  intro x
  choose U hU hfin using fun i => locallyFinite_integerIntervals (x i)
  refine ⟨Set.univ.pi U, set_pi_mem_nhds (Set.finite_univ) (fun i _ => hU i), ?_⟩
  apply (Set.Finite.pi' hfin).subset
  intro k hk i
  obtain ⟨y, hyk, hyU⟩ := hk
  exact ⟨y i, hyk i, hyU i (Set.mem_univ i)⟩

theorem isExtreme_integerIntervals_inter (k l : ℤ) :
    IsExtreme ℝ (Set.Icc (k : ℝ) ((k : ℝ) + 1))
      (Set.Icc (k : ℝ) ((k : ℝ) + 1) ∩ Set.Icc (l : ℝ) ((l : ℝ) + 1)) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, d, ha, hd, had, rfl⟩ := hseg
  refine ⟨hx, ?_⟩
  rcases lt_trichotomy k l with hkl | rfl | hlk
  · have hstep : (k : ℝ) + 1 ≤ l := by exact_mod_cast (Int.add_one_le_iff.mpr hkl)
    have heq : (l : ℝ) = k + 1 := by linarith [hz.1.2, hz.2.1]
    have hxlo : (k : ℝ) + 1 ≤ x :=
      AffineSign.weak_at_left_of_combo .negative .positive hx.2 hy.2
        (hstep.trans hz.2.1) ha hd had
    rw [heq]
    constructor <;> linarith [hx.1, hx.2]
  · exact hx
  · have hstep : (l : ℝ) + 1 ≤ k := by exact_mod_cast (Int.add_one_le_iff.mpr hlk)
    have heq : (k : ℝ) = l + 1 := by linarith [hz.1.1, hz.2.2]
    have hxhi : x ≤ (k : ℝ) :=
      AffineSign.weak_at_left_of_combo .positive .negative hx.1 hy.1
        (hz.2.2.trans hstep) ha hd had
    constructor <;> linarith [hx.1, hx.2]

theorem isExtreme_integerCubes_inter (k l : ι → ℤ) :
    IsExtreme ℝ (integerCube k) (integerCube k ∩ integerCube l) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, fun i => ?_⟩
  apply ((isExtreme_integerIntervals_inter (k i) (l i)).left_mem_of_mem_openSegment
    (hx i) (hy i) ⟨hz.1 i, hz.2 i⟩ ?_).2
  obtain ⟨a, d, ha, hd, had, rfl⟩ := hseg
  exact ⟨a, d, ha, hd, had, rfl⟩

end BrehmApprox
