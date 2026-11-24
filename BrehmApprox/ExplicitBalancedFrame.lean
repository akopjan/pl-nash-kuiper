module

public import BrehmApprox.SphereShortRigidity
public import BrehmApprox.SphereCounterexample
public import Mathlib.Tactic.FinCases

/-!
# Four explicit balanced equatorial anchors

The vertices are the positive and negative coordinate vectors in the equator
of the actual round two-sphere. Their balance, exact linear span and the
two-pole intersection of their closed hemispheres are proved directly.
-/

@[expose] public section
noncomputable section

namespace ExplicitBalancedFrame

open GeodesicSphere
open scoped BigOperators

def pole : GeodesicSphere 2 := coordinatePole 2 0
def first : GeodesicSphere 2 := coordinatePole 2 1
def second : GeodesicSphere 2 := coordinatePole 2 2

def vertices : Finset (GeodesicSphere 2) := by
  classical
  exact {first, antipode first, second, antipode second}

lemma first_ne_neg_first : first ≠ antipode first := by
  intro h
  have hh := congrArg (fun x : GeodesicSphere 2 => x.val 1) h
  norm_num [first, coordinatePole_val, antipode, PiLp.single_apply] at hh

lemma first_ne_second : first ≠ second := by
  intro h
  have hh := congrArg (fun x : GeodesicSphere 2 => x.val 1) h
  norm_num [first, second, coordinatePole_val, PiLp.single_apply] at hh

lemma first_ne_neg_second : first ≠ antipode second := by
  intro h
  have hh := congrArg (fun x : GeodesicSphere 2 => x.val 1) h
  norm_num [first, second, coordinatePole_val, antipode, PiLp.single_apply] at hh

lemma neg_first_ne_second : antipode first ≠ second := by
  intro h
  have hh := congrArg (fun x : GeodesicSphere 2 => x.val 1) h
  norm_num [first, second, coordinatePole_val, antipode, PiLp.single_apply] at hh

lemma neg_first_ne_neg_second : antipode first ≠ antipode second := by
  intro h
  have hh := congrArg (fun x : GeodesicSphere 2 => x.val 1) h
  norm_num [first, second, coordinatePole_val, antipode, PiLp.single_apply] at hh

lemma second_ne_neg_second : second ≠ antipode second := by
  intro h
  have hh := congrArg (fun x : GeodesicSphere 2 => x.val 2) h
  norm_num [second, coordinatePole_val, antipode, PiLp.single_apply] at hh

theorem balance : ∑ v ∈ vertices, v.val = 0 := by
  classical
  simp only [vertices, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    first_ne_neg_first, first_ne_second, first_ne_neg_second,
    neg_first_ne_second, neg_first_ne_neg_second, second_ne_neg_second,
    or_self, not_false_eq_true, Finset.sum_singleton]
  change first.val + (-first.val + (second.val + -second.val)) = 0
  abel

theorem orthogonal {v : GeodesicSphere 2} (hv : v ∈ vertices) :
    inner ℝ v.val pole.val = 0 := by
  classical
  simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;>
    simp [first, second, pole, coordinatePole_val, antipode,
      inner_neg_left, EuclideanSpace.inner_single_left]

theorem span :
    Submodule.span ℝ (GeodesicSphere.val '' (vertices : Set (GeodesicSphere 2))) =
      (Submodule.span ℝ ({pole.val} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨a, ha, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (orthogonal ha)
  · intro x hx
    have h0 : x 0 = 0 := by
      have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hx
      simpa [pole, coordinatePole_val, EuclideanSpace.inner_single_left] using h
    have heq : x = (x 1) • first.val + (x 2) • second.val := by
      ext i
      fin_cases i <;> simp [first, second, coordinatePole_val, h0]
    rw [heq]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨first, by simp [vertices], rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨second, by simp [vertices], rfl⟩

theorem cap_intersection (x : GeodesicSphere 2)
    (hx : ∀ v ∈ vertices, dist x v ≤ Real.pi / 2) : x = pole ∨ x = antipode pole := by
  have hx' : x ∈ ({pole, antipode pole} : Set (GeodesicSphere 2)) := by
    rw [← balanced_caps_eq_poles vertices pole balance span]
    exact hx
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx'

end ExplicitBalancedFrame
