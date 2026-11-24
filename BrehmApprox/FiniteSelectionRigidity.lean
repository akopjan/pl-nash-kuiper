module

public import BrehmApprox.FiniteContinuousSelection
public import Mathlib.Topology.Connected.Clopen

/-!
# Rigidity of a finite continuous selection

On a connected set, a continuous selection of finitely many candidates is
one fixed candidate, provided equality at a point propagates throughout the
set. This is the topological ingredient in the affine-arrangement proof of
piecewise isometry.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace BrehmApprox

universe u v w

theorem finite_selection_eq_of_eq_propagates
    {X : Type u} {Y : Type v} {ι : Type w}
    [MetricSpace X] [MetricSpace Y] [Finite ι] [PreconnectedSpace X]
    {f : X → Y} {F : ι → X → Y}
    (hf : Continuous f) (hF : ∀ i, Continuous (F i))
    (hsel : ∀ x, ∃ i, f x = F i x)
    (heq : ∀ x i j, F i x = F j x → F i = F j)
    (x₀ : X) : ∃ i, ∀ x, f x = F i x := by
  classical
  obtain ⟨i, hi⟩ := hsel x₀
  let A : Set X := {x | f x = F i x}
  have hclosed : IsClosed A := isClosed_eq hf (hF i)
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hnear := finite_selection_eventually_matches
      (s := Set.univ) (x := x) hf.continuousWithinAt
      (fun j => (hF j).continuousWithinAt)
    simp only [nhdsWithin_univ] at hnear
    filter_upwards [hnear] with y hy
    obtain ⟨j, hj⟩ := hsel y
    have hji : F j = F i := heq x j i ((hy j hj).symm.trans hx)
    change f y = F i y
    rw [hj, hji]
  have hA : A = Set.univ := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ ⟨x₀, hi⟩
  refine ⟨i, fun x => ?_⟩
  have hx : x ∈ A := by rw [hA]; trivial
  exact hx

theorem finite_selection_eqOn_of_eqOn_propagates
    {X : Type u} {Y : Type v} {ι : Type w}
    [MetricSpace X] [MetricSpace Y] [Finite ι]
    {s : Set X} (hs : IsPreconnected s) (hne : s.Nonempty)
    {f : X → Y} {F : ι → X → Y}
    (hf : ContinuousOn f s) (hF : ∀ i, ContinuousOn (F i) s)
    (hsel : ∀ x ∈ s, ∃ i, f x = F i x)
    (heq : ∀ x ∈ s, ∀ i j, F i x = F j x → Set.EqOn (F i) (F j) s) :
    ∃ i, Set.EqOn f (F i) s := by
  letI : PreconnectedSpace s := Subtype.preconnectedSpace hs
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨i, hi⟩ := finite_selection_eq_of_eq_propagates
    (f := fun x : s => f x) (F := fun i (x : s) => F i x)
    hf.restrict (fun i => (hF i).restrict)
    (fun x => hsel x x.property)
    (fun x i j hij => funext (fun y => heq x x.property i j hij y.property))
    (⟨x₀, hx₀⟩ : s)
  exact ⟨i, fun x hx => hi ⟨x, hx⟩⟩

end BrehmApprox
