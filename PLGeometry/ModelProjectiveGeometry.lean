module

public import PLGeometry.ModelBarycentricNaturality
public import BrehmApprox.PositiveBarycentricGeometry

/-! # Convex hulls and independence in canonical model coordinates -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.ModelBarycentric

variable {ι J : Type*} [Fintype ι] [Fintype J] {κ : Geometry} {n : ℕ}

local instance modelProjectiveDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance modelProjectiveEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance modelProjectiveSDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance modelProjectiveHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _

theorem euclidean_homogeneous_representation (v : ι → Model .euclidean n)
    (w : Weights ι) (x : Model .euclidean n) (h : Represents .euclidean n v w.val x) :
    (Fintype.linearCombination ℝ (fun i => ((1 : ℝ), v i))) w.val = ((1 : ℝ), x) := by
  apply Prod.ext
  · change (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))) (∑ i, w.val i • ((1 : ℝ), v i)) = 1
    simpa only [map_sum, map_smul, LinearMap.fst_apply, smul_eq_mul, mul_one] using w.property.2
  · change (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) (∑ i, w.val i • ((1 : ℝ), v i)) = x
    simpa only [Represents, map_sum, map_smul, LinearMap.snd_apply] using h

theorem represents_hull_iff (v : ι → Model κ n) (hv : Independent κ n v)
    (u : J → Model κ n) (hu : Function.Injective u)
    (w : J → Weights ι) (hw : ∀ j, Represents κ n v (w j).val (u j))
    (a : Weights ι) (x : Model κ n) (ha : Represents κ n v a.val x) :
    x ∈ hull κ n (Finset.univ.image u) ↔
      a.val ∈ convexHull ℝ (Set.range (fun j => (w j).val)) := by
  cases κ with
  | euclidean =>
    let L := Fintype.linearCombination ℝ (fun i => ((1 : ℝ), v i))
    have hL : Function.Injective L :=
      ((affineIndependent_iff_homogeneous_linearIndependent v).mp hv).fintypeLinearCombination_injective
    have hrep (j : J) : L (w j).val = (1 : ℝ) • ((1 : ℝ), u j) := by
      rw [one_smul]
      exact euclidean_homogeneous_representation v (w j) (u j) (hw j)
    have hax : L a.val = (1 : ℝ) • ((1 : ℝ), x) := by
      rw [one_smul]
      exact euclidean_homogeneous_representation v a x ha
    have hp := PositiveBarycentric.convexHull_iff_positive_lifts L hL w
      (fun j => ((1 : ℝ), u j)) (fun _ => 1) (fun _ => zero_lt_one) hrep
      a ((1 : ℝ), x) 1 zero_lt_one hax
    have hx := PositiveBarycentric.homogeneous_mem_convexHull_iff u x
    have hset : (Finset.univ.image u : Set (Model .euclidean n)) = Set.range u := by ext y; simp
    change x ∈ convexHull ℝ (Finset.univ.image u : Set _) ↔ _
    rw [hset]
    exact hx.trans hp.symm
  | spherical =>
    let L := Fintype.linearCombination ℝ (fun i => (v i).val)
    have hL : Function.Injective L := hv.fintypeLinearCombination_injective
    choose c hc hcvec using hw
    obtain ⟨d, hd, hdvec⟩ := ha
    have hp := PositiveBarycentric.convexHull_iff_positive_lifts L hL w
      (fun j => (u j).val) c hc hcvec a x.val d hd hdvec
    have hx := PositiveBarycentric.rayCombination_image_iff u hu GeodesicSphere.val x
    exact hx.trans hp.symm
  | hyperbolic =>
    let L := Fintype.linearCombination ℝ (fun i => HyperbolicSpace.lift (v i))
    have hL : Function.Injective L := hv.fintypeLinearCombination_injective
    choose c hc hcvec using hw
    obtain ⟨d, hd, hdvec⟩ := ha
    have hp := PositiveBarycentric.convexHull_iff_positive_lifts L hL w
      (fun j => HyperbolicSpace.lift (u j)) c hc hcvec a (HyperbolicSpace.lift x) d hd hdvec
    have hx := PositiveBarycentric.rayCombination_image_iff u hu HyperbolicSpace.lift x
    exact hx.trans hp.symm

theorem independent_of_barycentric (v : ι → Model κ n) (hv : Independent κ n v)
    (u : J → Model κ n) (w : J → Weights ι)
    (hw : ∀ j, Represents κ n v (w j).val (u j))
    (hi : AffineIndependent ℝ (fun j => (w j).val)) : Independent κ n u := by
  have hm (j : J) : PositiveBarycentric.mass (w j).val = 1 := (w j).property.2
  cases κ with
  | euclidean =>
    let L := Fintype.linearCombination ℝ (fun i => ((1 : ℝ), v i))
    have hL : Function.Injective L :=
      ((affineIndependent_iff_homogeneous_linearIndependent v).mp hv).fintypeLinearCombination_injective
    apply (affineIndependent_iff_homogeneous_linearIndependent u).mpr
    exact PositiveBarycentric.lift_independent L hL (fun j => (w j).val) hm hi
      (fun j => ((1 : ℝ), u j)) (fun _ => 1) (fun _ => one_ne_zero) (fun j => by
        rw [one_smul]
        exact euclidean_homogeneous_representation v (w j) (u j) (hw j))
  | spherical =>
    let L := Fintype.linearCombination ℝ (fun i => (v i).val)
    have hL : Function.Injective L := hv.fintypeLinearCombination_injective
    choose c hc hcvec using hw
    exact PositiveBarycentric.lift_independent L hL (fun j => (w j).val) hm hi
      (fun j => (u j).val) c (fun j => (hc j).ne') hcvec
  | hyperbolic =>
    let L := Fintype.linearCombination ℝ (fun i => HyperbolicSpace.lift (v i))
    have hL : Function.Injective L := hv.fintypeLinearCombination_injective
    choose c hc hcvec using hw
    exact PositiveBarycentric.lift_independent L hL (fun j => (w j).val) hm hi
      (fun j => HyperbolicSpace.lift (u j)) c (fun j => (hc j).ne') hcvec

end ArchivePLGeometry.ModelBarycentric
