module

public import BrehmApprox.Core
public import BrehmApprox.HyperbolicModel

/-!
# Finite determination on genuine hyperbolic polyhedra

The positive Lorentz hull of finitely many future unit vectors is a hyperbolic
polyhedral cell.  On every cell a piecewise isometry agrees with an actual
isometry equivalence of the hyperbolic metric space.  The rigidity proof uses
positive Lorentz barycentric coordinates and the formula for `cosh (dist x y)`.

No extension or approximation property is assumed in this file.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace BrehmApprox

variable {n : ℕ}

namespace HyperbolicSpace

/-- The represented future unit Lorentz vector. -/
def lift (x : HyperbolicSpace n) : ℝ × EuclideanSpace ℝ (Fin n) :=
  (Hyperboloid.height x.point, x.point)

@[ext] lemma ext {x y : HyperbolicSpace n} (h : x.point = y.point) : x = y := by
  cases x
  cases y
  congr

lemma cosh_dist (x y : HyperbolicSpace n) :
    Real.cosh (dist x y) = Hyperboloid.coshDist x.point y.point :=
  Hyperboloid.cosh_distance x.point y.point

end HyperbolicSpace

/-- Positive Lorentz hull of a finite set of future unit vectors, intersected
with the future unit hyperboloid.  The positive scale excludes the zero vector. -/
def hyperbolicCell (V : Finset (HyperbolicSpace n)) : Set (HyperbolicSpace n) :=
  {x | ∃ w : HyperbolicSpace n → ℝ, (∀ v ∈ V, 0 ≤ w v) ∧
    ∃ a : ℝ, 0 < a ∧
      ∑ v ∈ V, w v • HyperbolicSpace.lift v = a • HyperbolicSpace.lift x}

lemma mem_hyperbolicCell_of_mem {V : Finset (HyperbolicSpace n)}
    {v : HyperbolicSpace n} (hv : v ∈ V) : v ∈ hyperbolicCell V := by
  classical
  refine ⟨fun u => if u = v then 1 else 0, ?_, 1, zero_lt_one, ?_⟩
  · intro u _
    dsimp only
    split_ifs <;> norm_num
  · simp [ite_smul, hv]

lemma hyperbolic_weighted_cosh {V : Finset (HyperbolicSpace n)}
    {w : HyperbolicSpace n → ℝ} {a : ℝ} {x : HyperbolicSpace n}
    (hrep : ∑ v ∈ V, w v • HyperbolicSpace.lift v = a • HyperbolicSpace.lift x)
    (y : HyperbolicSpace n) :
    ∑ v ∈ V, w v * Hyperboloid.coshDist y.point v.point =
      a * Hyperboloid.coshDist y.point x.point := by
  have ht := congrArg (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))) hrep
  have hp := congrArg (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) hrep
  simp only [map_sum, map_smul, LinearMap.fst_apply, HyperbolicSpace.lift,
    smul_eq_mul] at ht
  simp only [map_sum, map_smul, LinearMap.snd_apply, HyperbolicSpace.lift] at hp
  calc
    _ = Hyperboloid.height y.point * (∑ v ∈ V, w v * Hyperboloid.height v.point) -
        ⟪y.point, ∑ v ∈ V, w v • v.point⟫_ℝ := by
      simp only [Hyperboloid.coshDist, mul_sub, Finset.sum_sub_distrib,
        Finset.mul_sum, inner_sum, real_inner_smul_right]
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = a * Hyperboloid.coshDist y.point x.point := by
      rw [ht, hp, real_inner_smul_right]
      unfold Hyperboloid.coshDist
      ring

/-- A short self-map of hyperbolic space fixing the vertices fixes their whole
geodesic polyhedral cell. -/
lemma short_eq_on_hyperbolicCell_of_fixed {f : HyperbolicSpace n → HyperbolicSpace n}
    (hf : Short f) (V : Finset (HyperbolicSpace n))
    (hV : ∀ v ∈ V, f v = v) : ∀ x ∈ hyperbolicCell V, f x = x := by
  classical
  intro x hx
  obtain ⟨w, hw, a, ha, hrep⟩ := hx
  have hc (v : HyperbolicSpace n) (hv : v ∈ V) :
      Hyperboloid.coshDist (f x).point v.point ≤ Hyperboloid.coshDist x.point v.point := by
    have hd : dist (f x) v ≤ dist x v := by simpa only [hV v hv] using hf x v
    have hh : |dist (f x) v| ≤ |dist x v| := by
      simpa only [abs_of_nonneg dist_nonneg] using hd
    have hcosh := Real.cosh_le_cosh.mpr hh
    simpa only [HyperbolicSpace.cosh_dist] using hcosh
  have hs := Finset.sum_le_sum (fun v hv =>
    mul_le_mul_of_nonneg_left (hc v hv) (hw v hv))
  rw [hyperbolic_weighted_cosh hrep (f x), hyperbolic_weighted_cosh hrep x,
    Hyperboloid.coshDist_self, mul_one] at hs
  have heq : Hyperboloid.coshDist (f x).point x.point = 1 := by
    have hge := Hyperboloid.one_le_coshDist (f x).point x.point
    nlinarith
  apply HyperbolicSpace.ext
  exact Hyperboloid.eq_of_coshDist_eq_one heq

/-- A finite hyperbolic piecewise isometry on a set.  Ambient motions are
actual isometry equivalences for the hyperbolic metric, not Euclidean maps
on the spatial coordinates. -/
def HyperbolicPLOn (A : Set (HyperbolicSpace n))
    (f : HyperbolicSpace n → HyperbolicSpace n) : Prop :=
  ∃ C : Finset (Finset (HyperbolicSpace n)),
    A = ⋃ V ∈ C, hyperbolicCell V ∧
    ∀ V ∈ C, ∃ r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n,
      ∀ x ∈ hyperbolicCell V, f x = r x

/-- Finite isometric subdivisions on every compact hyperbolic polytope. -/
def LocallyHyperbolicPL (f : HyperbolicSpace n → HyperbolicSpace n) : Prop :=
  ∀ V : Finset (HyperbolicSpace n), HyperbolicPLOn (hyperbolicCell V) f

lemma determinedOn_hyperbolicPL {A : Set (HyperbolicSpace n)}
    {g : HyperbolicSpace n → HyperbolicSpace n}
    (hg : HyperbolicPLOn A g) : DeterminedOn A g := by
  classical
  obtain ⟨C, hA, hg⟩ := hg
  let V : Finset (HyperbolicSpace n) := C.biUnion id
  have hVC (D : Finset (HyperbolicSpace n)) (hD : D ∈ C) :
      (D : Set (HyperbolicSpace n)) ⊆ (V : Set (HyperbolicSpace n)) := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨D, hD, hv⟩
  refine ⟨V, ?_, ?_⟩
  · intro v hv
    obtain ⟨D, hD, hvD⟩ := Finset.mem_biUnion.mp hv
    rw [hA]
    exact Set.mem_iUnion.mpr ⟨D, Set.mem_iUnion.mpr ⟨hD,
      mem_hyperbolicCell_of_mem hvD⟩⟩
  · intro h hh hV x hx
    rw [hA] at hx
    obtain ⟨D, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hD, hxD⟩ := Set.mem_iUnion.mp hx
    obtain ⟨e, he⟩ := hg D hD
    let k : HyperbolicSpace n → HyperbolicSpace n := fun y => e.symm (h y)
    have hk : Short k := by
      intro y z
      simpa only [k, e.symm.dist_eq] using hh y z
    have hfix : ∀ v ∈ D, k v = v := by
      intro v hv
      change e.symm (h v) = v
      rw [hV v (hVC D hD hv), he v (mem_hyperbolicCell_of_mem hv)]
      exact e.symm_apply_apply v
    have hxfix := short_eq_on_hyperbolicCell_of_fixed hk D hfix x hxD
    calc
      h x = e (e.symm (h x)) := (e.apply_symm_apply (h x)).symm
      _ = e x := congrArg e hxfix
      _ = g x := (he x hxD).symm

lemma determinedOn_hyperbolicCell {g : HyperbolicSpace n → HyperbolicSpace n}
    (hg : LocallyHyperbolicPL g) (V : Finset (HyperbolicSpace n)) :
    DeterminedOn (hyperbolicCell V) g :=
  determinedOn_hyperbolicPL (hg V)

end BrehmApprox
