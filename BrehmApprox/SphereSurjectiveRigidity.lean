module

public import BrehmApprox.Core
public import BrehmApprox.SphereModel
public import Mathlib.Tactic.Linarith

/-!
# Rigidity of onto short maps of the round sphere

This is one of the exact obstructions in the corrected spherical
counterexample.  The assertion concerns the angular metric and uses no
piecewise linearity, degree theory, or Brehm axiom.
-/

@[expose] public section

open InnerProductGeometry

namespace GeodesicSphere

variable {n : ℕ}

@[simp] theorem antipode_antipode (x : GeodesicSphere n) : antipode (antipode x) = x := by
  ext
  simp [antipode]

theorem dist_to_antipode (x y : GeodesicSphere n) :
    dist x (antipode y) = Real.pi - dist x y :=
  angle_neg_right x.val y.val

theorem eq_antipode_of_dist_pi {x y : GeodesicSphere n} (h : dist x y = Real.pi) :
    y = antipode x := by
  apply eq_of_dist_eq_zero
  rw [dist_to_antipode, dist_comm, h]
  ring

/-- An onto short map must send each antipodal pair to an antipodal pair. -/
theorem antipode_preserved_of_short_surjective {g : GeodesicSphere n → GeodesicSphere n}
    (hg : BrehmApprox.Short g) (hs : Function.Surjective g) (x : GeodesicSphere n) :
    g (antipode x) = antipode (g x) := by
  obtain ⟨z, hz⟩ := hs (antipode (g x))
  have hdist : dist x z = Real.pi := by
    apply le_antisymm (dist_le_pi x z)
    have hh := hg x z
    change dist (g x) (g z) ≤ dist x z at hh
    rwa [hz, dist_antipode] at hh
  have heq : z = antipode x := eq_antipode_of_dist_pi hdist
  simpa [heq] using hz

/-- Every surjective nonexpanding self-map of the round sphere is an isometry. -/
theorem isometry_of_short_surjective {g : GeodesicSphere n → GeodesicSphere n}
    (hg : BrehmApprox.Short g) (hs : Function.Surjective g) : Isometry g := by
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm (hg x y)
  have h := hg x (antipode y)
  rw [antipode_preserved_of_short_surjective hg hs y,
    dist_to_antipode, dist_to_antipode] at h
  linarith

/-- The same statement in mathlib's Lipschitz notation. -/
theorem isometry_of_lipschitz_surjective {g : GeodesicSphere n → GeodesicSphere n}
    (hg : LipschitzWith 1 g) (hs : Function.Surjective g) : Isometry g := by
  apply isometry_of_short_surjective ?_ hs
  intro x y
  simpa using hg.dist_le_mul x y

end GeodesicSphere
