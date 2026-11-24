module

public import BrehmApprox.SphereShortRigidity
public import BrehmApprox.SphereCounterexample
public import BrehmApprox.PiecewiseConsequences
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The metric obstruction in the branched spherical counterexample

The inputs are an actual isometric sphere and an actual nondegenerate
isometric interval inside a metric source. All points of the interval lie
within `pi/2` of balanced equatorial anchors on the sphere. A short map close
to the identity on that sphere is an orthogonal motion there. After removing
this motion, the balanced-cap lemma forces the entire interval to be constant,
contradicting finite polyhedral isometry pieces.

The quotient construction of the three-octant source is not formalized here.
The exact metric configuration it must satisfy is displayed in the theorem.
No assumption says that approximations fail, and no topological degree is used.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BrehmApprox

open GeodesicSphere

variable {n : ℕ} {P : Type*} [MetricSpace P]
variable {Good : (GeodesicSphere n → GeodesicSphere n) → Prop}
variable {M : PolytopeModel (GeodesicSphere n) Good} {q g : P → GeodesicSphere n}

/-- A genuine metric sphere and a genuine interval with the displayed anchor
distance bounds obstruct every short finite piecewise isometry which is less
than `pi/2` from the identity on the sphere. -/
theorem sphere_interval_obstruction
    (e : GeodesicSphere n → P) (he : Isometry e)
    {a b : ℝ} (hab : a < b) (γ : Set.Icc a b → P) (hγ : Isometry γ)
    (V : Finset (GeodesicSphere n)) (p : GeodesicSphere n)
    (hbalance : ∑ v ∈ V, v.val = 0)
    (hspan : Submodule.span ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere n))) =
      (Submodule.span ℝ ({p.val} : Set (EuclideanSpace ℝ (Fin (n + 1)))))ᗮ)
    (hcaps : ∀ t : Set.Icc a b, ∀ v ∈ V, dist (γ t) (e v) ≤ Real.pi / 2)
    (hPL : PolyhedralPiecewiseIsometry M q g) (hg : LipschitzWith 1 g)
    (hclose : ∀ x : GeodesicSphere n, dist (g (e x)) x < Real.pi / 2) : False := by
  have hr : Short (g ∘ e) := by
    intro x y
    simpa only [Function.comp_apply, NNReal.coe_one, one_mul, he.dist_eq] using
      hg.dist_le_mul (e x) (e y)
  obtain ⟨U, hU⟩ := orthogonal_of_short_close_to_id hr hclose
  let R := mapEquiv U
  have hanchor (v : GeodesicSphere n) : R v = g (e v) := by
    simpa only [R, Function.comp_apply] using (congrFun hU v).symm
  let u : Set.Icc a b → GeodesicSphere n := fun t => R.symm (g (γ t))
  have hu : Continuous u := R.symm.continuous.comp (hg.continuous.comp hγ.continuous)
  have hucaps : ∀ t : Set.Icc a b, ∀ v ∈ V, dist (u t) v ≤ Real.pi / 2 := by
    intro t v hv
    calc
      dist (u t) v = dist (R.symm (g (γ t))) (R.symm (R v)) := by simp only [u, R.symm_apply_apply]
      _ = dist (g (γ t)) (R v) := R.symm.dist_eq _ _
      _ = dist (g (γ t)) (g (e v)) := by rw [hanchor]
      _ ≤ dist (γ t) (e v) := by simpa using hg.dist_le_mul (γ t) (e v)
      _ ≤ Real.pi / 2 := hcaps t v hv
  let : PreconnectedSpace (Set.Icc a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let t₀ : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  have hconst : ∀ t, u t = u t₀ := by
    intro t
    exact eq_on_preconnected_of_balanced_caps V p hbalance hspan
      isPreconnected_univ u hu.continuousOn (fun t _ => hucaps t)
      t (Set.mem_univ t) t₀ (Set.mem_univ t₀)
  apply hPL.not_constant_on_isometric_interval hab γ hγ (g (γ t₀))
  intro t
  exact R.symm.injective (hconst t)

/-- The approximation formulation: a map which is the identity on the embedded
sphere cannot have such a piecewise isometric approximation at error `pi/2`.
The map away from the sphere is unrestricted in this conclusion. -/
theorem no_approximation_of_sphere_interval_configuration
    (e : GeodesicSphere n → P) (he : Isometry e)
    {a b : ℝ} (hab : a < b) (γ : Set.Icc a b → P) (hγ : Isometry γ)
    (V : Finset (GeodesicSphere n)) (p : GeodesicSphere n)
    (hbalance : ∑ v ∈ V, v.val = 0)
    (hspan : Submodule.span ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere n))) =
      (Submodule.span ℝ ({p.val} : Set (EuclideanSpace ℝ (Fin (n + 1)))))ᗮ)
    (hcaps : ∀ t : Set.Icc a b, ∀ v ∈ V, dist (γ t) (e v) ≤ Real.pi / 2)
    (f : P → GeodesicSphere n) (hf : ∀ x, f (e x) = x) :
    ¬ ∃ g : P → GeodesicSphere n, LipschitzWith 1 g ∧
      PolyhedralPiecewiseIsometry M q g ∧ ∀ x, dist (g x) (f x) < Real.pi / 2 := by
  rintro ⟨g, hg, hPL, hclose⟩
  apply sphere_interval_obstruction e he hab γ hγ V p hbalance hspan hcaps hPL hg
  intro x
  simpa only [hf x] using hclose (e x)

end BrehmApprox
