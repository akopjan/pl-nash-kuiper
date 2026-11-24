module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.NormNum

/-!
# The round unit sphere with its angular distance

`GeodesicSphere n` is a distinct wrapper around the unit sphere in real
Euclidean `(n+1)`-space.  Its distance is the angle between unit vectors,
not the ambient Euclidean chordal distance.  The metric axioms and compactness
are proved here, without additional axioms.
-/

@[expose] public section

noncomputable section

open InnerProductGeometry Metric
open scoped RealInnerProductSpace

/-- The unit sphere in Euclidean `(n+1)`-space, equipped below with angular distance. -/
structure GeodesicSphere (n : ℕ) where
  val : EuclideanSpace ℝ (Fin (n + 1))
  norm_val : ‖val‖ = 1

namespace GeodesicSphere

variable {n m : ℕ}

/-- A fixed unit vector, used to witness nonemptiness in every dimension. -/
def northPole (n : ℕ) : GeodesicSphere n :=
  ⟨EuclideanSpace.single (0 : Fin (n + 1)) 1, by simp⟩

instance : Inhabited (GeodesicSphere n) := ⟨northPole n⟩

@[ext]
theorem ext {x y : GeodesicSphere n} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

@[simp]
theorem val_ne_zero (x : GeodesicSphere n) : x.val ≠ 0 := by
  intro h
  have hx := x.norm_val
  rw [h, norm_zero] at hx
  norm_num at hx

theorem eq_of_angle_eq_zero {x y : GeodesicSphere n}
    (h : angle x.val y.val = 0) : x = y := by
  obtain ⟨_, r, hr, hyr⟩ := angle_eq_zero_iff.mp h
  have hn := congrArg norm hyr
  rw [y.norm_val, norm_smul, x.norm_val, Real.norm_eq_abs,
    abs_of_pos hr, mul_one] at hn
  apply ext
  simpa [← hn] using hyr.symm

/-- The standard round metric, in radians. -/
instance : MetricSpace (GeodesicSphere n) where
  dist x y := angle x.val y.val
  dist_self x := angle_self x.val_ne_zero
  dist_comm x y := angle_comm x.val y.val
  dist_triangle x y z := angle_le_angle_add_angle x.val y.val z.val
  eq_of_dist_eq_zero := eq_of_angle_eq_zero

@[simp]
theorem dist_eq_angle (x y : GeodesicSphere n) :
    dist x y = angle x.val y.val := rfl

/-- For unit vectors, spherical distance is the arccosine of the Euclidean inner product. -/
theorem dist_eq_arccos_inner (x y : GeodesicSphere n) :
    dist x y = Real.arccos (inner ℝ x.val y.val) := by
  simp [dist_eq_angle, angle, x.norm_val, y.norm_val]

theorem cos_dist (x y : GeodesicSphere n) :
    Real.cos (dist x y) = inner ℝ x.val y.val := by
  simpa [dist_eq_angle, x.norm_val, y.norm_val] using
    InnerProductGeometry.cos_angle x.val y.val

theorem dist_le_pi (x y : GeodesicSphere n) : dist x y ≤ Real.pi :=
  angle_le_pi x.val y.val

theorem dist_lt_pi_div_two_iff (x y : GeodesicSphere n) :
    dist x y < Real.pi / 2 ↔ 0 < inner ℝ x.val y.val := by
  rw [dist_eq_arccos_inner, Real.arccos_lt_pi_div_two]

/-- An open hemisphere is a spherical open ball of radius `pi / 2`. -/
theorem ball_pi_div_two (x : GeodesicSphere n) :
    ball x (Real.pi / 2) = {y | 0 < inner ℝ y.val x.val} := by
  ext y
  exact dist_lt_pi_div_two_iff y x

/-- The identity on unit vectors, viewed as an equivalence of underlying types. -/
def unitSphereEquiv (n : ℕ) :
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃ GeodesicSphere n where
  toFun x := ⟨x.val, by simp⟩
  invFun x := ⟨x.val, by simpa using x.norm_val⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem unitSphereEquiv_val (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (unitSphereEquiv n x).val = x.val := rfl

/-- The identity from the chordal unit sphere to the angular unit sphere is continuous. -/
theorem continuous_unitSphereEquiv (n : ℕ) : Continuous (unitSphereEquiv n) := by
  have h1 : Continuous (fun q :
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ×
        sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 => q.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous (fun q :
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ×
        sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  apply continuous_iff_continuous_dist.mpr
  simpa only [dist_eq_arccos_inner, unitSphereEquiv_val, Function.comp_def] using
    Real.continuous_arccos.comp (h1.inner h2)

/-- Angular and chordal distance induce the same topology on the unit sphere. -/
def unitSphereHomeomorph (n : ℕ) :
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃ₜ GeodesicSphere n :=
  (continuous_unitSphereEquiv n).homeoOfEquivCompactToT2

instance : CompactSpace (GeodesicSphere n) :=
  Function.Surjective.compactSpace (continuous_unitSphereEquiv n)
    (unitSphereEquiv n).surjective

/-- The vector-valued inclusion of the angular sphere is continuous. -/
theorem continuous_val : Continuous (val : GeodesicSphere n → EuclideanSpace ℝ (Fin (n + 1))) :=
  continuous_subtype_val.comp (unitSphereHomeomorph n).symm.continuous

/-- An ambient linear isometric embedding induces an isometric embedding of round spheres. -/
def map (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (x : GeodesicSphere n) : GeodesicSphere m :=
  ⟨f x.val, by rw [f.norm_map, x.norm_val]⟩

theorem isometry_map
    (f : EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    Isometry (map f) := by
  apply Isometry.of_dist_eq
  intro x y
  exact f.angle_map x.val y.val

/-- An orthogonal equivalence of ambient vector spaces acts by a round-sphere isometry. -/
def mapEquiv
    (f : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    GeodesicSphere n ≃ᵢ GeodesicSphere m where
  toFun := map f.toLinearIsometry
  invFun := map f.symm.toLinearIsometry
  left_inv x := by
    apply ext
    exact f.symm_apply_apply x.val
  right_inv x := by
    apply ext
    exact f.apply_symm_apply x.val
  isometry_toFun := isometry_map f.toLinearIsometry

@[simp]
theorem mapEquiv_apply_val
    (f : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (x : GeodesicSphere n) : (mapEquiv f x).val = f x.val := rfl

/-- The antipode in the round unit sphere. -/
def antipode (x : GeodesicSphere n) : GeodesicSphere n :=
  ⟨-x.val, by rw [norm_neg, x.norm_val]⟩

theorem isometry_antipode : Isometry (antipode : GeodesicSphere n → GeodesicSphere n) := by
  apply Isometry.of_dist_eq
  intro x y
  exact InnerProductGeometry.angle_neg_neg x.val y.val

@[simp]
theorem dist_antipode (x : GeodesicSphere n) : dist x (antipode x) = Real.pi :=
  angle_self_neg_of_ne_zero x.val_ne_zero

end GeodesicSphere
