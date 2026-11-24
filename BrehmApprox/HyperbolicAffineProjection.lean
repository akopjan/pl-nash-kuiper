module

public import BrehmApprox.HyperbolicMotions

/-!
# Hyperbolic planes through an arbitrary point

An explicit Lorentz boost moves the prescribed base point to the origin.
Conjugating the already proved normal projection gives a genuine nearest
projection to every translated totally geodesic plane.  Shortness, uniqueness,
Pythagoras and exact nested commutation are proved, not additional assumptions.

The file also proves that a hyperbolic motion with a linear Lorentz lift maps
the actual positive Lorentz hull of finite vertices onto the corresponding hull.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

/-- The complete hyperbolic plane through `a` whose tangent space is `K` after
the canonical boost moving `a` to the origin. -/
def affineGeodesicPlane (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set (HyperbolicSpace n) :=
  (boostEquiv a.point) ⁻¹' geodesicPlane K

lemma base_mem_affineGeodesicPlane (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : a ∈ affineGeodesicPlane a K := by
  change (boostBy a.point a).point ∈ K
  rw [boostBy_self]
  exact K.zero_mem

/-- Nearest normal projection to the complete hyperbolic plane `affineGeodesicPlane a K`. -/
def affineGeodesicProjection (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : HyperbolicSpace n) :
    HyperbolicSpace n :=
  (boostEquiv a.point).symm (geodesicProjection K (boostEquiv a.point x))

lemma boost_affineGeodesicProjection (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : HyperbolicSpace n) :
    boostEquiv a.point (affineGeodesicProjection a K x) =
      geodesicProjection K (boostEquiv a.point x) :=
  (boostEquiv a.point).apply_symm_apply _

lemma affineGeodesicProjection_mem (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : HyperbolicSpace n) :
    affineGeodesicProjection a K x ∈ affineGeodesicPlane a K := by
  change boostEquiv a.point (affineGeodesicProjection a K x) ∈ geodesicPlane K
  rw [boost_affineGeodesicProjection]
  exact geodesicProjection_mem K _

lemma affineGeodesicProjection_fix (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {x : HyperbolicSpace n}
    (hx : x ∈ affineGeodesicPlane a K) : affineGeodesicProjection a K x = x := by
  apply (boostEquiv a.point).injective
  rw [boost_affineGeodesicProjection]
  exact geodesicProjection_fix K hx

theorem affineGeodesicProjection_short (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Short (affineGeodesicProjection a K) := by
  intro x y
  simpa only [affineGeodesicProjection, (boostEquiv a.point).symm.dist_eq,
    (boostEquiv a.point).dist_eq] using
    geodesicProjection_short K (boostEquiv a.point x) (boostEquiv a.point y)

theorem affineGeodesicProjection_nested (a : HyperbolicSpace n)
    {J K : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (hJK : J ≤ K)
    (x : HyperbolicSpace n) :
    affineGeodesicProjection a J (affineGeodesicProjection a K x) =
      affineGeodesicProjection a J x := by
  apply (boostEquiv a.point).injective
  simp only [boost_affineGeodesicProjection, geodesicProjection_nested hJK]

theorem affineGeodesicProjection_pythagoras (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : HyperbolicSpace n)
    {z : HyperbolicSpace n} (hz : z ∈ affineGeodesicPlane a K) :
    Real.cosh (dist x z) = Real.cosh (dist x (affineGeodesicProjection a K x)) *
      Real.cosh (dist (affineGeodesicProjection a K x) z) := by
  have h := geodesicProjection_pythagoras K (boostEquiv a.point x) hz
  rw [← boost_affineGeodesicProjection] at h
  simpa only [(boostEquiv a.point).dist_eq] using h

theorem affineGeodesicProjection_nearest (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : HyperbolicSpace n)
    {z : HyperbolicSpace n} (hz : z ∈ affineGeodesicPlane a K) :
    dist x (affineGeodesicProjection a K x) ≤ dist x z := by
  have h := geodesicProjection_nearest K (boostEquiv a.point x) hz
  rw [← boost_affineGeodesicProjection] at h
  simpa only [(boostEquiv a.point).dist_eq] using h

theorem affineGeodesicProjection_nearest_unique (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : HyperbolicSpace n)
    {z : HyperbolicSpace n} (hz : z ∈ affineGeodesicPlane a K)
    (hmin : dist x z ≤ dist x (affineGeodesicProjection a K x)) :
    z = affineGeodesicProjection a K x := by
  apply (boostEquiv a.point).injective
  rw [boost_affineGeodesicProjection]
  apply geodesicProjection_nearest_unique K (boostEquiv a.point x) hz
  rw [← boost_affineGeodesicProjection]
  simpa only [(boostEquiv a.point).dist_eq] using hmin

end BrehmApprox.HyperbolicSpace

namespace BrehmApprox

variable {n : ℕ}

open Classical

/-- Finite hyperbolic hulls transform under any actual motion equipped with
its Lorentz-linear lift. -/
theorem mem_hyperbolicCell_image_of_linear_lift
    (e : HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    (L : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    (hL : ∀ x, L (HyperbolicSpace.lift x) = HyperbolicSpace.lift (e x))
    (V : Finset (HyperbolicSpace n)) {x : HyperbolicSpace n}
    (hx : x ∈ hyperbolicCell V) : e x ∈ hyperbolicCell (V.image e) := by
  classical
  obtain ⟨w, hw, a, ha, hrep⟩ := hx
  refine ⟨fun y => w (e.symm y), ?_, a, ha, ?_⟩
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    simpa only [e.symm_apply_apply] using hw v hv
  · rw [Finset.sum_image]
    · simp only [e.symm_apply_apply]
      have hm := congrArg L hrep
      simpa only [map_sum, map_smul, hL] using hm
    · intro y hy z hz heq
      exact e.injective heq

theorem hyperbolicCell_image_boost (z : EuclideanSpace ℝ (Fin n))
    (V : Finset (HyperbolicSpace n)) :
    HyperbolicSpace.boostBy z '' hyperbolicCell V =
      hyperbolicCell (V.image (HyperbolicSpace.boostBy z)) := by
  classical
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact mem_hyperbolicCell_image_of_linear_lift (HyperbolicSpace.boostEquiv z)
      (Hyperboloid.boostLinear z) (fun x => (HyperbolicSpace.lift_boostBy z x).symm) V hx
  · intro y hy
    have hx := mem_hyperbolicCell_image_of_linear_lift (HyperbolicSpace.boostEquiv (-z))
      (Hyperboloid.boostLinear (-z))
      (fun x => (HyperbolicSpace.lift_boostBy (-z) x).symm)
      (V.image (HyperbolicSpace.boostBy z)) hy
    have himage : (V.image (HyperbolicSpace.boostBy z)).image
        (HyperbolicSpace.boostEquiv (-z)) = V := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨u, ⟨v, hv, rfl⟩, hx⟩
        change HyperbolicSpace.boostBy (-z) (HyperbolicSpace.boostBy z v) = x at hx
        rw [HyperbolicSpace.boostBy_neg_inverse] at hx
        exact hx ▸ hv
      · intro hx
        refine ⟨HyperbolicSpace.boostBy z x, ⟨x, hx, rfl⟩, ?_⟩
        exact HyperbolicSpace.boostBy_neg_inverse z x
    rw [himage] at hx
    refine ⟨HyperbolicSpace.boostBy (-z) y, hx, ?_⟩
    simpa only [neg_neg] using HyperbolicSpace.boostBy_neg_inverse (-z) y

end BrehmApprox
