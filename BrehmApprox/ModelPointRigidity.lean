module

public import BrehmApprox.SphericalRigidity
public import BrehmApprox.HyperbolicRigidity
public import BrehmApprox.FiniteGramIsometry

/-!
# Finite distance determination in curved simplices

A point in a geodesic convex hull is uniquely determined, even among all
ambient points, by its distances to the vertices. In the spherical case,
a distance correspondence of independent vertices extends orthogonally.
-/

@[expose] public section
noncomputable section

open scoped BigOperators InnerProductSpace

namespace BrehmApprox

variable {n : ℕ}

theorem eq_of_mem_sphericalCell_of_dist_eq {V : Finset (GeodesicSphere n)}
    {x y : GeodesicSphere n} (hx : x ∈ sphericalCell V)
    (hd : ∀ v ∈ V, dist x v = dist y v) : x = y := by
  obtain ⟨w, _, a, ha, hrep⟩ := hx
  have hi (v : GeodesicSphere n) (hv : v ∈ V) :
      ⟪x.val, v.val⟫_ℝ = ⟪y.val, v.val⟫_ℝ := by
    rw [← GeodesicSphere.cos_dist, ← GeodesicSphere.cos_dist, hd v hv]
  have hs : ⟪x.val, ∑ v ∈ V, w v • v.val⟫_ℝ =
      ⟪y.val, ∑ v ∈ V, w v • v.val⟫_ℝ := by
    simp only [inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl (fun v hv => by rw [hi v hv])
  rw [hrep, inner_smul_right, inner_smul_right,
    inner_self_eq_one_of_norm_eq_one x.norm_val, mul_one] at hs
  have he : ⟪y.val, x.val⟫_ℝ = 1 := by nlinarith
  apply GeodesicSphere.ext
  exact ((inner_eq_one_iff_of_norm_eq_one y.norm_val x.norm_val).mp he).symm

theorem eq_of_mem_hyperbolicCell_of_dist_eq {V : Finset (HyperbolicSpace n)}
    {x y : HyperbolicSpace n} (hx : x ∈ hyperbolicCell V)
    (hd : ∀ v ∈ V, dist x v = dist y v) : x = y := by
  obtain ⟨w, _, a, ha, hrep⟩ := hx
  have hc (v : HyperbolicSpace n) (hv : v ∈ V) :
      Hyperboloid.coshDist x.point v.point = Hyperboloid.coshDist y.point v.point := by
    rw [← HyperbolicSpace.cosh_dist, ← HyperbolicSpace.cosh_dist, hd v hv]
  have hs : (∑ v ∈ V, w v * Hyperboloid.coshDist x.point v.point) =
      ∑ v ∈ V, w v * Hyperboloid.coshDist y.point v.point :=
    Finset.sum_congr rfl (fun v hv => by rw [hc v hv])
  rw [hyperbolic_weighted_cosh hrep x, hyperbolic_weighted_cosh hrep y,
    Hyperboloid.coshDist_self, mul_one] at hs
  have he : Hyperboloid.coshDist y.point x.point = 1 := by nlinarith
  exact HyperbolicSpace.ext (Hyperboloid.eq_of_coshDist_eq_one he).symm

theorem exists_spherical_vertex_motion {ι : Type*} [Fintype ι]
    (v w : ι → GeodesicSphere n)
    (hv : LinearIndependent ℝ (fun i => (v i).val))
    (hd : ∀ i j, dist (v i) (v j) = dist (w i) (w j)) :
    ∃ r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      ∀ i, GeodesicSphere.mapEquiv r (v i) = w i := by
  obtain ⟨r, hr⟩ := exists_ambient_gram_isometry
    (fun i => (v i).val) (fun i => (w i).val) hv (by
      intro i j
      rw [← GeodesicSphere.cos_dist, ← GeodesicSphere.cos_dist, hd i j])
  exact ⟨r, fun i => GeodesicSphere.ext (hr i)⟩

theorem sphericalMotion_eq_of_vertex_distances
    (r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {V : Finset (GeodesicSphere n)} {x y : GeodesicSphere n}
    (hx : x ∈ sphericalCell V)
    (hd : ∀ v ∈ V, dist y (GeodesicSphere.mapEquiv r v) = dist x v) :
    GeodesicSphere.mapEquiv r x = y := by
  let e := GeodesicSphere.mapEquiv r
  have he : x = e.symm y := eq_of_mem_sphericalCell_of_dist_eq hx (by
    intro v hv
    calc
      dist x v = dist y (e v) := (hd v hv).symm
      _ = dist (e.symm y) v := by rw [← e.dist_eq (e.symm y) v, e.apply_symm_apply])
  rw [he, e.apply_symm_apply]

theorem hyperbolicMotion_eq_of_vertex_distances
    (r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    {V : Finset (HyperbolicSpace n)} {x y : HyperbolicSpace n}
    (hx : x ∈ hyperbolicCell V)
    (hd : ∀ v ∈ V, dist y (r v) = dist x v) : r x = y := by
  have he : x = r.symm y := eq_of_mem_hyperbolicCell_of_dist_eq hx (by
    intro v hv
    calc
      dist x v = dist y (r v) := (hd v hv).symm
      _ = dist (r.symm y) v := by rw [← r.dist_eq (r.symm y) v, r.apply_symm_apply])
  rw [he, r.apply_symm_apply]

end BrehmApprox
