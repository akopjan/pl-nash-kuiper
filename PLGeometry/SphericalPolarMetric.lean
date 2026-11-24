module

public import PLGeometry.ModelCones

/-! # The spherical polar metric in an arbitrary tangent frame -/

@[expose] public section
noncomputable section

open scoped InnerProductSpace

namespace ArchivePLGeometry

variable {n : ℕ}

/-- Polar representations in one tangent frame satisfy the spherical cosine law. -/
theorem spherical_polar_cos_dist (p x y u v : GeodesicSphere n) (r s : ℝ)
    (hu : inner ℝ p.val u.val = 0) (hv : inner ℝ p.val v.val = 0)
    (hx : x.val = Real.cos r • p.val + Real.sin r • u.val)
    (hy : y.val = Real.cos s • p.val + Real.sin s • v.val) :
    Real.cos (dist x y) =
      Real.cos r * Real.cos s + Real.sin r * Real.sin s * Real.cos (dist u v) := by
  rw [GeodesicSphere.cos_dist, hx, hy]
  have hup : inner ℝ u.val p.val = 0 := by rw [real_inner_comm]; exact hu
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_self_eq_one_of_norm_eq_one p.norm_val, hv, hup, GeodesicSphere.cos_dist]
  ring

/-- The same radii and angular distance determine the canonical cone metric. -/
theorem spherical_polar_dist_eq_conePoint (p x y u v : GeodesicSphere n) (r s : ℝ)
    (hu : inner ℝ p.val u.val = 0) (hv : inner ℝ p.val v.val = 0)
    (hx : x.val = Real.cos r • p.val + Real.sin r • u.val)
    (hy : y.val = Real.cos s • p.val + Real.sin s • v.val)
    (o : GeodesicSphere (n + 1)) :
    dist x y = dist (conePoint .spherical n o u r) (conePoint .spherical n o v s) := by
  apply Real.strictAntiOn_cos.injOn
    ⟨dist_nonneg, GeodesicSphere.dist_le_pi _ _⟩
    ⟨dist_nonneg, GeodesicSphere.dist_le_pi _ _⟩
  rw [spherical_polar_cos_dist p x y u v r s hu hv hx hy, spherical_cone_cos_dist]

theorem spherical_polar_dist_eq_cone (p x y u v : GeodesicSphere n) (r s : ℝ)
    (hu : inner ℝ p.val u.val = 0) (hv : inner ℝ p.val v.val = 0)
    (hx : x.val = Real.cos r • p.val + Real.sin r • u.val)
    (hy : y.val = Real.cos s • p.val + Real.sin s • v.val) :
    dist x y =
      dist (conePoint .spherical n (GeodesicSphere.northPole (n + 1)) u r)
        (conePoint .spherical n (GeodesicSphere.northPole (n + 1)) v s) :=
  spherical_polar_dist_eq_conePoint p x y u v r s hu hv hx hy (GeodesicSphere.northPole (n + 1))

end ArchivePLGeometry
