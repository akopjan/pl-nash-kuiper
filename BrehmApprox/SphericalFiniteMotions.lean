module

public import BrehmApprox.EuclideanFiniteMotions
public import BrehmApprox.SphericalRigidity

/-!
# Spherical finite interpolation from Euclidean interpolation

Add the origin to the Euclidean data. A sufficiently small sphere meets only
affine motions fixing the origin, hence only orthogonal motions. Restriction
and rescaling therefore give the spherical finite extension.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite family of nonzero translation vectors stays uniformly away from
the origin. The extra bound on the radius is useful for radial segments. -/
private theorem exists_radius_avoiding_translations (S : Finset (E ≃ᵃⁱ[ℝ] E)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ r ∈ S, r 0 ≠ 0 → 2 * ρ < ‖r 0‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, le_rfl, by simp⟩
  | @insert r S hr ih =>
    obtain ⟨ρ, hρ, hρ1, hS⟩ := ih
    by_cases hr0 : r 0 = 0
    · refine ⟨ρ, hρ, hρ1, ?_⟩
      intro q hq hq0
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact (hq0 hr0).elim
      · exact hS q hq hq0
    · refine ⟨min ρ (‖r 0‖ / 4), lt_min hρ (by positivity),
        (min_le_left _ _).trans hρ1, ?_⟩
      intro q hq hq0
      rcases Finset.mem_insert.mp hq with rfl | hq
      · have hn := norm_pos_iff.mpr hr0
        have hm := min_le_right ρ (‖q 0‖ / 4)
        linarith
      · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)).trans_lt
          (hS q hq hq0)

/-- Near a fixed origin, a short finite-motion map selects only linear motions. -/
theorem exists_linear_motions_near_zero
    {g : E → E} (hg : Short g) (hgm : LocallyFiniteEuclideanMotions g)
    (hg0 : g 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ S : Finset (E ≃ₗᵢ[ℝ] E),
      ∀ x, ‖x‖ ≤ ρ → ∃ r ∈ S, g x = r x := by
  classical
  obtain ⟨S, hS⟩ := hgm 1
  obtain ⟨ρ, hρ, hρ1, havoid⟩ := exists_radius_avoiding_translations S
  refine ⟨ρ, hρ, hρ1, S.image AffineIsometryEquiv.linearIsometryEquiv, ?_⟩
  intro x hx
  obtain ⟨r, hr, heq⟩ := hS x (hx.trans hρ1)
  have hr0 : r 0 = 0 := by
    by_contra hn
    have hsmall := havoid r hr hn
    have hgnorm : ‖g x‖ ≤ ‖x‖ := by
      simpa only [hg0, dist_zero_right] using hg x 0
    have hrnorm : ‖r 0 - r x‖ = ‖x‖ := by
      simpa only [dist_eq_norm, zero_sub, norm_neg] using r.dist_map 0 x
    have hb : ‖r 0‖ ≤ ‖x‖ + ‖g x‖ := by
      calc
        ‖r 0‖ ≤ ‖r 0 - r x‖ + ‖r x‖ := by
          simpa only [sub_add_cancel] using norm_add_le (r 0 - r x) (r x)
        _ = ‖x‖ + ‖g x‖ := by rw [hrnorm, ← heq]
    linarith
  refine ⟨r.linearIsometryEquiv, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
  have hlin := r.map_vsub x 0
  simpa only [vsub_eq_sub, sub_zero, hr0, ← heq] using hlin.symm

/-- A short map fixing the origin and preserving the norm of one point is
linear along the segment joining that point to the origin. -/
theorem short_map_smul_of_norm_eq
    {g : E → E} (hg : Short g) (hg0 : g 0 = 0) {x : E}
    (hx : ‖g x‖ = ‖x‖) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    g (t • x) = t • g x := by
  let r : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (x - g x))ᗮ.reflection
  have hr : r x = g x := Submodule.reflection_sub hx.symm
  let k : E → E := fun z => r.symm (g z)
  have hk : Short k := by
    intro u v
    simpa only [k, r.symm.isometry.dist_eq] using hg u v
  have hk0 : k 0 = 0 := by simp [k, hg0]
  have hkx : k x = x := by simp only [k, ← hr, r.symm_apply_apply]
  have hfix := convex_fixedPoints_of_short hk hk0 hkx
    (sub_nonneg.mpr ht1) ht0 (show 1 - t + t = 1 by ring)
  change k ((1 - t) • 0 + t • x) = (1 - t) • 0 + t • x at hfix
  simp only [smul_zero, zero_add, k] at hfix
  have h := congrArg r hfix
  simpa only [r.apply_symm_apply, map_smul, hr] using h

variable {n : ℕ}

/-- Angular contraction of unit vectors is equivalent to contraction of their
Euclidean chords. -/
theorem sphere_dist_le_iff_chord_le (x y u v : GeodesicSphere n) :
    dist u v ≤ dist x y ↔ dist u.val v.val ≤ dist x.val y.val := by
  constructor
  · intro h
    have hi := Real.cos_le_cos_of_nonneg_of_le_pi (dist_nonneg : 0 ≤ dist u v)
      (GeodesicSphere.dist_le_pi x y) h
    rw [GeodesicSphere.cos_dist, GeodesicSphere.cos_dist] at hi
    have hs : ‖u.val - v.val‖ ^ 2 ≤ ‖x.val - y.val‖ ^ 2 := by
      simp only [norm_sub_sq_real, u.norm_val, v.norm_val, x.norm_val, y.norm_val]
      linarith
    rw [dist_eq_norm, dist_eq_norm]
    nlinarith [norm_nonneg (u.val - v.val), norm_nonneg (x.val - y.val)]
  · intro h
    have hs := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist u.val v.val) h 2
    simp only [dist_eq_norm, norm_sub_sq_real, u.norm_val, v.norm_val,
      x.norm_val, y.norm_val] at hs
    rw [GeodesicSphere.dist_eq_arccos_inner, GeodesicSphere.dist_eq_arccos_inner]
    exact Real.arccos_le_arccos (by linarith)

/-- A global finite selection of ambient orthogonal motions on the round sphere. -/
def FiniteSphericalMotions (f : GeodesicSphere n → GeodesicSphere n) : Prop :=
  ∃ S : Finset (EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n + 1))),
      ∀ x, ∃ r ∈ S, f x = GeodesicSphere.mapEquiv r x

/-- Extend spherical data to an ambient function, taking the value zero away
from the unit sphere. Only the prescribed unit vectors and the origin are used. -/
def sphericalDataLift (f : GeodesicSphere n → GeodesicSphere n)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  if h : ‖x‖ = 1 then (f ⟨x, h⟩).val else 0

@[simp] theorem sphericalDataLift_zero (f : GeodesicSphere n → GeodesicSphere n) :
    sphericalDataLift f 0 = 0 := by simp [sphericalDataLift]

@[simp] theorem sphericalDataLift_val (f : GeodesicSphere n → GeodesicSphere n)
    (x : GeodesicSphere n) : sphericalDataLift f x.val = (f x).val := by
  simp only [sphericalDataLift, dite_eq_left x.norm_val]

/-- Spherical short data, together with the fixed origin, are Euclidean short data. -/
theorem sphericalDataLift_shortOn
    (s : Finset (GeodesicSphere n)) (f : GeodesicSphere n → GeodesicSphere n)
    (hf : ShortOn f (s : Set (GeodesicSphere n))) :
    ShortOn (sphericalDataLift f)
      ((insert 0 (s.image GeodesicSphere.val) : Finset _) : Set _) := by
  classical
  intro x hx y hy
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rcases Finset.mem_insert.mp hy with rfl | hy
    · simp
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      simp only [sphericalDataLift_zero, sphericalDataLift_val, dist_zero_left,
        (f v).norm_val, v.norm_val, le_refl]
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simp only [sphericalDataLift_zero, sphericalDataLift_val, dist_zero_right,
        (f u).norm_val, u.norm_val, le_refl]
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      simp only [sphericalDataLift_val]
      exact (sphere_dist_le_iff_chord_le u v (f u) (f v)).mp (hf u hu v hv)

/-- Brehm's finite interpolation theorem on the round sphere, obtained from
Euclidean interpolation by taking the finite linear germ at a fixed origin. -/
theorem spherical_finite_extension_motions (n : ℕ) :
    FiniteExtension (FiniteSphericalMotions (n := n)) := by
  classical
  intro s f hf
  let V : Finset (EuclideanSpace ℝ (Fin (n + 1))) :=
    insert 0 (s.image GeodesicSphere.val)
  obtain ⟨g, hg, hgm, hgeq⟩ := euclidean_finite_extension_motions (n + 1)
    V (sphericalDataLift f) (sphericalDataLift_shortOn s f hf)
  have hg0 : g 0 = 0 := by
    simpa only [sphericalDataLift_zero] using hgeq 0 (Finset.mem_insert_self _ _)
  have hgs (x : GeodesicSphere n) (hx : x ∈ s) : g x.val = (f x).val := by
    exact (hgeq x.val (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨x, hx, rfl⟩))).trans (sphericalDataLift_val f x)
  obtain ⟨ρ, hρ, hρ1, S, hS⟩ := exists_linear_motions_near_zero hg hgm hg0
  have hform (x : GeodesicSphere n) :
      ∃ r ∈ S, ρ⁻¹ • g (ρ • x.val) = r x.val := by
    have hxnorm : ‖ρ • x.val‖ ≤ ρ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, x.norm_val, mul_one, le_refl]
    obtain ⟨r, hr, heq⟩ := hS (ρ • x.val) hxnorm
    exact ⟨r, hr, by rw [heq, map_smul, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]⟩
  let H : GeodesicSphere n → GeodesicSphere n := fun x =>
    ⟨ρ⁻¹ • g (ρ • x.val), by
      obtain ⟨r, hr, heq⟩ := hform x
      rw [heq, r.norm_map, x.norm_val]⟩
  have hscale (x : GeodesicSphere n) : ρ • (H x).val = g (ρ • x.val) := by
    simp only [H, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  have hH : Short H := by
    intro x y
    apply (sphere_dist_le_iff_chord_le x y (H x) (H y)).mpr
    apply radial_dist_le_of_scaled_dist_le hρ hρ
      ((H x).norm_val.trans x.norm_val.symm) ((H y).norm_val.trans y.norm_val.symm)
    rw [hscale, hscale]
    exact hg _ _
  refine ⟨H, hH, ⟨S, ?_⟩, ?_⟩
  · intro x
    obtain ⟨r, hr, heq⟩ := hform x
    exact ⟨r, hr, GeodesicSphere.ext heq⟩
  · intro x hx
    apply GeodesicSphere.ext
    have hn : ‖g x.val‖ = ‖x.val‖ := by rw [hgs x hx, (f x).norm_val, x.norm_val]
    have hseg := short_map_smul_of_norm_eq hg hg0 hn hρ.le hρ1
    change ρ⁻¹ • g (ρ • x.val) = (f x).val
    rw [hseg, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, hgs x hx]

end BrehmApprox
