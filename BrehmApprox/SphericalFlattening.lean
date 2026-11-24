module

public import BrehmApprox.SphericalLocalCharts
public import BrehmApprox.NormalFlattening

/-!
# Actual normal flattening in a spherical central chart

Conjugation by the gnomonic chart transfers the proved Euclidean normal
flattening to the round sphere. It preserves the normal projection, equals
that projection on an inner tube, equals the identity outside its support,
and has an explicit Lipschitz constant tending to one as both the flattening
parameter and the radius of the whole chart cap tend to zero.

This is a local lemma. The cap radius must cover the entire face being treated.
For a fixed triangulation it cannot be decreased by narrowing only the normal
support. Consequently this file does not prove the global almost nonexpansive
flattening lemma for an arbitrary fixed polyhedral complex, and its constants
must not be multiplied over a growing number of faces without an additional
uniform argument.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normalFlatten_norm_le (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (α R : ℝ) (z : E) : ‖normalFlatten K α R z‖ ≤ ‖z‖ := by
  have hz : z ∈ Metric.closedBall (0 : E) ‖z‖ := by simp
  have hPz : K.starProjection z ∈ Metric.closedBall (0 : E) ‖z‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using K.norm_starProjection_apply_le z
  have h := normalFlatten_mem_convex K α R (convex_closedBall (0 : E) ‖z‖) hz hPz
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

lemma taperedNormalFlatten_norm_le (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (α : ℝ) (R : E → ℝ) (z : E) : ‖taperedNormalFlatten K α R z‖ ≤ ‖z‖ :=
  normalFlatten_norm_le K α (R (K.starProjection z)) z

end BrehmApprox

namespace GeodesicSphere

open BrehmApprox

variable {n : ℕ}

/-- Spherical normal flattening, obtained from the actual Euclidean construction
in the tangent central chart. -/
def sphericalNormalFlatten (p : GeodesicSphere n) (K : Submodule ℝ (tangentPlane p))
    (α : ℝ) (R : tangentPlane p → ℝ) (x : openHemisphere p) : openHemisphere p :=
  gnomonicInverse p (taperedNormalFlatten K α R (gnomonic p x))

@[simp]
lemma gnomonic_sphericalNormalFlatten (p : GeodesicSphere n)
    (K : Submodule ℝ (tangentPlane p)) (α : ℝ) (R : tangentPlane p → ℝ)
    (x : openHemisphere p) :
    gnomonic p (sphericalNormalFlatten p K α R x) =
      taperedNormalFlatten K α R (gnomonic p x) :=
  gnomonic_gnomonicInverse p _

lemma sphericalNormalFlatten_projection (p : GeodesicSphere n)
    (K : Submodule ℝ (tangentPlane p)) (α : ℝ) (R : tangentPlane p → ℝ)
    (x : openHemisphere p) :
    K.starProjection (gnomonic p (sphericalNormalFlatten p K α R x)) =
      K.starProjection (gnomonic p x) := by
  rw [gnomonic_sphericalNormalFlatten]
  exact taperedNormalFlatten_projection K α R _

lemma sphericalNormalFlatten_inner (p : GeodesicSphere n)
    (K : Submodule ℝ (tangentPlane p)) {α : ℝ} (hα1 : α < 1)
    (R : tangentPlane p → ℝ) {x : openHemisphere p}
    (hin : ‖gnomonic p x - K.starProjection (gnomonic p x)‖ ≤
      α * R (K.starProjection (gnomonic p x))) :
    sphericalNormalFlatten p K α R x = gnomonicInverse p (K.starProjection (gnomonic p x)) := by
  unfold sphericalNormalFlatten
  rw [taperedNormalFlatten_inner K hα1 R hin]

lemma sphericalNormalFlatten_outer (p : GeodesicSphere n)
    (K : Submodule ℝ (tangentPlane p)) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (R : tangentPlane p → ℝ) {x : openHemisphere p}
    (hout : R (K.starProjection (gnomonic p x)) ≤
      ‖gnomonic p x - K.starProjection (gnomonic p x)‖) :
    sphericalNormalFlatten p K α R x = x := by
  unfold sphericalNormalFlatten
  rw [taperedNormalFlatten_outer K hα0 hα1 R hout, gnomonicInverse_gnomonic]

/-- The flattening stays inside each spherical ball centered at the chart pole. -/
lemma sphericalNormalFlatten_dist_pole_le (p : GeodesicSphere n)
    (K : Submodule ℝ (tangentPlane p)) (α : ℝ) (R : tangentPlane p → ℝ)
    (x : openHemisphere p) :
    dist p (sphericalNormalFlatten p K α R x).val ≤ dist p x.val := by
  have h := gnomonicInverse_dist_pole_mono p
    (taperedNormalFlatten_norm_le K α R (gnomonic p x))
  simpa only [sphericalNormalFlatten, gnomonicInverse_gnomonic] using h

lemma sphericalNormalFlatten_displacement (p : GeodesicSphere n)
    (K : Submodule ℝ (tangentPlane p)) {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi / 2)
    (R : tangentPlane p → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    (x : openHemisphere p) (hx : dist p x.val ≤ ρ) :
    dist (sphericalNormalFlatten p K α R x).val x.val ≤
      (Real.sinc ρ)⁻¹ * (α * R (K.starProjection (gnomonic p x))) := by
  have hflat := sphericalNormalFlatten_dist_pole_le p K α R x
  have hinv := gnomonicInverse_dist_le p hρ0 hρπ
    (taperedNormalFlatten K α R (gnomonic p x)) (gnomonic p x)
    (hflat.trans hx) (by simpa only [gnomonicInverse_gnomonic] using hx)
  have hsinc : 0 < Real.sinc ρ := Real.sinc_pos (by rw [abs_of_pos hρ0]; linarith [Real.pi_pos])
  have h := hinv.trans (mul_le_mul_of_nonneg_left
    (taperedNormalFlatten_displacement K hα0 hα1 R hR (gnomonic p x))
    (inv_nonneg.mpr hsinc.le))
  simpa only [sphericalNormalFlatten, gnomonicInverse_gnomonic] using h

/-- The exact distortion bound for this constructed local spherical flattening. -/
def sphericalFlattenFactor (α c ρ : ℝ) : ℝ :=
  (Real.sinc ρ)⁻¹ * ((1 + α * c) / (1 - α)) * gnomonicFactor ρ

/-- A true local spherical flattening with quantitatively almost unit
Lipschitz constant, not an assumed geometric interface. -/
theorem sphericalNormalFlatten_lipschitz (p : GeodesicSphere n)
    (K : Submodule ℝ (tangentPlane p)) {α c ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi / 2)
    (R : tangentPlane p → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    (hRlip : ∀ z ∈ K, ∀ w ∈ K, |R z - R w| ≤ c * dist z w)
    (x y : openHemisphere p) (hx : dist p x.val ≤ ρ) (hy : dist p y.val ≤ ρ) :
    dist (sphericalNormalFlatten p K α R x).val (sphericalNormalFlatten p K α R y).val ≤
      sphericalFlattenFactor α c ρ * dist x.val y.val := by
  have hsinc : 0 < Real.sinc ρ := Real.sinc_pos (by rw [abs_of_pos hρ0]; linarith [Real.pi_pos])
  have hcoef : 0 ≤ (1 + α * c) / (1 - α) := by positivity
  have hinv := gnomonicInverse_dist_le p hρ0 hρπ
    (taperedNormalFlatten K α R (gnomonic p x))
    (taperedNormalFlatten K α R (gnomonic p y))
    ((sphericalNormalFlatten_dist_pole_le p K α R x).trans hx)
    ((sphericalNormalFlatten_dist_pole_le p K α R y).trans hy)
  have hflat := taperedNormalFlatten_lipschitz K hα0 hα1 hc R hR hRlip
    (gnomonic p x) (gnomonic p y)
  have hchart := gnomonic_dist_le p hρ0.le hρπ x y hx hy
  calc
    _ ≤ (Real.sinc ρ)⁻¹ * dist (taperedNormalFlatten K α R (gnomonic p x))
        (taperedNormalFlatten K α R (gnomonic p y)) := hinv
    _ ≤ (Real.sinc ρ)⁻¹ * (((1 + α * c) / (1 - α)) *
        dist (gnomonic p x) (gnomonic p y)) :=
      mul_le_mul_of_nonneg_left hflat (inv_nonneg.mpr hsinc.le)
    _ ≤ (Real.sinc ρ)⁻¹ * (((1 + α * c) / (1 - α)) *
        (gnomonicFactor ρ * dist x.val y.val)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hchart hcoef)
        (inv_nonneg.mpr hsinc.le)
    _ = sphericalFlattenFactor α c ρ * dist x.val y.val := by
      unfold sphericalFlattenFactor
      ring

@[simp]
lemma sphericalFlattenFactor_zero (c : ℝ) : sphericalFlattenFactor 0 c 0 = 1 := by
  simp [sphericalFlattenFactor]

lemma continuousAt_sphericalFlattenFactor (c : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => sphericalFlattenFactor q.1 c q.2) (0, 0) := by
  have hinv : ContinuousAt (fun q : ℝ × ℝ => (Real.sinc q.2)⁻¹) (0, 0) :=
    (Real.continuous_sinc.comp continuous_snd).continuousAt.inv₀ (by simp)
  have hfrac : ContinuousAt (fun q : ℝ × ℝ => (1 + q.1 * c) / (1 - q.1)) (0, 0) :=
    (continuousAt_const.add (continuous_fst.continuousAt.mul continuousAt_const)).div
      (continuousAt_const.sub continuous_fst.continuousAt) (by norm_num)
  have hchart : ContinuousAt (fun q : ℝ × ℝ => gnomonicFactor q.2) (0, 0) :=
    ContinuousAt.comp (f := fun q : ℝ × ℝ => q.2) (x := (0, 0))
      continuousAt_gnomonicFactor continuous_snd.continuousAt
  exact (hinv.mul hfrac).mul hchart

end GeodesicSphere
