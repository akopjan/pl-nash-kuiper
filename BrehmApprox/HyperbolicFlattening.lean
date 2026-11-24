module

public import BrehmApprox.HyperbolicLocalCharts
public import BrehmApprox.NormalFlattening

/-!
# Genuine normal flattening in small hyperbolic charts

Euclidean tapered normal flattening is conjugated by the actual Klein chart.
It is a globally defined continuous hyperbolic map.  Exact normal projection,
nested projection, inner collapse, outer identity, convex-cell preservation,
displacement and quantitative local Lipschitz bounds are all proved.  The
bound is `(1-ρ²)⁻¹ * (1+α*c)/(1-α)` on a Klein ball of radius `ρ < 1`.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace BrehmApprox

lemma norm_taperedNormalFlatten_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (α : ℝ) (R : E → ℝ) (x : E) :
    ‖taperedNormalFlatten K α R x‖ ≤ ‖x‖ := by
  have hx : x ∈ Metric.closedBall (0 : E) ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (le_rfl : ‖x‖ ≤ ‖x‖)
  have hP : K.starProjection x ∈ Metric.closedBall (0 : E) ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using K.norm_starProjection_apply_le x
  have h := normalFlatten_mem_convex K α (R (K.starProjection x))
    (convex_closedBall (0 : E) ‖x‖) hx hP
  simpa only [Metric.mem_closedBall, dist_zero_right, taperedNormalFlatten] using h

namespace HyperbolicSpace

variable {n : ℕ}

def kleinNormalFlatten (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (α : ℝ) (R : EuclideanSpace ℝ (Fin n) → ℝ) (x : HyperbolicSpace n) :
    HyperbolicSpace n := fromKlein (taperedNormalFlatten K α R (klein x))

lemma norm_tapered_klein_lt_one (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (α : ℝ) (R : EuclideanSpace ℝ (Fin n) → ℝ) (x : HyperbolicSpace n) :
    ‖taperedNormalFlatten K α R (klein x)‖ < 1 :=
  (norm_taperedNormalFlatten_le K α R (klein x)).trans_lt (norm_klein_lt_one x)

lemma klein_kleinNormalFlatten (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (α : ℝ) (R : EuclideanSpace ℝ (Fin n) → ℝ) (x : HyperbolicSpace n) :
    klein (kleinNormalFlatten K α R x) = taperedNormalFlatten K α R (klein x) :=
  klein_fromKlein (norm_tapered_klein_lt_one K α R x)

lemma kleinNormalFlatten_projection (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (α : ℝ) (R : EuclideanSpace ℝ (Fin n) → ℝ) (x : HyperbolicSpace n) :
    geodesicProjection K (kleinNormalFlatten K α R x) = geodesicProjection K x := by
  apply klein_injective
  rw [klein_geodesicProjection, klein_geodesicProjection, klein_kleinNormalFlatten,
    taperedNormalFlatten_projection]

lemma kleinNormalFlatten_nested_projection {J K : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    (hJK : J ≤ K) (α : ℝ) (R : EuclideanSpace ℝ (Fin n) → ℝ) (x : HyperbolicSpace n) :
    geodesicProjection J (kleinNormalFlatten K α R x) = geodesicProjection J x := by
  calc
    _ = geodesicProjection J (geodesicProjection K (kleinNormalFlatten K α R x)) :=
      (geodesicProjection_nested hJK _).symm
    _ = geodesicProjection J (geodesicProjection K x) := by rw [kleinNormalFlatten_projection]
    _ = _ := geodesicProjection_nested hJK x

/-- Complete nested normal-projection compatibility.  The two base points
may differ; the base point of the larger plane need not belong to the smaller
one.  Hyperbolic Pythagoras identifies the two minimization problems. -/
theorem affineGeodesicProjection_nested_of_subset
    (a b : HyperbolicSpace n) (J K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hJK : affineGeodesicPlane a J ⊆ affineGeodesicPlane b K) (x : HyperbolicSpace n) :
    affineGeodesicProjection a J (affineGeodesicProjection b K x) =
      affineGeodesicProjection a J x := by
  let p := affineGeodesicProjection b K x
  let q := affineGeodesicProjection a J p
  let r := affineGeodesicProjection a J x
  have hqJ : q ∈ affineGeodesicPlane a J := affineGeodesicProjection_mem a J p
  have hrJ : r ∈ affineGeodesicPlane a J := affineGeodesicProjection_mem a J x
  apply affineGeodesicProjection_nearest_unique a J x hqJ
  have hnear : dist p q ≤ dist p r := affineGeodesicProjection_nearest a J p hrJ
  have hc : Real.cosh (dist p q) ≤ Real.cosh (dist p r) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg] using hnear
  have hqP := affineGeodesicProjection_pythagoras b K x (hJK hqJ)
  have hrP := affineGeodesicProjection_pythagoras b K x (hJK hrJ)
  apply (dist_le_iff_coshDist_le x q x r).mpr
  rw [← cosh_dist, ← cosh_dist, hqP, hrP]
  exact mul_le_mul_of_nonneg_left hc (Real.cosh_pos (dist x p)).le

theorem hyperbolicCellProjection_comp_plane_of_subset
    (b : HyperbolicSpace n) (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (V : Finset (HyperbolicSpace n)) (hV : V.Nonempty)
    (hVK : hyperbolicCell V ⊆ affineGeodesicPlane b K) (x : HyperbolicSpace n) :
    hyperbolicCellProjection V hV (affineGeodesicProjection b K x) =
      hyperbolicCellProjection V hV x := by
  let p := affineGeodesicProjection b K x
  let q := hyperbolicCellProjection V hV p
  let r := hyperbolicCellProjection V hV x
  have hqV : q ∈ hyperbolicCell V := hyperbolicCellProjection_mem V hV p
  have hrV : r ∈ hyperbolicCell V := hyperbolicCellProjection_mem V hV x
  apply hyperbolicCellProjection_unique V hV x hqV
  have hnear : dist p q ≤ dist p r := hyperbolicCellProjection_nearest V hV p hrV
  have hc : Real.cosh (dist p q) ≤ Real.cosh (dist p r) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg] using hnear
  have hqP := affineGeodesicProjection_pythagoras b K x (hVK hqV)
  have hrP := affineGeodesicProjection_pythagoras b K x (hVK hrV)
  apply (dist_le_iff_coshDist_le x q x r).mpr
  rw [← cosh_dist, ← cosh_dist, hqP, hrP]
  exact mul_le_mul_of_nonneg_left hc (Real.cosh_pos (dist x p)).le

lemma kleinNormalFlatten_inner (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {α : ℝ} (hα1 : α < 1) (R : EuclideanSpace ℝ (Fin n) → ℝ) {x : HyperbolicSpace n}
    (hin : ‖klein x - K.starProjection (klein x)‖ ≤ α * R (K.starProjection (klein x))) :
    kleinNormalFlatten K α R x = geodesicProjection K x := by
  unfold kleinNormalFlatten geodesicProjection
  rw [taperedNormalFlatten_inner K hα1 R hin]

lemma kleinNormalFlatten_outer (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (R : EuclideanSpace ℝ (Fin n) → ℝ)
    {x : HyperbolicSpace n}
    (hout : R (K.starProjection (klein x)) ≤ ‖klein x - K.starProjection (klein x)‖) :
    kleinNormalFlatten K α R x = x := by
  unfold kleinNormalFlatten
  rw [taperedNormalFlatten_outer K hα0 hα1 R hout, fromKlein_klein]

lemma kleinNormalFlatten_fix (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (R : EuclideanSpace ℝ (Fin n) → ℝ)
    (hR : ∀ z ∈ K, 0 ≤ R z) {x : HyperbolicSpace n} (hx : x ∈ geodesicPlane K) :
    kleinNormalFlatten K α R x = x := by
  have hproj : K.starProjection (klein x) = klein x :=
    K.starProjection_eq_self_iff.mpr ((klein_mem_iff K x).mpr hx)
  have hin : ‖klein x - K.starProjection (klein x)‖ ≤ α * R (K.starProjection (klein x)) := by
    rw [hproj, sub_self, norm_zero]
    exact mul_nonneg hα0 (hR _ ((klein_mem_iff K x).mpr hx))
  rw [kleinNormalFlatten_inner K hα1 R hin, geodesicProjection_fix K hx]

theorem kleinNormalFlatten_continuous (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    (hRlip : ∀ z ∈ K, ∀ w ∈ K, |R z - R w| ≤ c * dist z w) :
    Continuous (kleinNormalFlatten K α R) := by
  apply continuousOn_fromKlein.comp_continuous
    ((taperedNormalFlatten_continuous K hα0 hα1 hc R hR hRlip).comp continuous_klein)
  intro x
  simpa only [Metric.mem_ball, dist_zero_right, Function.comp_def] using
    norm_tapered_klein_lt_one K α R x

theorem kleinNormalFlatten_mem_hyperbolicCell (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (α : ℝ) (R : EuclideanSpace ℝ (Fin n) → ℝ) (V : Finset (HyperbolicSpace n))
    {x : HyperbolicSpace n} (hx : x ∈ hyperbolicCell V)
    (hPx : geodesicProjection K x ∈ hyperbolicCell V) :
    kleinNormalFlatten K α R x ∈ hyperbolicCell V := by
  classical
  apply (mem_hyperbolicCell_iff_klein_mem_convexHull V _).mpr
  rw [klein_kleinNormalFlatten]
  apply normalFlatten_mem_convex K α (R (K.starProjection (klein x))) (convex_convexHull ℝ _)
  · exact (mem_hyperbolicCell_iff_klein_mem_convexHull V x).mp hx
  · simpa only [klein_geodesicProjection] using
      (mem_hyperbolicCell_iff_klein_mem_convexHull V _).mp hPx

theorem kleinNormalFlatten_lipschitz_on_chart
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {ρ α c : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    (hRlip : ∀ z ∈ K, ∀ w ∈ K, |R z - R w| ≤ c * dist z w)
    {x y : HyperbolicSpace n} (hx : ‖klein x‖ ≤ ρ) (hy : ‖klein y‖ ≤ ρ) :
    dist (kleinNormalFlatten K α R x) (kleinNormalFlatten K α R y) ≤
      ((1 - ρ ^ 2)⁻¹ * ((1 + α * c) / (1 - α))) * dist x y := by
  have hρ : 0 ≤ (1 - ρ ^ 2)⁻¹ := by
    apply inv_nonneg.mpr
    nlinarith
  have hL : 0 ≤ (1 + α * c) / (1 - α) := by positivity
  calc
    _ ≤ (1 - ρ ^ 2)⁻¹ * ‖taperedNormalFlatten K α R (klein x) -
        taperedNormalFlatten K α R (klein y)‖ :=
      dist_fromKlein_le hρ0 hρ1 ((norm_taperedNormalFlatten_le K α R _).trans hx)
        ((norm_taperedNormalFlatten_le K α R _).trans hy)
    _ ≤ (1 - ρ ^ 2)⁻¹ * (((1 + α * c) / (1 - α)) * dist (klein x) (klein y)) := by
      apply mul_le_mul_of_nonneg_left _ hρ
      simpa only [dist_eq_norm] using taperedNormalFlatten_lipschitz K hα0 hα1 hc R hR hRlip
        (klein x) (klein y)
    _ ≤ (1 - ρ ^ 2)⁻¹ * (((1 + α * c) / (1 - α)) * dist x y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (klein_dist_le x y) hL) hρ
    _ = _ := by ring

theorem kleinNormalFlatten_displacement_on_chart
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {ρ α : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    {x : HyperbolicSpace n} (hx : ‖klein x‖ ≤ ρ) :
    dist (kleinNormalFlatten K α R x) x ≤
      (1 - ρ ^ 2)⁻¹ * (α * R (K.starProjection (klein x))) := by
  have hρ : 0 ≤ (1 - ρ ^ 2)⁻¹ := by
    apply inv_nonneg.mpr
    nlinarith
  have h := dist_fromKlein_le hρ0 hρ1 ((norm_taperedNormalFlatten_le K α R _).trans hx) hx
  rw [fromKlein_klein] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hρ
  simpa only [dist_eq_norm] using taperedNormalFlatten_displacement K hα0 hα1 R hR (klein x)

/-- The same genuine construction around a plane through an arbitrary base point. -/
def affineKleinNormalFlatten (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (x : HyperbolicSpace n) : HyperbolicSpace n :=
  (boostEquiv a.point).symm (kleinNormalFlatten K α R (boostEquiv a.point x))

lemma affineKleinNormalFlatten_inner (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {α : ℝ} (hα1 : α < 1)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) {x : HyperbolicSpace n}
    (hin : ‖klein (boostEquiv a.point x) - K.starProjection (klein (boostEquiv a.point x))‖ ≤
      α * R (K.starProjection (klein (boostEquiv a.point x)))) :
    affineKleinNormalFlatten a K α R x = affineGeodesicProjection a K x := by
  unfold affineKleinNormalFlatten affineGeodesicProjection
  rw [kleinNormalFlatten_inner K hα1 R hin]

lemma affineKleinNormalFlatten_outer (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) {x : HyperbolicSpace n}
    (hout : R (K.starProjection (klein (boostEquiv a.point x))) ≤
      ‖klein (boostEquiv a.point x) - K.starProjection (klein (boostEquiv a.point x))‖) :
    affineKleinNormalFlatten a K α R x = x := by
  unfold affineKleinNormalFlatten
  rw [kleinNormalFlatten_outer K hα0 hα1 R hout, (boostEquiv a.point).symm_apply_apply]

theorem affineKleinNormalFlatten_continuous (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    (hRlip : ∀ z ∈ K, ∀ w ∈ K, |R z - R w| ≤ c * dist z w) :
    Continuous (affineKleinNormalFlatten a K α R) := by
  exact (boostEquiv a.point).symm.continuous.comp
    ((kleinNormalFlatten_continuous K hα0 hα1 hc R hR hRlip).comp (boostEquiv a.point).continuous)

theorem affineKleinNormalFlatten_mem_hyperbolicCell (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (V : Finset (HyperbolicSpace n))
    {x : HyperbolicSpace n} (hx : x ∈ hyperbolicCell V)
    (hPx : affineGeodesicProjection a K x ∈ hyperbolicCell V) :
    affineKleinNormalFlatten a K α R x ∈ hyperbolicCell V := by
  classical
  let W := V.image (boostBy a.point)
  have hmap {z : HyperbolicSpace n} (hz : z ∈ hyperbolicCell V) :
      boostEquiv a.point z ∈ hyperbolicCell W :=
    mem_hyperbolicCell_image_of_linear_lift (boostEquiv a.point)
      (Hyperboloid.boostLinear a.point) (fun z => (lift_boostBy a.point z).symm) V hz
  have hx' := hmap hx
  have hPx' := hmap hPx
  rw [boost_affineGeodesicProjection] at hPx'
  have hout := kleinNormalFlatten_mem_hyperbolicCell K α R W hx' hPx'
  change kleinNormalFlatten K α R (boostEquiv a.point x) ∈
    hyperbolicCell (V.image (boostBy a.point)) at hout
  rw [← hyperbolicCell_image_boost a.point V] at hout
  obtain ⟨z, hz, heq⟩ := hout
  have hresult : affineKleinNormalFlatten a K α R x = z := by
    apply (boostEquiv a.point).injective
    unfold affineKleinNormalFlatten
    rw [(boostEquiv a.point).apply_symm_apply]
    exact heq.symm
  rw [hresult]
  exact hz

lemma affineKleinNormalFlatten_projection (a : HyperbolicSpace n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (x : HyperbolicSpace n) :
    affineGeodesicProjection a K (affineKleinNormalFlatten a K α R x) =
      affineGeodesicProjection a K x := by
  unfold affineGeodesicProjection affineKleinNormalFlatten
  rw [(boostEquiv a.point).apply_symm_apply, kleinNormalFlatten_projection]

theorem affineKleinNormalFlatten_nested_projection
    (a b : HyperbolicSpace n) (J K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hJK : affineGeodesicPlane a J ⊆ affineGeodesicPlane b K)
    (α : ℝ) (R : EuclideanSpace ℝ (Fin n) → ℝ) (x : HyperbolicSpace n) :
    affineGeodesicProjection a J (affineKleinNormalFlatten b K α R x) =
      affineGeodesicProjection a J x := by
  calc
    _ = affineGeodesicProjection a J
        (affineGeodesicProjection b K (affineKleinNormalFlatten b K α R x)) :=
      (affineGeodesicProjection_nested_of_subset a b J K hJK _).symm
    _ = affineGeodesicProjection a J (affineGeodesicProjection b K x) := by
      rw [affineKleinNormalFlatten_projection]
    _ = _ := affineGeodesicProjection_nested_of_subset a b J K hJK x

theorem affineKleinNormalFlatten_lipschitz_on_chart
    (a : HyperbolicSpace n) (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {ρ α c : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    (hRlip : ∀ z ∈ K, ∀ w ∈ K, |R z - R w| ≤ c * dist z w)
    {x y : HyperbolicSpace n} (hx : ‖klein (boostEquiv a.point x)‖ ≤ ρ)
    (hy : ‖klein (boostEquiv a.point y)‖ ≤ ρ) :
    dist (affineKleinNormalFlatten a K α R x) (affineKleinNormalFlatten a K α R y) ≤
      ((1 - ρ ^ 2)⁻¹ * ((1 + α * c) / (1 - α))) * dist x y := by
  simpa only [affineKleinNormalFlatten, (boostEquiv a.point).symm.dist_eq,
    (boostEquiv a.point).dist_eq] using
    kleinNormalFlatten_lipschitz_on_chart K hρ0 hρ1 hα0 hα1 hc R hR hRlip hx hy

theorem affineKleinNormalFlatten_displacement_on_chart
    (a : HyperbolicSpace n) (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {ρ α : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (R : EuclideanSpace ℝ (Fin n) → ℝ) (hR : ∀ z ∈ K, 0 ≤ R z)
    {x : HyperbolicSpace n} (hx : ‖klein (boostEquiv a.point x)‖ ≤ ρ) :
    dist (affineKleinNormalFlatten a K α R x) x ≤
      (1 - ρ ^ 2)⁻¹ * (α * R (K.starProjection (klein (boostEquiv a.point x)))) := by
  have h := kleinNormalFlatten_displacement_on_chart K hρ0 hρ1 hα0 hα1 R hR hx
  have hd : dist (affineKleinNormalFlatten a K α R x) x =
      dist (kleinNormalFlatten K α R (boostEquiv a.point x)) (boostEquiv a.point x) := by
    rw [← (boostEquiv a.point).dist_eq (affineKleinNormalFlatten a K α R x) x]
    unfold affineKleinNormalFlatten
    rw [(boostEquiv a.point).apply_symm_apply]
  rwa [hd]

/-- The actual local Lipschitz coefficient tends to one as both the chart and
the flattening parameter shrink. -/
theorem flattening_constant_tendsto_one (c : ℝ) :
    Filter.Tendsto (fun p : ℝ × ℝ => (1 - p.1 ^ 2)⁻¹ * ((1 + p.2 * c) / (1 - p.2)))
      (𝓝 (0, 0)) (𝓝 1) := by
  have h : ContinuousAt
      (fun p : ℝ × ℝ => (1 - p.1 ^ 2)⁻¹ * ((1 + p.2 * c) / (1 - p.2))) (0, 0) := by
    fun_prop (disch := norm_num)
  simpa using h.tendsto

end HyperbolicSpace
end BrehmApprox
