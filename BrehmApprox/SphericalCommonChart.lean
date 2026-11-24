module

public import BrehmApprox.SphericalFaceTransport
public import BrehmApprox.SphericalLocalCharts

/-!
# A total central chart and quantitative common-cap transport

The chart is extended by zero outside its hemisphere solely to provide an
ordinary total function. All geometric claims use its genuine hemisphere
domain, and the quantitative assertions use an explicitly smaller spherical
cap. Exact core images link the concrete finite face transport to the
Euclidean intrinsic chain construction.
-/

@[expose] public section

noncomputable section

namespace GeodesicSphere

variable {n : ℕ}

def gnomonicTotal (p : GeodesicSphere n) (x : GeodesicSphere n) : tangentPlane p := by
  classical
  exact if hx : x ∈ openHemisphere p then gnomonic p ⟨x, hx⟩ else 0

lemma gnomonicTotal_apply (p : GeodesicSphere n) {x : GeodesicSphere n}
    (hx : x ∈ openHemisphere p) : gnomonicTotal p x = gnomonic p ⟨x, hx⟩ := by
  classical
  simp only [gnomonicTotal, dite_eq_left hx]

@[simp]
lemma gnomonicTotal_gnomonicPoint (p : GeodesicSphere n) (z : tangentPlane p) :
    gnomonicTotal p (gnomonicPoint p z) = z := by
  rw [gnomonicTotal_apply p (gnomonicPoint_mem p z)]
  exact gnomonic_gnomonicInverse p z

lemma gnomonicPoint_gnomonicTotal (p : GeodesicSphere n) {x : GeodesicSphere n}
    (hx : x ∈ openHemisphere p) : gnomonicPoint p (gnomonicTotal p x) = x := by
  rw [gnomonicTotal_apply p hx]
  exact congrArg Subtype.val (gnomonicInverse_gnomonic p ⟨x, hx⟩)

lemma gnomonicTotal_injOn (p : GeodesicSphere n) : Set.InjOn (gnomonicTotal p) (openHemisphere p) := by
  intro x hx y hy heq
  have h := congrArg (gnomonicPoint p) heq
  rwa [gnomonicPoint_gnomonicTotal p hx, gnomonicPoint_gnomonicTotal p hy] at h

lemma continuousOn_gnomonicTotal (p : GeodesicSphere n) :
    ContinuousOn (gnomonicTotal p) (openHemisphere p) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have heq : (openHemisphere p).domRestrict (gnomonicTotal p) = gnomonic p := by
    funext x
    exact gnomonicTotal_apply p x.property
  rw [heq]
  exact continuous_gnomonic p

/-- The image of an actual hemispherical set equals the inverse image under
the explicit inverse central map. -/
theorem gnomonicTotal_image_eq_preimage (p : GeodesicSphere n)
    {A : Set (GeodesicSphere n)} (hA : A ⊆ openHemisphere p) :
    gnomonicTotal p '' A = gnomonicPoint p ⁻¹' A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change gnomonicPoint p (gnomonicTotal p x) ∈ A
    rwa [gnomonicPoint_gnomonicTotal p (hA hx)]
  · intro hz
    exact ⟨gnomonicPoint p z, hz, gnomonicTotal_gnomonicPoint p z⟩

lemma one_le_gnomonicFactor {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρπ : ρ < Real.pi / 2) :
    1 ≤ gnomonicFactor ρ := by
  have hc : 0 < Real.cos ρ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hρπ⟩
  have hsec : 1 ≤ (Real.cos ρ)⁻¹ := (one_le_inv₀ hc).mpr (Real.cos_le_one ρ)
  have hnonneg : 0 ≤ ρ / (Real.cos ρ) ^ 2 := div_nonneg hρ0 (sq_nonneg _)
  exact hsec.trans (le_add_of_nonneg_right hnonneg)

lemma one_le_inv_sinc {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρπ : ρ < Real.pi / 2) :
    1 ≤ (Real.sinc ρ)⁻¹ := by
  have hs : 0 < Real.sinc ρ := Real.sinc_pos (by rw [abs_of_nonneg hρ0]; linarith [Real.pi_pos])
  exact (one_le_inv₀ hs).mpr (Real.sinc_le_one ρ)

/-- The actual total chart has the near-unit Lipschitz bound on every cap
strictly contained in its hemisphere. -/
theorem gnomonicTotal_dist_le (p : GeodesicSphere n) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρπ : ρ < Real.pi / 2) (x y : GeodesicSphere n)
    (hx : dist p x ≤ ρ) (hy : dist p y ≤ ρ) :
    dist (gnomonicTotal p x) (gnomonicTotal p y) ≤ gnomonicFactor ρ * dist x y := by
  have hxp : x ∈ openHemisphere p := (dist_lt_pi_div_two_iff p x).mp (hx.trans_lt hρπ)
  have hyp : y ∈ openHemisphere p := (dist_lt_pi_div_two_iff p y).mp (hy.trans_lt hρπ)
  rw [gnomonicTotal_apply p hxp, gnomonicTotal_apply p hyp]
  exact gnomonic_dist_le p hρ0 hρπ ⟨x, hxp⟩ ⟨y, hyp⟩ hx hy

/-- The inverse bound for any two points in the same concrete spherical cap. -/
theorem dist_le_gnomonicTotal_dist (p : GeodesicSphere n) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi / 2) (x y : GeodesicSphere n)
    (hx : dist p x ≤ ρ) (hy : dist p y ≤ ρ) :
    dist x y ≤ (Real.sinc ρ)⁻¹ * dist (gnomonicTotal p x) (gnomonicTotal p y) := by
  have hxp : x ∈ openHemisphere p := (dist_lt_pi_div_two_iff p x).mp (hx.trans_lt hρπ)
  have hyp : y ∈ openHemisphere p := (dist_lt_pi_div_two_iff p y).mp (hy.trans_lt hρπ)
  rw [gnomonicTotal_apply p hxp, gnomonicTotal_apply p hyp]
  exact dist_le_gnomonic_dist p hρ0 hρπ ⟨x, hxp⟩ ⟨y, hyp⟩ hx hy

/-- The two chart distortions have product tending to one, so every fixed
strict Lipschitz margin survives a sufficiently small common chart. -/
theorem exists_gnomonic_distortion_margin {k : ℝ} (hk : k < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 2 ∧
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ δ → k * gnomonicFactor ρ * (Real.sinc ρ)⁻¹ < 1 := by
  have hcont : ContinuousAt (fun ρ : ℝ => k * gnomonicFactor ρ * (Real.sinc ρ)⁻¹) 0 :=
    (continuousAt_const.mul continuousAt_gnomonicFactor).mul
      (Real.continuous_sinc.continuousAt.inv₀ (by simp))
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp hcont (1 - k) (by linarith)
  let δ := min (η / 2) (Real.pi / 4)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hδπ : δ < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  refine ⟨δ, hδ0, hδπ, ?_⟩
  intro ρ hρ0 hρδ
  have hd : dist ρ 0 < η := by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hρ0] using hρδ.trans_lt hδη
  have h := hηbound hd
  simp only [gnomonicFactor_zero, Real.sinc_zero, inv_one, mul_one, Real.dist_eq] at h
  have hu := (abs_lt.mp h).2
  linarith

end GeodesicSphere

namespace BrehmApprox.SphericalSimplicialFaceData

open GeodesicSphere

variable {n N : ℕ} {D : PolyhedralFaceData (sphericalPolytopeModel n) N}
  (T : SphericalSimplicialFaceData D) (p : GeodesicSphere n)
  (hp : ∀ i, ∀ v ∈ T.vertices i, 0 < inner ℝ p.val v.val)

lemma gnomonicFaceData_core_eq_image (i : Fin N) :
    (T.gnomonicFaceData p hp).core i = gnomonicTotal p '' D.core i := by
  rw [T.gnomonicFaceData_core p hp i,
    gnomonicTotal_image_eq_preimage p (T.core_subset_hemisphere p hp i)]

include T hp in
lemma gnomonicTotal_injective_core (i : Fin N) : Set.InjOn (gnomonicTotal p) (D.core i) :=
  (gnomonicTotal_injOn p).mono (T.core_subset_hemisphere p hp i)

end BrehmApprox.SphericalSimplicialFaceData
