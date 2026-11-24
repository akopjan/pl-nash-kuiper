module

public import BrehmApprox.SphericalActiveProjection
public import BrehmApprox.FiniteGramIsometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Nearest projection near the positive part of a spherical simplex

The coefficients of orthogonal projection in the actual vertex basis are
continuous. At a point with strictly positive simplex coordinates they remain
positive on a neighborhood. Hence projection to the vertex cone agrees there
with ordinary orthogonal projection to its span, and spherical nearest
projection agrees with genuine great-sphere projection.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace BrehmApprox

open GeodesicSphere

variable {n : ℕ}

lemma span_range_vertices_eq (V : Finset (GeodesicSphere n)) :
    Submodule.span ℝ (Set.range (fun v : V => v.val.val)) = sphericalVertexSpan V := by
  congr 1
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.val, v.property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact Set.mem_range_self (⟨v, hv⟩ : V)

/-- Actual orthogonal projections into the supporting span have positive
vertex coordinates near any positive point of an independent simplex. -/
theorem starProjection_eventually_mem_vertexCone
    (V : Finset (GeodesicSphere n))
    (hlin : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ positiveSphericalCell V) :
    ∀ᶠ x in 𝓝 p, (sphericalVertexSpan V).starProjection x.val ∈ vertexCone V := by
  classical
  obtain ⟨w, hw, a, ha, hrep⟩ := hp
  let W := Submodule.span ℝ (Set.range (fun v : V => v.val.val))
  let B : Module.Basis V ℝ W := Module.Basis.span hlin
  have hB (v : V) : (B v).val = v.val.val := Module.Basis.coe_span_apply hlin v
  have hW : W = sphericalVertexSpan V := span_range_vertices_eq V
  have hpW : p.val ∈ W := by
    rw [hW]
    exact vertexCone_subset_vertexSpan V ((mem_vertexCone_unit_iff V p).mpr
      ⟨w, fun v hv => (hw v hv).le, a, ha, hrep⟩)
  let pW : W := ⟨p.val, hpW⟩
  have hPp : W.orthogonalProjectionOnto p.val = pW := by
    apply Subtype.ext
    exact W.starProjection_eq_self_iff.mpr hpW
  have hrep' : ∑ v ∈ V, (w v / a) • v.val = p.val := by
    calc
      _ = a⁻¹ • ∑ v ∈ V, w v • v.val := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro v _
        simp only [div_eq_mul_inv, smul_smul, mul_comm]
      _ = a⁻¹ • (a • p.val) := congrArg (fun z => a⁻¹ • z) hrep
      _ = p.val := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  have hpRep : ∑ v : V, (w v.val / a) • B v = pW := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ v : V, (w v.val / a) • (B v).val) = p.val
    simp only [hB]
    rw [Finset.univ_eq_attach]
    exact (Finset.sum_attach V (fun v => (w v / a) • v.val)).trans hrep'
  let coeff : V → GeodesicSphere n → ℝ := fun i x => B.repr (W.orthogonalProjectionOnto x.val) i
  have hcoef (i : V) : coeff i p = w i.val / a := by
    dsimp only [coeff]
    rw [hPp, ← hpRep]
    exact congrFun (B.repr_sum_self (fun v : V => w v.val / a)) i
  have hcont (i : V) : Continuous (coeff i) :=
    (continuous_apply i).comp (B.continuous_coe_repr.comp
      (W.orthogonalProjectionOnto.continuous.comp continuous_val))
  have hpos : ∀ᶠ x in 𝓝 p, ∀ i : V, 0 < coeff i x := by
    apply Filter.eventually_all.mpr
    intro i
    have hpcoef : 0 < coeff i p := by rw [hcoef]; exact div_pos (hw i.val i.property) ha
    exact (hcont i).continuousAt.eventually (isOpen_Ioi.mem_nhds hpcoef)
  filter_upwards [hpos] with x hx
  let u : GeodesicSphere n → ℝ := fun v => if hv : v ∈ V then coeff ⟨v, hv⟩ x else 0
  have hu (v : V) : u v.val = coeff v x := by simp only [u, dite_eq_left v.property]
  have hsum : (∑ v : V, coeff v x • v.val.val) = W.starProjection x.val := by
    have h := congrArg (fun z : W => z.val) (B.sum_repr (W.orthogonalProjectionOnto x.val))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    change (∑ v : V, coeff v x • (B v).val) = W.starProjection x.val at h
    simpa only [hB] using h
  rw [← hW]
  refine ⟨u, ?_, ?_⟩
  · intro v hv
    simpa only [u, dite_eq_left hv] using (hx ⟨v, hv⟩).le
  · calc
      _ = ∑ v : V, u v.val • v.val.val := by
        rw [Finset.univ_eq_attach]
        exact (Finset.sum_attach V (fun v => u v • v.val)).symm
      _ = ∑ v : V, coeff v x • v.val.val := by simp only [hu]
      _ = _ := hsum

/-- The true cone projection agrees with projection onto the supporting
linear subspace near a positive simplex point. -/
theorem coneProjection_eventually_eq_starProjection
    (V : Finset (GeodesicSphere n)) (hV : InOpenHemisphere V)
    (hlin : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ positiveSphericalCell V) :
    ∀ᶠ x in 𝓝 p, coneProjection (sphericalCellCone V hV) x.val =
      (sphericalVertexSpan V).starProjection x.val := by
  filter_upwards [starProjection_eventually_mem_vertexCone V hlin hp] with x hx
  calc
    _ = coneProjection (sphericalCellCone V hV) ((sphericalVertexSpan V).starProjection x.val) :=
      (coneProjection_after_starProjection (sphericalCellCone V hV) (sphericalVertexSpan V)
        (fun _ hv => vertexCone_subset_vertexSpan V hv) x.val).symm
    _ = _ := coneProjection_fix (sphericalCellCone V hV) hx

/-- Actual spherical nearest projection is ordinary great-sphere projection
on a neighborhood of every point with positive simplex coordinates. -/
theorem sphericalCellProjection_eventually_eq_greatSphereProjection
    (V : Finset (GeodesicSphere n)) (hV : InOpenHemisphere V)
    (hlin : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ positiveSphericalCell V)
    (q : GeodesicSphere n) (hqL : q.val ∈ sphericalVertexSpan V) (hpq : p ∈ openHemisphere q) :
    ∀ᶠ x in 𝓝 p, ∃ hx : x ∈ openHemisphere q,
      sphericalCellProjection V hV x = (greatSphereProjection q (sphericalVertexSpan V) ⟨x, hx⟩).val := by
  filter_upwards [coneProjection_eventually_eq_starProjection V hV hlin hp,
    (isOpen_openHemisphere q).mem_nhds hpq] with x hx hxp
  refine ⟨hxp, ?_⟩
  have hn : coneProjection (sphericalCellCone V hV) x.val ≠ 0 := by
    rw [hx]
    exact ambientProjection_ne_zero q (sphericalVertexSpan V) hqL ⟨x, hxp⟩
  apply GeodesicSphere.ext
  rw [sphericalCellProjection, sphericalConeProjection_val (sphericalCellCone V hV) x hn,
    greatSphereProjection_val q (sphericalVertexSpan V) hqL, hx]

end BrehmApprox
