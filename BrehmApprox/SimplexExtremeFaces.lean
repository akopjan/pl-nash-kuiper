module

public import BrehmApprox.SimplexFaces
public import BrehmApprox.ExtremeBarycentricSupport

/-! # Vertex faces of a simplex are extreme subsets -/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance simplexExtremeDecidableEq : DecidableEq E := Classical.decEq _

theorem simplex_weights_zero_outside_face
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    {U : Finset E} (hUV : U ⊆ V) (w : E → ℝ)
    (hw1 : ∑ v ∈ V, w v = 1) {x : E}
    (hwx : ∑ v ∈ V, w v • v = x) (hx : x ∈ convexHull ℝ (U : Set E)) :
    ∀ v ∈ V, v ∉ U → w v = 0 := by
  obtain ⟨u, _, hu1, hux⟩ := Finset.mem_convexHull'.mp hx
  let u' : E → ℝ := fun v => if v ∈ U then u v else 0
  have hu'1 : ∑ v ∈ V, u' v = 1 := by
    calc
      _ = ∑ v ∈ U, u' v :=
        (Finset.sum_subset hUV (fun v _ hv => by simp [u', hv])).symm
      _ = 1 := by simpa only [u', Finset.sum_ite_mem, Finset.inter_self] using hu1
  have hu'x : ∑ v ∈ V, u' v • v = x := by
    calc
      _ = ∑ v ∈ U, u' v • v :=
        (Finset.sum_subset hUV (fun v _ hv => by simp [u', hv])).symm
      _ = x := by
        convert hux using 1
        apply Finset.sum_congr rfl
        intro v hv
        simp only [u', ite_eq_left hv]
  have he := hV.eq_of_sum_eq_sum_subtype (hw1.trans hu'1.symm) (hwx.trans hu'x.symm)
  intro v hv hvU
  simpa only [u', ite_eq_right hvU] using he v hv

theorem simplex_face_isExtreme
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    {U : Finset E} (hUV : U ⊆ V) :
    _root_.IsExtreme ℝ (convexHull ℝ (V : Set E)) (convexHull ℝ (U : Set E)) := by
  refine ⟨convexHull_mono (Finset.coe_subset.mpr hUV), ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, habz⟩ := hseg
  obtain ⟨w, hw, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨u, hu, hu1, huy⟩ := Finset.mem_convexHull'.mp hy
  have hsum : ∑ v ∈ V, (a * w v + b * u v) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, hu1]
    simpa only [mul_one] using hab
  have hrep : ∑ v ∈ V, (a * w v + b * u v) • v = z := by
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hwx, huy]
    exact habz
  have hzcoeff := simplex_weights_zero_outside_face V hV hUV
    (fun v => a * w v + b * u v) hsum hrep hz
  have hwzero (v : E) (hv : v ∈ V) (hvU : v ∉ U) : w v = 0 := by
    have he := hzcoeff v hv hvU
    have hbu := mul_nonneg hb.le (hu v hv)
    have haw := mul_nonneg ha.le (hw v hv)
    have haw0 : a * w v = 0 := by linarith
    exact (mul_eq_zero.mp haw0).resolve_left ha.ne'
  exact Finset.mem_convexHull'.mpr ⟨w, fun v hv => hw v (hUV hv),
    (Finset.sum_subset hUV hwzero).trans hw1,
    (Finset.sum_subset hUV (fun v hv hvU => by rw [hwzero v hv hvU, zero_smul])).trans hwx⟩

end BrehmApprox
