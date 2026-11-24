module

public import BrehmApprox.SimplexExtremeFaces
public import BrehmApprox.SimplexStellar
public import BrehmApprox.FiniteGramIsometry

/-! # Radial projection of the faces avoiding a simplex point -/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance radialBoundaryDecidableEq : DecidableEq E := Classical.decEq _

theorem eq_of_normalize_sub_eq_of_extreme
    {C D F : Set E} (hD : IsExtreme ℝ C D) (hF : IsExtreme ℝ C F)
    {p x y : E} (hp : p ∈ C) (hpD : p ∉ D) (hpF : p ∉ F)
    (hx : x ∈ D) (hy : y ∈ F)
    (he : NormedSpace.normalize (x - p) = NormedSpace.normalize (y - p)) : x = y := by
  have hxp : x - p ≠ 0 := fun h => hpD ((sub_eq_zero.mp h) ▸ hx)
  have hyp : y - p ≠ 0 := fun h => hpF ((sub_eq_zero.mp h) ▸ hy)
  have hxpos := norm_pos_iff.mpr hxp
  have hypos := norm_pos_iff.mpr hyp
  let t : ℝ := ‖x - p‖ / ‖y - p‖
  have ht : 0 < t := div_pos hxpos hypos
  have hvec : x - p = t • (y - p) := by
    calc
      x - p = ‖x - p‖ • NormedSpace.normalize (x - p) :=
        (NormedSpace.norm_smul_normalize _).symm
      _ = ‖x - p‖ • NormedSpace.normalize (y - p) := by rw [he]
      _ = t • (y - p) := by simp only [NormedSpace.normalize, smul_smul, t, div_eq_mul_inv]
  have hrad : p + t • (y - p) = x := by rw [← hvec]; abel
  have ht1 : t = 1 := by
    rcases lt_trichotomy t 1 with hlt | heq | hgt
    · exfalso
      apply hpD
      apply hD.left_mem_of_mem_openSegment hp (hF.subset hy) hx
      refine ⟨1 - t, t, sub_pos.mpr hlt, ht, by ring, ?_⟩
      rw [sub_smul, one_smul]
      calc
        p - t • p + t • y = p + t • (y - p) := by rw [smul_sub]; abel
        _ = x := hrad
    · exact heq
    · exfalso
      apply hpF
      apply hF.left_mem_of_mem_openSegment hp (hD.subset hx) hy
      have hi : 0 < t⁻¹ := inv_pos.mpr ht
      have hi1 : t⁻¹ < 1 := (inv_lt_one₀ ht).mpr hgt
      refine ⟨1 - t⁻¹, t⁻¹, sub_pos.mpr hi1, hi, by ring, ?_⟩
      have hv : t⁻¹ • (x - p) = y - p := by
        rw [hvec, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      calc
        (1 - t⁻¹) • p + t⁻¹ • x = p + t⁻¹ • (x - p) := by
          rw [sub_smul, one_smul, smul_sub]
          abel
        _ = y := by rw [hv]; abel
  rw [ht1, one_smul] at hvec
  simpa only [sub_add_cancel] using congrArg (fun z => z + p) hvec

def visibleBoundary (V : Finset E) (p : E) : Set E :=
  {x | ∃ U : Finset E, U ⊆ V ∧ p ∉ convexHull ℝ (U : Set E) ∧
    x ∈ convexHull ℝ (U : Set E)}

theorem radialProjection_injectiveOn_visibleBoundary
    (V : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    {p : E} (hp : p ∈ convexHull ℝ (V : Set E)) :
    Set.InjOn (fun x : E => NormedSpace.normalize (x - p)) (visibleBoundary V p) := by
  rintro x ⟨U, hUV, hpU, hx⟩ y ⟨W, hWV, hpW, hy⟩ he
  exact eq_of_normalize_sub_eq_of_extreme
    (simplex_face_isExtreme V hV hUV) (simplex_face_isExtreme V hV hWV)
    hp hpU hpW hx hy he

end BrehmApprox
