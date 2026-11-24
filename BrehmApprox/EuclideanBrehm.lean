module

public import BrehmApprox.AffineArrangement
public import BrehmApprox.EuclideanFiniteMotions
public import BrehmApprox.EuclideanRigidity

/-!
# Brehm's Euclidean extension theorem

Bounded radial corrections give finite interpolation with locally finite
affine-motion selections. The affine-arrangement theorem turns those
selections into actual finite polyhedral pieces.
-/

@[expose] public section
noncomputable section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem euclideanPLOn_of_finite_motions
    (V : Finset E) {f : E → E}
    (hf : ContinuousOn f (convexHull ℝ (V : Set E)))
    (S : Finset (E ≃ᵃⁱ[ℝ] E))
    (hS : ∀ x ∈ convexHull ℝ (V : Set E), ∃ r ∈ S, f x = r x) :
    EuclideanPLOn (convexHull ℝ (V : Set E)) f := by
  obtain ⟨C, hC, hpieces⟩ := finite_selection_affine_polytope_cover V
    (fun r : S => r.val.toAffineMap) hf
    (fun x hx => by obtain ⟨r, hr, heq⟩ := hS x hx; exact ⟨⟨r, hr⟩, heq⟩)
  refine ⟨C, hC, ?_⟩
  intro W hW
  obtain ⟨r, hr⟩ := hpieces W hW
  exact ⟨r.val, hr⟩

theorem locallyEuclideanPL_of_locallyFinite_motions
    {f : E → E} (hf : Continuous f) (hm : LocallyFiniteEuclideanMotions f) :
    LocallyEuclideanPL f := by
  intro V
  obtain ⟨R, hR⟩ := (V.finite_toSet.isCompact_convexHull ℝ).isBounded.exists_norm_le
  obtain ⟨S, hS⟩ := hm R
  exact euclideanPLOn_of_finite_motions V hf.continuousOn S
    (fun x hx => hS x (hR x hx))

/-- Finite short Euclidean data have a global locally PL-isometric extension. -/
theorem euclideanBrehm_proved (n : ℕ) :
    FiniteExtension (LocallyEuclideanPL (E := EuclideanSpace ℝ (Fin n))) := by
  intro s f hf
  obtain ⟨h, hh, hm, heq⟩ := euclidean_finite_extension_motions n s f hf
  have hLip : LipschitzWith 1 h := LipschitzWith.of_dist_le_mul (by
    intro x y
    simpa only [NNReal.coe_one, one_mul] using hh x y)
  exact ⟨h, hh, locallyEuclideanPL_of_locallyFinite_motions hLip.continuous hm, heq⟩

end BrehmApprox
