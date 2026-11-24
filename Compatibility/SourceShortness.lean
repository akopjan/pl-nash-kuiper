module

public import Compatibility.Models
public import Compatibility.SourceDistance

/-! Original short maps are short on every model simplex. -/

@[expose] public section
noncomputable section

open scoped NNReal

namespace PLGeometry

theorem modelDist_nonneg (κ : Geometry) (n : ℕ) (x y : Model κ n) :
    0 ≤ modelDist κ n x y := by
  rw [← modelEquiv_dist]
  exact dist_nonneg

theorem Lipschitz.modelEquiv_cellwise {κ : Geometry} {d m n : ℕ}
    {K : Polyhedron κ d m} {f : ↥K.K.space → Model κ n} {L : ℝ≥0}
    (hf : Lipschitz K f L) (σ : Finset (E m)) (hσ : σ ∈ K.K.faces)
    (x y : ↥K.K.space) (hx : x.val ∈ cell σ) (hy : y.val ∈ cell σ) :
    dist (modelEquiv κ n (f x)) (modelEquiv κ n (f y)) ≤
      (L : ℝ) * modelDist κ d ((K.simplex σ hσ).toModel x.val)
        ((K.simplex σ hσ).toModel y.val) := by
  have he := (hf x y).trans (mul_le_mul_of_nonneg_left
    (K.intrinsicEDist_le_chart σ hσ x y hx hy) (bot_le : 0 ≤ (L : ENNReal)))
  have htop : (L : ENNReal) * ENNReal.ofReal
      (modelDist κ d ((K.simplex σ hσ).toModel x.val)
        ((K.simplex σ hσ).toModel y.val)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop he
  rw [modelEquiv_dist]
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (modelDist_nonneg κ n (f x) (f y)),
    ENNReal.toReal_ofReal (modelDist_nonneg κ d
      ((K.simplex σ hσ).toModel x.val) ((K.simplex σ hσ).toModel y.val))] using hreal

end PLGeometry
