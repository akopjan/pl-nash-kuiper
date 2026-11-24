module

public import BrehmApprox.BarycentricReweighting
public import BrehmApprox.PositiveBarycentricGeometry

/-! # Convex hulls and independence under positive simplex reweighting -/

@[expose] public section
noncomputable section

namespace BrehmApprox.BarycentricReweighting

variable {ι J : Type*} [Fintype ι] [Fintype J]

/-- The diagonal homogeneous-coordinate map underlying reweighting. -/
def diagonal (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun w i := a i * w i
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' c x := by ext i; change a i * (c * x i) = c * (a i * x i); ring

theorem diagonal_injective (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Function.Injective (diagonal a) := by
  intro x y h
  funext i
  exact mul_left_cancel₀ (ha i).ne' (congrFun h i)

theorem diagonal_reweight (a : ι → ℝ) (ha : ∀ i, 0 < a i) (w : Weights ι) :
    diagonal a w.val = total a w.val • (reweight a ha w).val := by
  ext i
  change a i * w.val i = total a w.val * (a i * w.val i / total a w.val)
  field_simp [(total_pos a ha w).ne']

/-- Positive reweighting carries every subsimplex onto the subsimplex spanned
by the reweighted vertices. -/
theorem reweight_mem_convexHull_iff (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (w : J → Weights ι) (x : Weights ι) :
    (reweight a ha x).val ∈ convexHull ℝ (Set.range (fun j => (reweight a ha (w j)).val)) ↔
      x.val ∈ convexHull ℝ (Set.range (fun j => (w j).val)) := by
  have h₁ := PositiveBarycentric.convexHull_iff_positive_lifts
    (diagonal a) (diagonal_injective a ha) w (fun j => (reweight a ha (w j)).val)
    (fun j => total a (w j).val) (fun j => total_pos a ha (w j))
    (fun j => diagonal_reweight a ha (w j)) x (reweight a ha x).val
    (total a x.val) (total_pos a ha x) (diagonal_reweight a ha x)
  have h₂ := PositiveBarycentric.convexHull_iff_positive_lifts
    (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (fun _ _ h => h)
    (fun j => reweight a ha (w j)) (fun j => (reweight a ha (w j)).val)
    (fun _ => 1) (fun _ => zero_lt_one)
    (fun _ => by simp only [LinearMap.id_apply, one_smul])
    (reweight a ha x) (reweight a ha x).val 1 zero_lt_one
    (by simp only [LinearMap.id_apply, one_smul])
  exact h₂.trans h₁.symm

theorem affineIndependent_reweight (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (w : J → Weights ι) (hw : AffineIndependent ℝ (fun j => (w j).val)) :
    AffineIndependent ℝ (fun j => (reweight a ha (w j)).val) := by
  have h := PositiveBarycentric.lift_independent
    (diagonal a) (diagonal_injective a ha) (fun j => (w j).val)
    (fun j => (w j).property.2) hw (fun j => (reweight a ha (w j)).val)
    (fun j => total a (w j).val) (fun j => (total_pos a ha (w j)).ne')
    (fun j => diagonal_reweight a ha (w j))
  exact h.affineIndependent

theorem affineIndependent_reweight_iff (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (w : J → Weights ι) :
    AffineIndependent ℝ (fun j => (reweight a ha (w j)).val) ↔
      AffineIndependent ℝ (fun j => (w j).val) := by
  constructor
  · intro h
    have hi := affineIndependent_reweight (fun i => (a i)⁻¹)
      (fun i => inv_pos.mpr (ha i)) (fun j => reweight a ha (w j)) h
    simpa only [inverse_reweight] using hi
  · exact affineIndependent_reweight a ha w

end BrehmApprox.BarycentricReweighting
