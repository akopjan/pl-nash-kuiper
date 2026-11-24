module

public import BrehmApprox.PolytopeArrangementCover

/-!
# The arrangement determined by finite affine branches

Scalar coordinate differences detect equality of affine maps. Their sign
arrangement gives a locally finite face-to-face polyhedral cover on which a
continuous selection is one fixed affine branch.
-/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox

variable {E F J I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [Fintype J]

abbrev AffineEqualityIndex (F J : Type*) [AddCommGroup F] [Module ℝ F] :=
  J × J × Fin (Module.finrank ℝ F)

def affineEqualityCoordinate (a : J → E →ᵃ[ℝ] F) (k : AffineEqualityIndex F J) :
    E →ᵃ[ℝ] ℝ :=
  ((Module.finBasis ℝ F).coord k.2.2).toAffineMap.comp (a k.1 - a k.2.1)

def affineEqualityLinear (a : J → E →ᵃ[ℝ] F) (k : AffineEqualityIndex F J) :
    E →ₗ[ℝ] ℝ := (affineEqualityCoordinate a k).linear

def affineEqualityBound (a : J → E →ᵃ[ℝ] F) (k : AffineEqualityIndex F J) : ℝ :=
  -(affineEqualityCoordinate a k) 0

theorem affineEquality_iff (a : J → E →ᵃ[ℝ] F) (k : AffineEqualityIndex F J) (x : E) :
    affineEqualityLinear a k x = affineEqualityBound a k ↔
      (Module.finBasis ℝ F).coord k.2.2 (a k.1 x - a k.2.1 x) = 0 := by
  have hd := congrFun (AffineMap.decomp (affineEqualityCoordinate a k)) x
  change (affineEqualityCoordinate a k) x =
    (affineEqualityCoordinate a k).linear x + (affineEqualityCoordinate a k) 0 at hd
  have heval : (affineEqualityCoordinate a k) x =
      (Module.finBasis ℝ F).coord k.2.2 (a k.1 x - a k.2.1 x) := rfl
  change (affineEqualityCoordinate a k).linear x = -(affineEqualityCoordinate a k) 0 ↔ _
  rw [← heval, hd]
  constructor <;> intro h <;> linarith

theorem affine_eq_of_zero_pattern (a : J → E →ᵃ[ℝ] F) (x y : E)
    (hzero : ∀ k, affineEqualityLinear a k x = affineEqualityBound a k ↔
      affineEqualityLinear a k y = affineEqualityBound a k)
    (i j : J) (hij : a i x = a j x) : a i y = a j y := by
  apply sub_eq_zero.mp
  apply (Module.finBasis ℝ F).forall_coord_eq_zero_iff.mp
  intro k
  apply (affineEquality_iff a (i, j, k) y).mp
  apply (hzero (i, j, k)).mp
  apply (affineEquality_iff a (i, j, k) x).mpr
  rw [hij, sub_self, map_zero]

theorem affine_selection_eqOn_weakCell
    {C : Set E} (hC : IsFinitePolytope C)
    (a : J → E →ᵃ[ℝ] F) {f : E → F} (hf : ContinuousOn f C)
    (hsel : ∀ x ∈ C, ∃ j, f x = a j x)
    (s : AffineEqualityIndex F J → AffineSign)
    (hne : (affineStratum C (affineEqualityLinear a) (affineEqualityBound a) s).Nonempty) :
    ∃ j, EqOn f (a j)
      (affineWeakCell C (affineEqualityLinear a) (affineEqualityBound a) s) := by
  let L := affineEqualityLinear a
  let b := affineEqualityBound a
  have hsub : affineStratum C L b s ⊆ C := fun _ hx => hx.1
  obtain ⟨j, hj⟩ := finite_selection_eqOn_of_eqOn_propagates
    (convex_affineStratum hC.convex L b s).isPreconnected hne
    (hf.mono hsub)
    (fun j => (a j).continuous_of_finiteDimensional.continuousOn)
    (fun x hx => hsel x hx.1)
    (fun x hx i j hij y hy => affine_eq_of_zero_pattern a x y
      (fun k => AffineSign.holds_eq_iff (hx.2 k) (hy.2 k)) i j hij)
  refine ⟨j, ?_⟩
  have hweak : affineWeakCell C L b s ⊆ C := fun _ hx => hx.1
  apply hj.of_subset_closure (hf.mono hweak)
    (a j).continuous_of_finiteDimensional.continuousOn
    (affineStratum_subset_weakCell C L b s)
  rw [closure_affineStratum hC.convex hC.isCompact.isClosed L b s hne]

theorem affine_selection_eqOn_arrangement
    (K : PolytopeCover E I) (a : J → E →ᵃ[ℝ] F) {f : E → F}
    (hf : Continuous f) (hsel : ∀ x, ∃ j, f x = a j x)
    (p : K.ArrangementIndex (affineEqualityLinear a) (affineEqualityBound a)) :
    ∃ j, EqOn f (a j)
      (K.arrangementCell (affineEqualityLinear a) (affineEqualityBound a) p) :=
  affine_selection_eqOn_weakCell (K.polytope p.val.1) a hf.continuousOn
    (fun x _ => hsel x) p.val.2 p.property

end BrehmApprox
