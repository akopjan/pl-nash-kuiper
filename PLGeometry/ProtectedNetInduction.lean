module

public import PLGeometry.ProtectedNetLinks
public import PLGeometry.ProtectedNetFinite
public import PLGeometry.SphericalLinkComplex

/-!
# Induction on the number of vertices in a face

The angular link is represented in the same ambient sphere, while its
faces have strictly fewer vertices. This gives a well-founded induction
without any hypothesis about a pre-existing folding.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

local instance protectedNetInductionDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {n : ℕ}
    (hpolar : ∀ (P : Type u) [TopologicalSpace P] [T2Space P]
      (T : FiniteChartedComplex .spherical n P) (p : P),
      ∃ D : PolarNetData T p (T.sphericalLink p),
        ∀ σ ∈ T.simplices, p ∈ T.cell σ → ∀ x ∈ T.cell σ,
          dist (T.chart σ p) (T.chart σ x) < 2 * D.radius → x ∈ T.openStar p)

include hpolar

/-- The induction step uses actual polar coordinates and the strict
decrease in the number of vertices of every angular face. -/
theorem spherical_protected_net_of_card_bound (N : ℕ) :
    ∀ (P : Type u) [TopologicalSpace P] [T2Space P]
      (T : FiniteChartedComplex .spherical n P),
      (∀ σ ∈ T.simplices, σ.card ≤ N) → ∀ η : ℝ, 0 < η →
        ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  induction N with
  | zero =>
    intro P _ _ T hN η hη
    letI : IsEmpty P := T.isEmpty_of_face_card_zero hN
    exact T.exists_protected_net_of_finite hη
  | succ N ih =>
    intro P _ _ T hN η hη
    apply T.exists_protected_net_of_link_nets T.sphericalLinkData
      (fun p => hpolar P T p) (fun p ε hε => ?_) hη
    apply ih (T.linkComplex p).Space (T.sphericalLink p)
      (T.link_face_card_le (T.sphericalLinkData p) hN) ε hε

theorem spherical_protected_net_of_polar_coordinates
    {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .spherical n P) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  obtain ⟨N, hN⟩ := T.exists_face_card_bound
  exact spherical_protected_net_of_card_bound hpolar N P T hN η hη

end ArchivePLGeometry.FiniteChartedComplex
