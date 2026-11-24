module

public import PLGeometry.ChartedStars
public import BrehmApprox.ProtectedNetPropagation

/-!
# Cellwise protected nets and their local assembly

All distances here are measured in an actual source simplex chart. The
finite assembly lemma combines radial grids in open stars. Its hypotheses
are local geometric properties of those grids, with a common mesh size.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance protectedNetDecidableEq : DecidableEq P := Classical.decEq P

/-- Every cell has a site at distance less than the prescribed mesh. -/
def IsCellwiseNet (S : Finset P) (η : ℝ) : Prop :=
  ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ,
    ∃ a ∈ S, a ∈ T.cell σ ∧ dist (T.chart σ x) (T.chart σ a) < η

/-- Every nearest site within a cell lies in each other cell containing the
query point. Common-face compatibility makes this the usual protection
condition for all simplex faces. -/
def IsCellwiseProtected (S : Finset P) : Prop :=
  ∀ σ ∈ T.simplices, ∀ τ ∈ T.simplices, ∀ x ∈ T.cell σ ∩ T.cell τ, ∀ a,
    BrehmApprox.IsNearestFor (fun z w => dist (T.chart σ z) (T.chart σ w))
      ((S : Set P) ∩ T.cell σ) x a → a ∈ T.cell τ

/-- The union of finitely many radial grids is protected once its mesh is
smaller than every star radius. -/
theorem protected_net_of_finite_local_grids
    (I : Finset P) (r : P → ℝ) (G : P → Finset P) {δ : ℝ}
    (hδ : ∀ p ∈ I, δ < r p)
    (hcover : ∀ x : P, ∃ p ∈ I, x ∈ T.starBall p (r p))
    (hstar : ∀ p ∈ I, ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < 2 * r p →
        x ∈ T.openStar p)
    (hgridStar : ∀ p ∈ I, ∀ a ∈ G p, a ∈ T.openStar p)
    (hgridRadius : ∀ p ∈ I, ∀ a ∈ G p, T.radialDistance p a ≤ r p)
    (hgridNet : ∀ p ∈ I, ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ,
      x ∈ T.starBall p (r p) → ∃ a ∈ G p,
        a ∈ T.cell σ ∧ dist (T.chart σ x) (T.chart σ a) < δ)
    (hgridProtected : ∀ p ∈ I, ∀ σ ∈ T.simplices, ∀ τ ∈ T.simplices,
      p ∈ T.cell σ → p ∈ T.cell τ →
      ∀ x ∈ T.cell σ ∩ T.cell τ, T.radialDistance p x < 2 * r p → ∀ a,
        BrehmApprox.IsNearestFor (fun z w => dist (T.chart σ z) (T.chart σ w))
          ((G p : Set P) ∩ T.cell σ) x a → a ∈ T.cell τ) :
    T.IsCellwiseNet (I.biUnion G) δ ∧ T.IsCellwiseProtected (I.biUnion G) := by
  classical
  have hnet : T.IsCellwiseNet (I.biUnion G) δ := by
    intro σ hσ x hx
    obtain ⟨p, hp, hxp⟩ := hcover x
    obtain ⟨a, ha, haσ, hdist⟩ := hgridNet p hp σ hσ x hx hxp
    exact ⟨a, Finset.mem_biUnion.mpr ⟨p, hp, ha⟩, haσ, hdist⟩
  refine ⟨hnet, ?_⟩
  intro σ hσ τ hτ x hx a ha
  obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp ha.1.1
  have haσ : a ∈ T.cell σ := ha.1.2
  have hpσ : p ∈ T.cell σ := hgridStar p hp a hap σ hσ haσ
  obtain ⟨b, hb, hbσ, hxb⟩ := hnet σ hσ x hx.1
  have hxa : dist (T.chart σ x) (T.chart σ a) < δ :=
    (ha.2 b ⟨hb, hbσ⟩).trans_lt hxb
  have hpa : dist (T.chart σ p) (T.chart σ a) ≤ r p := by
    rw [← T.radialDistance_eq p hσ hpσ haσ]
    exact hgridRadius p hp a hap
  have hpx : dist (T.chart σ p) (T.chart σ x) < 2 * r p := by
    have ht := dist_triangle (T.chart σ p) (T.chart σ a) (T.chart σ x)
    rw [dist_comm (T.chart σ a) (T.chart σ x)] at ht
    linarith [hδ p hp]
  have hxstar := hstar p hp σ hσ hpσ x hx.1 hpx
  have hpτ : p ∈ T.cell τ := hxstar τ hτ hx.2
  apply hgridProtected p hp σ hσ τ hτ hpσ hpτ x hx
  · rwa [T.radialDistance_eq p hσ hpσ hx.1]
  · apply ha.mono
    · intro b hb
      exact ⟨Finset.mem_biUnion.mpr ⟨p, hp, hb.1⟩, hb.2⟩
    · exact ⟨hap, haσ⟩

end ArchivePLGeometry.FiniteChartedComplex
