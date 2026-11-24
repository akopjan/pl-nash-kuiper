module

public import PLGeometry.PolarNetData

/-! # Compact assembly of local protected grids -/

@[expose] public section
noncomputable section

open Set

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance protectedNetAssemblyDecidableEq : DecidableEq P := Classical.decEq _

theorem exists_protected_net_of_local_grids
    (r : P → ℝ) (hr : ∀ p, 0 < r p)
    (hstar : ∀ p, ∀ σ ∈ T.simplices, p ∈ T.cell σ →
      ∀ x ∈ T.cell σ, dist (T.chart σ p) (T.chart σ x) < 2 * r p → x ∈ T.openStar p)
    (hgrids : ∀ p, ∀ δ : ℝ, 0 < δ → Nonempty (LocalProtectedGrid T p (r p) δ))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset P, T.IsCellwiseNet S η ∧ T.IsCellwiseProtected S := by
  let : CompactSpace P := T.compactSpace
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun p => T.starBall p (r p)) (fun p => T.isOpen_starBall p (r p))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, T.mem_starBall_self x (hr x)⟩)
  have hcover : ∀ x : P, ∃ p ∈ I, x ∈ T.starBall p (r p) := by
    intro x
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp (hI (Set.mem_univ x))
    exact ⟨p, hp, hx⟩
  by_cases hIn : I.Nonempty
  · let δ : ℝ := min η (I.inf' hIn r) / 2
    have hmin : 0 < I.inf' hIn r := by
      rw [Finset.lt_inf'_iff]
      exact fun p _ => hr p
    have hδ : 0 < δ := div_pos (lt_min hη hmin) (by norm_num)
    have hδη : δ < η := by
      have hh := min_le_left η (I.inf' hIn r)
      dsimp only [δ]
      linarith [lt_min hη hmin]
    have hδr : ∀ p ∈ I, δ < r p := by
      intro p hp
      have hh := min_le_right η (I.inf' hIn r)
      have hh' := Finset.inf'_le r hp
      dsimp only [δ]
      linarith [lt_min hη hmin]
    let G : ∀ p, LocalProtectedGrid T p (r p) δ := fun p => Classical.choice (hgrids p δ hδ)
    have h := T.protected_net_of_finite_local_grids I r (fun p => (G p).sites)
      hδr hcover (fun p _ => hstar p)
      (fun p _ => (G p).star) (fun p _ => (G p).radius)
      (fun p _ => (G p).net) (fun p _ => (G p).protection)
    refine ⟨I.biUnion (fun p => (G p).sites), ?_, h.2⟩
    intro σ hσ x hx
    obtain ⟨a, ha, haσ, hxa⟩ := h.1 σ hσ x hx
    exact ⟨a, ha, haσ, hxa.trans hδη⟩
  · have hempty : ∀ x : P, False := by
      intro x
      obtain ⟨p, hp, _⟩ := hcover x
      exact hIn ⟨p, hp⟩
    exact ⟨∅, fun _ _ x _ => (hempty x).elim,
      fun _ _ _ _ x _ _ _ => (hempty x).elim⟩

end ArchivePLGeometry.FiniteChartedComplex
