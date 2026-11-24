module

public import PLGeometry.ProtectedNetAssembly
public import PLGeometry.LinkCombinatorics
public import PLGeometry.SphericalComplexRealization

/-! # Protected nets from the spherical links -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n m : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance protectedNetLinksDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- A finite charted complex has a uniform finite bound on face cardinality. -/
theorem exists_face_card_bound : ∃ N : ℕ, ∀ σ ∈ T.simplices, σ.card ≤ N := by
  let F : Finset (Finset P) := T.finite_simplices.toFinset
  exact ⟨F.sup Finset.card, fun σ hσ => Finset.le_sup
    (f := Finset.card) ((Set.Finite.mem_toFinset T.finite_simplices).mpr hσ)⟩

/-- Every realized link face has strictly fewer vertices than an incident
source face, independently of the ambient dimension used to represent it. -/
theorem link_face_card_le {p : P} (D : Barycentric.SphericalData (T.linkComplex p) m)
    {N : ℕ} (hN : ∀ σ ∈ T.simplices, σ.card ≤ N + 1) :
    ∀ S ∈ D.toChartedComplex.simplices, S.card ≤ N := by
  letI : DecidableEq (T.linkComplex p).Space := Classical.decEq _
  intro S hS
  obtain ⟨τ, hτ, rfl⟩ := hS
  have hc := T.linkFace_card_lt hτ
  have hb := hN _ (T.linkCoface_spec hτ).1
  have hv : ((T.linkComplex p).vertices τ).card = τ.card := by
    exact Finset.card_image_of_injective τ (T.linkComplex p).vertex_injective
  rw [hv]
  omega

/-- A complex with no nonempty face has empty realization. -/
theorem isEmpty_of_face_card_zero
    (hN : ∀ σ ∈ T.simplices, σ.card ≤ 0) : IsEmpty P := by
  refine ⟨fun x => ?_⟩
  obtain ⟨σ, hσ, hx⟩ := T.cover x
  have hσ0 : σ = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hN σ hσ))
  have hempty := T.faces σ hσ ∅ (Finset.empty_subset _)
  rw [hσ0, T.cell_empty hempty] at hx
  exact hx

/-- Finite protected nets in the actual spherical links produce finite
protected nets in the source complex by compactly assembling polar grids. -/
theorem exists_protected_net_of_link_nets
    (L : ∀ p : P, Barycentric.SphericalData (T.linkComplex p) m)
    (hpolar : ∀ p : P, ∃ D : PolarNetData T p (L p).toChartedComplex,
      ∀ σ ∈ T.simplices, p ∈ T.cell σ → ∀ x ∈ T.cell σ,
        dist (T.chart σ p) (T.chart σ x) < 2 * D.radius → x ∈ T.openStar p)
    (hlinks : ∀ p : P, ∀ ε : ℝ, 0 < ε →
      ∃ S : Finset (T.linkComplex p).Space,
        (L p).toChartedComplex.IsCellwiseNet S ε ∧
        (L p).toChartedComplex.IsCellwiseProtected S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset P, T.IsCellwiseNet S ε ∧ T.IsCellwiseProtected S := by
  let D (p : P) : PolarNetData T p (L p).toChartedComplex := (hpolar p).choose
  apply T.exists_protected_net_of_local_grids (fun p => (D p).radius)
    (fun p => (D p).radius_pos) (fun p => (hpolar p).choose_spec)
  · intro p δ hδ
    exact (D p).exists_localProtectedGrid (hlinks p) hδ
  · exact hε

end ArchivePLGeometry.FiniteChartedComplex
