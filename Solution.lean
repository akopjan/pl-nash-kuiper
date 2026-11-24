module

public import Compatibility

@[expose] public section
noncomputable section

open scoped NNReal

namespace PLGeometry

/-- PL Nash--Kuiper--Gromov approximation (Akopyan, 2010, Thms. 3.7,
3.17, 3.18): every short map from a finite polyhedral space is uniformly
approximable by PL-isometries. In the spherical case, require uniform strict
shortness or containment of the image in an open hemisphere. -/
theorem akopyan_pl_nash_kuiper (κ : Geometry) {d m n : ℕ}
    (hdn : d ≤ n) (K : Polyhedron κ d m)
    (f : ↥K.K.space → Model κ n)
    (hf : Lipschitz K f 1)
    (hsphere : κ = .spherical →
      ((∃ L : ℝ≥0, L < 1 ∧ Lipschitz K f L) ∨
       ∃ o : Model κ n, ∀ x,
         modelDist κ n (f x) o < Real.pi / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ↥K.K.space → Model κ n,
      PLIsometry K g ∧
      ∀ x, modelDist κ n (g x) (f x) < ε := by
  have hf' : Lipschitz (K.raiseDimension hdn) f 1 :=
    (K.lipschitz_raiseDimension_iff hdn f 1).mpr hf
  have hsphere' : κ = .spherical →
      ((∃ L : ℝ≥0, L < 1 ∧ Lipschitz (K.raiseDimension hdn) f L) ∨
       ∃ o : Model κ n, ∀ x,
         modelDist κ n (f x) o < Real.pi / 2) := by
    intro hk
    rcases hsphere hk with ⟨L, hL, hshort⟩ | hhem
    · exact Or.inl ⟨L, hL, (K.lipschitz_raiseDimension_iff hdn f L).mpr hshort⟩
    · exact Or.inr hhem
  obtain ⟨g, hg, hclose⟩ := Compatibility.approximation_equal_dimension κ
    (K.raiseDimension hdn) f hf' hsphere' hε
  exact ⟨g, (K.plIsometry_raiseDimension_iff hdn g).mp hg, hclose⟩

end PLGeometry
