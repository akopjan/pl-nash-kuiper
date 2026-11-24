module

public import BrehmApprox.SphericalFiniteMotions
public import BrehmApprox.SphericalFiniteSelection

/-! # Brehm's finite extension theorem on the round sphere -/

@[expose] public section

namespace BrehmApprox

/-- Every finite short map of the round sphere extends to a global short map
with actual finite hemispherical isometric pieces on every spherical polytope. -/
theorem sphericalBrehm_proved (n : ℕ) :
    FiniteExtension (LocallySphericalPL (n := n)) := by
  intro s f hf
  obtain ⟨g, hg, ⟨S, hS⟩, heq⟩ := spherical_finite_extension_motions n s f hf
  exact ⟨g, hg, locallySphericalPL_of_finset_orthogonal_selection hg.continuous S hS, heq⟩

end BrehmApprox
