module

public import BrehmApprox.EuclideanPreparation
public import BrehmApprox.EuclideanReferenceAtlas
public import BrehmApprox.ModelTheorems

/-!
# Euclidean approximation on a genuinely folded simplicial source

This theorem has no prepared reference atlas, collar, separation parameter,
flattening map, or locally constant reference map among its hypotheses.
All those objects are constructed by the preceding modules.

An initial folding and its actual simplex vertex data are explicit inputs
to this intermediate theorem. `ArchivePLGeometry.FiniteFoldingExistence` constructs
the folding, and the approximation transport modules supply a compatible
geodesic triangulation for the public theorem.
-/

@[expose] public section

namespace BrehmApprox

variable {P : Type*} [MetricSpace P] {n N : ℕ}

/-- The complete approximation construction after a genuine initial folding.
The finite Euclidean Brehm theorem used in the construction is proved. -/
theorem euclidean_folded_polyhedron_approximation
    (G : FoldedGeometry (P := P) (euclideanPolytopeModel n) N)
    (T : SimplicialFaceData G.toPolyhedralFaceData)
    (f : P → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → EuclideanSpace ℝ (Fin n), LipschitzWith 1 g ∧
      PolyhedralPiecewiseIsometry (euclideanPolytopeModel n) G.fold g ∧
      ∀ x, dist (g x) (f x) < ε := by
  let : CompactSpace P := G.compactSpace 0
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨L, hL0, hL1, u, hu, huf⟩ :=
    euclidean_strictification_on_compact (K := Set.univ) isCompact_univ hf hε3
  let κ : NNReal := ⟨L, hL0⟩
  have huκ : LipschitzWith κ u := LipschitzWith.of_dist_le_mul hu
  obtain ⟨K, hK, f₀, hf₀, hclose, hflat⟩ :=
    G.exists_strict_flat_approximation T u huκ hL1 hε3
  let R := G.euclideanLocalReferences T f₀ hf₀ hflat
  obtain ⟨g, hg, hPL, hgf₀⟩ := G.approximate R (euclideanBrehm n) K.coe_nonneg hK f₀
    (fun i x hx => G.euclideanReference_on_cell T i f₀ hx) hε3
  refine ⟨g, hg, hPL, ?_⟩
  intro x
  have h₁ := hgf₀ x
  have h₂ := hclose x
  have h₃ := huf x (Set.mem_univ x)
  have ht₁ := dist_triangle (g x) (f₀ x) (f x)
  have ht₂ := dist_triangle (f₀ x) (u x) (f x)
  linarith

end BrehmApprox
