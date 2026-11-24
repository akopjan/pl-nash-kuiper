module

public import PLGeometry.FiniteFoldingExistence
public import PLGeometry.ApproximationFromFolding
public import PLGeometry.Dimension

/-! # The three PL Nash–Kuiper approximation theorems -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u

/-- Every short map of a finite intrinsic Euclidean polyhedron admits
arbitrarily close PL-isometric approximations in the same or a larger dimension. -/
theorem pl_nash_kuiper_euclidean {d n : ℕ} (hdn : d ≤ n)
    (P : Type u) [MetricSpace P] (hP : IsFinitePolyhedron .euclidean d P)
    (f : P → Model .euclidean n) (hf : LipschitzWith 1 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → Model .euclidean n,
      LipschitzWith 1 g ∧ PLIsometry .euclidean n g ∧
      ∀ x, dist (g x) (f x) < ε := by
  have hPn := hP.mono hdn
  obtain ⟨q, hq, _⟩ := hPn.exists_small_plIsometry 0 zero_lt_one
  exact euclidean_approximation_of_pl_folding hPn q hq f hf hε

/-- Strict shortness or containment in a closed hemisphere suffices for
uniform PL-isometric approximation of finite spherical polyhedra. -/
theorem pl_nash_kuiper_spherical {d n : ℕ} (hdn : d ≤ n)
    (P : Type u) [MetricSpace P] (hP : IsFinitePolyhedron .spherical d P)
    (f : P → Model .spherical n) (hf : LipschitzWith 1 f)
    (hs : StrictlyShort f ∨ ∃ p : Model .spherical n, ∀ x, dist (f x) p ≤ Real.pi / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → Model .spherical n,
      LipschitzWith 1 g ∧ PLIsometry .spherical n g ∧
      ∀ x, dist (g x) (f x) < ε := by
  have hPn := hP.mono hdn
  let p := GeodesicSphere.northPole n
  obtain ⟨q, hq, hnear⟩ := hPn.exists_small_plIsometry p
    (show 0 < Real.pi / 2 by positivity)
  have hhem : ∀ x, q x ∈ GeodesicSphere.openHemisphere p := by
    intro x
    apply (GeodesicSphere.dist_lt_pi_div_two_iff p (q x)).mp
    simpa only [dist_comm] using hnear x
  apply spherical_approximation_of_hemispherical_pl_folding hPn q hq p hhem f hf _ hε
  rcases hs with hstrict | ⟨c, hc⟩
  · exact Or.inl hstrict
  · exact Or.inr ⟨c, fun x => by simpa only [dist_comm] using hc x⟩

/-- Every short map of a finite intrinsic hyperbolic polyhedron admits
arbitrarily close PL-isometric approximations in the same or a larger dimension. -/
theorem pl_nash_kuiper_hyperbolic {d n : ℕ} (hdn : d ≤ n)
    (P : Type u) [MetricSpace P] (hP : IsFinitePolyhedron .hyperbolic d P)
    (f : P → Model .hyperbolic n) (hf : LipschitzWith 1 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → Model .hyperbolic n,
      LipschitzWith 1 g ∧ PLIsometry .hyperbolic n g ∧
      ∀ x, dist (g x) (f x) < ε := by
  have hPn := hP.mono hdn
  obtain ⟨q, hq, _⟩ := hPn.exists_small_plIsometry (⟨0⟩ : BrehmApprox.HyperbolicSpace n)
    zero_lt_one
  exact hyperbolic_approximation_of_pl_folding hPn q hq f hf hε

end ArchivePLGeometry
