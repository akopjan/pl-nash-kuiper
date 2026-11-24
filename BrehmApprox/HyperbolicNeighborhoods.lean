module

public import BrehmApprox.HyperbolicCoordinates
public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Polyhedral neighborhoods in actual hyperbolic space

Every finite hyperbolic polyhedral cell has arbitrarily small compact
polyhedral neighborhoods with nonempty ambient interior around the cell.
The proof transfers the finite dimensional Euclidean polytope neighborhood
theorem through the genuine Klein chart.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace BrehmApprox

variable {n : ℕ}

theorem hyperbolicCell_neighborhood_basis (V : Finset (HyperbolicSpace n))
    {U : Set (HyperbolicSpace n)} (hU : IsOpen U) (hVU : hyperbolicCell V ⊆ U) :
    ∃ W : Finset (HyperbolicSpace n),
      hyperbolicCell V ⊆ interior (hyperbolicCell W) ∧ hyperbolicCell W ⊆ U := by
  classical
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    convexHull ℝ ((V.image HyperbolicSpace.klein : Finset (EuclideanSpace ℝ (Fin n))) : Set _)
  let O : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.ball 0 1 ∩ HyperbolicSpace.fromKlein ⁻¹' U
  have hO : IsOpen O :=
    HyperbolicSpace.continuousOn_fromKlein.isOpen_inter_preimage Metric.isOpen_ball hU
  have hKO : K ⊆ O := by
    intro p hp
    refine ⟨hyperbolic_klein_hull_subset_ball V hp, hVU ?_⟩
    rw [hyperbolicCell_eq_fromKlein_image]
    exact ⟨p, hp, rfl⟩
  have hKcompact : IsCompact K := (V.image HyperbolicSpace.klein).finite_toSet.isCompact_convexHull ℝ
  have hKconvex : Convex ℝ K := convex_convexHull ℝ _
  obtain ⟨S, hKS, hSO⟩ := hKconvex.exists_subset_interior_convexHull_finset_of_isCompact
    hKcompact (hO.mem_nhdsSet.mpr hKO)
  have hSball : ∀ p ∈ S, p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro p hp
    exact (hSO (subset_convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))
      (show p ∈ (S : Set (EuclideanSpace ℝ (Fin n))) from hp))).1
  let W : Finset (HyperbolicSpace n) := S.image HyperbolicSpace.fromKlein
  have himg : W.image HyperbolicSpace.klein = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      simpa only [HyperbolicSpace.klein_fromKlein
        (by simpa only [Metric.mem_ball, dist_zero_right] using hSball q hq)] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨HyperbolicSpace.fromKlein p,
        Finset.mem_image.mpr ⟨p, hp, rfl⟩, HyperbolicSpace.klein_fromKlein
          (by simpa only [Metric.mem_ball, dist_zero_right] using hSball p hp)⟩
  have hopen : IsOpen (HyperbolicSpace.klein ⁻¹' interior
      (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n))))) :=
    isOpen_interior.preimage HyperbolicSpace.continuous_klein
  have hpre : HyperbolicSpace.klein ⁻¹' interior
      (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin n)))) ⊆
      hyperbolicCell W := by
    intro x hx
    apply (mem_hyperbolicCell_iff_klein_mem_convexHull W x).mpr
    rw [himg]
    exact interior_subset hx
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    apply interior_maximal hpre hopen
    exact hKS ((mem_hyperbolicCell_iff_klein_mem_convexHull V x).mp hx)
  · intro x hx
    have hp := (mem_hyperbolicCell_iff_klein_mem_convexHull W x).mp hx
    rw [himg] at hp
    have hu := (hSO hp).2
    simpa only [Set.mem_preimage, HyperbolicSpace.fromKlein_klein] using hu

theorem hyperbolicCell_compact_neighborhood_basis (V : Finset (HyperbolicSpace n))
    {U : Set (HyperbolicSpace n)} (hU : IsOpen U) (hVU : hyperbolicCell V ⊆ U) :
    ∃ W : Finset (HyperbolicSpace n),
      IsCompact (hyperbolicCell W) ∧
      hyperbolicCell V ⊆ interior (hyperbolicCell W) ∧ hyperbolicCell W ⊆ U := by
  obtain ⟨W, hVW, hWU⟩ := hyperbolicCell_neighborhood_basis V hU hVU
  exact ⟨W, isCompact_hyperbolicCell W, hVW, hWU⟩

end BrehmApprox
