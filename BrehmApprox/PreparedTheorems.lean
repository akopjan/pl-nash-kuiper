module

public import BrehmApprox.IntrinsicChains
public import BrehmApprox.ModelTheorems

/-!
# Concrete final theorems for already prepared polyhedral sources

Each theorem uses the actual metric and actual polytope interface of the
indicated geometry. These intermediate interfaces consume `ReferenceAtlas`
and `FoldedSource` data. The preparation and initial-folding constructions
supply those data in the unconditional public declarations of
`ArchivePLGeometry.PLNashKuiper`.
-/

@[expose] public section

namespace BrehmApprox

variable {P : Type*} [MetricSpace P] {n N : ℕ} {L ε : ℝ}

theorem euclidean_prepared_approximation
    {D : ReferenceAtlas (euclideanPolytopeModel n) N L}
    (S : FoldedSource D P) (hintrinsic : ChainGenerated S.cell)
    (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : P → EuclideanSpace ℝ (Fin n))
    (href : ∀ i, ∀ x ∈ S.cell i, D.reference i (S.fold x) = f x)
    (hε : 0 < ε) :
    ∃ g : P → EuclideanSpace ℝ (Fin n), LipschitzWith 1 g ∧
      PolyhedralPiecewiseIsometry (euclideanPolytopeModel n) S.fold g ∧
      ∀ x, dist (g x) (f x) < ε :=
  S.approximate_short hintrinsic (euclideanBrehm n) hL0 hL1 f href hε

theorem spherical_prepared_approximation
    {D : ReferenceAtlas (sphericalPolytopeModel n) N L}
    (S : FoldedSource D P) (hintrinsic : ChainGenerated S.cell)
    (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : P → GeodesicSphere n)
    (href : ∀ i, ∀ x ∈ S.cell i, D.reference i (S.fold x) = f x)
    (hε : 0 < ε) :
    ∃ g : P → GeodesicSphere n, LipschitzWith 1 g ∧
      PolyhedralPiecewiseIsometry (sphericalPolytopeModel n) S.fold g ∧
      ∀ x, dist (g x) (f x) < ε :=
  S.approximate_short hintrinsic (sphericalBrehm n) hL0 hL1 f href hε

theorem hyperbolic_prepared_approximation
    {D : ReferenceAtlas (hyperbolicPolytopeModel n) N L}
    (S : FoldedSource D P) (hintrinsic : ChainGenerated S.cell)
    (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : P → HyperbolicSpace n)
    (href : ∀ i, ∀ x ∈ S.cell i, D.reference i (S.fold x) = f x)
    (hε : 0 < ε) :
    ∃ g : P → HyperbolicSpace n, LipschitzWith 1 g ∧
      PolyhedralPiecewiseIsometry (hyperbolicPolytopeModel n) S.fold g ∧
      ∀ x, dist (g x) (f x) < ε :=
  S.approximate_short hintrinsic (hyperbolicBrehm n) hL0 hL1 f href hε

end BrehmApprox
