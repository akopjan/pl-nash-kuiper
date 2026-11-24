module

public import BrehmApprox.SphericalRigidity
public import BrehmApprox.HyperbolicRigidity

/-!
# Concrete statement definitions

The definitions in this module are also written explicitly in `Challenge.lean`.
The Challenge does not import this module. Keeping the definitions visible there
makes the registered mathematical statement independently readable.
-/

@[expose] public section
noncomputable section

open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry

universe u

/-- The Euclidean, spherical, and hyperbolic model geometries. -/
inductive Geometry where
  | euclidean
  | spherical
  | hyperbolic

/-- The `n`-dimensional model space. -/
abbrev Model : Geometry → ℕ → Type
  | .euclidean, n => EuclideanSpace ℝ (Fin n)
  | .spherical, n => GeodesicSphere n
  | .hyperbolic, n => BrehmApprox.HyperbolicSpace n

instance modelMetric (κ : Geometry) (n : ℕ) : MetricSpace (Model κ n) := by
  cases κ <;> exact inferInstance

/-- Geodesic convex hull, with spherical hulls restricted below to hemispheres. -/
def hull (κ : Geometry) (n : ℕ) : Finset (Model κ n) → Set (Model κ n) :=
  match κ with
  | .euclidean => fun V => convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n)))
  | .spherical => BrehmApprox.sphericalCell
  | .hyperbolic => BrehmApprox.hyperbolicCell

/-- Nondegenerate simplex vertices; the empty simplex is allowed. -/
def simplexVertices (κ : Geometry) (n : ℕ) : Finset (Model κ n) → Prop :=
  match κ with
  | .euclidean => fun V =>
      AffineIndependent ℝ (fun v : (V : Set (EuclideanSpace ℝ (Fin n))) => v.val)
  | .spherical => fun V => BrehmApprox.InOpenHemisphere V ∧
      LinearIndependent ℝ (fun v : (V : Set (GeodesicSphere n)) => v.val.val)
  | .hyperbolic => fun V =>
      LinearIndependent ℝ (fun v : (V : Set (BrehmApprox.HyperbolicSpace n)) =>
        BrehmApprox.HyperbolicSpace.lift v.val)

local instance definitionsLocalInstance1 (α : Type*) : DecidableEq α := Classical.decEq α

/-- A locally finite geodesic triangulation. Each simplex has its own isometric
chart. Face compatibility is imposed in the source, without a global folding. -/
structure Triangulation (κ : Geometry) (n : ℕ) (P : Type u) [MetricSpace P] where
  simplices : Set (Finset P)
  cell : Finset P → Set P
  chart : Finset P → P → Model κ n
  cover : ∀ x : P, ∃ σ ∈ simplices, x ∈ cell σ
  locallyFinite : LocallyFinite (fun σ : simplices => cell σ.val)
  vertices_mem : ∀ σ ∈ simplices, (σ : Set P) ⊆ cell σ
  simplex : ∀ σ ∈ simplices, simplexVertices κ n (σ.image (chart σ))
  image_cell : ∀ σ ∈ simplices, chart σ '' cell σ = hull κ n (σ.image (chart σ))
  isometry_cell : ∀ σ ∈ simplices, ∀ x ∈ cell σ, ∀ y ∈ cell σ,
    dist (chart σ x) (chart σ y) = dist x y
  faces : ∀ σ ∈ simplices, ∀ τ ⊆ σ, τ ∈ simplices
  image_face : ∀ σ ∈ simplices, ∀ τ ⊆ σ,
    chart σ '' cell τ = hull κ n (τ.image (chart σ))
  intersection : ∀ σ ∈ simplices, ∀ τ ∈ simplices, cell σ ∩ cell τ = cell (σ ∩ τ)

/-- The metric is the infimum of lengths of finite chains within simplices. -/
def Intrinsic {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]
    (T : Triangulation κ n P) : Prop :=
  ∀ x y : P, ∀ ε : ℝ, 0 < ε →
    ∃ m : ℕ, ∃ z : ℕ → P, z 0 = x ∧ z m = y ∧
      (∀ j < m, ∃ σ ∈ T.simplices, z j ∈ T.cell σ ∧ z (j + 1) ∈ T.cell σ) ∧
      (∑ j ∈ Finset.range m, dist (z j) (z (j + 1))) < dist x y + ε

/-- A finite intrinsic polyhedral space of curvature `κ` and dimension at most `n`. -/
def IsFinitePolyhedron (κ : Geometry) (n : ℕ) (P : Type u) [MetricSpace P] : Prop :=
  ∃ T : Triangulation κ n P, T.simplices.Finite ∧ Intrinsic T

/-- A PL-isometry is continuous and isometric on each simplex of some locally
finite geodesic triangulation. It need not be injective on the whole source. -/
def PLIsometry {P : Type u} [MetricSpace P] (κ : Geometry) (n : ℕ)
    (f : P → Model κ n) : Prop :=
  Continuous f ∧ ∃ T : Triangulation κ n P,
    ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (f x) (f y) = dist x y

/-- Strict shortness has a single global Lipschitz constant below one. -/
def StrictlyShort {P Q : Type*} [MetricSpace P] [MetricSpace Q] (f : P → Q) : Prop :=
  ∃ L : NNReal, L < 1 ∧ LipschitzWith L f

end ArchivePLGeometry
