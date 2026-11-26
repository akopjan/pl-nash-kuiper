module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Akopyan's PL Nash--Kuiper--Gromov theorem

Formalization of the PL analogue of the Nash--Kuiper--Gromov theorem
(Akopyan, 2010; Theorems 3.7, 3.17, and 3.18).

Let `P` be a finite `d`-dimensional polyhedral space whose simplices have
constant curvature `κ ∈ {-1, 0, 1}`. Let `f : P → M_κ^n` be short, with `d ≤ n`.
Then `f` can be uniformly approximated by PL-isometries. In the spherical
case, `f` must be uniformly strictly short or have image in an open hemisphere.

References: Akopyan (2010); Akopyan--Tarasov (2008); Brehm (1981);
Petrunin--Yashinski (2014). See `REFERENCES.md` for complete citations.
-/

@[expose] public section
noncomputable section
open scoped InnerProductSpace NNReal

namespace PLGeometry

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

inductive Geometry where
  | euclidean | hyperbolic | spherical

abbrev Model : Geometry → ℕ → Type
  | .euclidean, n => E n
  | .hyperbolic, n => ↥(Metric.ball (0 : E n) 1)
  | .spherical, n => ↥(Metric.sphere (0 : E (n + 1)) 1)

instance modelTopology (κ : Geometry) (n : ℕ) : TopologicalSpace (Model κ n) := by
  cases κ <;> infer_instance

/-- Euclidean, Klein hyperbolic, and spherical geodesic distances. -/
def modelDist (κ : Geometry) (n : ℕ) : Model κ n → Model κ n → ℝ :=
  match κ with
  | .euclidean => fun x y => dist x y
  | .hyperbolic => fun x y =>
      Real.arcosh ((1 - inner ℝ x.val y.val) /
        (Real.sqrt (1 - ‖x.val‖ ^ 2) * Real.sqrt (1 - ‖y.val‖ ^ 2)))
  | .spherical => fun x y => InnerProductGeometry.angle x.val y.val

/-- The geodesic convex hull in a model space. -/
def hull (κ : Geometry) (n : ℕ)
    (V : Set (Model κ n)) : Set (Model κ n) :=
  match κ with
  | .euclidean => convexHull ℝ V
  | .hyperbolic => {x | x.val ∈ convexHull ℝ (Subtype.val '' V)}
  | .spherical => {x | ∃ y ∈ convexHull ℝ (Subtype.val '' V),
      ∃ t : ℝ, 0 < t ∧ x.val = t • y}

def cell {m : ℕ} (σ : Finset (E m)) : Set (E m) :=
  convexHull ℝ (σ : Set (E m))

/-- A simplex chart preserving geodesic hulls of all finite subsets.
This also covers the simplices of subdivisions. -/
structure Simplex (κ : Geometry) (d m : ℕ) (σ : Finset (E m)) where
  toModel : E m → Model κ d
  continuous : ContinuousOn toModel (cell σ)
  injective : Set.InjOn toModel (cell σ)
  convex : ∀ (V : Finset (E m)),
    (V : Set (E m)) ⊆ cell σ →
      toModel '' convexHull ℝ (V : Set (E m)) =
        hull κ d (toModel '' (V : Set (E m)))

/-- A finite complex of geodesic simplices with compatible face metrics. -/
structure Polyhedron (κ : Geometry) (d m : ℕ) where
  K : _root_.Geometry.SimplicialComplex ℝ (E m)
  finite : K.faces.Finite
  simplex : ∀ (σ : Finset (E m)), σ ∈ K.faces → Simplex κ d m σ
  compatible : ∀ σ τ (hσ : σ ∈ K.faces) (hτ : τ ∈ K.faces),
    ∀ x ∈ cell (σ ∩ τ), ∀ y ∈ cell (σ ∩ τ),
      modelDist κ d ((simplex σ hσ).toModel x) ((simplex σ hσ).toModel y) =
        modelDist κ d ((simplex τ hτ).toModel x) ((simplex τ hτ).toModel y)

/-- Length of one segment inside a simplex; `⊤` if no simplex contains both
endpoints. The infimum is over geometric realizations of the same segment. -/
def segmentEDist {κ : Geometry} {d m : ℕ}
    (K : Polyhedron κ d m) (x y : ↥K.K.space) : ENNReal :=
  ⨅ (σ : Finset (E m)) (hσ : σ ∈ K.K.faces)
      (_ : x.val ∈ cell σ) (_ : y.val ∈ cell σ),
    ENNReal.ofReal
      (modelDist κ d ((K.simplex σ hσ).toModel x.val)
        ((K.simplex σ hσ).toModel y.val))

/-- Intrinsic extended distance: the infimum of lengths of finite
piecewise-geodesic paths. -/
def intrinsicEDist {κ : Geometry} {d m : ℕ}
    (K : Polyhedron κ d m) (x y : ↥K.K.space) : ENNReal :=
  ⨅ (N : ℕ) (p : ℕ → ↥K.K.space)
      (_ : p 0 = x ∧ p N = y),
    ∑ i ∈ Finset.range N, segmentEDist K (p i) (p (i + 1))

/-- Global Lipschitz continuity for the intrinsic distance of the polyhedron. -/
def Lipschitz {κ : Geometry} {d m n : ℕ}
    (K : Polyhedron κ d m)
    (f : ↥K.K.space → Model κ n) (L : ℝ≥0) : Prop :=
  ∀ x y,
    ENNReal.ofReal (modelDist κ n (f x) (f y)) ≤
      (L : ENNReal) * intrinsicEDist K x y

/-- Isometric on every simplex of a finite subdivision. -/
def PLIsometry {κ : Geometry} {d m n : ℕ}
    (K : Polyhedron κ d m) (f : ↥K.K.space → Model κ n) : Prop :=
  ∃ T : _root_.Geometry.SimplicialComplex ℝ (E m),
    T.faces.Finite ∧ T.space = K.K.space ∧
    ∀ σ ∈ T.faces, ∃ (τ : Finset (E m)) (hτ : τ ∈ K.K.faces),
      cell σ ⊆ cell τ ∧
      ∀ x y : ↥K.K.space,
        x.val ∈ cell σ → y.val ∈ cell σ →
          modelDist κ n (f x) (f y) =
            modelDist κ d ((K.simplex τ hτ).toModel x.val)
              ((K.simplex τ hτ).toModel y.val)

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
  sorry

end PLGeometry
