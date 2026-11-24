module

public import BrehmApprox.EuclideanPolytopeNeighborhoods
public import BrehmApprox.SphericalPolytopeNeighborhoods
public import BrehmApprox.HyperbolicNeighborhoods

/-!
# A proved polytope interface for all three genuine model spaces

The abstract fields below are instantiated by geometric definitions and
proved theorems. None of these instances declares an axiom.
-/

@[expose] public section

namespace BrehmApprox

universe u

lemma finite_pieces_image {X : Type u} [MetricSpace X] {ι : Type*}
    (C : Finset ι) (cell : ι → Set X) (A : Set X) (f : X → X)
    (Polytope : Set X → Prop) (hA : A = ⋃ v ∈ C, cell v)
    (hcell : ∀ v ∈ C, Polytope (cell v) ∧
      ∀ x ∈ cell v, ∀ y ∈ cell v, dist (f x) (f y) = dist x y) :
    ∃ S : Finset (Set X), A = ⋃ B ∈ S, B ∧
      ∀ B ∈ S, Polytope B ∧
        ∀ x ∈ B, ∀ y ∈ B, dist (f x) (f y) = dist x y := by
  classical
  refine ⟨C.image cell, ?_, ?_⟩
  · rw [hA]
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨cell v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hxv⟩
    · intro hx
      obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
      exact Set.mem_iUnion₂.mpr ⟨v, hv, hxB⟩
  · intro B hB
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
    exact hcell v hv

/-- Exactly the polytope properties used in the collar construction. -/
structure PolytopeModel (X : Type u) [MetricSpace X] (Good : (X → X) → Prop) where
  Polytope : Set X → Prop
  compact : ∀ A, Polytope A → IsCompact A
  determined : ∀ A f, Polytope A → Good f → DeterminedOn A f
  neighborhoods : ∀ A U, Polytope A → IsOpen U → A ⊆ U →
    ∃ W : Set X, Polytope W ∧ IsCompact W ∧ A ⊆ interior W ∧ W ⊆ U
  pieces : ∀ A f, Polytope A → Good f →
    ∃ S : Finset (Set X), A = ⋃ B ∈ S, B ∧
      ∀ B ∈ S, Polytope B ∧
        ∀ x ∈ B, ∀ y ∈ B, dist (f x) (f y) = dist x y

/-- The same proved Euclidean polytope model on an arbitrary finite-dimensional
real inner-product space. This geometric interface uses no Brehm axiom. -/
def euclideanPolytopeModelOf (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : PolytopeModel E LocallyEuclideanPL where
  Polytope := EuclideanPolytope
  compact := fun _ h => isCompact_euclideanPolytope h
  determined := fun _ _ hA hf => determinedOn_euclideanPolytope hA hf
  neighborhoods := fun _ _ hA hU hAU => euclidean_polytope_neighborhood_basis hA hU hAU
  pieces := by
    rintro A f ⟨V, rfl⟩ hf
    obtain ⟨C, hC, hr⟩ := hf V
    apply finite_pieces_image C (fun W => convexHull ℝ (W : Set _)) _ f EuclideanPolytope hC
    intro W hW
    obtain ⟨r, hrW⟩ := hr W hW
    refine ⟨⟨W, rfl⟩, ?_⟩
    intro x hx y hy
    rw [hrW x hx, hrW y hy]
    exact r.isometry.dist_eq x y

def euclideanPolytopeModel (n : ℕ) :
    PolytopeModel (EuclideanSpace ℝ (Fin n)) LocallyEuclideanPL where
  Polytope := EuclideanPolytope
  compact := fun _ h => isCompact_euclideanPolytope h
  determined := fun _ _ hA hf => determinedOn_euclideanPolytope hA hf
  neighborhoods := fun _ _ hA hU hAU => euclidean_polytope_neighborhood_basis hA hU hAU
  pieces := by
    rintro A f ⟨V, rfl⟩ hf
    obtain ⟨C, hC, hr⟩ := hf V
    apply finite_pieces_image C (fun W => convexHull ℝ (W : Set _)) _ f EuclideanPolytope hC
    intro W hW
    obtain ⟨r, hrW⟩ := hr W hW
    refine ⟨⟨W, rfl⟩, ?_⟩
    intro x hx y hy
    rw [hrW x hx, hrW y hy]
    exact r.isometry.dist_eq x y

/-- A genuine hemispherical geodesic polytope. -/
def SphericalPolytope {n : ℕ} (A : Set (GeodesicSphere n)) : Prop :=
  ∃ V : Finset (GeodesicSphere n), InOpenHemisphere V ∧ A = sphericalCell V

def sphericalPolytopeModel (n : ℕ) :
    PolytopeModel (GeodesicSphere n) LocallySphericalPL where
  Polytope := SphericalPolytope
  compact := by
    rintro A ⟨V, hV, rfl⟩
    exact isCompact_sphericalCell V hV
  determined := by
    rintro A f ⟨V, hV, rfl⟩ hf
    exact determinedOn_sphericalCell hf V hV
  neighborhoods := by
    rintro A U ⟨V, hV, rfl⟩ hU hVU
    obtain ⟨W, hW, hVW, hWU⟩ := exists_sphericalCell_neighborhood V hV hU hVU
    exact ⟨sphericalCell W, ⟨W, hW, rfl⟩, isCompact_sphericalCell W hW, hVW, hWU⟩
  pieces := by
    rintro A f ⟨V, hV, rfl⟩ hf
    obtain ⟨C, hC, hr⟩ := hf V hV
    apply finite_pieces_image C sphericalCell _ f SphericalPolytope hC
    intro W hW
    obtain ⟨hhem, r, hrW⟩ := hr W hW
    refine ⟨⟨W, hhem, rfl⟩, ?_⟩
    intro x hx y hy
    rw [hrW x hx, hrW y hy]
    exact (GeodesicSphere.mapEquiv r).dist_eq x y

/-- A genuine compact geodesic polytope in the hyperboloid model. -/
def HyperbolicPolytope {n : ℕ} (A : Set (HyperbolicSpace n)) : Prop :=
  ∃ V : Finset (HyperbolicSpace n), A = hyperbolicCell V

def hyperbolicPolytopeModel (n : ℕ) :
    PolytopeModel (HyperbolicSpace n) LocallyHyperbolicPL where
  Polytope := HyperbolicPolytope
  compact := by
    rintro A ⟨V, rfl⟩
    exact isCompact_hyperbolicCell V
  determined := by
    rintro A f ⟨V, rfl⟩ hf
    exact determinedOn_hyperbolicCell hf V
  neighborhoods := by
    rintro A U ⟨V, rfl⟩ hU hVU
    obtain ⟨W, hW, hVW, hWU⟩ := hyperbolicCell_compact_neighborhood_basis V hU hVU
    exact ⟨hyperbolicCell W, ⟨W, rfl⟩, hW, hVW, hWU⟩
  pieces := by
    rintro A f ⟨V, rfl⟩ hf
    obtain ⟨C, hC, hr⟩ := hf V
    apply finite_pieces_image C hyperbolicCell _ f HyperbolicPolytope hC
    intro W hW
    obtain ⟨r, hrW⟩ := hr W hW
    refine ⟨⟨W, rfl⟩, ?_⟩
    intro x hx y hy
    rw [hrW x hx, hrW y hy]
    exact r.dist_eq x y

end BrehmApprox
