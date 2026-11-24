module

public import Compatibility.SetRigidity
public import PLGeometry.CompactTriangulation
public import PLGeometry.FoldedEuclideanPL
public import PLGeometry.FoldedHyperbolicPL
public import PLGeometry.FoldedSphericalPL

/-! Retaining the finite refinement in the genuine finite-motion constructions. -/

@[expose] public section
noncomputable section

open Set BrehmApprox ArchivePLGeometry

namespace PLGeometry.Refined

universe u

variable {P : Type u} [MetricSpace P] {I : Type*}

/-- A finite PL decomposition refining the displayed finite source cover. -/
def FinitePLRefinement (κ : ArchivePLGeometry.Geometry) (n : ℕ)
    (cell : I → Set P) (g : P → ArchivePLGeometry.Model κ n) : Prop :=
  Continuous g ∧ ∃ T : ArchivePLGeometry.Triangulation κ n P,
    T.simplices.Finite ∧
    (∀ σ ∈ T.simplices, ∃ i, T.cell σ ⊆ cell i) ∧
    ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (g x) (g y) = dist x y

theorem FinitePLRefinement.plIsometry {κ : ArchivePLGeometry.Geometry} {n : ℕ}
    {cell : I → Set P} {g : P → ArchivePLGeometry.Model κ n}
    (h : FinitePLRefinement κ n cell g) : ArchivePLGeometry.PLIsometry κ n g := by
  obtain ⟨hg, T, _, _, hT⟩ := h
  exact ⟨hg, T, hT⟩

local instance refinedDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

section Euclidean

variable {n : ℕ} {q : P → EuclideanSpace ℝ (Fin n)}

theorem euclidean_of_motion_selection
    [Finite I] (K : FoldedPolytopeCover q I)
    (hc : ∀ i, IsCompact (K.cell i)) (hq : Continuous q)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y)
    {J : Type*} [Finite J]
    (r : J → EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    {g : P → EuclideanSpace ℝ (Fin n)} (hg : Continuous g)
    (hsel : ∀ x, ∃ j, g x = r j (q x)) : FinitePLRefinement .euclidean n K.cell g := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : LinearOrder P := IsWellOrder.linearOrder (WellOrderingRel : P → P → Prop)
  let a := fun j => (r j).toAffineMap
  let A := K.arrangement (affineEqualityLinear a) (affineEqualityBound a)
  have hisoA : ∀ i, ∀ x ∈ A.cell i, ∀ y ∈ A.cell i,
      dist (q x) (q y) = dist x y :=
    fun i x hx y hy => hiso i.val.1 x hx.1 y hy.1
  let T := euclideanTriangulationOfFoldedCover A hisoA
  refine ⟨hg, T, A.simplices_finite, ?_, ?_⟩
  · intro S hS
    obtain ⟨i, hi⟩ := hS
    refine ⟨i.val.1, ?_⟩
    intro x hx
    change x ∈ A.simplexCell S at hx
    rw [A.simplexCell_eq S i (A.simplex_vertices_subset hi)] at hx
    exact hx.1.1
  · intro S hS x hx y hy
    obtain ⟨i, hi⟩ := hS
    change x ∈ A.simplexCell S at hx
    change y ∈ A.simplexCell S at hy
    rw [A.simplexCell_eq S i (A.simplex_vertices_subset hi)] at hx hy
    obtain ⟨j, hj⟩ := K.affine_selection_eqOn_arrangement hc hq a hg hsel i
    rw [hj x hx.1, hj y hy.1]
    exact ((r j).isometry.dist_eq (q x) (q y)).trans (hisoA i x hx.1 y hy.1)

end Euclidean

section Hyperbolic
open BrehmApprox.HyperbolicSpace

variable {n : ℕ} {q : P → HyperbolicSpace n}

theorem hyperbolic_of_motion_selection
    [Finite I] (K : FoldedPolytopeCover (fun x => klein (q x)) I)
    (hc : ∀ i, IsCompact (K.cell i)) (hq : Continuous q)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y)
    {J : Type*} [Finite J] (r : J → HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    (L : J → (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    (hL : ∀ j x, lift (r j x) = L j (lift x))
    {g : P → HyperbolicSpace n} (hg : Continuous g)
    (hsel : ∀ x, ∃ j, g x = r j (q x)) : FinitePLRefinement .hyperbolic n K.cell g := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : LinearOrder P := IsWellOrder.linearOrder (WellOrderingRel : P → P → Prop)
  let f : P → ℝ × EuclideanSpace ℝ (Fin n) := fun x =>
    (Hyperboloid.height (q x).point)⁻¹ • lift (g x)
  have hf : Continuous f :=
    (((Hyperboloid.continuous_height.comp continuous_point).comp hq).inv₀
      (fun x => (Hyperboloid.height_pos (q x).point).ne')).smul (continuous_lift.comp hg)
  let a := fun j => kleinAffine (L j)
  have hr (j : J) (x : P) :
      (Hyperboloid.height (q x).point)⁻¹ • lift (r j (q x)) = a j (klein (q x)) := by
    have h := kleinLift_eq_affine_of_lift (g := r j) (L j) (norm_klein_lt_one (q x))
      (hL j (fromKlein (klein (q x))))
    simpa only [kleinLift, fromKlein_klein] using h
  have hselect : ∀ x, ∃ j, f x = a j (klein (q x)) := by
    intro x
    obtain ⟨j, hj⟩ := hsel x
    exact ⟨j, by dsimp only [f]; rw [hj]; exact hr j x⟩
  let A := K.arrangement (affineEqualityLinear a) (affineEqualityBound a)
  have hisoA : ∀ i, ∀ x ∈ A.cell i, ∀ y ∈ A.cell i,
      dist (q x) (q y) = dist x y := fun i x hx y hy => hiso i.val.1 x hx.1 y hy.1
  let T := hyperbolicTriangulationOfFoldedCover A hisoA
  refine ⟨hg, T, A.simplices_finite, ?_, ?_⟩
  · intro S hS
    obtain ⟨i, hi⟩ := hS
    refine ⟨i.val.1, ?_⟩
    intro x hx
    change x ∈ A.simplexCell S at hx
    rw [A.simplexCell_eq S i (A.simplex_vertices_subset hi)] at hx
    exact hx.1.1
  · intro S hS x hx y hy
    obtain ⟨i, hi⟩ := hS
    change x ∈ A.simplexCell S at hx
    change y ∈ A.simplexCell S at hy
    rw [A.simplexCell_eq S i (A.simplex_vertices_subset hi)] at hx hy
    obtain ⟨j, hj⟩ := K.affine_selection_eqOn_arrangement hc (continuous_klein.comp hq)
      a hf hselect i
    have heq (z : P) (hz : z ∈ A.cell i) : g z = r j (q z) := by
      apply lift_injective
      apply (smul_right_injective _ (inv_ne_zero (Hyperboloid.height_pos (q z).point).ne'))
      exact (hj z hz).trans (hr j z).symm
    rw [heq x hx.1, heq y hy.1, (r j).dist_eq]
    exact hisoA i x hx.1 y hy.1

end Hyperbolic

section Spherical
open GeodesicSphere

variable {n : ℕ} {q : P → GeodesicSphere n}

theorem spherical_of_motion_selection
    [Finite I] (p : GeodesicSphere n) (hhem : ∀ x, q x ∈ openHemisphere p)
    (K : FoldedPolytopeCover (fun x => gnomonicTotal p (q x)) I)
    (hc : ∀ i, IsCompact (K.cell i)) (hq : Continuous q)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y)
    {J : Type*} [Finite J]
    (r : J → EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {g : P → GeodesicSphere n} (hg : Continuous g)
    (hsel : ∀ x, ∃ j, g x = mapEquiv (r j) (q x)) : FinitePLRefinement .spherical n K.cell g := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : LinearOrder P := IsWellOrder.linearOrder (WellOrderingRel : P → P → Prop)
  let coord : P → tangentPlane p := fun x => gnomonicTotal p (q x)
  have hcoord : Continuous coord := (continuousOn_gnomonicTotal p).comp_continuous hq hhem
  let f : P → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => gnomonicScale p (coord x) • (g x).val
  have hf : Continuous f :=
    (continuous_const.add (continuous_subtype_val.comp hcoord)).norm.smul (continuous_val.comp hg)
  let a := fun j => sphericalAffine p (r j)
  have hr (j : J) (x : P) :
      gnomonicScale p (coord x) • (mapEquiv (r j) (q x)).val = a j (coord x) := by
    have h := sphericalLift_eq_affine_of_eq p (r j)
      (f := mapEquiv (r j)) (z := coord x) rfl
    simpa only [sphericalLift, coord, gnomonicPoint_gnomonicTotal p (hhem x)] using h
  have hselect : ∀ x, ∃ j, f x = a j (coord x) := by
    intro x
    obtain ⟨j, hj⟩ := hsel x
    exact ⟨j, by dsimp only [f]; rw [hj]; exact hr j x⟩
  let A := K.arrangement (affineEqualityLinear a) (affineEqualityBound a)
  have hisoA : ∀ i, ∀ x ∈ A.cell i, ∀ y ∈ A.cell i,
      dist (q x) (q y) = dist x y := fun i x hx y hy => hiso i.val.1 x hx.1 y hy.1
  let T := sphericalTriangulationOfFoldedCover p hhem A hisoA
  refine ⟨hg, T, A.simplices_finite, ?_, ?_⟩
  · intro S hS
    obtain ⟨i, hi⟩ := hS
    refine ⟨i.val.1, ?_⟩
    intro x hx
    change x ∈ A.simplexCell S at hx
    rw [A.simplexCell_eq S i (A.simplex_vertices_subset hi)] at hx
    exact hx.1.1
  · intro S hS x hx y hy
    obtain ⟨i, hi⟩ := hS
    change x ∈ A.simplexCell S at hx
    change y ∈ A.simplexCell S at hy
    rw [A.simplexCell_eq S i (A.simplex_vertices_subset hi)] at hx hy
    obtain ⟨j, hj⟩ := K.affine_selection_eqOn_arrangement hc hcoord a hf hselect i
    have heq (z : P) (hz : z ∈ A.cell i) : g z = mapEquiv (r j) (q z) := by
      apply GeodesicSphere.ext
      apply smul_right_injective _ (gnomonicScale_pos p (coord z)).ne'
      exact (hj z hz).trans (hr j z).symm
    rw [heq x hx.1, heq y hy.1, (mapEquiv (r j)).dist_eq]
    exact hisoA i x hx.1 y hy.1

end Spherical

end PLGeometry.Refined
