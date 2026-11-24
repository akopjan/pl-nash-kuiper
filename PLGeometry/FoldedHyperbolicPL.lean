module

public import PLGeometry.FoldedCoordinateCover
public import BrehmApprox.HyperbolicFiniteSelection
public import BrehmApprox.HyperbolicFaceTransport
public import BrehmApprox.HyperbolicIsometryClassification

/-! # Compatible hyperbolic triangulations of folded motion selections -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.HyperbolicSpace

namespace ArchivePLGeometry

universe u
variable {P : Type u} [MetricSpace P] {n : ℕ} {I : Type*}
    {q : P → HyperbolicSpace n}

local instance foldedHyperbolicPLDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

set_option maxHeartbeats 800000 in
def hyperbolicTriangulationOfFoldedCover [Finite I] [LinearOrder P]
    (K : FoldedPolytopeCover (fun x => klein (q x)) I)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y) : Triangulation .hyperbolic n P where
  simplices := K.simplices
  cell := K.simplexCell
  chart _ := q
  cover := K.simplex_cover
  locallyFinite := by
    let : Finite K.simplices := K.simplices_finite.to_subtype
    exact locallyFinite_of_finite _
  vertices_mem _ hS := K.vertices_mem_simplex hS
  simplex S hS := by
    change LinearIndependent ℝ (fun v : S.image q => lift v.val)
    apply (linearIndependent_lift_iff_affineIndependent_klein
      ((↑) : S.image q → HyperbolicSpace n)).mpr
    let e : S.image q ↪ (S.image q).image klein :=
      ⟨fun v => ⟨klein v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩,
        fun v w h => Subtype.ext (klein_injective (congrArg Subtype.val h))⟩
    have hind : AffineIndependent ℝ ((↑) : (S.image q).image klein → EuclideanSpace ℝ (Fin n)) := by
      change AffineIndependent ℝ
        ((↑) : ((S.image q).image klein : Set (EuclideanSpace ℝ (Fin n))) →
          EuclideanSpace ℝ (Fin n))
      have hset : ((S.image q).image klein : Set (EuclideanSpace ℝ (Fin n))) =
          (fun x => klein (q x)) '' (S : Set P) := by
        ext z
        constructor
        · intro hz
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact Finset.mem_image.mpr ⟨q x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩
      rw [hset]
      exact K.simplex_independent_image hS
    exact AffineIndependent.comp_embedding e hind
  image_cell S hS := by
    obtain ⟨i, hi⟩ := hS
    change q '' K.simplexCell S = hyperbolicCell (S.image q)
    apply (Set.image_injective.mpr klein_injective)
    rw [Set.image_image, klein_image_cell]
    simpa only [Finset.coe_image, Set.image_image, Function.comp_def] using
      K.image_simplexCell S i (K.simplex_vertices_subset hi)
  isometry_cell S hS x hx y hy := by
    obtain ⟨i, hi⟩ := hS
    rw [K.simplexCell_eq S i (K.simplex_vertices_subset hi)] at hx hy
    exact hiso i x hx.1 y hy.1
  faces _ hS _ hTS := K.simplices_downward hS hTS
  image_face S hS T hTS := by
    obtain ⟨i, hi⟩ := hS
    change q '' K.simplexCell T = hyperbolicCell (T.image q)
    apply (Set.image_injective.mpr klein_injective)
    rw [Set.image_image, klein_image_cell]
    simpa only [Finset.coe_image, Set.image_image, Function.comp_def] using
      K.image_simplexCell T i
        ((Finset.coe_subset.mpr hTS).trans (K.simplex_vertices_subset hi))
  intersection _ hS _ hT := K.simplex_intersection hS hT

theorem plIsometry_hyperbolic_of_folded_lorentz_selection
    [Finite I] (K : FoldedPolytopeCover (fun x => klein (q x)) I)
    (hc : ∀ i, IsCompact (K.cell i)) (hq : Continuous q)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y)
    {J : Type*} [Finite J] (r : J → HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    (L : J → (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    (hL : ∀ j x, lift (r j x) = L j (lift x))
    {g : P → HyperbolicSpace n} (hg : Continuous g)
    (hsel : ∀ x, ∃ j, g x = r j (q x)) : PLIsometry .hyperbolic n g := by
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
  refine ⟨hg, T, ?_⟩
  intro S hS x hx y hy
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

end ArchivePLGeometry

namespace BrehmApprox.FoldedGeometry

variable {P : Type*} [MetricSpace P] {n N : ℕ}
    (G : FoldedGeometry (P := P) (hyperbolicPolytopeModel n) N)

def kleinPolytopeCover (T : HyperbolicSimplicialFaceData G.toPolyhedralFaceData) :
    FoldedPolytopeCover (fun x => klein (G.fold x)) (Fin N) :=
  G.coordinatePolytopeCover T.kleinFaceData T.kleinSimplicialFaceData klein
    (fun _ _ => Iff.rfl) (fun _ => rfl) (fun _ => klein_injective.injOn)

end BrehmApprox.FoldedGeometry

namespace ArchivePLGeometry

variable {P : Type*} [MetricSpace P] {n N : ℕ}
    (G : FoldedGeometry (P := P) (hyperbolicPolytopeModel n) N)
    (T : HyperbolicSimplicialFaceData G.toPolyhedralFaceData)

include T in
theorem plIsometry_hyperbolic_of_model_maps
    {g : P → HyperbolicSpace n} (hg : Continuous g)
    (hm : G.RealizedByModelMaps g) : PLIsometry .hyperbolic n g := by
  classical
  obtain ⟨R, hR⟩ := hm.hyperbolic_motions
  have hlinear := fun r : R => exists_lorentz_linear_lift r.val
  choose L hL using hlinear
  apply plIsometry_hyperbolic_of_folded_lorentz_selection (G.kleinPolytopeCover T)
    (G.compact_cell ⟨0⟩) ((G.constantSource ⟨0⟩).fold_lipschitz G.intrinsic).continuous
    G.isometry_cell (fun r : R => r.val) L (fun r x => (hL r x).symm) hg
  intro x
  obtain ⟨r, hr, heq⟩ := hR x
  exact ⟨⟨r, hr⟩, heq⟩

end ArchivePLGeometry
