module

public import PLGeometry.FoldedCoordinateCover
public import BrehmApprox.SphericalFiniteSelection
public import BrehmApprox.SphericalCommonChart

/-! # Compatible spherical triangulations in a common hemisphere -/

@[expose] public section
noncomputable section

open Set BrehmApprox GeodesicSphere

namespace ArchivePLGeometry

universe u
variable {P : Type u} [MetricSpace P] {n : ℕ} {I : Type*}
    {q : P → GeodesicSphere n}

local instance foldedSphericalPLDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

omit [MetricSpace P] in
theorem chartVertices_folded_image (p : GeodesicSphere n)
    (hhem : ∀ x, q x ∈ openHemisphere p) (S : Finset P) :
    chartVertices p (S.image (fun x => gnomonicTotal p (q x))) = S.image q := by
  unfold chartVertices
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact gnomonicPoint_gnomonicTotal p (hhem x)

omit [MetricSpace P] in
theorem spherical_image_simplexCell (p : GeodesicSphere n)
    (hhem : ∀ x, q x ∈ openHemisphere p)
    (K : FoldedPolytopeCover (fun x => gnomonicTotal p (q x)) I)
    (S : Finset P) (i : I) (hSi : (S : Set P) ⊆ K.cell i) :
    q '' K.simplexCell S = sphericalCell (S.image q) := by
  calc
    q '' K.simplexCell S = gnomonicPoint p ''
        ((fun x => gnomonicTotal p (q x)) '' K.simplexCell S) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨gnomonicTotal p (q x), ⟨x, hx, rfl⟩, gnomonicPoint_gnomonicTotal p (hhem x)⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, (gnomonicPoint_gnomonicTotal p (hhem x)).symm⟩
    _ = gnomonicPoint p '' convexHull ℝ
        (S.image (fun x => gnomonicTotal p (q x)) : Set (tangentPlane p)) := by
      have h := congrArg (Set.image (gnomonicPoint p)) (K.image_simplexCell S i hSi)
      simpa only [Finset.coe_image] using h
    _ = sphericalCell (S.image q) := by
      rw [← sphericalCell_chartVertices_eq_image, chartVertices_folded_image p hhem S]

set_option maxHeartbeats 800000 in
def sphericalTriangulationOfFoldedCover [Finite I] [LinearOrder P]
    (p : GeodesicSphere n) (hhem : ∀ x, q x ∈ openHemisphere p)
    (K : FoldedPolytopeCover (fun x => gnomonicTotal p (q x)) I)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y) : Triangulation .spherical n P where
  simplices := K.simplices
  cell := K.simplexCell
  chart _ := q
  cover := K.simplex_cover
  locallyFinite := by
    let : Finite K.simplices := K.simplices_finite.to_subtype
    exact locallyFinite_of_finite _
  vertices_mem _ hS := K.vertices_mem_simplex hS
  simplex S hS := by
    have hpV : ∀ v ∈ S.image q, v ∈ openHemisphere p := by
      intro v hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
      exact hhem x
    refine ⟨⟨p, hpV⟩, ?_⟩
    apply (gnomonic_affineIndependent_iff p
      (fun v : S.image q => ⟨v.val, hpV v.val v.property⟩)).mp
    let e : S.image q ↪ (S.image q).image (gnomonicTotal p) :=
      ⟨fun v => ⟨gnomonicTotal p v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩,
        fun v w h => Subtype.ext ((gnomonicTotal_injOn p)
          (hpV v.val v.property) (hpV w.val w.property) (congrArg Subtype.val h))⟩
    have hind : AffineIndependent ℝ
        ((↑) : (S.image q).image (gnomonicTotal p) → tangentPlane p) := by
      change AffineIndependent ℝ
        ((↑) : ((S.image q).image (gnomonicTotal p) : Set (tangentPlane p)) → tangentPlane p)
      have hset : ((S.image q).image (gnomonicTotal p) : Set (tangentPlane p)) =
          (fun x => gnomonicTotal p (q x)) '' (S : Set P) := by
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
    have hi := AffineIndependent.comp_embedding e hind
    convert hi using 1
    funext v
    exact (gnomonicTotal_apply p (hpV v.val v.property)).symm
  image_cell S hS := by
    obtain ⟨i, hi⟩ := hS
    exact spherical_image_simplexCell p hhem K S i (K.simplex_vertices_subset hi)
  isometry_cell S hS x hx y hy := by
    obtain ⟨i, hi⟩ := hS
    rw [K.simplexCell_eq S i (K.simplex_vertices_subset hi)] at hx hy
    exact hiso i x hx.1 y hy.1
  faces _ hS _ hTS := K.simplices_downward hS hTS
  image_face S hS T hTS := by
    obtain ⟨i, hi⟩ := hS
    exact spherical_image_simplexCell p hhem K T i
      ((Finset.coe_subset.mpr hTS).trans (K.simplex_vertices_subset hi))
  intersection _ hS _ hT := K.simplex_intersection hS hT

theorem plIsometry_spherical_of_folded_orthogonal_selection
    [Finite I] (p : GeodesicSphere n) (hhem : ∀ x, q x ∈ openHemisphere p)
    (K : FoldedPolytopeCover (fun x => gnomonicTotal p (q x)) I)
    (hc : ∀ i, IsCompact (K.cell i)) (hq : Continuous q)
    (hiso : ∀ i, ∀ x ∈ K.cell i, ∀ y ∈ K.cell i,
      dist (q x) (q y) = dist x y)
    {J : Type*} [Finite J]
    (r : J → EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {g : P → GeodesicSphere n} (hg : Continuous g)
    (hsel : ∀ x, ∃ j, g x = mapEquiv (r j) (q x)) : PLIsometry .spherical n g := by
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
  refine ⟨hg, T, ?_⟩
  intro S hS x hx y hy
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

end ArchivePLGeometry

namespace BrehmApprox.FoldedGeometry

variable {P : Type*} [MetricSpace P] {n N : ℕ}
    (G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N)

def gnomonicPolytopeCover (T : SphericalSimplicialFaceData G.toPolyhedralFaceData)
    (p : GeodesicSphere n) (hp : ∀ i, ∀ v ∈ T.vertices i, 0 < inner ℝ p.val v.val) :
    FoldedPolytopeCover (fun x => gnomonicTotal p (G.fold x)) (Fin N) :=
  G.coordinatePolytopeCover (T.gnomonicFaceData p hp) (T.gnomonicSimplicialFaceData p hp)
    (gnomonicTotal p) (fun _ _ => Iff.rfl) (T.gnomonicFaceData_core_eq_image p hp)
    (T.gnomonicTotal_injective_core p hp)

end BrehmApprox.FoldedGeometry

namespace ArchivePLGeometry

variable {P : Type*} [MetricSpace P] {n N : ℕ}
    (G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N)
    (T : SphericalSimplicialFaceData G.toPolyhedralFaceData)

include T in
theorem plIsometry_spherical_of_model_maps
    (p : GeodesicSphere n) (hhem : ∀ x, G.fold x ∈ openHemisphere p)
    {g : P → GeodesicSphere n} (hg : Continuous g)
    (hm : G.RealizedByModelMaps g) : PLIsometry .spherical n g := by
  have hp : ∀ i, ∀ v ∈ T.vertices i, 0 < inner ℝ p.val v.val := by
    intro i v hv
    have hvi : v ∈ G.core i := by
      rw [T.core_eq i]
      exact mem_sphericalCell_of_mem hv
    rw [← G.image_cell i] at hvi
    obtain ⟨x, _, rfl⟩ := hvi
    exact hhem x
  obtain ⟨R, hR⟩ := hm.spherical_motions
  apply plIsometry_spherical_of_folded_orthogonal_selection p hhem (G.gnomonicPolytopeCover T p hp)
    (G.compact_cell p) ((G.constantSource p).fold_lipschitz G.intrinsic).continuous
    G.isometry_cell (fun r : R => r.val) hg
  intro x
  obtain ⟨r, hr, heq⟩ := hR x
  exact ⟨⟨r, hr⟩, heq⟩

end ArchivePLGeometry
