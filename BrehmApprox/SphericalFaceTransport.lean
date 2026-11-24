module

public import BrehmApprox.SphericalActiveProjection
public import BrehmApprox.SimplexFaces

/-!
# Actual spherical face systems in one common Euclidean chart

Central projection converts linearly independent spherical vertex vectors
to affinely independent Euclidean tangent coordinates. Finite spherical
cells become the exact convex hulls of the projected vertices. The face
order, all vertex subfaces, and cofacial intersections are transported
without assuming any reference map or approximation theorem.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeodesicSphere

variable {n : ℕ}

/-- Affine independence of central coordinates is exactly linear
independence of the corresponding unit vectors. -/
theorem gnomonic_affineIndependent_iff {ι : Type*} [Fintype ι]
    (p : GeodesicSphere n) (v : ι → openHemisphere p) :
    AffineIndependent ℝ (fun i => gnomonic p (v i)) ↔
      LinearIndependent ℝ (fun i => (v i).val.val) := by
  constructor
  · intro hai
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    let w : ι → ℝ := fun j => c j * inner ℝ p.val (v j).val.val
    have hw : ∑ j, w j = 0 := by
      have h := congrArg (fun z => inner ℝ p.val z) hc
      simpa only [inner_sum, inner_smul_right, inner_zero_right] using h
    have hsum : ∑ j, w j • gnomonic p (v j) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero, gnomonic_val, smul_sub,
        smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, zero_smul, sub_zero]
      have hterm (j : ι) : w j * (inner ℝ p.val (v j).val.val)⁻¹ = c j := by
        dsimp [w]
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (v j).property), mul_one]
      simpa only [hterm] using hc
    have hweighted : Finset.univ.weightedVSub (fun j => gnomonic p (v j)) w = 0 := by
      rw [Finset.weightedVSub_eq_linear_combination _ hw]
      exact hsum
    have hz := (affineIndependent_iff_of_fintype ℝ _).mp hai w hw hweighted i
    exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (v i).property)
  · intro hlin
    apply (affineIndependent_iff_of_fintype ℝ _).mpr
    intro c hc hweighted i
    rw [Finset.weightedVSub_eq_linear_combination _ hc] at hweighted
    have hsum := congrArg (fun z : tangentPlane p => z.val) hweighted
    simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero, gnomonic_val, smul_sub,
      smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul, hc, zero_smul, sub_zero] at hsum
    have hz := Fintype.linearIndependent_iff.mp hlin _ hsum i
    exact (mul_eq_zero.mp hz).resolve_right (inv_ne_zero (ne_of_gt (v i).property))

end GeodesicSphere

namespace BrehmApprox

open GeodesicSphere

variable {n : ℕ}

theorem projectVertices_independent (p : GeodesicSphere n) (V : Finset (GeodesicSphere n))
    (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (hlin : LinearIndependent ℝ (fun v : V => v.val.val)) :
    AffineIndependent ℝ ((↑) : projectVertices p V hp → tangentPlane p) := by
  have hfamily : AffineIndependent ℝ (fun v : V => gnomonic p ⟨v.val, hp v.val v.property⟩) :=
    (gnomonic_affineIndependent_iff p (fun v : V => ⟨v.val, hp v.val v.property⟩)).mpr hlin
  have hset : (projectVertices p V hp : Set (tangentPlane p)) =
      Set.range (fun v : V => gnomonic p ⟨v.val, hp v.val v.property⟩) := by
    classical
    ext z
    constructor
    · intro hz
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hz
      exact Set.mem_range_self v
    · rintro ⟨v, rfl⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_attach _ _, rfl⟩
  have hprop : AffineIndepOn ℝ id (projectVertices p V hp : Set (tangentPlane p)) := by
    rw [hset]
    exact hfamily.range
  exact hprop

lemma chartVertices_mono (p : GeodesicSphere n) {Q R : Finset (tangentPlane p)}
    (hQR : Q ⊆ R) : chartVertices p Q ⊆ chartVertices p R := by
  classical
  exact Finset.image_subset_image hQR

lemma chartVertices_injective (p : GeodesicSphere n) : Function.Injective (chartVertices p) := by
  classical
  exact Finset.image_injective (gnomonicPoint_injective p)

lemma projectVertices_mono (p : GeodesicSphere n) {V W : Finset (GeodesicSphere n)}
    (hpV : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (hpW : ∀ v ∈ W, 0 < inner ℝ p.val v.val) (hVW : V ⊆ W) :
    projectVertices p V hpV ⊆ projectVertices p W hpW := by
  classical
  intro z hz
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨⟨v.val, hVW v.property⟩, Finset.mem_attach _ _, rfl⟩

lemma projectVertices_subset_iff (p : GeodesicSphere n) {V W : Finset (GeodesicSphere n)}
    (hpV : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (hpW : ∀ v ∈ W, 0 < inner ℝ p.val v.val) :
    projectVertices p V hpV ⊆ projectVertices p W hpW ↔ V ⊆ W := by
  constructor
  · intro h
    have h' := chartVertices_mono p h
    simpa only [chartVertices_projectVertices] using h'
  · exact projectVertices_mono p hpV hpW

lemma projectVertices_chartVertices (p : GeodesicSphere n) (Q : Finset (tangentPlane p))
    (hp : ∀ v ∈ chartVertices p Q, 0 < inner ℝ p.val v.val) :
    projectVertices p (chartVertices p Q) hp = Q := by
  apply chartVertices_injective p
  exact chartVertices_projectVertices p (chartVertices p Q) hp

/-- Exact set-theoretic equality for every finite hemispherical cell, in
the common chart. -/
theorem convexHull_projectVertices_eq_preimage (p : GeodesicSphere n)
    (V : Finset (GeodesicSphere n)) (hp : ∀ v ∈ V, 0 < inner ℝ p.val v.val) :
    convexHull ℝ (projectVertices p V hp : Set (tangentPlane p)) =
      gnomonicPoint p ⁻¹' sphericalCell V := by
  ext z
  exact (gnomonicInverse_mem_cell_iff p V hp z).symm

/-- Genuine finite spherical simplex vertices, their complete subface data,
and the original geometric face incidence relation. -/
structure SphericalSimplicialFaceData {N : ℕ}
    (D : PolyhedralFaceData (sphericalPolytopeModel n) N) where
  vertices : Fin N → Finset (GeodesicSphere n)
  core_eq : ∀ i, D.core i = sphericalCell (vertices i)
  independent : ∀ i, LinearIndependent ℝ (fun v : vertices i => v.val.val)
  vertices_mono : ∀ i j, D.faceLE i j → vertices i ⊆ vertices j
  all_subfaces : ∀ i W, W ⊆ vertices i →
    ∃ j, D.faceLE j i ∧ vertices j = W
  face_of_vertices : ∀ i j k, D.faceLE i k → D.faceLE j k →
    vertices i ⊆ vertices j → D.faceLE i j

namespace SphericalSimplicialFaceData

variable {N : ℕ} {D : PolyhedralFaceData (sphericalPolytopeModel n) N}
  (T : SphericalSimplicialFaceData D) (p : GeodesicSphere n)
  (hp : ∀ i, ∀ v ∈ T.vertices i, 0 < inner ℝ p.val v.val)

include T hp in
lemma core_subset_hemisphere (i : Fin N) : D.core i ⊆ openHemisphere p := by
  rw [T.core_eq i]
  exact fun _ hx => sphericalCell_inner_pos (T.vertices i) p (hp i) hx

/-- The actual Euclidean face system in the common tangent chart.
Its core sets are inverse images under the explicit inverse central map. -/
def gnomonicFaceData : PolyhedralFaceData (euclideanPolytopeModelOf (tangentPlane p)) N where
  faceLE := D.faceLE
  le_refl := D.le_refl
  le_trans := D.le_trans
  index_strict := D.index_strict
  meet := D.meet
  meet_comm := D.meet_comm
  meet_le_left := D.meet_le_left
  meet_le_right := D.meet_le_right
  core := fun i => gnomonicPoint p ⁻¹' D.core i
  polytope_core := by
    intro i
    refine ⟨projectVertices p (T.vertices i) (hp i), ?_⟩
    rw [T.core_eq i, convexHull_projectVertices_eq_preimage]
  core_mono := fun i j hij => Set.preimage_mono (D.core_mono i j hij)
  core_inter := by
    intro i j k hji hki
    rw [← Set.preimage_inter, D.core_inter i j k hji hki]

@[simp]
lemma gnomonicFaceData_core (i : Fin N) :
    (T.gnomonicFaceData p hp).core i = gnomonicPoint p ⁻¹' D.core i := rfl

lemma gnomonicFaceData_core_eq_hull (i : Fin N) :
    (T.gnomonicFaceData p hp).core i =
      convexHull ℝ (projectVertices p (T.vertices i) (hp i) : Set (tangentPlane p)) := by
  rw [gnomonicFaceData_core, T.core_eq i, convexHull_projectVertices_eq_preimage]

/-- Every spherical face and every one of its vertex subfaces is transported
to an actual Euclidean simplex face. No face-incidence assumption is added. -/
def gnomonicSimplicialFaceData : SimplicialFaceData (T.gnomonicFaceData p hp) where
  vertices := fun i => projectVertices p (T.vertices i) (hp i)
  core_eq := T.gnomonicFaceData_core_eq_hull p hp
  independent := fun i => projectVertices_independent p (T.vertices i) (hp i) (T.independent i)
  vertices_mono := fun i j hij => projectVertices_mono p (hp i) (hp j) (T.vertices_mono i j hij)
  all_subfaces := by
    intro i W hW
    have hsub : chartVertices p W ⊆ T.vertices i := by
      have h := chartVertices_mono p hW
      simpa only [chartVertices_projectVertices] using h
    obtain ⟨j, hji, hj⟩ := T.all_subfaces i (chartVertices p W) hsub
    refine ⟨j, hji, ?_⟩
    apply chartVertices_injective p
    rw [chartVertices_projectVertices, hj]
  face_of_vertices := by
    intro i j k hik hjk hij
    exact T.face_of_vertices i j k hik hjk ((projectVertices_subset_iff p (hp i) (hp j)).mp hij)

end SphericalSimplicialFaceData

end BrehmApprox
