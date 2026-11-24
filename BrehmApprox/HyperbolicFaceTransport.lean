module

public import BrehmApprox.HyperbolicSimplicialCharts
public import BrehmApprox.SimplexFaces
public import BrehmApprox.PolytopeModels

/-!
# Actual hyperbolic simplex faces in Klein coordinates

Finite vertex families are required to be linearly independent in the genuine
Lorentz lift. Klein projection converts their geodesic cells exactly into
ordinary Euclidean simplices. The original face relation, all vertex subfaces,
and cofacial intersections are transported without adding preparation or
approximation hypotheses.
-/

@[expose] public section

noncomputable section

open Classical

namespace BrehmApprox

open HyperbolicSpace

variable {n N : ℕ}

/-- Genuine finite hyperbolic simplex data, including every vertex subface.
No reference map, flattening, collar, or approximation occurs in these data. -/
structure HyperbolicSimplicialFaceData
    (D : PolyhedralFaceData (hyperbolicPolytopeModel n) N) where
  vertices : Fin N → Finset (HyperbolicSpace n)
  core_eq : ∀ i, D.core i = hyperbolicCell (vertices i)
  independent : ∀ i, LinearIndependent ℝ (fun v : vertices i => lift (v : HyperbolicSpace n))
  vertices_mono : ∀ i j, D.faceLE i j → vertices i ⊆ vertices j
  all_subfaces : ∀ i W, W ⊆ vertices i →
    ∃ j, D.faceLE j i ∧ vertices j = W
  face_of_vertices : ∀ i j k, D.faceLE i k → D.faceLE j k →
    vertices i ⊆ vertices j → D.faceLE i j

namespace HyperbolicSimplicialFaceData

variable {D : PolyhedralFaceData (hyperbolicPolytopeModel n) N}
    (T : HyperbolicSimplicialFaceData D)

include T in
lemma klein_core_polytope (i : Fin N) :
    (euclideanPolytopeModel n).Polytope (klein '' D.core i) := by
  refine ⟨(T.vertices i).image klein, ?_⟩
  rw [T.core_eq i, klein_image_cell]

/-- The face system whose cores are the actual images under the global Klein
chart. Unlike the spherical chart, this map is globally defined and injective. -/
def kleinFaceData : PolyhedralFaceData (euclideanPolytopeModel n) N where
  faceLE := D.faceLE
  le_refl := D.le_refl
  le_trans := D.le_trans
  index_strict := D.index_strict
  meet := D.meet
  meet_comm := D.meet_comm
  meet_le_left := D.meet_le_left
  meet_le_right := D.meet_le_right
  core := fun i => klein '' D.core i
  polytope_core := T.klein_core_polytope
  core_mono := fun i j hij => Set.image_mono (D.core_mono i j hij)
  core_inter := by
    intro i j k hji hki
    rw [← D.core_inter i j k hji hki]
    exact (Set.image_inter klein_injective).symm

@[simp]
lemma kleinFaceData_core (i : Fin N) :
    T.kleinFaceData.core i = klein '' D.core i := rfl

@[simp]
lemma kleinFaceData_faceLE (i j : Fin N) :
    T.kleinFaceData.faceLE i j ↔ D.faceLE i j := Iff.rfl

@[simp]
lemma kleinFaceData_meet (i j : Fin N) :
    T.kleinFaceData.meet i j = D.meet i j := rfl

lemma kleinFaceData_core_eq_hull (i : Fin N) :
    T.kleinFaceData.core i =
      convexHull ℝ ((T.vertices i).image klein : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [kleinFaceData_core, T.core_eq i, klein_image_cell]

/-- Exact transport of all the geometric simplex information, including the
vertex subfaces used to construct the Euclidean flattening. -/
def kleinSimplicialFaceData : SimplicialFaceData T.kleinFaceData where
  vertices := fun i => (T.vertices i).image klein
  core_eq := T.kleinFaceData_core_eq_hull
  independent := fun i => affineIndependent_klein_vertices (T.vertices i) (T.independent i)
  vertices_mono := fun i j hij => Finset.image_subset_image (T.vertices_mono i j hij)
  all_subfaces := by
    intro i W hW
    obtain ⟨V, hV, hVW⟩ := exists_vertex_subface_of_klein_image (T.vertices i) W hW
    obtain ⟨j, hji, hj⟩ := T.all_subfaces i V hV
    refine ⟨j, hji, ?_⟩
    rw [hj, hVW]
  face_of_vertices := by
    intro i j k hik hjk hij
    exact T.face_of_vertices i j k hik hjk
      ((klein_vertex_image_subset_iff (T.vertices i) (T.vertices j)).mp hij)

include T in
lemma norm_klein_le_on_core {ρ : ℝ}
    (hV : ∀ i v, v ∈ T.vertices i → ‖klein v‖ ≤ ρ)
    (i : Fin N) {x : HyperbolicSpace n} (hx : x ∈ D.core i) : ‖klein x‖ ≤ ρ := by
  apply norm_klein_le_of_vertex_bounds (T.vertices i) (hV i)
  rwa [← T.core_eq i]

include T in
/-- One uniform chart comparison across any pair of folded cores. The
constant depends on their common radius and not on the number of faces. -/
theorem core_chart_distortion {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hV : ∀ i v, v ∈ T.vertices i → ‖klein v‖ ≤ ρ)
    (i j : Fin N) {x y : HyperbolicSpace n} (hx : x ∈ D.core i) (hy : y ∈ D.core j) :
    dist (klein x) (klein y) ≤ dist x y ∧
      dist x y ≤ (1 - ρ ^ 2)⁻¹ * dist (klein x) (klein y) := by
  refine ⟨klein_dist_le x y, ?_⟩
  have h := dist_fromKlein_le hρ0 hρ1
    (T.norm_klein_le_on_core hV i hx) (T.norm_klein_le_on_core hV j hy)
  simpa only [fromKlein_klein, dist_eq_norm] using h

end HyperbolicSimplicialFaceData
end BrehmApprox
