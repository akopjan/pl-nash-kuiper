module

public import PLGeometry.ModelBarycentric

/-! # Barycentric coordinates are preserved by model isometries -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.ModelBarycentric

variable {ι : Type*} [Fintype ι] {κ : Geometry} {n : ℕ}

local instance modelBarycentricNaturalityDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance modelBarycentricNaturalityEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance modelBarycentricNaturalitySDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance modelBarycentricNaturalityHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _

theorem represents_transfer (v u : ι → Model κ n) (hv : Independent κ n v)
    (hd : ∀ i j, dist (v i) (v j) = dist (u i) (u j))
    (w : Weights ι) (x y : Model κ n)
    (hxy : ∀ i, dist y (u i) = dist x (v i))
    (hrep : Represents κ n v w.val x) : Represents κ n u w.val y := by
  have hx : x ∈ hull κ n (Finset.univ.image v) := by
    rw [← point_eq_of_represents v hv w x hrep]
    exact point_mem v hv w
  cases κ with
  | euclidean =>
    obtain ⟨r, hr⟩ := exists_ambient_distance_isometry v u hv hd
    have hmove : r x = y := affineIsometry_eq_of_vertex_distances r hx (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      rw [hr i]
      exact hxy i)
    have hm := Finset.univ.map_affineCombination v w.val w.property.2 r.toAffineMap
    simp only [Finset.affineCombination_eq_linear_combination _ _ _ w.property.2] at hm
    change ∑ i, w.val i • u i = y
    change ∑ i, w.val i • v i = x at hrep
    calc
      ∑ i, w.val i • u i = ∑ i, w.val i • r (v i) := by simp only [hr]
      _ = r (∑ i, w.val i • v i) := hm.symm
      _ = y := by rw [hrep, hmove]
  | spherical =>
    obtain ⟨r, hr⟩ := exists_spherical_vertex_motion v u hv hd
    have hmove : GeodesicSphere.mapEquiv r x = y := sphericalMotion_eq_of_vertex_distances r hx (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      rw [hr i]
      exact hxy i)
    obtain ⟨c, hc, he⟩ := hrep
    refine ⟨c, hc, ?_⟩
    have hvmap (i : ι) : r (v i).val = (u i).val := congrArg GeodesicSphere.val (hr i)
    have hxmap : r x.val = y.val := congrArg GeodesicSphere.val hmove
    have hh := congrArg r he
    simpa only [map_sum, map_smul, hvmap, hxmap] using hh
  | hyperbolic =>
    obtain ⟨r, hr⟩ := HyperbolicSpace.exists_vertex_motion v u hv hd
    have hmove : r x = y := hyperbolicMotion_eq_of_vertex_distances r hx (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      rw [hr i]
      exact hxy i)
    obtain ⟨L, hL⟩ := HyperbolicSpace.exists_lorentz_linear_lift r
    obtain ⟨c, hc, he⟩ := hrep
    refine ⟨c, hc, ?_⟩
    have hh := congrArg L he
    simpa only [map_sum, map_smul, hL, hr, hmove] using hh

end ArchivePLGeometry.ModelBarycentric
