module

public import BrehmApprox.HyperbolicLocalCharts
public import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Simplicial data in an actual hyperbolic Klein chart

Lorentz linear independence is equivalent to affine independence of the
Klein coordinates.  The exact finite cell image, radius control from finite
vertices and the metric chart bounds give the local simplex data needed to
transport a supplied initial folding to an ordinary Euclidean simplicial
source metric.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace BrehmApprox

lemma affineIndependent_iff_homogeneous_linearIndependent
    {ι E : Type*} [AddCommGroup E] [Module ℝ E] (p : ι → E) :
    AffineIndependent ℝ p ↔ LinearIndependent ℝ (fun i => ((1 : ℝ), p i)) := by
  rw [affineIndependent_iff, linearIndependent_iff']
  constructor
  · intro h s w hsum
    have h0 := congrArg (LinearMap.fst ℝ ℝ E) hsum
    have h1 := congrArg (LinearMap.snd ℝ ℝ E) hsum
    simp only [map_sum, map_smul, map_zero, LinearMap.fst_apply, smul_eq_mul, mul_one] at h0
    simp only [map_sum, map_smul, map_zero, LinearMap.snd_apply] at h1
    exact h s w h0 h1
  · intro h s w h0 h1
    apply h s w
    apply Prod.ext
    · change (LinearMap.fst ℝ ℝ E) (∑ i ∈ s, w i • ((1 : ℝ), p i)) = 0
      simpa only [map_sum, map_smul, LinearMap.fst_apply, smul_eq_mul, mul_one] using h0
    · change (LinearMap.snd ℝ ℝ E) (∑ i ∈ s, w i • ((1 : ℝ), p i)) = 0
      simpa only [map_sum, map_smul, LinearMap.snd_apply] using h1

namespace HyperbolicSpace

variable {n : ℕ}

lemma lift_eq_height_smul_klein (x : HyperbolicSpace n) :
    lift x = Hyperboloid.height x.point • ((1 : ℝ), klein x) := by
  apply Prod.ext
  · change Hyperboloid.height x.point = Hyperboloid.height x.point * 1
    ring
  · change x.point = Hyperboloid.height x.point • klein x
    rw [klein, smul_smul, mul_inv_cancel₀ (Hyperboloid.height_pos x.point).ne', one_smul]

/-- Actual hyperbolic simplex nondegeneracy is exactly ordinary affine
independence in Klein coordinates, in every dimension and for any index type. -/
theorem linearIndependent_lift_iff_affineIndependent_klein {ι : Type*}
    (v : ι → HyperbolicSpace n) :
    LinearIndependent ℝ (fun i => lift (v i)) ↔
      AffineIndependent ℝ (fun i => klein (v i)) := by
  let u : ι → ℝˣ := fun i => Units.mk0 (Hyperboloid.height (v i).point)
    (Hyperboloid.height_pos (v i).point).ne'
  have hvec : (fun i => lift (v i)) = u • (fun i => ((1 : ℝ), klein (v i))) := by
    funext i
    change lift (v i) = Hyperboloid.height (v i).point • ((1 : ℝ), klein (v i))
    exact lift_eq_height_smul_klein (v i)
  rw [hvec, LinearIndependent.units_smul_iff]
  exact (affineIndependent_iff_homogeneous_linearIndependent (fun i => klein (v i))).symm

theorem affineIndependent_klein_vertices (V : Finset (HyperbolicSpace n))
    (hV : LinearIndependent ℝ (fun v : V => lift (v : HyperbolicSpace n))) :
    AffineIndependent ℝ ((↑) : V.image klein → EuclideanSpace ℝ (Fin n)) := by
  have h := (linearIndependent_lift_iff_affineIndependent_klein ((↑) : V → HyperbolicSpace n)).mp hV
  have hset : Set.range (fun v : V => klein (v : HyperbolicSpace n)) =
      (V.image klein : Set (EuclideanSpace ℝ (Fin n))) := by
    ext p
    simp
  have hrange := h.range
  change AffineIndependent ℝ
    ((↑) : Set.range (fun v : V => klein (v : HyperbolicSpace n)) →
      EuclideanSpace ℝ (Fin n)) at hrange
  rw [hset] at hrange
  exact hrange

theorem klein_image_cell (V : Finset (HyperbolicSpace n)) :
    klein '' hyperbolicCell V =
      convexHull ℝ (V.image klein : Set (EuclideanSpace ℝ (Fin n))) := by
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    exact (mem_hyperbolicCell_iff_klein_mem_convexHull V x).mp hx
  · intro p hp
    have hp1 : ‖p‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hyperbolic_klein_hull_subset_ball V hp
    refine ⟨fromKlein p, ?_, klein_fromKlein hp1⟩
    apply (mem_hyperbolicCell_iff_klein_mem_convexHull V _).mpr
    rwa [klein_fromKlein hp1]

theorem norm_klein_le_of_vertex_bounds (V : Finset (HyperbolicSpace n)) {ρ : ℝ}
    (hV : ∀ v ∈ V, ‖klein v‖ ≤ ρ) {x : HyperbolicSpace n} (hx : x ∈ hyperbolicCell V) :
    ‖klein x‖ ≤ ρ := by
  have hvertices : (V.image klein : Set (EuclideanSpace ℝ (Fin n))) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    simpa only [Metric.mem_closedBall, dist_zero_right] using hV v hv
  have hcell := convexHull_min hvertices (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ)
  have hm := hcell ((mem_hyperbolicCell_iff_klein_mem_convexHull V x).mp hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hm

theorem cell_chart_distortion (V : Finset (HyperbolicSpace n))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hV : ∀ v ∈ V, ‖klein v‖ ≤ ρ)
    {x y : HyperbolicSpace n} (hx : x ∈ hyperbolicCell V) (hy : y ∈ hyperbolicCell V) :
    dist (klein x) (klein y) ≤ dist x y ∧
      dist x y ≤ (1 - ρ ^ 2)⁻¹ * dist (klein x) (klein y) := by
  refine ⟨klein_dist_le x y, ?_⟩
  have h := dist_fromKlein_le hρ0 hρ1
    (norm_klein_le_of_vertex_bounds V hV hx) (norm_klein_le_of_vertex_bounds V hV hy)
  simpa only [fromKlein_klein, dist_eq_norm] using h

/-- The chart bound is global across different cells of a supplied folded
complex whenever all its finite vertex sets satisfy the common radius bound. -/
theorem union_cells_chart_distortion {ι : Type*} (V : ι → Finset (HyperbolicSpace n))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hV : ∀ i v, v ∈ V i → ‖klein v‖ ≤ ρ)
    {x y : HyperbolicSpace n} (hx : x ∈ ⋃ i, hyperbolicCell (V i))
    (hy : y ∈ ⋃ i, hyperbolicCell (V i)) :
    dist (klein x) (klein y) ≤ dist x y ∧
      dist x y ≤ (1 - ρ ^ 2)⁻¹ * dist (klein x) (klein y) := by
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
  refine ⟨klein_dist_le x y, ?_⟩
  have h := dist_fromKlein_le hρ0 hρ1
    (norm_klein_le_of_vertex_bounds (V i) (hV i) hxi)
    (norm_klein_le_of_vertex_bounds (V j) (hV j) hyj)
  simpa only [fromKlein_klein, dist_eq_norm] using h

/-- Every Euclidean vertex subface in the chart comes from a unique original
vertex subface.  This avoids adding nonexistent faces during chart transport. -/
theorem exists_vertex_subface_of_klein_image (V : Finset (HyperbolicSpace n))
    (W : Finset (EuclideanSpace ℝ (Fin n))) (hW : W ⊆ V.image klein) :
    ∃ U : Finset (HyperbolicSpace n), U ⊆ V ∧ U.image klein = W := by
  let U := V.filter fun v => klein v ∈ W
  refine ⟨U, Finset.filter_subset _ _, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hv).2
  · intro hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hW hp)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hp⟩, rfl⟩

theorem klein_vertex_image_subset_iff (V W : Finset (HyperbolicSpace n)) :
    V.image klein ⊆ W.image klein ↔ V ⊆ W := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, hkw⟩ := Finset.mem_image.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
    have heq : w = v := klein_injective hkw
    exact heq ▸ hw
  · exact fun h => Finset.image_subset_image h

end HyperbolicSpace
end BrehmApprox
