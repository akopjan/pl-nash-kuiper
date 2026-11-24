module

public import BrehmApprox.FiniteGramIsometry
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Geometry.Euclidean.PerpBisector
public import Mathlib.Analysis.Convex.Combination

/-!
# Rigid motions determined by simplex distances

A distance-preserving correspondence between independent finite vertex
families extends to an affine isometry of the ambient Euclidean space.
Distances to the vertices then determine every point of their convex hull.
These lemmas identify chart transitions without assuming their linearity.
-/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox

variable {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eq_of_mem_convexHull_of_dist_eq {V : Set E} {x y : E}
    (hx : x ∈ convexHull ℝ V) (hd : ∀ v ∈ V, dist x v = dist y v) : x = y := by
  apply AffineSubspace.left_mem_perpBisector.mp
  apply convexHull_min (s := V) ?_ (AffineSubspace.perpBisector x y).convex hx
  intro v hv
  exact AffineSubspace.mem_perpBisector_iff_dist_eq'.mpr (hd v hv)

/-- The finite-distance form of the Gram extension theorem. -/
theorem exists_ambient_distance_isometry [FiniteDimensional ℝ E]
    (v w : ι → E) (hv : AffineIndependent ℝ v)
    (hd : ∀ i j, dist (v i) (v j) = dist (w i) (w j)) :
    ∃ r : E ≃ᵃⁱ[ℝ] E, ∀ i, r (v i) = w i := by
  classical
  by_cases hι : Nonempty ι
  · let i₀ : ι := Classical.choice hι
    let J := {i : ι // i ≠ i₀}
    let a : J → E := fun i => v i - v i₀
    let b : J → E := fun i => w i - w i₀
    have ha : LinearIndependent ℝ a :=
      (affineIndependent_iff_linearIndependent_vsub ℝ v i₀).mp hv
    have hn (i : J) : ‖a i‖ = ‖b i‖ := by
      simpa only [a, b, dist_eq_norm] using hd i i₀
    have hab (i j : J) : ‖a i - a j‖ = ‖b i - b j‖ := by
      simpa only [a, b, sub_sub_sub_cancel_right, dist_eq_norm] using hd i j
    have hg (i j : J) : inner ℝ (a i) (a j) = inner ℝ (b i) (b j) := by
      have h := congrArg (fun t : ℝ => t ^ 2) (hab i j)
      rw [norm_sub_sq_real (a i) (a j), norm_sub_sq_real (b i) (b j), hn i, hn j] at h
      linarith
    obtain ⟨l, hl⟩ := exists_ambient_gram_isometry a b ha hg
    let r : E ≃ᵃⁱ[ℝ] E :=
      ((AffineIsometryEquiv.vaddConst ℝ (v i₀)).symm.trans
        l.toAffineIsometryEquiv).trans (AffineIsometryEquiv.vaddConst ℝ (w i₀))
    refine ⟨r, ?_⟩
    intro i
    by_cases hi : i = i₀
    · subst i
      simp [r]
    · have he := hl ⟨i, hi⟩
      change l (v i - v i₀) = w i - w i₀ at he
      change l (v i - v i₀) + w i₀ = w i
      rw [he, sub_add_cancel]
  · let : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    exact ⟨AffineIsometryEquiv.refl ℝ E, fun i => isEmptyElim i⟩

/-- Once a motion agrees at the vertices, an isometric chart transition
agrees with that motion throughout the simplex. -/
theorem affineIsometry_eq_of_vertex_distances
    (r : E ≃ᵃⁱ[ℝ] E) {V : Set E} {x y : E}
    (hx : x ∈ convexHull ℝ V)
    (hd : ∀ v ∈ V, dist y (r v) = dist x v) : r x = y := by
  have he : x = r.symm y := eq_of_mem_convexHull_of_dist_eq hx (by
    intro v hv
    calc
      dist x v = dist y (r v) := (hd v hv).symm
      _ = dist (r.symm y) v := by
        rw [← r.isometry.dist_eq (r.symm y) v, r.apply_symm_apply])
  rw [he, r.apply_symm_apply]

end BrehmApprox
