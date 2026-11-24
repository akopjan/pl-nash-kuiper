module

public import PLGeometry.HyperbolicRadialSites
public import BrehmApprox.ExtremeRadialSupport
public import BrehmApprox.SimplexExtremeFaces
public import PLGeometry.SourceBarycentricProperties

/-! # Exact old-cell incidence of hyperbolic radial sites -/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.HyperbolicSpace BrehmApprox.HyperbolicLink
open scoped BigOperators

namespace BrehmApprox.HyperbolicLink

theorem radialVector_eq_height_smul_frame {n : ℕ} (p v : HyperbolicSpace (n + 1)) :
    radialVector p v = Hyperboloid.height (boostBy p.point v).point • frame p v := by
  rw [frame, klein, smul_smul, mul_inv_cancel₀ (Hyperboloid.height_pos _).ne', one_smul]
  rfl

end BrehmApprox.HyperbolicLink

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .hyperbolic (n + 1) P)

local instance hyperbolicRadialIncidenceDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance hyperbolicRadialIncidenceModelEq : DecidableEq (Model .hyperbolic (n + 1)) := Classical.decEq _
local instance hyperbolicRadialIncidenceLinkEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem hyperbolicLinkAngularPoint_positive_combination
    (p : P) (x : (T.linkComplex p).Space) :
    ∃ w : ((T.linkComplex p).support x) → ℝ, (∀ i, 0 < w i) ∧
      ∃ c : ℝ, 0 < c ∧ (T.hyperbolicLinkAngularPoint p x).val =
        c • (∑ i, w i • T.hyperbolicLinkVector p ((T.linkComplex p).support x) i.val) := by
  let τ := (T.linkComplex p).support x
  have hτ := (T.linkComplex p).support_mem x
  let a : Barycentric.weightsOn τ := ⟨x.val, (T.linkComplex p).weightsOn_support x⟩
  let v : τ → GeodesicSphere n := fun i => T.hyperbolicLinkPoint p τ i.val
  let z := SphericalBarycentric.vector v (Barycentric.restrict τ a).val
  have hz : z ≠ 0 := SphericalBarycentric.vector_ne_zero v
    (T.hyperbolicLinkPoint_independent hτ) (Barycentric.restrict τ a)
  let w : τ → ℝ := fun i => x.val i.val * ‖T.hyperbolicLinkVector p τ i.val‖⁻¹
  have hw (i : τ) : 0 < w i :=
    mul_pos ((T.linkComplex p).mem_support_iff x i.val |>.mp i.property)
      (inv_pos.mpr (norm_pos_iff.mpr (T.hyperbolicLinkVector_ne_zero hτ i.property)))
  have he : z = ∑ i : τ, w i • T.hyperbolicLinkVector p τ i.val := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [v, SphericalBarycentric.vector, Barycentric.restrict]
    rw [hyperbolicLinkPoint, CrossPolytope.sphereNormalize_val
      (T.hyperbolicLinkVector_ne_zero hτ i.property)]
    simp only [NormedSpace.normalize, smul_smul, w]
    rfl
  refine ⟨w, hw, ‖z‖⁻¹, inv_pos.mpr (norm_pos_iff.mpr hz), ?_⟩
  change (Barycentric.chartPoint (T.hyperbolicLinkPoint p τ) x.val).val = _
  rw [Barycentric.chartPoint_restrict τ _ (T.hyperbolicLinkPoint_independent hτ) a]
  change NormedSpace.normalize z = _
  rw [NormedSpace.normalize, he]

theorem support_subset_of_hyperbolicRadialSite_mem
    (p : P) {r : ℝ} (hr : T.HyperbolicRadialAdmissible p r) (hr0 : 0 < r)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hqσ : T.hyperbolicRadialSite p hr x ∈ T.cell σ) :
    T.linkSourceVertices ((T.linkComplex p).support x) ⊆ σ := by
  let τ := (T.linkComplex p).support x
  let γ := T.linkCoface p τ
  let a := T.chart γ p
  have hτ := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, hsub, _⟩ := T.linkCoface_spec hτ
  let V := HyperbolicLink.frameVertices a (γ.image (T.chart γ))
  let U := HyperbolicLink.frameVertices a ((γ ∩ σ).image (T.chart γ))
  have hV : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))) :=
    HyperbolicLink.frameVertices_independent a (T.simplex γ hγ)
  have hUV : U ⊆ V := Finset.image_subset_image (Finset.image_subset_image Finset.inter_subset_left)
  have hface : T.chart γ '' T.cell (γ ∩ σ) = hyperbolicCell ((γ ∩ σ).image (T.chart γ)) :=
    T.image_face γ hγ (γ ∩ σ) Finset.inter_subset_left
  have hpD : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ convexHull ℝ (U : Set _) := by
    rw [← HyperbolicLink.frame_self a]
    apply (HyperbolicLink.mem_cell_iff_frame_mem_hull a a _).mp
    rw [← hface, ← T.intersection γ hγ σ hσ]
    exact ⟨p, ⟨hpγ, hpσ⟩, rfl⟩
  have hqD : HyperbolicLink.frame a (T.chart γ (T.hyperbolicRadialSite p hr x)) ∈
      convexHull ℝ (U : Set _) := by
    apply (HyperbolicLink.mem_cell_iff_frame_mem_hull a _ _).mp
    rw [← hface, ← T.intersection γ hγ σ hσ]
    exact ⟨_, ⟨T.hyperbolicRadialSite_mem p hr x, hqσ⟩, rfl⟩
  obtain ⟨w, hw, c, hc, he⟩ := T.hyperbolicLinkAngularPoint_positive_combination p x
  let w' : τ → ℝ := fun i => w i * Hyperboloid.height (boostBy a.point (T.chart γ i.val.val)).point
  have hw' (i : τ) : 0 < w' i := mul_pos (hw i) (Hyperboloid.height_pos _)
  have he' : (∑ i : τ, w i • T.hyperbolicLinkVector p τ i.val) =
      ∑ i : τ, w' i • HyperbolicLink.frame a (T.chart γ i.val.val) := by
    apply Finset.sum_congr rfl
    intro i _
    change w i • radialVector a (T.chart γ i.val.val) = _
    rw [HyperbolicLink.radialVector_eq_height_smul_frame, smul_smul]
  letI : Nonempty τ := (T.linkComplex p).support_nonempty x |>.to_subtype
  have hs : 0 < ∑ i : τ, w' i := Finset.sum_pos (fun i _ => hw' i) Finset.univ_nonempty
  have hv (i : τ) : HyperbolicLink.frame a (T.chart γ i.val.val) ∈ convexHull ℝ (V : Set _) :=
    subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨T.chart γ i.val.val,
      Finset.mem_image.mpr ⟨i.val.val, hsub (T.mem_linkSourceVertices.mpr ⟨i.val, i.property, rfl⟩), rfl⟩, rfl⟩)
  have hrad : (0 : EuclideanSpace ℝ (Fin (n + 1))) +
      (Real.sinh r / Real.cosh r * c) •
      (∑ i : τ, w' i • (HyperbolicLink.frame a (T.chart γ i.val.val) - 0)) ∈
      convexHull ℝ (U : Set _) := by
    rw [T.chart_hyperbolicRadialSite p hr x, HyperbolicLink.frame_radialPoint, he, he', smul_smul] at hqD
    simpa only [sub_zero, zero_add] using hqD
  intro b hb
  obtain ⟨i, hi, rfl⟩ := T.mem_linkSourceVertices.mp hb
  have hiD := IsExtreme.mem_of_positive_radial_weight
    (simplex_face_isExtreme V hV hUV) (convex_convexHull ℝ _) (convex_convexHull ℝ _) hpD
    (fun j : τ => HyperbolicLink.frame a (T.chart γ j.val.val)) w' hv
    (fun j => (hw' j).le) hs (mul_pos (div_pos (Real.sinh_pos_iff.mpr hr0) (Real.cosh_pos r)) hc)
    hrad ⟨i, hi⟩ (hw' ⟨i, hi⟩)
  have hiCellChart := (HyperbolicLink.mem_cell_iff_frame_mem_hull a (T.chart γ i.val)
    ((γ ∩ σ).image (T.chart γ))).mpr hiD
  rw [← hface] at hiCellChart
  obtain ⟨b, hb, heb⟩ := hiCellChart
  have hbi : b = i.val := T.chart_injectiveOn γ hγ (T.cell_mono hγ Finset.inter_subset_left hb)
    (T.vertices_mem γ hγ (hsub (T.mem_linkSourceVertices.mpr ⟨i, hi, rfl⟩))) heb
  have hiCell : i.val ∈ T.cell (γ ∩ σ) := hbi ▸ hb
  exact T.vertex_mem_of_mem_cell hσ
    ⟨i.val, T.vertex_mem hγ (hsub (T.mem_linkSourceVertices.mpr ⟨i, hi, rfl⟩))⟩
    (T.cell_mono hσ Finset.inter_subset_right hiCell)

end ArchivePLGeometry.FiniteChartedComplex
