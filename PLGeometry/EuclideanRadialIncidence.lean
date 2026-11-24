module

public import PLGeometry.EuclideanRadialSites
public import BrehmApprox.ExtremeRadialSupport
public import BrehmApprox.SimplexExtremeFaces
public import PLGeometry.SourceBarycentricProperties

/-! # Exact old-cell incidence of Euclidean radial sites -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean (n + 1) P)

local instance euclideanRadialIncidenceDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance euclideanRadialIncidenceModelEq : DecidableEq (Model .euclidean (n + 1)) := Classical.decEq _
local instance euclideanRadialIncidenceLinkEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

theorem euclideanLinkAngularPoint_positive_combination
    (p : P) (x : (T.linkComplex p).Space) :
    ∃ w : ((T.linkComplex p).support x) → ℝ, (∀ i, 0 < w i) ∧
      ∃ c : ℝ, 0 < c ∧ (T.euclideanLinkAngularPoint p x).val =
        c • (∑ i, w i • T.euclideanLinkVector p ((T.linkComplex p).support x) i.val) := by
  let τ := (T.linkComplex p).support x
  have hτ := (T.linkComplex p).support_mem x
  let a : Barycentric.weightsOn τ := ⟨x.val, (T.linkComplex p).weightsOn_support x⟩
  let v : τ → GeodesicSphere n := fun i => T.euclideanLinkPoint p τ i.val
  let z := SphericalBarycentric.vector v (Barycentric.restrict τ a).val
  have hz : z ≠ 0 := SphericalBarycentric.vector_ne_zero v
    (T.euclideanLinkPoint_independent hτ) (Barycentric.restrict τ a)
  let w : τ → ℝ := fun i => x.val i.val * ‖T.euclideanLinkVector p τ i.val‖⁻¹
  have hw (i : τ) : 0 < w i :=
    mul_pos ((T.linkComplex p).mem_support_iff x i.val |>.mp i.property)
      (inv_pos.mpr (norm_pos_iff.mpr (T.euclideanLinkVector_ne_zero hτ i.property)))
  have he : z = ∑ i : τ, w i • T.euclideanLinkVector p τ i.val := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [v, SphericalBarycentric.vector, Barycentric.restrict]
    rw [euclideanLinkPoint, CrossPolytope.sphereNormalize_val
      (T.euclideanLinkVector_ne_zero hτ i.property)]
    simp only [NormedSpace.normalize, smul_smul, w]
    rfl
  refine ⟨w, hw, ‖z‖⁻¹, inv_pos.mpr (norm_pos_iff.mpr hz), ?_⟩
  change (Barycentric.chartPoint (T.euclideanLinkPoint p τ) x.val).val = _
  rw [Barycentric.chartPoint_restrict τ _ (T.euclideanLinkPoint_independent hτ) a]
  change NormedSpace.normalize z = _
  rw [NormedSpace.normalize, he]

theorem support_subset_of_euclideanRadialSite_mem
    (p : P) {r : ℝ} (hr : T.EuclideanRadialAdmissible p r) (hr0 : 0 < r)
    (x : (T.linkComplex p).Space) {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) (hqσ : T.euclideanRadialSite p hr x ∈ T.cell σ) :
    T.linkSourceVertices ((T.linkComplex p).support x) ⊆ σ := by
  let τ := (T.linkComplex p).support x
  let γ := T.linkCoface p τ
  have hτ := (T.linkComplex p).support_mem x
  obtain ⟨hγ, hpγ, hsub, _⟩ := T.linkCoface_spec hτ
  let V := γ.image (T.chart γ)
  let U := (γ ∩ σ).image (T.chart γ)
  have hV : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa only [simplexVertices, Finset.coe_sort_coe, V, γ] using T.simplex γ hγ
  have hface : T.chart γ '' T.cell (γ ∩ σ) = convexHull ℝ (U : Set _) :=
    T.image_face γ hγ (γ ∩ σ) Finset.inter_subset_left
  have hpD : T.chart γ p ∈ convexHull ℝ (U : Set _) := by
    rw [← hface, ← T.intersection γ hγ σ hσ]
    exact ⟨p, ⟨hpγ, hpσ⟩, rfl⟩
  have hqD : T.chart γ (T.euclideanRadialSite p hr x) ∈ convexHull ℝ (U : Set _) := by
    rw [← hface, ← T.intersection γ hγ σ hσ]
    exact ⟨_, ⟨T.euclideanRadialSite_mem p hr x, hqσ⟩, rfl⟩
  obtain ⟨w, hw, c, hc, he⟩ := T.euclideanLinkAngularPoint_positive_combination p x
  have hnonempty : Nonempty τ :=
    (T.linkComplex p).support_nonempty x |>.to_subtype
  letI : Nonempty τ := hnonempty
  have hs : 0 < ∑ i : τ, w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have hv (i : τ) : T.chart γ i.val.val ∈ convexHull ℝ (V : Set _) :=
    subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨i.val.val,
      hsub (T.mem_linkSourceVertices.mpr ⟨i.val, i.property, rfl⟩), rfl⟩)
  have hrad : T.chart γ p + (r * c) •
      (∑ i : τ, w i • (T.chart γ i.val.val - T.chart γ p)) ∈
      convexHull ℝ (U : Set _) := by
    rw [T.chart_euclideanRadialSite p hr x, he, smul_smul] at hqD
    exact hqD
  intro a ha
  obtain ⟨i, hi, rfl⟩ := T.mem_linkSourceVertices.mp ha
  have hiD := IsExtreme.mem_of_positive_radial_weight
    (simplex_face_isExtreme V hV (Finset.image_subset_image Finset.inter_subset_left))
    (convex_convexHull ℝ _) (convex_convexHull ℝ _) hpD
    (fun j : τ => T.chart γ j.val.val) w hv (fun j => (hw j).le) hs
    (mul_pos hr0 hc) hrad ⟨i, hi⟩ (hw ⟨i, hi⟩)
  rw [← hface] at hiD
  obtain ⟨a, ha, hea⟩ := hiD
  have hai : a = i.val := T.chart_injectiveOn γ hγ
    (T.cell_mono hγ Finset.inter_subset_left ha)
    (T.vertices_mem γ hγ (hsub (T.mem_linkSourceVertices.mpr ⟨i, hi, rfl⟩))) hea
  have hiCell : i.val ∈ T.cell (γ ∩ σ) := hai ▸ ha
  exact T.vertex_mem_of_mem_cell hσ
    ⟨i.val, T.vertex_mem hγ (hsub (T.mem_linkSourceVertices.mpr ⟨i, hi, rfl⟩))⟩
    (T.cell_mono hσ Finset.inter_subset_right hiCell)

end ArchivePLGeometry.FiniteChartedComplex
