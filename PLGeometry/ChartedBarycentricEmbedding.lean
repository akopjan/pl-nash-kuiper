module

public import PLGeometry.ChartedBarycentricCoordinates
public import BrehmApprox.SimplexExtremeFaces

/-! # The barycentric embedding of a finite charted complex -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance chartedBarycentricEmbeddingDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance chartedBarycentricEmbeddingVertexEq : DecidableEq T.Vertex := Classical.decEq _

theorem localCoords_mem_weightsOn {σ : Finset P} (hσ : σ ∈ T.simplices) (x : T.cell σ) :
    T.localCoords σ hσ x ∈ Barycentric.weightsOn (T.faceLabels σ) := by
  have hsub : σ ⊆ T.vertexFinset := fun _ hv => T.vertex_mem hσ hv
  refine ⟨?_, ?_⟩
  · exact (ModelBarycentric.extendWeights hsub (T.cellWeights σ hσ x)).property
  · intro v hv
    have hv' : v.val ∉ σ := fun h => hv ((T.mem_faceLabels σ v).mpr h)
    simp only [localCoords, dite_eq_right hv']

def weightsOfSupported {σ : Finset P} (hσ : σ ∈ T.simplices)
    (w : Barycentric.weightsOn (T.faceLabels σ)) : ModelBarycentric.Weights σ :=
  ⟨fun v => w.val ⟨v.val, T.vertex_mem hσ v.property⟩,
    ⟨fun v => w.property.1.1 _, by
      let a : P → ℝ := fun p => if hp : p ∈ T.vertexFinset then w.val ⟨p, hp⟩ else 0
      have hsub : σ ⊆ T.vertexFinset := fun _ hv => T.vertex_mem hσ hv
      calc
        (∑ v : σ, w.val ⟨v.val, T.vertex_mem hσ v.property⟩) = ∑ v ∈ σ, a v := by
          rw [← Finset.sum_coe_sort σ a]
          apply Finset.sum_congr rfl
          intro v _
          simp only [a, dite_eq_left (T.vertex_mem hσ v.property)]
        _ = ∑ v ∈ T.vertexFinset, a v := Finset.sum_subset hsub (by
          intro v hv hvσ
          simp only [a, dite_eq_left hv]
          exact w.property.2 ⟨v, hv⟩ (by simpa only [mem_faceLabels] using hvσ))
        _ = ∑ v : T.Vertex, w.val v := by
          rw [← Finset.sum_coe_sort T.vertexFinset a]
          apply Finset.sum_congr rfl
          intro v _
          simp only [a, dite_eq_left v.property]
        _ = 1 := w.property.1.2⟩⟩

theorem range_localCoords {σ : Finset P} (hσ : σ ∈ T.simplices) :
    Set.range (T.localCoords σ hσ) = Barycentric.weightsOn (T.faceLabels σ) := by
  apply Set.Subset.antisymm
  · rintro w ⟨x, rfl⟩
    exact T.localCoords_mem_weightsOn hσ x
  · intro w hw
    refine ⟨(T.cellWeights σ hσ).symm (T.weightsOfSupported hσ ⟨w, hw⟩), ?_⟩
    funext v
    by_cases hv : v.val ∈ σ
    · simp only [localCoords, dite_eq_left hv, Homeomorph.apply_symm_apply, weightsOfSupported]
    · simp only [localCoords, dite_eq_right hv]
      exact (hw.2 v (by simpa only [mem_faceLabels] using hv)).symm

theorem localCoords_injective {σ : Finset P} (hσ : σ ∈ T.simplices) :
    Function.Injective (T.localCoords σ hσ) := by
  intro x y hxy
  apply (T.cellWeights σ hσ).injective
  apply Subtype.ext
  funext v
  have hh := congrFun hxy ⟨v.val, T.vertex_mem hσ v.property⟩
  simpa only [localCoords, dite_eq_left v.property] using hh

theorem barycentricCoords_image_cell {σ : Finset P} (hσ : σ ∈ T.simplices) :
    T.barycentricCoords '' T.cell σ = Barycentric.weightsOn (T.faceLabels σ) := by
  rw [← T.range_localCoords hσ]
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (T.barycentricCoords_eq hσ hx).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, T.barycentricCoords_eq hσ x.property⟩

theorem barycentricCoords_injectiveOn {σ : Finset P} (hσ : σ ∈ T.simplices) :
    Set.InjOn T.barycentricCoords (T.cell σ) := by
  intro x hx y hy he
  have he' := he
  rw [T.barycentricCoords_eq hσ hx, T.barycentricCoords_eq hσ hy] at he'
  exact congrArg Subtype.val (T.localCoords_injective hσ he')

theorem barycentricCoords_injective : Function.Injective T.barycentricCoords := by
  intro x y hxy
  obtain ⟨σ, hσ, hx⟩ := T.cover x
  obtain ⟨τ, hτ, hy⟩ := T.cover y
  have hwσ : T.barycentricCoords x ∈ Barycentric.weightsOn (T.faceLabels σ) := by
    rw [← T.barycentricCoords_image_cell hσ]
    exact ⟨x, hx, rfl⟩
  have hwτ : T.barycentricCoords x ∈ Barycentric.weightsOn (T.faceLabels τ) := by
    rw [hxy, ← T.barycentricCoords_image_cell hτ]
    exact ⟨y, hy, rfl⟩
  have hw : T.barycentricCoords x ∈ Barycentric.weightsOn (T.faceLabels (σ ∩ τ)) := by
    refine ⟨hwσ.1, fun v hv => ?_⟩
    by_cases hs : v.val ∈ σ
    · apply hwτ.2 v
      intro ht
      apply hv
      apply (T.mem_faceLabels (σ ∩ τ) v).mpr
      exact Finset.mem_inter.mpr ⟨hs, (T.mem_faceLabels τ v).mp ht⟩
    · exact hwσ.2 v (fun h => hs ((T.mem_faceLabels σ v).mp h))
  rw [← T.barycentricCoords_image_cell (T.faces σ hσ (σ ∩ τ) Finset.inter_subset_left)] at hw
  obtain ⟨z, hz, hzx⟩ := hw
  have hzσ := T.cell_mono hσ Finset.inter_subset_left hz
  have hzτ := T.cell_mono hτ Finset.inter_subset_right hz
  exact (T.barycentricCoords_injectiveOn hσ hzσ hx hzx).symm.trans
    (T.barycentricCoords_injectiveOn hτ hzτ hy (hzx.trans hxy))

def barycentricHomeomorph : P ≃ₜ Set.range T.barycentricCoords := by
  let : CompactSpace P := T.compactSpace
  let e := Equiv.ofInjective T.barycentricCoords T.barycentricCoords_injective
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (T.continuous_barycentricCoords.subtype_mk _)

end ArchivePLGeometry.FiniteChartedComplex
