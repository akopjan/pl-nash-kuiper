module

public import PLGeometry.ChartedBarycentricLinear

/-! # Support of canonical source coordinates -/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance sourcePropertiesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance sourcePropertiesVertexDecidableEq : DecidableEq T.Vertex := Classical.decEq _

theorem barycentricCoords_mem_weightsOn {σ : Finset P} (hσ : σ ∈ T.simplices)
    {x : P} (hx : x ∈ T.cell σ) :
    T.barycentricCoords x ∈ Barycentric.weightsOn (T.faceLabels σ) := by
  rw [← T.barycentricCoords_image_cell hσ]
  exact ⟨x, hx, rfl⟩

theorem mem_cell_iff_barycentricCoords {σ : Finset P} (hσ : σ ∈ T.simplices) (x : P) :
    x ∈ T.cell σ ↔ T.barycentricCoords x ∈ Barycentric.weightsOn (T.faceLabels σ) := by
  constructor
  · exact T.barycentricCoords_mem_weightsOn hσ
  · intro hx
    rw [← T.barycentricCoords_image_cell hσ] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact (T.barycentricCoords_injective he) ▸ hy

theorem barycentricCoords_nonneg (x : P) (v : T.Vertex) : 0 ≤ T.barycentricCoords x v := by
  obtain ⟨σ, hσ, hx⟩ := T.cover x
  exact (T.barycentricCoords_mem_weightsOn hσ hx).1.1 v

theorem barycentricCoords_sum (x : P) : ∑ v, T.barycentricCoords x v = 1 := by
  obtain ⟨σ, hσ, hx⟩ := T.cover x
  exact (T.barycentricCoords_mem_weightsOn hσ hx).1.2

theorem barycentricCoords_zero_of_not_mem {σ : Finset P} (hσ : σ ∈ T.simplices)
    {x : P} (hx : x ∈ T.cell σ) (v : T.Vertex) (hv : v.val ∉ σ) :
    T.barycentricCoords x v = 0 :=
  (T.barycentricCoords_mem_weightsOn hσ hx).2 v (by simpa only [mem_faceLabels] using hv)

theorem mem_cell_iff_barycentricCoords_support {σ : Finset P} (hσ : σ ∈ T.simplices)
    (x : P) : x ∈ T.cell σ ↔ ∀ v : T.Vertex, 0 < T.barycentricCoords x v → v.val ∈ σ := by
  rw [T.mem_cell_iff_barycentricCoords hσ]
  constructor
  · intro hx v hv
    by_contra hn
    have he := hx.2 v (by simpa only [mem_faceLabels] using hn)
    linarith
  · intro hx
    refine ⟨⟨T.barycentricCoords_nonneg x, T.barycentricCoords_sum x⟩, ?_⟩
    intro v hv
    apply le_antisymm _ (T.barycentricCoords_nonneg x v)
    by_contra hn
    exact hv ((T.mem_faceLabels σ v).mpr (hx v (lt_of_not_ge hn)))

@[simp] theorem faceLabels_singleton (v : T.Vertex) :
    T.faceLabels {v.val} = {v} := by
  ext w
  simp only [mem_faceLabels, Finset.mem_singleton, Subtype.ext_iff]

@[simp] theorem barycentricCoords_vertex (v : T.Vertex) :
    T.barycentricCoords v.val = Pi.single v 1 := by
  have hv := T.singleton_mem_of_vertex ((T.mem_vertexFinset v.val).mp v.property)
  have hw := T.barycentricCoords_mem_weightsOn hv
    (T.vertices_mem {v.val} hv (Finset.mem_singleton_self _))
  rw [T.faceLabels_singleton] at hw
  have hz (w : T.Vertex) (h : w ≠ v) : T.barycentricCoords v.val w = 0 :=
    hw.2 w (by simpa only [Finset.mem_singleton] using h)
  have he : T.barycentricCoords v.val v = 1 := by
    calc
      T.barycentricCoords v.val v = ∑ w, T.barycentricCoords v.val w := by
        symm
        exact Finset.sum_eq_single v (fun w _ h => hz w h) (by simp)
      _ = 1 := hw.1.2
  funext w
  by_cases h : w = v
  · subst w
    simpa only [Pi.single_eq_same] using he
  · simpa only [Pi.single_eq_of_ne h] using hz w h

theorem vertex_mem_of_mem_cell {σ : Finset P} (hσ : σ ∈ T.simplices)
    (v : T.Vertex) (hv : v.val ∈ T.cell σ) : v.val ∈ σ := by
  apply (T.mem_cell_iff_barycentricCoords_support hσ v.val).mp hv v
  simp only [T.barycentricCoords_vertex, Pi.single_eq_same]
  exact zero_lt_one

end ArchivePLGeometry.FiniteChartedComplex
