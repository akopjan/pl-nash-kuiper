module

public import PLGeometry.LinkRegions
public import PLGeometry.SourceBarycentricProperties

/-! # The link boundary as an actual subspace of the source -/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance linkBoundaryDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance linkBoundaryVertexEq : DecidableEq T.Vertex := Classical.decEq _
local instance linkBoundaryLabelEq (p : P) : DecidableEq (T.LinkVertex p) := Classical.decEq _

def linkVertexEmbedding (p : P) : T.LinkVertex p ↪ T.Vertex where
  toFun v := ⟨v.val, by
    obtain ⟨_, σ, hσ, _, hv⟩ := v.property
    exact T.vertex_mem hσ hv⟩
  inj' _ _ h := Subtype.ext (congrArg (fun z : T.Vertex => z.val) h)

def linkCoordinates (p : P) (w : T.LinkVertex p → ℝ) : T.Vertex → ℝ :=
  ∑ i, Pi.single (T.linkVertexEmbedding p i) (w i)

theorem linkCoordinates_apply (p : P) (w : T.LinkVertex p → ℝ) (i : T.LinkVertex p) :
    T.linkCoordinates p w (T.linkVertexEmbedding p i) = w i := by
  unfold linkCoordinates
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · exact Pi.single_eq_same _ _
  · intro j _ hji
    exact Pi.single_eq_of_ne (fun he => hji (T.linkVertexEmbedding p |>.injective he.symm)) _
  · simp

theorem linkCoordinates_sum (p : P) (w : T.LinkVertex p → ℝ) :
    ∑ v, T.linkCoordinates p w v = ∑ i, w i := by
  simp only [linkCoordinates, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

theorem linkCoordinates_mem_weightsOn (p : P) (x : (T.linkComplex p).Space) :
    T.linkCoordinates p x.val ∈
      Barycentric.weightsOn (T.faceLabels (T.linkSourceVertices ((T.linkComplex p).support x))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v
    unfold linkCoordinates
    rw [Finset.sum_apply]
    apply Finset.sum_nonneg
    intro i _
    by_cases h : v = T.linkVertexEmbedding p i
    · subst v
      simpa only [Pi.single_eq_same] using (T.linkComplex p).weight_nonneg x i
    · simp only [Pi.single_eq_of_ne h]
      exact le_refl _
  · rw [T.linkCoordinates_sum, (T.linkComplex p).weight_sum]
  · intro v hv
    unfold linkCoordinates
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ (T.linkComplex p).support x
    · apply Pi.single_eq_of_ne
      intro he
      apply hv
      apply (T.mem_faceLabels _ v).mpr
      have hi' := T.mem_linkSourceVertices.mpr ⟨i, hi, rfl⟩
      have hval : v.val = i.val := congrArg Subtype.val he
      exact hval.symm ▸ hi'
    · rw [(T.linkComplex p).weight_eq_zero_of_not_mem_support x hi]
      simp

def linkBoundaryInclusion (p : P) (x : (T.linkComplex p).Space) : P :=
  T.barycentricHomeomorph.symm ⟨T.linkCoordinates p x.val, by
    have hσ := T.linkSourceVertices_mem ((T.linkComplex p).support_mem x)
    have hm := T.linkCoordinates_mem_weightsOn p x
    rw [← T.barycentricCoords_image_cell hσ] at hm
    obtain ⟨y, _, he⟩ := hm
    exact ⟨y, he⟩⟩

@[simp] theorem barycentricCoords_linkBoundaryInclusion (p : P) (x : (T.linkComplex p).Space) :
    T.barycentricCoords (T.linkBoundaryInclusion p x) = T.linkCoordinates p x.val := by
  exact congrArg Subtype.val (T.barycentricHomeomorph.apply_symm_apply _)

theorem linkBoundaryInclusion_injective (p : P) : Function.Injective (T.linkBoundaryInclusion p) := by
  intro x y h
  apply Subtype.ext
  funext i
  have he := congrArg T.barycentricCoords h
  rw [T.barycentricCoords_linkBoundaryInclusion, T.barycentricCoords_linkBoundaryInclusion] at he
  have hv := congrFun he (T.linkVertexEmbedding p i)
  simpa only [T.linkCoordinates_apply] using hv

theorem linkBoundaryInclusion_mem_support (p : P) (x : (T.linkComplex p).Space) :
    T.linkBoundaryInclusion p x ∈ T.cell (T.linkSourceVertices ((T.linkComplex p).support x)) := by
  apply (T.mem_cell_iff_barycentricCoords
    (T.linkSourceVertices_mem ((T.linkComplex p).support_mem x)) _).mpr
  rw [T.barycentricCoords_linkBoundaryInclusion]
  exact T.linkCoordinates_mem_weightsOn p x

theorem linkBoundaryInclusion_ne_center (p : P) (x : (T.linkComplex p).Space) :
    T.linkBoundaryInclusion p x ≠ p := by
  intro he
  have hs := T.linkCoface_spec ((T.linkComplex p).support_mem x)
  apply hs.2.2.2
  simpa only [he] using T.linkBoundaryInclusion_mem_support p x

theorem linkBoundaryInclusion_mem_of_region {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) {x : (T.linkComplex p).Space} (hx : x ∈ T.linkRegion p σ) :
    T.linkBoundaryInclusion p x ∈ T.cell σ :=
  T.cell_mono hσ hx (T.linkBoundaryInclusion_mem_support p x)

theorem continuous_linkBoundaryInclusion (p : P) : Continuous (T.linkBoundaryInclusion p) := by
  have hc : Continuous (fun x : (T.linkComplex p).Space => T.linkCoordinates p x.val) := by
    unfold linkCoordinates
    apply continuous_finsetSum
    intro i _
    apply continuous_pi
    intro v
    by_cases hv : v = T.linkVertexEmbedding p i
    · subst v
      simp only [Pi.single_eq_same]
      exact (continuous_apply i).comp continuous_subtype_val
    · simpa only [Pi.single_eq_of_ne hv] using
        (continuous_const : Continuous (fun _ : (T.linkComplex p).Space => (0 : ℝ)))
  exact T.barycentricHomeomorph.symm.continuous.comp (hc.subtype_mk _)

theorem sum_cellWeights_linkBoundaryInclusion
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : P} {σ : Finset P} (hσ : σ ∈ T.simplices)
    (x : (T.linkComplex p).Space) (hx : x ∈ T.linkRegion p σ) (f : P → E) :
    (∑ v : σ, (T.cellWeights σ hσ
      ⟨T.linkBoundaryInclusion p x, T.linkBoundaryInclusion_mem_of_region hσ hx⟩).val v • f v.val) =
      ∑ i, x.val i • f i.val := by
  have he := T.restriction_barycentricCoords hσ
    ⟨T.linkBoundaryInclusion p x, T.linkBoundaryInclusion_mem_of_region hσ hx⟩
  rw [T.barycentricCoords_linkBoundaryInclusion] at he
  rw [← he]
  change (∑ v : σ, T.linkCoordinates p x.val
    ⟨v.val, T.vertex_mem hσ v.property⟩ • f v.val) = _
  simp only [linkCoordinates, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ∈ σ
  · let j : σ := ⟨i.val, hi⟩
    rw [Finset.sum_eq_single j]
    · have heq : (⟨j.val, T.vertex_mem hσ j.property⟩ : T.Vertex) = T.linkVertexEmbedding p i :=
        Subtype.ext rfl
      rw [heq, Pi.single_eq_same]
    · intro v _ hvj
      have hne : (⟨v.val, T.vertex_mem hσ v.property⟩ : T.Vertex) ≠ T.linkVertexEmbedding p i := by
        intro heq
        apply hvj
        exact Subtype.ext (congrArg (fun z : T.Vertex => z.val) heq)
      rw [Pi.single_eq_of_ne hne, zero_smul]
    · simp
  · have hz : x.val i = 0 :=
      ((T.mem_linkRegion_iff_weightsOn p σ x).mp hx).2 i
        (by simpa only [T.mem_linkLabels] using hi)
    rw [hz, zero_smul]
    apply Finset.sum_eq_zero
    intro v _
    simp

end ArchivePLGeometry.FiniteChartedComplex
