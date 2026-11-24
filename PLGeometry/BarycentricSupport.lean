module

public import PLGeometry.BarycentricRealization

/-! # The minimal face of a barycentric realization point -/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry.Barycentric.Complex

universe u
variable {ι : Type u} [Fintype ι] (K : Barycentric.Complex ι)

local instance barycentricSupportDecidableEq : DecidableEq ι := Classical.decEq _

def support (x : K.Space) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => 0 < x.val i

theorem weight_nonneg (x : K.Space) (i : ι) : 0 ≤ x.val i := by
  obtain ⟨σ, _, hx⟩ := Set.mem_iUnion₂.mp x.property
  exact hx.1.1 i

theorem weight_sum (x : K.Space) : ∑ i, x.val i = 1 := by
  obtain ⟨σ, _, hx⟩ := Set.mem_iUnion₂.mp x.property
  exact hx.1.2

@[simp] theorem mem_support_iff (x : K.Space) (i : ι) :
    i ∈ K.support x ↔ 0 < x.val i := by simp [support]

theorem weight_eq_zero_of_not_mem_support (x : K.Space) {i : ι} (hi : i ∉ K.support x) :
    x.val i = 0 := by
  exact le_antisymm (le_of_not_gt (fun h => hi ((K.mem_support_iff x i).mpr h)))
    (K.weight_nonneg x i)

theorem support_subset_of_mem_weightsOn (x : K.Space) {σ : Finset ι}
    (hx : x.val ∈ Barycentric.weightsOn σ) : K.support x ⊆ σ := by
  intro i hi
  by_contra hiσ
  have hh := (K.mem_support_iff x i).mp hi
  rw [hx.2 i hiσ] at hh
  exact lt_irrefl _ hh

theorem support_mem (x : K.Space) : K.support x ∈ K.faces := by
  obtain ⟨σ, hσ, hx⟩ := Set.mem_iUnion₂.mp x.property
  exact K.downward σ hσ _ (K.support_subset_of_mem_weightsOn x hx)

theorem weightsOn_support (x : K.Space) : x.val ∈ Barycentric.weightsOn (K.support x) := by
  exact ⟨⟨K.weight_nonneg x, K.weight_sum x⟩,
    fun _ h => K.weight_eq_zero_of_not_mem_support x h⟩

theorem support_nonempty (x : K.Space) : (K.support x).Nonempty := by
  have hs : 0 < ∑ i, x.val i := by rw [K.weight_sum x]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => K.weight_nonneg x i)).mp hs
  exact ⟨i, (K.mem_support_iff x i).mpr hi⟩

theorem mem_weightsOn_iff_support_subset (x : K.Space) (σ : Finset ι) :
    x.val ∈ Barycentric.weightsOn σ ↔ K.support x ⊆ σ := by
  refine ⟨K.support_subset_of_mem_weightsOn x, ?_⟩
  intro h
  exact Barycentric.weightsOn_mono h (K.weightsOn_support x)

theorem mem_cell_vertices_iff_support_subset (x : K.Space) (σ : Finset ι) :
    x ∈ K.cell (K.vertices σ) ↔ K.support x ⊆ σ := by
  change x.val ∈ Barycentric.weightsOn (K.labels (K.vertices σ)) ↔ _
  rw [K.labels_vertices]
  exact K.mem_weightsOn_iff_support_subset x σ

end ArchivePLGeometry.Barycentric.Complex
