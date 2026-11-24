module

public import BrehmApprox.SphericalBarycentricSimplex

/-!
# The standard realization of a finite abstract complex

A point is a nonnegative barycentric vector of total mass one, supported in
an abstract face. The cells and all their intersections are explicit closed
subsets of a finite-dimensional real vector space.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace ArchivePLGeometry.Barycentric

universe u
variable {ι : Type u} [Fintype ι]

local instance barycentricRealizationDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def weightsOn (σ : Finset ι) : Set (ι → ℝ) :=
  BrehmApprox.Pulling.simplexWeights ι ∩ {w | ∀ i ∉ σ, w i = 0}

theorem weightsOn_mono {σ τ : Finset ι} (h : σ ⊆ τ) : weightsOn σ ⊆ weightsOn τ :=
  fun _ hw => ⟨hw.1, fun i hi => hw.2 i (fun hσ => hi (h hσ))⟩

theorem weightsOn_inter (σ τ : Finset ι) : weightsOn σ ∩ weightsOn τ = weightsOn (σ ∩ τ) := by
  ext w
  constructor
  · rintro ⟨hσ, hτ⟩
    refine ⟨hσ.1, fun i hi => ?_⟩
    by_cases his : i ∈ σ
    · exact hτ.2 i (fun hit => hi (Finset.mem_inter.mpr ⟨his, hit⟩))
    · exact hσ.2 i his
  · intro h
    exact ⟨weightsOn_mono Finset.inter_subset_left h, weightsOn_mono Finset.inter_subset_right h⟩

theorem isClosed_weightsOn (σ : Finset ι) : IsClosed (weightsOn σ) := by
  apply BrehmApprox.Pulling.isCompact_simplexWeights.isClosed.inter
  have he : {w : ι → ℝ | ∀ i ∉ σ, w i = 0} = ⋂ i ∉ σ, {w : ι → ℝ | w i = 0} := by ext w; simp
  rw [he]
  have hc (i : ι) : IsClosed {w : ι → ℝ | w i = 0} :=
    isClosed_eq (continuous_apply i) continuous_const
  exact isClosed_iInter (fun i => isClosed_iInter (fun _ : i ∉ σ => hc i))

theorem isCompact_weightsOn (σ : Finset ι) : IsCompact (weightsOn σ) :=
  BrehmApprox.Pulling.isCompact_simplexWeights.of_isClosed_subset
    (isClosed_weightsOn σ) (fun _ h => h.1)

theorem sum_restrict {σ : Finset ι} (w : weightsOn σ) : (∑ i : σ, w.val i.val) = 1 := by
  rw [Finset.sum_coe_sort]
  calc
    ∑ i ∈ σ, w.val i = ∑ i, w.val i :=
      Finset.sum_subset (Finset.subset_univ σ) (fun i _ hi => w.property.2 i hi)
    _ = 1 := w.property.1.2

def restrict (σ : Finset ι) (w : weightsOn σ) : BrehmApprox.SphericalBarycentric.Weights σ :=
  ⟨fun i => w.val i.val, ⟨fun i => w.property.1.1 i.val, sum_restrict w⟩⟩

theorem restrict_injective (σ : Finset ι) : Function.Injective (restrict σ) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ σ
  · exact congrFun (congrArg Subtype.val hxy) ⟨i, hi⟩
  · rw [x.property.2 i hi, y.property.2 i hi]

theorem restrict_surjective (σ : Finset ι) : Function.Surjective (restrict σ) := by
  intro w
  let a : ι → ℝ := fun i => if hi : i ∈ σ then w.val ⟨i, hi⟩ else 0
  have ha : a ∈ weightsOn σ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      by_cases hi : i ∈ σ
      · simpa only [a, dite_eq_left hi] using w.property.1 ⟨i, hi⟩
      · simp [a, hi]
    · have hsum : ∑ i, a i = ∑ i : σ, w.val i := by
        calc
          ∑ i, a i = ∑ i : σ, a i.val := by
            rw [Finset.sum_coe_sort]
            exact (Finset.sum_subset (Finset.subset_univ σ) (fun i _ hi => by simp [a, hi])).symm
          _ = ∑ i : σ, w.val i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [a, i.property]
      exact hsum.trans w.property.2
    · intro i hi
      simp [a, hi]
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  funext i
  simp [restrict, a, i.property]

def restrictHomeomorph (σ : Finset ι) :
    weightsOn σ ≃ₜ BrehmApprox.SphericalBarycentric.Weights σ := by
  let : CompactSpace (weightsOn σ) := isCompact_iff_compactSpace.mp (isCompact_weightsOn σ)
  let e := Equiv.ofBijective (restrict σ) ⟨restrict_injective σ, restrict_surjective σ⟩
  apply Continuous.homeoOfEquivCompactToT2 (f := e)
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.val).comp continuous_subtype_val)

@[simp] theorem restrictHomeomorph_apply (σ : Finset ι) (w : weightsOn σ) :
    restrictHomeomorph σ w = restrict σ w := rfl

theorem single_mem_weightsOn (i : ι) : Pi.single i 1 ∈ weightsOn ({i} : Finset ι) := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun j => ?_, by simp⟩
    by_cases hj : j = i <;> simp [hj]
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [Pi.single_apply, hj]

structure Complex (ι : Type u) [Fintype ι] where
  faces : Set (Finset ι)
  downward : ∀ σ ∈ faces, ∀ τ ⊆ σ, τ ∈ faces
  singleton : ∀ i, ({i} : Finset ι) ∈ faces

namespace Complex

variable (K : Complex ι)

def carrier : Set (ι → ℝ) := ⋃ σ ∈ K.faces, weightsOn σ

abbrev Space := K.carrier

local instance barycentricSpaceDecidableEq : DecidableEq K.Space := Classical.decEq _

def vertex (i : ι) : K.Space :=
  ⟨Pi.single i 1, Set.mem_iUnion₂.mpr ⟨{i}, K.singleton i, single_mem_weightsOn i⟩⟩

theorem vertex_injective : Function.Injective K.vertex := by
  intro i j hij
  by_contra hne
  have h := congrFun (congrArg Subtype.val hij) i
  simp [vertex, Pi.single_apply, hne, Ne.symm hne] at h

def vertices (σ : Finset ι) : Finset K.Space := σ.image K.vertex

def labels (S : Finset K.Space) : Finset ι := Finset.univ.filter (fun i => K.vertex i ∈ S)

@[simp] theorem labels_vertices (σ : Finset ι) : K.labels (K.vertices σ) = σ := by
  ext i
  simp only [labels, Finset.mem_filter, Finset.mem_univ, true_and, vertices, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    exact K.vertex_injective he ▸ hj
  · exact fun hi => ⟨i, hi, rfl⟩

theorem labels_mono {S T : Finset K.Space} (h : S ⊆ T) : K.labels S ⊆ K.labels T := by
  intro i hi
  simp only [labels, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h hi

theorem vertices_labels_of_subset {σ : Finset ι} {S : Finset K.Space}
    (hS : S ⊆ K.vertices σ) : K.vertices (K.labels S) = S := by
  ext x
  simp only [vertices, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.mp hi).2
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hS hx)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

@[simp] theorem labels_inter (S T : Finset K.Space) : K.labels (S ∩ T) = K.labels S ∩ K.labels T := by
  ext i
  simp [labels]

def cell (S : Finset K.Space) : Set K.Space :=
  (Subtype.val : K.Space → (ι → ℝ)) ⁻¹' weightsOn (K.labels S)

theorem cell_inter (S T : Finset K.Space) : K.cell S ∩ K.cell T = K.cell (S ∩ T) := by
  simp only [cell, ← Set.preimage_inter, weightsOn_inter, labels_inter]

def simplices : Set (Finset K.Space) := K.vertices '' K.faces

theorem finite_simplices : K.simplices.Finite := (Set.toFinite K.faces).image K.vertices

theorem cover (x : K.Space) : ∃ S ∈ K.simplices, x ∈ K.cell S := by
  obtain ⟨σ, hσ, hx⟩ := Set.mem_iUnion₂.mp x.property
  exact ⟨K.vertices σ, ⟨σ, hσ, rfl⟩, by simpa only [cell, labels_vertices, Set.mem_preimage] using hx⟩

theorem simplices_downward {S : Finset K.Space} (hS : S ∈ K.simplices)
    {T : Finset K.Space} (hTS : T ⊆ S) : T ∈ K.simplices := by
  obtain ⟨σ, hσ, rfl⟩ := hS
  have hl : K.labels T ⊆ σ := by
    simpa only [labels_vertices] using K.labels_mono hTS
  exact ⟨K.labels T, K.downward σ hσ _ hl, K.vertices_labels_of_subset hTS⟩

theorem vertices_mem {S : Finset K.Space} (hS : S ∈ K.simplices) : (S : Set K.Space) ⊆ K.cell S := by
  obtain ⟨σ, hσ, rfl⟩ := hS
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  change Pi.single i 1 ∈ weightsOn (K.labels (K.vertices σ))
  rw [K.labels_vertices]
  exact weightsOn_mono (Finset.singleton_subset_iff.mpr hi) (single_mem_weightsOn i)

def cellWeightsHomeomorph (σ : Finset ι) (hσ : σ ∈ K.faces) :
    K.cell (K.vertices σ) ≃ₜ weightsOn σ := by
  let f : K.cell (K.vertices σ) → weightsOn σ := fun x =>
    ⟨x.val.val, by simpa only [cell, labels_vertices, Set.mem_preimage] using x.property⟩
  let g : weightsOn σ → K.cell (K.vertices σ) := fun w =>
    ⟨⟨w.val, Set.mem_iUnion₂.mpr ⟨σ, hσ, w.property⟩⟩,
      by simpa only [cell, labels_vertices, Set.mem_preimage] using w.property⟩
  exact
    { toFun := f
      invFun := g
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

@[simp] theorem cellWeightsHomeomorph_apply (σ : Finset ι) (hσ : σ ∈ K.faces)
    (x : K.cell (K.vertices σ)) : (K.cellWeightsHomeomorph σ hσ x).val = x.val.val := rfl

end Complex
end ArchivePLGeometry.Barycentric
