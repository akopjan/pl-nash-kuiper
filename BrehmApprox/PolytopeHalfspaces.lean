module

public import BrehmApprox.PolytopeIntersection

/-!
# Cutting a finite polytope by finitely many affine halfspaces

Barycentric coordinates and nonnegative slack variables realize the cut as
the linear image of a compact nonnegative affine slice. The finite-extreme-
point theorem therefore gives a genuine finite vertex set.
-/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def halfspaceSliceData (V : Finset E) (L : ι → E →ₗ[ℝ] ℝ) :
    ((V ⊕ ι) → ℝ) →ₗ[ℝ] (ℝ × (ι → ℝ)) where
  toFun t := (∑ v : V, t (Sum.inl v),
    fun i => (∑ v : V, t (Sum.inl v) * L i v.val) + t (Sum.inr i))
  map_add' t u := by
    ext i <;> simp [Finset.sum_add_distrib, add_mul] <;> ring
  map_smul' c t := by
    ext i <;> simp [Finset.mul_sum, mul_add, mul_assoc]

def halfspaceSliceImage (V : Finset E) : ((V ⊕ ι) → ℝ) →ₗ[ℝ] E where
  toFun t := ∑ v : V, t (Sum.inl v) • v.val
  map_add' t u := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c t := by simp [Finset.smul_sum, mul_smul]

theorem halfspaceSlice_mem_iff
    (V : Finset E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (t : (V ⊕ ι) → ℝ) :
    t ∈ nonnegativeSlice (halfspaceSliceData V L) (1, b) ↔
      (∑ v : V, t (Sum.inl v)) = 1 ∧
      (∀ i, (∑ v : V, t (Sum.inl v) * L i v.val) + t (Sum.inr i) = b i) ∧
      ∀ i, 0 ≤ t i := by
  simp only [nonnegativeSlice, Set.mem_setOf_eq, halfspaceSliceData,
    LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq, funext_iff, and_assoc]

theorem isCompact_halfspaceSlice
    (V : Finset E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    IsCompact (nonnegativeSlice (halfspaceSliceData V L) (1, b)) := by
  classical
  let U : (V ⊕ ι) → ℝ := Sum.elim (fun _ => 1)
    (fun i => |b i| + ∑ v : V, |L i v.val|)
  have hc : IsClosed (nonnegativeSlice (halfspaceSliceData V L) (1, b)) := by
    change IsClosed ({t | halfspaceSliceData V L t = (1, b)} ∩ {t | ∀ i, 0 ≤ t i})
    apply IsClosed.inter
    · exact isClosed_eq (halfspaceSliceData V L).continuous_of_finiteDimensional continuous_const
    · simp only [Set.setOf_forall]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := 0) (b := U)) hc
  intro t ht
  obtain ⟨hsum, hrow, hnonneg⟩ := (halfspaceSlice_mem_iff V L b t).mp ht
  have hw (v : V) : t (Sum.inl v) ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun u _ => hnonneg (Sum.inl u)) (Finset.mem_univ v)
  refine ⟨hnonneg, ?_⟩
  intro j
  cases j with
  | inl v => exact hw v
  | inr i =>
    change t (Sum.inr i) ≤ |b i| + ∑ v : V, |L i v.val|
    have hbound : -(∑ v : V, t (Sum.inl v) * L i v.val) ≤
        ∑ v : V, |L i v.val| := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro v _
      calc
        -(t (Sum.inl v) * L i v.val) = t (Sum.inl v) * (-L i v.val) := by ring
        _ ≤ t (Sum.inl v) * |L i v.val| :=
          mul_le_mul_of_nonneg_left (neg_le_abs _) (hnonneg _)
        _ ≤ 1 * |L i v.val| := mul_le_mul_of_nonneg_right (hw v) (abs_nonneg _)
        _ = |L i v.val| := one_mul _
    linarith [hrow i, le_abs_self (b i)]

theorem image_halfspaceSlice
    (V : Finset E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    halfspaceSliceImage (ι := ι) V ''
      nonnegativeSlice (halfspaceSliceData V L) (1, b) =
      convexHull ℝ (V : Set E) ∩ {x | ∀ i, L i x ≤ b i} := by
  classical
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨hsum, hrow, hnonneg⟩ := (halfspaceSlice_mem_iff V L b t).mp ht
    constructor
    · exact mem_convexHull_of_exists_fintype (fun v : V => t (Sum.inl v))
        (fun v => v.val) (fun v => hnonneg _) hsum (fun v => v.property) rfl
    · intro i
      have heq : L i (halfspaceSliceImage (ι := ι) V t) =
          ∑ v : V, t (Sum.inl v) * L i v.val := by
        simp [halfspaceSliceImage, map_sum, map_smul]
      rw [heq]
      linarith [hrow i, hnonneg (Sum.inr i)]
  · rintro ⟨hx, hbound⟩
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx
    let t : (V ⊕ ι) → ℝ := Sum.elim (fun v : V => w v.val)
      (fun i => b i - L i x)
    have hsum : (∑ v : V, t (Sum.inl v)) = 1 := by
      simpa only [t, Sum.elim_inl, Finset.sum_coe_sort] using hw1
    have himage : halfspaceSliceImage (ι := ι) V t = x := by
      simpa only [halfspaceSliceImage, LinearMap.coe_mk, AddHom.coe_mk,
        t, Sum.elim_inl] using
        (Finset.sum_coe_sort V (fun v => w v • v)).trans hwx
    refine ⟨t, (halfspaceSlice_mem_iff V L b t).mpr ⟨hsum, ?_, ?_⟩, himage⟩
    · intro i
      have h := congrArg (L i) himage
      simp only [halfspaceSliceImage, LinearMap.coe_mk, AddHom.coe_mk,
        map_sum, map_smul, smul_eq_mul] at h
      change (∑ v : V, t (Sum.inl v) * L i v.val) + (b i - L i x) = b i
      rw [h]
      ring
    · intro j
      cases j with
      | inl v => exact hw0 v.val v.property
      | inr i => exact sub_nonneg.mpr (hbound i)

theorem exists_finset_convexHull_inter_halfspaces
    (V : Finset E) (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    ∃ W : Finset E,
      convexHull ℝ (V : Set E) ∩ {x | ∀ i, L i x ≤ b i} =
      convexHull ℝ (W : Set E) := by
  classical
  obtain ⟨C, hC⟩ := exists_finset_nonnegativeSlice (halfspaceSliceData V L) (1, b)
    (isCompact_halfspaceSlice V L b)
  refine ⟨C.image (halfspaceSliceImage (ι := ι) V), ?_⟩
  rw [← image_halfspaceSlice V L b, hC, LinearMap.image_convexHull, Finset.coe_image]

end BrehmApprox
