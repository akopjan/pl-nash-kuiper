module

public import BrehmApprox.LexicographicTriangulation

/-! # Barycentric coordinates on an affinely independent Euclidean simplex -/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox.EuclideanBarycentric

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance euclideanBarycentricDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

abbrev Weights (ι : Type*) [Fintype ι] := Pulling.simplexWeights ι

def point (v : ι → E) (w : Weights ι) : E := ∑ i, w.val i • v i

theorem continuous_point (v : ι → E) : Continuous (point v) :=
  Pulling.continuous_barycenter v |>.comp continuous_subtype_val

theorem point_injective (v : ι → E) (hv : AffineIndependent ℝ v) :
    Function.Injective (point v) := by
  intro w z he
  apply Subtype.ext
  funext i
  exact hv.eq_of_sum_eq_sum (w.property.2.trans z.property.2.symm) he i (Finset.mem_univ i)

theorem point_mem (v : ι → E) (w : Weights ι) :
    point v w ∈ convexHull ℝ (Set.range v) := by
  have hm := Finset.univ.centerMass_mem_convexHull (z := v) (s := Set.range v)
    (fun i _ => w.property.1 i) (by rw [w.property.2]; norm_num) (fun i _ => Set.mem_range_self i)
  simpa only [point, Finset.centerMass_eq_of_sum_1 _ _ w.property.2] using hm

theorem range_point (v : ι → E) : Set.range (point v) = convexHull ℝ (Set.range v) := by
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have he : (Finset.univ.image v : Set E) = Set.range v := by ext x; simp
  rw [← he, Pulling.convexHull_eq_barycenter_image]
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.val, ⟨w.property, by simp⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw.1⟩, rfl⟩

def homeomorph (v : ι → E) (hv : AffineIndependent ℝ v) :
    Weights ι ≃ₜ convexHull ℝ (Set.range v) := by
  let : CompactSpace (Weights ι) := isCompact_iff_compactSpace.mp Pulling.isCompact_simplexWeights
  let f : Weights ι → convexHull ℝ (Set.range v) := fun w => ⟨point v w, point_mem v w⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      exact point_injective v hv (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ Set.range (point v) := by rw [range_point]; exact x.property
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, Subtype.ext hw⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    ((continuous_point v).subtype_mk _)

@[simp] theorem homeomorph_apply (v : ι → E) (hv : AffineIndependent ℝ v) (w : Weights ι) :
    (homeomorph v hv w).val = point v w := rfl

end BrehmApprox.EuclideanBarycentric
