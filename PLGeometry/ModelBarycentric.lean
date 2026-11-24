module

public import PLGeometry.Definitions
public import BrehmApprox.EuclideanBarycentricSimplex
public import BrehmApprox.HyperbolicBarycentricSimplex
public import BrehmApprox.FiniteDistanceIsometry
public import BrehmApprox.ModelPointRigidity
public import BrehmApprox.HyperbolicFiniteDistanceIsometry
public import BrehmApprox.HyperbolicIsometryClassification

/-!
# Canonical barycentric coordinates in the three model geometries

Euclidean coordinates use affine combinations. Spherical and hyperbolic
coordinates use positive combinations of the unit ambient lifts, with the
sum of coefficients normalized to one.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.ModelBarycentric

variable {ι : Type*} [Fintype ι] {κ : Geometry} {n : ℕ}

local instance modelBarycentricDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance modelBarycentricEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance modelBarycentricSDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance modelBarycentricHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _

abbrev Weights (ι : Type*) [Fintype ι] := Pulling.simplexWeights ι

def Independent (κ : Geometry) (n : ℕ) (v : ι → Model κ n) : Prop :=
  match κ with
  | .euclidean => AffineIndependent ℝ v
  | .spherical => LinearIndependent ℝ (fun i => (v i).val)
  | .hyperbolic => LinearIndependent ℝ (fun i => HyperbolicSpace.lift (v i))

def Represents (κ : Geometry) (n : ℕ) (v : ι → Model κ n) (w : ι → ℝ) (x : Model κ n) : Prop :=
  match κ with
  | .euclidean => ∑ i, w i • v i = x
  | .spherical => ∃ c : ℝ, 0 < c ∧ ∑ i, w i • (v i).val = c • x.val
  | .hyperbolic => ∃ c : ℝ, 0 < c ∧ ∑ i, w i • HyperbolicSpace.lift (v i) = c • HyperbolicSpace.lift x

def point (κ : Geometry) (n : ℕ) (v : ι → Model κ n) (hv : Independent κ n v)
    (w : Weights ι) : Model κ n :=
  match κ with
  | .euclidean => EuclideanBarycentric.point v w
  | .spherical => SphericalBarycentric.point v hv w
  | .hyperbolic => HyperbolicBarycentric.point v w

theorem point_represents (v : ι → Model κ n) (hv : Independent κ n v) (w : Weights ι) :
    Represents κ n v w.val (point κ n v hv w) := by
  cases κ with
  | euclidean => rfl
  | spherical =>
    refine ⟨‖SphericalBarycentric.vector v w.val‖,
      norm_pos_iff.mpr (SphericalBarycentric.vector_ne_zero v hv w), ?_⟩
    exact (NormedSpace.norm_smul_normalize (SphericalBarycentric.vector v w.val)).symm
  | hyperbolic => exact HyperbolicBarycentric.vector_point v w

theorem point_eq_of_represents (v : ι → Model κ n) (hv : Independent κ n v)
    (w : Weights ι) (x : Model κ n) (h : Represents κ n v w.val x) : point κ n v hv w = x := by
  cases κ with
  | euclidean => exact h
  | spherical =>
    obtain ⟨c, hc, he⟩ := h
    apply GeodesicSphere.ext
    change NormedSpace.normalize (SphericalBarycentric.vector v w.val) = x.val
    change SphericalBarycentric.vector v w.val = c • x.val at he
    rw [he, NormedSpace.normalize_smul_of_pos hc, NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val]
  | hyperbolic =>
    obtain ⟨c, hc, he⟩ := h
    exact HyperbolicBarycentric.point_unique v w x hc he

theorem continuous_point (v : ι → Model κ n) (hv : Independent κ n v) :
    Continuous (point κ n v hv) := by
  cases κ with
  | euclidean => exact EuclideanBarycentric.continuous_point v
  | spherical => exact SphericalBarycentric.continuous_point v hv
  | hyperbolic => exact HyperbolicBarycentric.continuous_point v

theorem point_injective (v : ι → Model κ n) (hv : Independent κ n v) :
    Function.Injective (point κ n v hv) := by
  cases κ with
  | euclidean => exact EuclideanBarycentric.point_injective v hv
  | spherical => exact SphericalBarycentric.point_injective v hv
  | hyperbolic => exact HyperbolicBarycentric.point_injective v hv

theorem range_point (v : ι → Model κ n) (hv : Independent κ n v) :
    Set.range (point κ n v hv) = hull κ n (Finset.univ.image v) := by
  cases κ with
  | euclidean =>
    have hp : point .euclidean n v hv = EuclideanBarycentric.point v := by
      funext w
      rfl
    rw [hp]
    simpa only [hull, Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      EuclideanBarycentric.range_point v
  | spherical => exact SphericalBarycentric.range_point v hv
  | hyperbolic => exact HyperbolicBarycentric.range_point v hv

theorem point_mem (v : ι → Model κ n) (hv : Independent κ n v) (w : Weights ι) :
    point κ n v hv w ∈ hull κ n (Finset.univ.image v) := by
  rw [← range_point v hv]
  exact Set.mem_range_self w

def homeomorph (v : ι → Model κ n) (hv : Independent κ n v) :
    Weights ι ≃ₜ hull κ n (Finset.univ.image v) := by
  let : CompactSpace (Weights ι) := isCompact_iff_compactSpace.mp Pulling.isCompact_simplexWeights
  let f : Weights ι → hull κ n (Finset.univ.image v) := fun w => ⟨point κ n v hv w, point_mem v hv w⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      exact point_injective v hv (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ Set.range (point κ n v hv) := by rw [range_point]; exact x.property
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, Subtype.ext hw⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    ((continuous_point v hv).subtype_mk _)

@[simp] theorem homeomorph_apply (v : ι → Model κ n) (hv : Independent κ n v) (w : Weights ι) :
    (homeomorph v hv w).val = point κ n v hv w := rfl

theorem weights_unique (v : ι → Model κ n) (hv : Independent κ n v)
    (w z : Weights ι) (x : Model κ n) (hw : Represents κ n v w.val x)
    (hz : Represents κ n v z.val x) : w = z :=
  point_injective v hv ((point_eq_of_represents v hv w x hw).trans
    (point_eq_of_represents v hv z x hz).symm)

theorem represents_congr_weights (v : ι → Model κ n) {w z : ι → ℝ}
    (h : ∀ i, w i = z i) (x : Model κ n) : Represents κ n v w x ↔ Represents κ n v z x := by
  have he : w = z := funext h
  rw [he]

end ArchivePLGeometry.ModelBarycentric
