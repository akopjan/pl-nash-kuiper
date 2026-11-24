module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic
public import BrehmApprox.PolytopeModels
public import BrehmApprox.HyperbolicSimplicialCharts

/-!
# Finite polytope intersections in the three model geometries

A compact nonnegative affine slice has finitely many extreme points, because
an extreme point is determined by its zero-coordinate pattern. Applying this
to simultaneous barycentric representations proves closure of finite convex
hulls under intersection. The result is transported to the hyperbolic Klein
model and to spherical cells lying in one common open hemisphere.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace BrehmApprox

variable {ι F : Type*} [Fintype ι] [AddCommGroup F] [Module ℝ F]

def nonnegativeSlice (L : (ι → ℝ) →ₗ[ℝ] F) (b : F) : Set (ι → ℝ) :=
  {x | L x = b ∧ ∀ i, 0 ≤ x i}

theorem extreme_eq_of_zero_pattern
    (L : (ι → ℝ) →ₗ[ℝ] F) (b : F) {x y : ι → ℝ}
    (hx : x ∈ (nonnegativeSlice L b).extremePoints ℝ)
    (hy : y ∈ nonnegativeSlice L b)
    (hzero : ∀ i, x i = 0 → y i = 0) : y = x := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 ≤ (x + t • (x - y)) i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => by simp [hi, hzero i hi])
    · have hxi : 0 < x i := lt_of_le_of_ne (hx.1.2 i) (Ne.symm hi)
      have hcont : Continuous (fun t : ℝ => (x + t • (x - y)) i) := by fun_prop
      have hp : 0 < (x + (0 : ℝ) • (x - y)) i := by simpa using hxi
      exact (hcont.continuousAt.eventually (eventually_gt_nhds hp)).mono
        (fun _ h => h.le)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let t : ℝ := r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htball : dist t 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  let z := x + t • (x - y)
  have hz : z ∈ nonnegativeSlice L b := by
    constructor
    · simp [z, map_add, map_smul, map_sub, hx.1.1, hy.1]
    · exact hball htball
  have hopen : x ∈ openSegment ℝ y z := by
    refine ⟨t / (1 + t), 1 / (1 + t), div_pos ht (by linarith),
      div_pos zero_lt_one (by linarith), ?_, ?_⟩
    · field_simp
      ring
    · ext i
      dsimp [z]
      field_simp
      ring
  exact hx.2 hy hz hopen

theorem finite_extremePoints_nonnegativeSlice
    (L : (ι → ℝ) →ₗ[ℝ] F) (b : F) :
    ((nonnegativeSlice L b).extremePoints ℝ).Finite := by
  classical
  let code : (nonnegativeSlice L b).extremePoints ℝ → Finset ι :=
    fun x => Finset.univ.filter (fun i => x.val i = 0)
  have hinj : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    symm
    apply extreme_eq_of_zero_pattern L b x.property y.property.1
    intro i hi
    have : i ∈ code x := by simp [code, hi]
    rw [hxy] at this
    simpa [code] using this
  have : Finite ((nonnegativeSlice L b).extremePoints ℝ) := Finite.of_injective code hinj
  exact Set.toFinite _

omit [Fintype ι] in
theorem convex_nonnegativeSlice (L : (ι → ℝ) →ₗ[ℝ] F) (b : F) :
    Convex ℝ (nonnegativeSlice L b) := by
  intro x hx y hy a c ha hc hac
  constructor
  · simp only [map_add, map_smul, hx.1, hy.1, ← add_smul, hac, one_smul]
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.2 i)) (mul_nonneg hc (hy.2 i))

theorem exists_finset_nonnegativeSlice
    (L : (ι → ℝ) →ₗ[ℝ] F) (b : F)
    (hcompact : IsCompact (nonnegativeSlice L b)) :
    ∃ V : Finset (ι → ℝ), nonnegativeSlice L b = convexHull ℝ (V : Set (ι → ℝ)) := by
  classical
  have hfinite := finite_extremePoints_nonnegativeSlice L b
  refine ⟨hfinite.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  have hclosed := hfinite.isClosed_convexHull (𝕜 := ℝ)
  simpa only [hclosed.closure_eq] using
    (closure_convexHull_extremePoints hcompact (convex_nonnegativeSlice L b)).symm

section Intersection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def intersectionLeft (V W : Finset E) : ((V ⊕ W) → ℝ) →ₗ[ℝ] E where
  toFun t := ∑ v : V, t (Sum.inl v) • v.val
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]

def intersectionData (V W : Finset E) : ((V ⊕ W) → ℝ) →ₗ[ℝ] (ℝ × ℝ × E) where
  toFun t := (∑ v : V, t (Sum.inl v), ∑ w : W, t (Sum.inr w),
    (∑ v : V, t (Sum.inl v) • v.val) - ∑ w : W, t (Sum.inr w) • w.val)
  map_add' x y := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_smul, Prod.mk_add_mk]
    congr 2
    abel
  map_smul' c x := by
    simp [Finset.mul_sum, Finset.smul_sum, mul_smul, smul_sub]

theorem intersectionData_mem_iff (V W : Finset E) (t : (V ⊕ W) → ℝ) :
    t ∈ nonnegativeSlice (intersectionData V W) (1, 1, 0) ↔
      (∑ v : V, t (Sum.inl v)) = 1 ∧ (∑ w : W, t (Sum.inr w)) = 1 ∧
      (∑ v : V, t (Sum.inl v) • v.val) = (∑ w : W, t (Sum.inr w) • w.val) ∧
      ∀ i, 0 ≤ t i := by
  simp only [nonnegativeSlice, Set.mem_ofPred_eq, intersectionData,
    LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq, sub_eq_zero]
  tauto

theorem isCompact_intersectionData (V W : Finset E) :
    IsCompact (nonnegativeSlice (intersectionData V W) (1, 1, 0)) := by
  classical
  have hclosed : IsClosed (nonnegativeSlice (intersectionData V W) (1, 1, 0)) := by
    change IsClosed ({t | intersectionData V W t = (1, 1, 0)} ∩
      {t | ∀ i, 0 ≤ t i})
    apply IsClosed.inter
    · exact isClosed_eq (intersectionData V W).continuous_of_finiteDimensional continuous_const
    · simp only [ofPred_forall]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : (V ⊕ W) → ℝ)) (b := 1)) hclosed
  intro t ht
  obtain ⟨hV, hW, _, ht⟩ := (intersectionData_mem_iff V W t).mp ht
  constructor
  · exact ht
  · intro i
    cases i with
    | inl v =>
      change t (Sum.inl v) ≤ 1
      rw [← hV]
      exact Finset.single_le_sum (fun j _ => ht (Sum.inl j)) (Finset.mem_univ v)
    | inr w =>
      change t (Sum.inr w) ≤ 1
      rw [← hW]
      exact Finset.single_le_sum (fun j _ => ht (Sum.inr j)) (Finset.mem_univ w)

theorem image_intersectionData (V W : Finset E) :
    (intersectionLeft V W) '' nonnegativeSlice (intersectionData V W) (1, 1, 0) =
      convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨hV, hW, heq, ht⟩ := (intersectionData_mem_iff V W t).mp ht
    constructor
    · exact mem_convexHull_of_exists_fintype (fun v : V => t (Sum.inl v))
        (fun v => v.val) (fun v => ht (Sum.inl v)) hV (fun v => v.property) rfl
    · apply mem_convexHull_of_exists_fintype (fun w : W => t (Sum.inr w))
        (fun w => w.val) (fun w => ht (Sum.inr w)) hW (fun w => w.property)
      exact heq.symm
  · rintro ⟨hxV, hxW⟩
    obtain ⟨v, hv0, hv1, hvx⟩ := Finset.mem_convexHull'.mp hxV
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxW
    let t : (V ⊕ W) → ℝ := Sum.elim (fun a : V => v a.val) (fun b : W => w b.val)
    have htv : (∑ a : V, t (Sum.inl a)) = 1 := by
      simpa only [t, Sum.elim_inl, Finset.sum_coe_sort] using hv1
    have htw : (∑ b : W, t (Sum.inr b)) = 1 := by
      simpa only [t, Sum.elim_inr, Finset.sum_coe_sort] using hw1
    have htvx : (∑ a : V, t (Sum.inl a) • a.val) = x := by
      simpa only [t, Sum.elim_inl] using
        (Finset.sum_coe_sort V (fun y => v y • y)).trans hvx
    have htwx : (∑ b : W, t (Sum.inr b) • b.val) = x := by
      simpa only [t, Sum.elim_inr] using
        (Finset.sum_coe_sort W (fun y => w y • y)).trans hwx
    refine ⟨t, (intersectionData_mem_iff V W t).mpr ⟨htv, htw, htvx.trans htwx.symm, ?_⟩, htvx⟩
    intro i
    cases i with
    | inl a => exact hv0 a.val a.property
    | inr b => exact hw0 b.val b.property

/-- The intersection of two genuine finite convex hulls is again a finite
convex hull. No polyhedral-intersection or triangulation axiom is used. The
ambient normed real vector space need not itself be finite dimensional. -/
theorem exists_finset_convexHull_inter (V W : Finset E) :
    ∃ Z : Finset E, convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E) =
      convexHull ℝ (Z : Set E) := by
  classical
  obtain ⟨C, hC⟩ := exists_finset_nonnegativeSlice (intersectionData V W) (1, 1, 0)
    (isCompact_intersectionData V W)
  refine ⟨C.image (intersectionLeft V W), ?_⟩
  rw [← image_intersectionData V W, hC, LinearMap.image_convexHull]
  rw [Finset.coe_image]

end Intersection

theorem EuclideanPolytope.inter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B : Set E} (hA : EuclideanPolytope A) (hB : EuclideanPolytope B) :
    EuclideanPolytope (A ∩ B) := by
  obtain ⟨V, rfl⟩ := hA
  obtain ⟨W, rfl⟩ := hB
  exact exists_finset_convexHull_inter V W

open HyperbolicSpace in
/-- Actual hyperbolic cells are closed under intersection. The finite
Euclidean hull intersection is transported through the globally defined
Klein chart, with its unit-ball domain checked at every new vertex. -/
theorem exists_finset_hyperbolicCell_inter {n : ℕ}
    (V W : Finset (HyperbolicSpace n)) :
    ∃ U : Finset (HyperbolicSpace n),
      hyperbolicCell V ∩ hyperbolicCell W = hyperbolicCell U := by
  classical
  obtain ⟨Z, hZ⟩ := exists_finset_convexHull_inter (V.image klein) (W.image klein)
  have hZball : ∀ z ∈ Z, ‖z‖ < 1 := by
    intro z hz
    have hm : z ∈ convexHull ℝ (Z : Set (EuclideanSpace ℝ (Fin n))) :=
      (subset_convexHull ℝ (Z : Set (EuclideanSpace ℝ (Fin n)))) hz
    rw [← hZ] at hm
    simpa only [Metric.mem_ball, dist_zero_right] using
      hyperbolic_klein_hull_subset_ball V hm.1
  let U : Finset (HyperbolicSpace n) := Z.image fromKlein
  have hU : U.image klein = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rwa [klein_fromKlein (hZball p hp)]
    · intro hz
      exact Finset.mem_image.mpr ⟨fromKlein z,
        Finset.mem_image.mpr ⟨z, hz, rfl⟩, klein_fromKlein (hZball z hz)⟩
  refine ⟨U, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, mem_hyperbolicCell_iff_klein_mem_convexHull]
  rw [hU, ← hZ]
  rfl

theorem HyperbolicPolytope.inter {n : ℕ}
    {A B : Set (HyperbolicSpace n)} (hA : HyperbolicPolytope A)
    (hB : HyperbolicPolytope B) : HyperbolicPolytope (A ∩ B) := by
  obtain ⟨V, rfl⟩ := hA
  obtain ⟨W, rfl⟩ := hB
  exact exists_finset_hyperbolicCell_inter V W

open GeodesicSphere in
/-- Two spherical cells in one actual open hemisphere have an actual finite
hemispherical cell as their intersection. This is the common-chart case used
when refining pieces inside a single original spherical cell. -/
theorem exists_finset_sphericalCell_inter_of_common_hemisphere {n : ℕ}
    (p : GeodesicSphere n) (V W : Finset (GeodesicSphere n))
    (hpV : ∀ v ∈ V, 0 < inner ℝ p.val v.val)
    (hpW : ∀ w ∈ W, 0 < inner ℝ p.val w.val) :
    ∃ U : Finset (GeodesicSphere n), InOpenHemisphere U ∧
      sphericalCell V ∩ sphericalCell W = sphericalCell U := by
  obtain ⟨Z, hZ⟩ := exists_finset_convexHull_inter
    (projectVertices p V hpV) (projectVertices p W hpW)
  have hV := sphericalCell_chartVertices_eq_image p (projectVertices p V hpV)
  rw [chartVertices_projectVertices] at hV
  have hW := sphericalCell_chartVertices_eq_image p (projectVertices p W hpW)
  rw [chartVertices_projectVertices] at hW
  refine ⟨chartVertices p Z, chartVertices_hemisphere p Z, ?_⟩
  rw [hV, hW, ← Set.image_inter (gnomonicPoint_injective p), hZ,
    ← sphericalCell_chartVertices_eq_image]

open GeodesicSphere in
theorem SphericalPolytope.inter_of_common_hemisphere {n : ℕ}
    {A B : Set (GeodesicSphere n)} (hA : SphericalPolytope A)
    (hB : SphericalPolytope B) (p : GeodesicSphere n)
    (hpA : ∀ a ∈ A, 0 < inner ℝ p.val a.val)
    (hpB : ∀ b ∈ B, 0 < inner ℝ p.val b.val) :
    SphericalPolytope (A ∩ B) := by
  obtain ⟨V, _, rfl⟩ := hA
  obtain ⟨W, _, rfl⟩ := hB
  exact exists_finset_sphericalCell_inter_of_common_hemisphere p V W
    (fun v hv => hpA v (mem_sphericalCell_of_mem hv))
    (fun w hw => hpB w (mem_sphericalCell_of_mem hw))

end BrehmApprox
