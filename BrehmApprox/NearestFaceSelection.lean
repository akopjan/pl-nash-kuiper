module

public import BrehmApprox.AffineNormalFlattening
public import Mathlib.Analysis.Convex.Intrinsic

/-!+# Nearest-point selection along a finite face decomposition

The closest point in the relative interior of a face is the orthogonal
projection onto its affine span. A finite closed face decomposition therefore
gives local preservation of every incident affine face projection. This is the
geometric step that passes from relative-interior flattening to whole-face
reference agreement.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Relative interior written as an actual ball in the indicated affine
subspace. For the affine span this equals mathlib's intrinsic interior. -/
def RelativeInteriorIn (F : AffineSubspace ℝ E) (A : Set E) (p : E) : Prop :=
  p ∈ F ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ F, dist y p < ε → y ∈ A

lemma relativeInteriorIn_iff_intrinsicInterior (A : Set E) (p : E) :
    RelativeInteriorIn (affineSpan ℝ A) A p ↔ p ∈ intrinsicInterior ℝ A := by
  constructor
  · rintro ⟨hp, ε, hε, hball⟩
    apply mem_intrinsicInterior.mpr
    refine ⟨⟨p, hp⟩, mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨ε, hε, ?_⟩), rfl⟩
    intro y hy
    exact hball y y.property hy
  · intro hp
    obtain ⟨y, hy, hyeq⟩ := mem_intrinsicInterior.mp hp
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
    subst p
    refine ⟨y.property, ε, hε, ?_⟩
    intro z hz hdist
    exact hball (show (⟨z, hz⟩ : affineSpan ℝ A) ∈ Metric.ball y ε from hdist)

lemma relativeInteriorIn_mem {F : AffineSubspace ℝ E} {A : Set E} {p : E}
    (hp : RelativeInteriorIn F A p) : p ∈ A :=
  hp.2.choose_spec.2 p hp.1 (by simpa only [dist_self] using hp.2.choose_spec.1)

/-- Two-sided tangent variations force the normal vector to be orthogonal to
the affine face. The small variations are constructed explicitly. -/
lemma variational_orthogonal_of_relativeInterior (F : AffineSubspace ℝ E)
    {A : Set E} {x p : E} (hp : RelativeInteriorIn F A p)
    (hvar : ∀ y ∈ A, inner ℝ (x - p) (y - p) ≤ 0) : x - p ∈ F.directionᗮ := by
  obtain ⟨hpF, ε, hε, hball⟩ := hp
  apply (F.direction.mem_orthogonal' _).2
  intro v hv
  let t : ℝ := ε / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have ht : 0 < t := div_pos hε hden
  have hteq : t * (‖v‖ + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have hsize : t * ‖v‖ < ε := by nlinarith
  have hplusF : p + t • v ∈ F := by
    simpa only [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction (F.direction.smul_mem t hv) hpF
  have hminusF : p + (-t) • v ∈ F := by
    simpa only [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction (F.direction.smul_mem (-t) hv) hpF
  have hplusA : p + t • v ∈ A := hball _ hplusF (by
    simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht] using hsize)
  have hminusA : p + (-t) • v ∈ A := hball _ hminusF (by
    simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos ht] using hsize)
  have hplus := hvar _ hplusA
  have hminus := hvar _ hminusA
  simp only [add_sub_cancel_left, real_inner_smul_right] at hplus hminus
  nlinarith

/-- The closest point, when it lies in the relative interior of a face, is
also the affine orthogonal projection onto that face's span. -/
theorem convexProjection_affine_of_relativeInterior
    (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C) (hconvex : Convex ℝ C)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    {A : Set E} (hAC : A ⊆ C) (x : E)
    (hp : RelativeInteriorIn F A (convexProjection C hne hcomplete hconvex x)) :
    affineProjection F x = convexProjection C hne hcomplete hconvex x := by
  apply EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mpr
  refine ⟨hp.1, ?_⟩
  exact variational_orthogonal_of_relativeInterior F hp
    (fun y hy => convexProjection_variational C hne hcomplete hconvex x y (hAC hy))

/-- A finite decomposition into closed faces with relative-interior coverage
gives the needed local commutation. The nonincidence condition is explicit:
the selected point belongs to no face whose affine span fails to contain `F`.
No nearest-face or local-normal-selection axiom is used. -/
theorem convexProjection_locally_preserves_affine
    {ι : Type*} (I : Finset ι) (A : ι → Set E) (G : ι → AffineSubspace ℝ E)
    [∀ i, Nonempty (G i)] [∀ i, (G i).direction.HasOrthogonalProjection]
    (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C) (hconvex : Convex ℝ C)
    (hclosed : ∀ i ∈ I, IsClosed (A i)) (hsub : ∀ i ∈ I, A i ⊆ C)
    (hcover : ∀ q ∈ C, ∃ i ∈ I, RelativeInteriorIn (G i) (A i) q)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    {p : E} (hp : p ∈ C) (havoid : ∀ i ∈ I, ¬ F ≤ G i → p ∉ A i) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U,
      affineProjection F (convexProjection C hne hcomplete hconvex x) = affineProjection F x := by
  classical
  let J : Finset ι := I.filter fun i => ¬ F ≤ G i
  let V : Set E := ⋂ i ∈ J, (A i)ᶜ
  have hV : IsOpen V := isOpen_biInter_finset fun i hi =>
    (hclosed i (Finset.mem_filter.mp hi).1).isOpen_compl
  have hpV : p ∈ V := by
    apply Set.mem_iInter₂.mpr
    intro i hi
    exact havoid i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  let π := convexProjection C hne hcomplete hconvex
  refine ⟨π ⁻¹' V, hV.preimage (convexProjection_continuous C hne hcomplete hconvex), ?_, ?_⟩
  · change convexProjection C hne hcomplete hconvex p ∈ V
    rw [convexProjection_fix C hne hcomplete hconvex hp]
    exact hpV
  · intro x hx
    obtain ⟨i, hi, hrel⟩ := hcover (π x) (convexProjection_mem C hne hcomplete hconvex x)
    have hFG : F ≤ G i := by
      by_contra hnot
      have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨hi, hnot⟩
      exact Set.mem_iInter₂.mp hx i hiJ (relativeInteriorIn_mem hrel)
    have hproj := convexProjection_affine_of_relativeInterior C hne hcomplete hconvex
      (G i) (hsub i hi) x hrel
    rw [← hproj]
    exact affineProjection_nested hFG x

/-- Equal affine projections give equal nearest projections onto every
complete convex subset of that affine subspace. -/
lemma convexProjection_eq_of_affine_eq
    (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C) (hconvex : Convex ℝ C)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (hCF : C ⊆ F) {x y : E} (hxy : affineProjection F x = affineProjection F y) :
    convexProjection C hne hcomplete hconvex x =
      convexProjection C hne hcomplete hconvex y := by
  calc
    _ = convexProjection C hne hcomplete hconvex (affineProjection F x) :=
      (convexProjection_after_affine_projection C hne hcomplete hconvex F hCF x).symm
    _ = convexProjection C hne hcomplete hconvex (affineProjection F y) := by rw [hxy]
    _ = _ := convexProjection_after_affine_projection C hne hcomplete hconvex F hCF y

/-- The local affine commutation supplied by finite face selection transfers
to the nearest projection onto the whole closed face. -/
lemma convexProjection_eventually_commutes
    (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C) (hconvex : Convex ℝ C)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (hCF : C ⊆ F) {Q : E → E} {p : E}
    (hQ : (fun x => affineProjection F (Q x)) =ᶠ[𝓝 p] affineProjection F) :
    (fun x => convexProjection C hne hcomplete hconvex (Q x)) =ᶠ[𝓝 p]
      convexProjection C hne hcomplete hconvex := by
  filter_upwards [hQ] with x hx
  exact convexProjection_eq_of_affine_eq C hne hcomplete hconvex F hCF hx

end BrehmApprox
