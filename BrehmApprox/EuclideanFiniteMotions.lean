module

public import BrehmApprox.EuclideanRadialCorrection
public import BrehmApprox.EuclideanBoundedFolding

/-!
# The finite-motion form of Brehm's correction

A locally finite selection of affine Euclidean motions remains such a selection
under the bounded radial correction. Finite interpolation then follows by
induction, starting from any bounded short folding with this property.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On every bounded ball, the map selects from finitely many affine motions. -/
def LocallyFiniteEuclideanMotions (f : E → E) : Prop :=
  ∀ R : ℝ, ∃ S : Finset (E ≃ᵃⁱ[ℝ] E),
    ∀ x, ‖x‖ ≤ R → ∃ r ∈ S, f x = r x

/-- A radial replacement has a single finite family of linear motions because
all its norm-matching witnesses lie in one bounded ball. -/
theorem radial_replacement_finite_motions
    {ψ H : E → E} (hψ : LocallyFiniteEuclideanMotions ψ)
    {R : ℝ} (hHnorm : ∀ x, ‖H x‖ = ‖x‖)
    (hscale : ∀ x, x ≠ 0 → ∃ t : ℝ, 0 < t ∧
      ψ (t • x) = t • H x ∧ ‖t • x‖ ≤ R) :
    ∃ S : Finset (E ≃ᵃⁱ[ℝ] E), ∀ x, ∃ r ∈ S, H x = r x := by
  classical
  obtain ⟨S, hS⟩ := hψ R
  let T := S.image fun r => (radialLinearMotion r).toAffineIsometryEquiv
  refine ⟨insert (AffineIsometryEquiv.refl ℝ E) T, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    refine ⟨AffineIsometryEquiv.refl ℝ E, Finset.mem_insert_self _ _, ?_⟩
    exact norm_eq_zero.mp (by simpa using hHnorm 0)
  obtain ⟨t, ht, htx, hbound⟩ := hscale x hx
  obtain ⟨r, hr, heq⟩ := hS (t • x) hbound
  refine ⟨(radialLinearMotion r).toAffineIsometryEquiv,
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, hr, rfl⟩), ?_⟩
  have hmatch : ‖r (t • x)‖ = ‖t • x‖ := by
    rw [← heq, htx, norm_smul, hHnorm, norm_smul]
  have hrad := radialLinearMotion_eq r hmatch
  rw [map_smul, ← heq, htx] at hrad
  have hcancel := congrArg (fun z : E => t⁻¹ • z) hrad
  simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul,
    LinearIsometryEquiv.coe_toAffineIsometryEquiv] using hcancel.symm

/-- The pasted radial correction preserves the local finiteness of its motions. -/
theorem locallyFiniteEuclideanMotions_piecewise
    {ψ H : E → E} (hψ : LocallyFiniteEuclideanMotions ψ)
    (hH : ∃ S : Finset (E ≃ᵃⁱ[ℝ] E), ∀ x, ∃ r ∈ S, H x = r x)
    (p : E → Prop) [DecidablePred p] :
    LocallyFiniteEuclideanMotions (fun x => if p x then H x else ψ x) := by
  classical
  intro R
  obtain ⟨S, hS⟩ := hψ R
  obtain ⟨T, hT⟩ := hH
  refine ⟨S ∪ T, ?_⟩
  intro x hx
  by_cases hp : p x
  · obtain ⟨r, hr, heq⟩ := hT x
    exact ⟨r, Finset.mem_union_right _ hr, by simpa only [ite_eq_left hp] using heq⟩
  · obtain ⟨r, hr, heq⟩ := hS x hx
    exact ⟨r, Finset.mem_union_left _ hr, by simpa only [ite_eq_right hp] using heq⟩

/-- The origin correction, with its finite affine-motion certificate. -/
theorem exists_bounded_origin_correction_finite_motions
    {ψ : E → E} (hψ : Short ψ) (hψmotions : LocallyFiniteEuclideanMotions ψ)
    {R : ℝ} (hR : ∀ x, ‖ψ x‖ ≤ R) :
    ∃ G : E → E, Short G ∧ LocallyFiniteEuclideanMotions G ∧ G 0 = 0 ∧
      (∀ x, ‖G x‖ ≤ R) ∧ ∀ x, ‖ψ x‖ ≤ ‖x‖ → G x = ψ x := by
  classical
  by_cases hzero : ψ 0 = 0
  · exact ⟨ψ, hψ, hψmotions, hzero, hR, fun _ _ => rfl⟩
  obtain ⟨G, H, hG, hH, hGzero, hGbound, hHnorm, hGdef, hGfixed, hscale⟩ :=
    exists_bounded_origin_correction hψ hR hzero
  refine ⟨G, hG, ?_, hGzero, hGbound, hGfixed⟩
  have hGfun : G = fun x => if ‖x‖ < ‖ψ x‖ then H x else ψ x := funext hGdef
  rw [hGfun]
  exact locallyFiniteEuclideanMotions_piecewise hψmotions
    (radial_replacement_finite_motions hψmotions hHnorm hscale) _

/-- Translating source and target preserves the local finite-motion property. -/
theorem LocallyFiniteEuclideanMotions.translate
    {f : E → E} (hf : LocallyFiniteEuclideanMotions f) (a b : E) :
    LocallyFiniteEuclideanMotions (fun x => f (x + a) - b) := by
  classical
  intro R
  obtain ⟨S, hS⟩ := hf (R + ‖a‖)
  let transform (r : E ≃ᵃⁱ[ℝ] E) :=
    (AffineIsometryEquiv.vaddConst ℝ a).trans
      (r.trans (AffineIsometryEquiv.vaddConst ℝ b).symm)
  refine ⟨S.image transform, ?_⟩
  intro x hx
  obtain ⟨r, hr, heq⟩ := hS (x + a) ((norm_add_le x a).trans (add_le_add hx le_rfl))
  refine ⟨transform r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
  simpa only [transform, AffineIsometryEquiv.coe_trans,
    AffineIsometryEquiv.coe_vaddConst, AffineIsometryEquiv.coe_vaddConst_symm,
    Function.comp_apply, vadd_eq_add, vsub_eq_sub] using congrArg (· - b) heq

/-- A bounded short finite-motion map can be corrected at one prescribed point,
while preserving every value already compatible with that prescription. -/
theorem exists_bounded_point_correction_finite_motions
    {f : E → E} (hf : Short f) (hfm : LocallyFiniteEuclideanMotions f)
    (hfb : ∃ R : ℝ, ∀ x, ‖f x‖ ≤ R) (a b : E) :
    ∃ G : E → E, Short G ∧ LocallyFiniteEuclideanMotions G ∧
      (∃ R : ℝ, ∀ x, ‖G x‖ ≤ R) ∧ G a = b ∧
      ∀ x, dist (f x) b ≤ dist x a → G x = f x := by
  obtain ⟨R, hR⟩ := hfb
  let ψ : E → E := fun x => f (x + a) - b
  have hψ : Short ψ := by
    intro x y
    simpa only [ψ, dist_sub_right, dist_add_right] using hf (x + a) (y + a)
  have hψm : LocallyFiniteEuclideanMotions ψ := hfm.translate a b
  have hψb (x : E) : ‖ψ x‖ ≤ R + ‖b‖ :=
    (norm_sub_le _ _).trans (add_le_add (hR (x + a)) le_rfl)
  obtain ⟨G, hG, hGm, hG0, hGb, hGfixed⟩ :=
    exists_bounded_origin_correction_finite_motions hψ hψm hψb
  let F : E → E := fun x => G (x - a) + b
  refine ⟨F, ?_, ?_, ⟨R + ‖b‖ + ‖b‖, ?_⟩, ?_, ?_⟩
  · intro x y
    simpa only [F, dist_add_right, dist_sub_right] using hG (x - a) (y - a)
  · simpa only [sub_neg_eq_add, ← sub_eq_add_neg] using hGm.translate (-a) (-b)
  · intro x
    exact (norm_add_le _ _).trans (add_le_add (hGb (x - a)) le_rfl)
  · simp [F, hG0]
  · intro x hx
    have hnorm : ‖ψ (x - a)‖ ≤ ‖x - a‖ := by
      simpa only [ψ, sub_add_cancel, dist_eq_norm] using hx
    simp only [F, hGfixed (x - a) hnorm, ψ, sub_add_cancel]

/-- The finite interpolation induction keeps the image bounded. -/
theorem bounded_finite_extension_finite_motions_of_bounded_folding
    (hbase : ∃ ψ : E → E, Short ψ ∧ LocallyFiniteEuclideanMotions ψ ∧
      ∃ R : ℝ, ∀ x, ‖ψ x‖ ≤ R) :
    ∀ (s : Finset E) (f : E → E), ShortOn f (s : Set E) →
      ∃ h : E → E, Short h ∧ LocallyFiniteEuclideanMotions h ∧
        (∃ R : ℝ, ∀ x, ‖h x‖ ≤ R) ∧ ∀ x ∈ s, h x = f x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    obtain ⟨ψ, hψ, hψm, hψb⟩ := hbase
    exact ⟨ψ, hψ, hψm, hψb, by simp⟩
  | @insert a s ha ih =>
    intro f hf
    have hfs : ShortOn f (s : Set E) :=
      fun x hx y hy => hf x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
    obtain ⟨ψ, hψ, hψm, hψb, hψeq⟩ := ih f hfs
    obtain ⟨G, hG, hGm, hGb, hGa, hGfixed⟩ :=
      exists_bounded_point_correction_finite_motions hψ hψm hψb a (f a)
    refine ⟨G, hG, hGm, hGb, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hGa
    · rw [hGfixed x, hψeq x hx]
      rw [hψeq x hx]
      exact hf x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self _ _)

/-- The finite interpolation induction from a bounded short folding. -/
theorem finite_extension_finite_motions_of_bounded_folding
    (hbase : ∃ ψ : E → E, Short ψ ∧ LocallyFiniteEuclideanMotions ψ ∧
      ∃ R : ℝ, ∀ x, ‖ψ x‖ ≤ R) :
    FiniteExtension (LocallyFiniteEuclideanMotions (E := E)) := by
  intro s f hf
  obtain ⟨h, hh, hhm, hhb, heq⟩ :=
    bounded_finite_extension_finite_motions_of_bounded_folding hbase s f hf
  exact ⟨h, hh, hhm, heq⟩

/-- Brehm's finite interpolation theorem in its finite-motion form. -/
theorem euclidean_finite_extension_motions (n : ℕ) :
    FiniteExtension
      (LocallyFiniteEuclideanMotions (E := EuclideanSpace ℝ (Fin n))) := by
  apply finite_extension_finite_motions_of_bounded_folding
  exact ⟨coordinateFolding, coordinateFolding_short n,
    coordinateFolding_finite_motions n, Real.sqrt n, coordinateFolding_bounded⟩

end BrehmApprox
