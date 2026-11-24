module

public import BrehmApprox.EuclideanFiniteMotions

/-!
# Globally finite Euclidean Brehm extensions

A bounded local folding is made globally finite by replacing its exterior
with the radial extension of its equal-norm locus. Translating the target far
enough leaves all prescribed values inside the region where the map is kept.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A global finite selection of affine Euclidean isometries. -/
def FiniteEuclideanMotions (f : E → E) : Prop :=
  ∃ S : Finset (E ≃ᵃⁱ[ℝ] E), ∀ x, ∃ r ∈ S, f x = r x

theorem FiniteEuclideanMotions.locallyFinite
    {f : E → E} (hf : FiniteEuclideanMotions f) : LocallyFiniteEuclideanMotions f := by
  obtain ⟨S, hS⟩ := hf
  exact fun _ => ⟨S, fun x _ => hS x⟩

theorem FiniteEuclideanMotions.short_of_continuous
    {f : E → E} (hf : FiniteEuclideanMotions f) (hc : Continuous f) : Short f := by
  obtain ⟨S, hS⟩ := hf
  apply short_iff_lipschitz.mpr
  apply finite_selection_lipschitz_normed hc (F := fun r : S => (r.val : E → E))
    (fun r => r.val.isometry.lipschitzWith)
  intro x
  obtain ⟨r, hr, heq⟩ := hS x
  exact ⟨⟨r, hr⟩, heq⟩

theorem FiniteEuclideanMotions.translate
    {f : E → E} (hf : FiniteEuclideanMotions f) (a b : E) :
    FiniteEuclideanMotions (fun x => f (x + a) - b) := by
  classical
  obtain ⟨S, hS⟩ := hf
  let transform (r : E ≃ᵃⁱ[ℝ] E) :=
    (AffineIsometryEquiv.vaddConst ℝ a).trans
      (r.trans (AffineIsometryEquiv.vaddConst ℝ b).symm)
  refine ⟨S.image transform, ?_⟩
  intro x
  obtain ⟨r, hr, heq⟩ := hS (x + a)
  refine ⟨transform r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
  simpa only [transform, AffineIsometryEquiv.coe_trans,
    AffineIsometryEquiv.coe_vaddConst, AffineIsometryEquiv.coe_vaddConst_symm,
    Function.comp_apply, vadd_eq_add, vsub_eq_sub] using congrArg (· - b) heq

/-- Radial replacement outside the displacement region makes a bounded local
finite-motion map globally finite, while leaving the entire region unchanged. -/
theorem exists_finite_euclidean_motions_completion
    {ψ : E → E} (hψ : Short ψ) (hψm : LocallyFiniteEuclideanMotions ψ)
    {R : ℝ} (hR : ∀ x, ‖ψ x‖ ≤ R) (hzero : ψ 0 ≠ 0) :
    ∃ K : E → E, Short K ∧ FiniteEuclideanMotions K ∧
      ∀ x, ‖x‖ < ‖ψ x‖ → K x = ψ x := by
  classical
  obtain ⟨H, hH, hHnorm, hmatch, hscale⟩ :=
    exists_short_radial_replacement hψ hR hzero
  obtain ⟨S, hS⟩ := hψm R
  obtain ⟨T, hT⟩ := radial_replacement_finite_motions hψm hHnorm hscale
  let U : Set E := {x | ‖x‖ < ‖ψ x‖}
  let K : E → E := U.piecewise ψ H
  have hKcont : Continuous K := by
    apply Continuous.piecewise ?_ hψ.continuous hH.continuous
    intro x hx
    exact (hmatch x ((frontier_lt_subset_eq continuous_norm hψ.continuous.norm hx).symm)).symm
  have hKm : FiniteEuclideanMotions K := by
    refine ⟨S ∪ T, ?_⟩
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨r, hr, heq⟩ := hS x (hx.le.trans (hR x))
      exact ⟨r, Finset.mem_union_left _ hr, by simpa only [K, Set.piecewise, ite_eq_left hx] using heq⟩
    · obtain ⟨r, hr, heq⟩ := hT x
      exact ⟨r, Finset.mem_union_right _ hr, by simpa only [K, Set.piecewise, ite_eq_right hx] using heq⟩
  exact ⟨K, hKm.short_of_continuous hKcont, hKm, fun x hx => by
    exact Set.piecewise_eq_of_mem U ψ H hx⟩

/-- A bounded finite-motion interpolation can be completed to a globally finite
one. The nontriviality hypothesis is used only to move the target far away. -/
theorem finite_euclidean_motions_interpolation_of_bounded [Nontrivial E]
    (s : Finset E) {f h : E → E} (hh : Short h)
    (hhm : LocallyFiniteEuclideanMotions h) (hhb : ∃ R : ℝ, ∀ x, ‖h x‖ ≤ R)
    (heq : ∀ x ∈ s, h x = f x) :
    ∃ g : E → E, Short g ∧ FiniteEuclideanMotions g ∧ ∀ x ∈ s, g x = f x := by
  classical
  obtain ⟨R, hR⟩ := hhb
  let A : ℝ := ((s.sup (fun x => ‖x‖₊) : NNReal) : ℝ)
  have hA0 : 0 ≤ A := NNReal.coe_nonneg _
  have hA (x : E) (hx : x ∈ s) : ‖x‖ ≤ A := by
    exact_mod_cast Finset.le_sup (f := fun x => ‖x‖₊) hx
  obtain ⟨b, hb⟩ := NormedSpace.exists_lt_norm ℝ E (A + R + 1)
  let ψ : E → E := fun x => h x - b
  have hψ : Short ψ := by
    intro x y
    simpa only [ψ, dist_sub_right] using hh x y
  have hψm : LocallyFiniteEuclideanMotions ψ := by
    simpa only [add_zero] using hhm.translate 0 b
  have hψb (x : E) : ‖ψ x‖ ≤ R + ‖b‖ :=
    (norm_sub_le _ _).trans (add_le_add (hR x) le_rfl)
  have hbR : R < ‖b‖ := by linarith
  have hzero : ψ 0 ≠ 0 := by
    intro hz
    have he : h 0 = b := sub_eq_zero.mp hz
    have hh0 := hR 0
    rw [he] at hh0
    linarith
  obtain ⟨K, hK, hKm, hKfixed⟩ :=
    exists_finite_euclidean_motions_completion hψ hψm hψb hzero
  let g : E → E := fun x => K x + b
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x y
    simpa only [g, dist_add_right] using hK x y
  · simpa only [add_zero, sub_neg_eq_add] using hKm.translate 0 (-b)
  · intro x hx
    have hnorm : ‖x‖ < ‖ψ x‖ := by
      have htriangle : ‖b‖ ≤ ‖h x‖ + ‖h x - b‖ := norm_le_insert (h x) b
      have hxn := hA x hx
      have hhn := hR x
      dsimp [ψ]
      linarith
    simp only [g, hKfixed x hnorm, ψ, sub_add_cancel, heq x hx]

/-- Classical Brehm finite interpolation with one globally finite family of
affine isometries, in every Euclidean dimension. -/
theorem euclidean_finite_extension_global_motions (n : ℕ) :
    FiniteExtension (FiniteEuclideanMotions (E := EuclideanSpace ℝ (Fin n))) := by
  classical
  by_cases hn : n = 0
  · subst n
    intro s f hf
    let g : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0) := id
    refine ⟨g, fun _ _ => le_rfl, ⟨{AffineIsometryEquiv.refl ℝ _}, ?_⟩, ?_⟩
    · intro x
      exact ⟨AffineIsometryEquiv.refl ℝ _, Finset.mem_singleton_self _, rfl⟩
    · intro x hx
      exact Subsingleton.elim _ _
  · have : NeZero n := ⟨hn⟩
    intro s f hf
    have hbase : ∃ ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Short ψ ∧ LocallyFiniteEuclideanMotions ψ ∧ ∃ R : ℝ, ∀ x, ‖ψ x‖ ≤ R :=
      ⟨coordinateFolding, coordinateFolding_short n, coordinateFolding_finite_motions n,
        Real.sqrt n, coordinateFolding_bounded⟩
    obtain ⟨h, hh, hhm, hhb, heq⟩ :=
      bounded_finite_extension_finite_motions_of_bounded_folding hbase s f hf
    exact finite_euclidean_motions_interpolation_of_bounded s hh hhm hhb heq

end BrehmApprox
