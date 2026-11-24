module

public import BrehmApprox.HyperbolicPogorelovMotions
public import BrehmApprox.EuclideanPolytopeNeighborhoods
public import BrehmApprox.EuclideanFiniteMotions

/-!
# Transfer of finite interpolation from Euclidean to hyperbolic geometry

The finite family formulation allows coincident source entries: shortness
forces their prescribed values to coincide. The Pogorelov transform then
transfers a Euclidean finite PL extension to a short hyperbolic extension
selected pointwise from finitely many explicitly Lorentz-linear motions.

The Euclidean finite extension theorem is an explicit input to this reduction;
no geometric axiom is declared or imported here.
-/

@[expose] public section
noncomputable section

namespace BrehmApprox

theorem FiniteExtension.realizes_finite_family
    {X : Type*} [MetricSpace X] [Inhabited X]
    {Good : (X → X) → Prop} (hExt : FiniteExtension Good)
    {ι : Type*} [Fintype ι] (p q : ι → X)
    (h : ∀ i j, dist (q i) (q j) ≤ dist (p i) (p j)) :
    ∃ F : X → X, Short F ∧ Good F ∧ ∀ i, F (p i) = q i := by
  classical
  let f : X → X := fun x => if hx : ∃ i, p i = x then q (Classical.choose hx) else default
  have hf (i : ι) : f (p i) = q i := by
    have hex : ∃ j, p j = p i := ⟨i, rfl⟩
    dsimp [f]
    rw [dite_eq_left hex]
    have hp := Classical.choose_spec hex
    have hh := h (Classical.choose hex) i
    rw [hp, dist_self] at hh
    exact dist_eq_zero.mp (le_antisymm hh dist_nonneg)
  let V : Finset X := Finset.univ.image p
  have hshort : ShortOn f (V : Set X) := by
    intro x hx y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    rw [hf, hf]
    exact h i j
  obtain ⟨F, hF, hGood, hV⟩ := hExt V f hshort
  refine ⟨F, hF, hGood, ?_⟩
  intro i
  rw [hV (p i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hf]

theorem locallyEuclideanPL_finite_motions_on_ball {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : LocallyEuclideanPL F) :
    ∃ R : Finset (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)),
      ∀ u, ‖u‖ < 2 → ∃ r ∈ R, F u = r u := by
  classical
  obtain ⟨V, hV, _⟩ :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 : ℝ)).exists_subset_interior_convexHull_finset_of_isCompact
      (isCompact_closedBall 0 2) (show Set.univ ∈ nhdsSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 2) from Filter.univ_mem)
  obtain ⟨C, hC, hpieces⟩ := hF V
  let r : C → (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun D => Classical.choose (hpieces D.val D.property)
  refine ⟨C.attach.image r, ?_⟩
  intro u hu
  have huK : u ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin n))) :=
    interior_subset (hV (by simpa only [Metric.mem_closedBall, dist_zero_right] using hu.le))
  rw [hC] at huK
  obtain ⟨D, huK⟩ := Set.mem_iUnion.mp huK
  obtain ⟨hD, huD⟩ := Set.mem_iUnion.mp huK
  refine ⟨r ⟨D, hD⟩, Finset.mem_image.mpr ⟨⟨D, hD⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  exact Classical.choose_spec (hpieces D hD) u huD

namespace Pogorelov

variable {n : ℕ}

theorem finite_hyperbolic_interpolation_of_euclidean_motions
    (hExt : FiniteExtension (LocallyFiniteEuclideanMotions (E := EuclideanSpace ℝ (Fin n))))
    {ι : Type*} [Fintype ι] [Nonempty ι] (p q : ι → HyperbolicSpace n)
    (h : ∀ i j, dist (q i) (q j) ≤ dist (p i) (p j)) :
    ∃ g : HyperbolicSpace n → HyperbolicSpace n,
      LipschitzWith 1 g ∧
      (∃ R : Finset (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)),
        ∀ x, ∃ r ∈ R, g x = affineMotion r x) ∧
      ∀ i, g (p i) = q i := by
  classical
  let u : ι → EuclideanSpace ℝ (Fin n) := fun i => pairLeft (p i).point (q i).point
  let v : ι → EuclideanSpace ℝ (Fin n) := fun i => pairRight (p i).point (q i).point
  have hpair : ∀ i j, dist (v i) (v j) ≤ dist (u i) (u j) := by
    intro i j
    exact (distance_le_iff_pair_dist _ _ _ _).mp (h i j)
  obtain ⟨F, hF, hFmotions, hFi⟩ := hExt.realizes_finite_family u v hpair
  have hFLip : LipschitzWith 1 F := short_iff_lipschitz.mp hF
  have hzero : ‖F 0‖ < 2 := by
    let i : ι := Classical.choice inferInstance
    have htri := dist_triangle (F 0) (F (u i)) 0
    have hdist := hF 0 (u i)
    rw [hFi i] at htri
    rw [hFi i] at hdist
    simp only [dist_zero_left, dist_zero_right] at htri hdist
    have hnorm := norm_pairLeft_add_norm_pairRight_lt_two (p i).point (q i).point
    change ‖u i‖ + ‖v i‖ < 2 at hnorm
    linarith
  let g := liftShort F hFLip hzero
  refine ⟨g, liftShort_lipschitz F hFLip hzero, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := hFmotions 2
    refine ⟨R, ?_⟩
    intro x
    let a := pairLeft x.point (g x).point
    have ha : ‖a‖ < 2 := by
      have hh := norm_pairLeft_add_norm_pairRight_lt_two x.point (g x).point
      dsimp [a]
      linarith [norm_nonneg (pairRight x.point (g x).point)]
    obtain ⟨r, hrR, hr⟩ := hR a ha.le
    exact ⟨r, hrR, liftShort_eq_affineMotion F hFLip hzero r x hr⟩
  · intro i
    apply liftShort_interpolates F hFLip hzero (p i) (q i)
    exact (hFi i).symm

/-- Akopyan–Tarasov finite interpolation, before the polyhedral arrangement
is transferred through Klein coordinates. The finite-motion conclusion is
global, even though the Euclidean construction need only be locally finite. -/
theorem finite_hyperbolic_interpolation
    {ι : Type*} [Fintype ι] [Nonempty ι] (p q : ι → HyperbolicSpace n)
    (h : ∀ i j, dist (q i) (q j) ≤ dist (p i) (p j)) :
    ∃ g : HyperbolicSpace n → HyperbolicSpace n,
      LipschitzWith 1 g ∧
      (∃ R : Finset (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)),
        ∀ x, ∃ r ∈ R, g x = affineMotion r x) ∧
      ∀ i, g (p i) = q i :=
  finite_hyperbolic_interpolation_of_euclidean_motions
    (euclidean_finite_extension_motions n) p q h

end Pogorelov
end BrehmApprox
