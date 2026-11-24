module

public import BrehmApprox.HyperbolicPogorelovExtension
public import BrehmApprox.HyperbolicSimplicialCharts
public import BrehmApprox.AffineArrangement

/-!
# Finite Lorentz motion selections in Klein coordinates

Dividing the lifted graph by the source height turns every Lorentz-linear
motion into an ordinary affine map on the Klein ball. Consequently a finite
polyhedral subdivision of this normalized graph pulls back to a finite
hyperbolic piecewise isometry.
-/

@[expose] public section
noncomputable section

namespace BrehmApprox

open HyperbolicSpace
open Classical

variable {n : ℕ}

theorem HyperbolicSpace.continuous_lift :
    Continuous (lift : HyperbolicSpace n → ℝ × EuclideanSpace ℝ (Fin n)) :=
  (Hyperboloid.continuous_height.comp continuous_point).prodMk continuous_point

theorem HyperbolicSpace.lift_injective :
    Function.Injective (lift : HyperbolicSpace n → ℝ × EuclideanSpace ℝ (Fin n)) := by
  intro x y h
  exact HyperbolicSpace.ext (congrArg Prod.snd h)

/-- The normalized graph in the affine slice of the Klein model. -/
def kleinLift (g : HyperbolicSpace n → HyperbolicSpace n)
    (p : EuclideanSpace ℝ (Fin n)) : ℝ × EuclideanSpace ℝ (Fin n) :=
  (Hyperboloid.height (fromKlein p).point)⁻¹ • lift (g (fromKlein p))

theorem continuousOn_kleinLift {g : HyperbolicSpace n → HyperbolicSpace n}
    (hg : Continuous g) : ContinuousOn (kleinLift g) (Metric.ball 0 1) := by
  have hsource := continuousOn_fromKlein (n := n)
  have hh := (Hyperboloid.continuous_height.comp continuous_point).continuousOn.comp
    hsource (Set.mapsTo_univ _ _)
  have hi := hh.inv₀ (fun p _ => (Hyperboloid.height_pos (fromKlein p).point).ne')
  exact hi.smul ((continuous_lift.comp hg).continuousOn.comp hsource (Set.mapsTo_univ _ _))

/-- Homogeneous coordinates in the affine slice with time coordinate one. -/
def kleinHomogeneous : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) where
  toFun p := (1, p)
  linear := (0 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ).prod LinearMap.id
  map_vadd' p v := by ext <;> simp

/-- The affine expression of a Lorentz-linear map in the Klein slice. -/
def kleinAffine
    (L : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) :=
  L.toAffineMap.comp kleinHomogeneous

theorem kleinAffine_apply
    (L : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    (p : EuclideanSpace ℝ (Fin n)) : kleinAffine L p = L (1, p) := rfl

theorem kleinLift_eq_affine_of_lift
    {g : HyperbolicSpace n → HyperbolicSpace n}
    (L : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    {p : EuclideanSpace ℝ (Fin n)} (hp : ‖p‖ < 1)
    (hL : lift (g (fromKlein p)) = L (lift (fromKlein p))) :
    kleinLift g p = kleinAffine L p := by
  unfold kleinLift
  rw [hL, lift_eq_height_smul_klein, klein_fromKlein hp, map_smul, smul_smul,
    inv_mul_cancel₀ (Hyperboloid.height_pos (fromKlein p).point).ne', one_smul]
  rfl

theorem eq_of_kleinLift_eq_affine
    {g : HyperbolicSpace n → HyperbolicSpace n}
    (r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    (L : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    (hL : ∀ x, lift (r x) = L (lift x)) (x : HyperbolicSpace n)
    (h : kleinLift g (klein x) = kleinAffine L (klein x)) : g x = r x := by
  apply lift_injective
  have hr := kleinLift_eq_affine_of_lift L (norm_klein_lt_one x)
    (hL (fromKlein (klein x)))
  have heq : kleinLift g (klein x) = kleinLift r (klein x) := h.trans hr.symm
  simp only [kleinLift, fromKlein_klein] at heq
  exact (smul_right_injective _ (inv_ne_zero (Hyperboloid.height_pos x.point).ne')) heq

theorem klein_image_fromKlein_finset
    (W : Finset (EuclideanSpace ℝ (Fin n)))
    (hW : ∀ p ∈ W, ‖p‖ < 1) :
    (W.image fromKlein).image klein = W := by
  classical
  rw [Finset.image_image]
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    simpa only [Function.comp_apply, klein_fromKlein (hW q hq)] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, klein_fromKlein (hW p hp)⟩

theorem hyperbolicCell_fromKlein_finset
    (W : Finset (EuclideanSpace ℝ (Fin n)))
    (hW : ∀ p ∈ W, ‖p‖ < 1) :
    hyperbolicCell (W.image fromKlein) = fromKlein '' convexHull ℝ (W : Set _) := by
  rw [hyperbolicCell_eq_fromKlein_image, klein_image_fromKlein_finset W hW]

theorem mem_hyperbolicCell_fromKlein_finset
    (W : Finset (EuclideanSpace ℝ (Fin n)))
    (hW : ∀ p ∈ W, ‖p‖ < 1) (x : HyperbolicSpace n) :
    x ∈ hyperbolicCell (W.image fromKlein) ↔ klein x ∈ convexHull ℝ (W : Set _) := by
  rw [mem_hyperbolicCell_iff_klein_mem_convexHull, klein_image_fromKlein_finset W hW]

/-- A finite affine subdivision of the normalized lifted graph is a finite
hyperbolic subdivision of the original map. -/
theorem hyperbolicPLOn_of_klein_cover
    {ι : Type*} (r : ι → HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    (L : ι → (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    (hL : ∀ i x, lift (r i x) = L i (lift x))
    (g : HyperbolicSpace n → HyperbolicSpace n)
    (V : Finset (HyperbolicSpace n))
    (C : Finset (Finset (EuclideanSpace ℝ (Fin n))))
    (hcover : convexHull ℝ (V.image klein : Set (EuclideanSpace ℝ (Fin n))) =
      ⋃ W ∈ C, convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin n))))
    (hpieces : ∀ W ∈ C, ∃ i, ∀ p ∈ convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin n))),
      kleinLift g p = kleinAffine (L i) p) :
    HyperbolicPLOn (hyperbolicCell V) g := by
  have hsub (W : Finset (EuclideanSpace ℝ (Fin n))) (hW : W ∈ C) :
      convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin n))) ⊆
        convexHull ℝ (V.image klein : Set (EuclideanSpace ℝ (Fin n))) := by
    intro p hp
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hW, hp⟩⟩
  have hball (W : Finset (EuclideanSpace ℝ (Fin n))) (hW : W ∈ C) :
      ∀ p ∈ W, ‖p‖ < 1 := by
    intro p hp
    have hpK := hsub W hW (subset_convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin n))) hp)
    simpa only [Metric.mem_ball, dist_zero_right] using hyperbolic_klein_hull_subset_ball V hpK
  refine ⟨C.image (fun W => W.image fromKlein), ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have hp := (mem_hyperbolicCell_iff_klein_mem_convexHull V x).mp hx
      rw [hcover] at hp
      obtain ⟨W, hp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hW, hpW⟩ := Set.mem_iUnion.mp hp
      exact Set.mem_iUnion.mpr ⟨W.image fromKlein, Set.mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨W, hW, rfl⟩,
          (mem_hyperbolicCell_fromKlein_finset W (hball W hW) x).mpr hpW⟩⟩
    · intro hx
      obtain ⟨D, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hD, hxD⟩ := Set.mem_iUnion.mp hx
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hD
      apply (mem_hyperbolicCell_iff_klein_mem_convexHull V x).mpr
      exact hsub W hW ((mem_hyperbolicCell_fromKlein_finset W (hball W hW) x).mp hxD)
  · intro D hD
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨i, hi⟩ := hpieces W hW
    refine ⟨r i, ?_⟩
    intro x hx
    apply eq_of_kleinLift_eq_affine (r i) (L i) (hL i) x
    exact hi (klein x) ((mem_hyperbolicCell_fromKlein_finset W (hball W hW) x).mp hx)

/-- A continuous finite selection of Lorentz-linear isometries is locally
piecewise isometric on finite hyperbolic polytopes. -/
theorem locallyHyperbolicPL_of_finite_lorentz_selection
    {ι : Type*} [Finite ι] (r : ι → HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    (L : ι → (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    (hL : ∀ i x, lift (r i x) = L i (lift x))
    {g : HyperbolicSpace n → HyperbolicSpace n} (hg : Continuous g)
    (hselect : ∀ x, ∃ i, g x = r i x) : LocallyHyperbolicPL g := by
  intro V
  have hcontinuous := (continuousOn_kleinLift hg).mono (hyperbolic_klein_hull_subset_ball V)
  have hsel : ∀ p ∈ convexHull ℝ (V.image klein : Set (EuclideanSpace ℝ (Fin n))),
      ∃ i, kleinLift g p = kleinAffine (L i) p := by
    intro p hp
    have hpball : ‖p‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hyperbolic_klein_hull_subset_ball V hp
    obtain ⟨i, hi⟩ := hselect (fromKlein p)
    refine ⟨i, kleinLift_eq_affine_of_lift (L i) hpball ?_⟩
    rw [hi, hL]
  obtain ⟨C, hC, hpieces⟩ := finite_selection_affine_polytope_cover
    (V.image klein) (fun i => kleinAffine (L i)) hcontinuous hsel
  exact hyperbolicPLOn_of_klein_cover r L hL g V C hC hpieces

theorem locallyHyperbolicPL_of_finite_pogorelov_selection
    {g : HyperbolicSpace n → HyperbolicSpace n} (hg : Continuous g)
    (R : Finset (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)))
    (hR : ∀ x, ∃ r ∈ R, g x = Pogorelov.affineMotion r x) : LocallyHyperbolicPL g := by
  apply locallyHyperbolicPL_of_finite_lorentz_selection
    (fun r : R => Pogorelov.affineMotion r.val)
    (fun r : R => Pogorelov.motionLinear r.val.linearIsometryEquiv (r.val 0))
    (fun r x => Pogorelov.lift_affineMotion r.val x) hg
  intro x
  obtain ⟨r, hr, heq⟩ := hR x
  exact ⟨⟨r, hr⟩, heq⟩

/-- Akopyan–Tarasov finite interpolation for the actual hyperbolic metric,
with finite isometric subdivisions on every compact hyperbolic polytope. -/
theorem hyperbolic_finite_extension (n : ℕ) :
    FiniteExtension (LocallyHyperbolicPL (n := n)) := by
  intro s f hf
  by_cases hs : s.Nonempty
  · let : Nonempty s := hs.to_subtype
    obtain ⟨g, hg, ⟨R, hR⟩, hdata⟩ := Pogorelov.finite_hyperbolic_interpolation
      (fun i : s => i.val) (fun i : s => f i.val) (fun i j => hf i.val i.property j.val j.property)
    refine ⟨g, short_iff_lipschitz.mpr hg,
      locallyHyperbolicPL_of_finite_pogorelov_selection hg.continuous R hR, ?_⟩
    intro x hx
    exact hdata ⟨x, hx⟩
  · refine ⟨id, ?_, ?_, ?_⟩
    · intro x y
      rfl
    · intro V
      refine ⟨{V}, ?_, ?_⟩
      · simp
      · intro W hW
        have hWV : W = V := Finset.mem_singleton.mp hW
        subst W
        exact ⟨IsometryEquiv.refl _, fun _ _ => rfl⟩
    · intro x hx
      exact (hs ⟨x, hx⟩).elim

end BrehmApprox
