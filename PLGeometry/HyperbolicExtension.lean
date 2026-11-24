module

public import PLGeometry.Definitions
public import BrehmApprox.HyperbolicFiniteSelection
public import BrehmApprox.CarrierPolytopeArrangement
public import BrehmApprox.PullingPolytopeFamily
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Hyperbolic finite interpolation with a compatible triangulation

A locally finite polyhedral complex fills the open Klein ball. The affine
equality arrangement of the normalized Lorentz graph refines this complex.
Compatible pulling triangulations then give an actual locally finite
geodesic triangulation of hyperbolic space.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox BrehmApprox.HyperbolicSpace

namespace ArchivePLGeometry

variable {n : ℕ} {I : Type*}

local instance hyperbolicExtensionLocalInstance1 (α : Type*) : DecidableEq α := Classical.decEq α

def hyperbolicTriangulationOfCover
    [LinearOrder (EuclideanSpace ℝ (Fin n))]
    (K : PolytopeCoverOn (EuclideanSpace ℝ (Fin n)) I (Metric.ball 0 1)) :
    Triangulation .hyperbolic n (HyperbolicSpace n) where
  simplices := {σ | σ.image klein ∈ Pulling.familyFaces K.cell K.polytope}
  cell := hyperbolicCell
  chart _ := id
  cover x := by
    have hx : klein x ∈ ⋃ i, K.cell i :=
      Set.mem_iUnion.mpr (K.cover (klein x) (by simpa using norm_klein_lt_one x))
    rw [Pulling.family_faces_cover K.cell K.polytope] at hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hx
    have hball : ∀ p ∈ W, ‖p‖ < 1 := by
      obtain ⟨i, hi⟩ := hW
      intro p hp
      have hpHull : p ∈ convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin n))) :=
        subset_convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin n))) hp
      have hpC := Pulling.family_face_subset_cell K.cell K.polytope hi
        hpHull
      simpa only [Metric.mem_ball, dist_zero_right] using K.cell_subset i hpC
    refine ⟨W.image fromKlein, ?_, ?_⟩
    · change (W.image fromKlein).image klein ∈ Pulling.familyFaces K.cell K.polytope
      rwa [klein_image_fromKlein_finset W hball]
    · exact (mem_hyperbolicCell_fromKlein_finset W hball x).mpr hxW
  locallyFinite := by
    let B : Set (Finset (HyperbolicSpace n)) :=
      {σ | σ.image klein ∈ Pulling.familyFaces K.cell K.polytope}
    let φ : B → Pulling.familyFaces K.cell K.polytope :=
      fun σ => ⟨σ.val.image klein, σ.property⟩
    have hφ : Function.Injective φ := by
      intro σ τ h
      apply Subtype.ext
      exact Finset.image_injective klein_injective (congrArg Subtype.val h)
    have hlocal := Pulling.family_faces_locallyFinite_on K.cell K.polytope
      (Metric.ball 0 1) K.locallyFinite
    have hlocal' := (hlocal.comp_injective hφ).preimage_continuous
      (kleinHomeomorph (n := n)).continuous
    convert hlocal' using 1
    funext σ
    ext x
    exact mem_hyperbolicCell_iff_klein_mem_convexHull σ.val x
  vertices_mem _ _ _ hx := mem_hyperbolicCell_of_mem hx
  simplex σ hσ := by
    rw [Finset.image_id]
    change LinearIndependent ℝ (fun v : σ => lift v.val)
    apply (linearIndependent_lift_iff_affineIndependent_klein
      ((↑) : σ → HyperbolicSpace n)).mpr
    let e : σ ↪ σ.image klein :=
      ⟨fun v => ⟨klein v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩,
        fun v w h => Subtype.ext (klein_injective (congrArg Subtype.val h))⟩
    exact AffineIndependent.comp_embedding e
      (Pulling.family_face_independent K.cell K.polytope hσ)
  image_cell _ _ := by simp only [Set.image_id, Finset.image_id]; rfl
  isometry_cell _ _ _ _ _ _ := rfl
  faces σ hσ τ hτσ := Pulling.family_face_downward K.cell K.polytope hσ
    (Finset.image_subset_image hτσ)
  image_face _ _ _ _ := by simp only [Set.image_id, Finset.image_id]; rfl
  intersection σ hσ τ hτ := by
    ext x
    simp only [Set.mem_inter_iff, mem_hyperbolicCell_iff_klein_mem_convexHull]
    rw [Finset.image_inter σ τ klein_injective, Finset.coe_inter]
    rw [← Pulling.family_faces_intersection K.cell K.polytope K.face_inter hσ hτ]
    rfl

/-- Continuous finite Lorentz motion selection gives the concrete PL predicate. -/
theorem plIsometry_hyperbolic_of_finite_lorentz_selection
    {J : Type} [Finite J] (r : J → HyperbolicSpace n ≃ᵢ HyperbolicSpace n)
    (L : J → (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)))
    (hL : ∀ j x, lift (r j x) = L j (lift x))
    {g : HyperbolicSpace n → HyperbolicSpace n} (hg : Continuous g)
    (hselect : ∀ x, ∃ j, g x = r j x) : PLIsometry .hyperbolic n g := by
  classical
  let : LinearOrder (EuclideanSpace ℝ (Fin n)) :=
    IsWellOrder.linearOrder (WellOrderingRel : EuclideanSpace ℝ (Fin n) → _ → Prop)
  have hsel : ∀ p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∃ j, kleinLift g p = kleinAffine (L j) p := by
    intro p hp
    obtain ⟨j, hj⟩ := hselect (fromKlein p)
    refine ⟨j, kleinLift_eq_affine_of_lift (L j) (by simpa using hp) ?_⟩
    rw [hj, hL]
  obtain ⟨I', K, hK⟩ := refine_polytopeCoverOn_affine_selection
    (UnitBallCover.polytopeCover (E := EuclideanSpace ℝ (Fin n)))
    (fun j => kleinAffine (L j)) (continuousOn_kleinLift hg) hsel
  let T := hyperbolicTriangulationOfCover K
  refine ⟨hg, T, ?_⟩
  intro σ hσ x hx y hy
  obtain ⟨i, hi⟩ := hσ
  have hsub := Pulling.family_face_subset_cell K.cell K.polytope hi
  obtain ⟨j, hj⟩ := hK i
  have hx' := (mem_hyperbolicCell_iff_klein_mem_convexHull σ x).mp hx
  have hy' := (mem_hyperbolicCell_iff_klein_mem_convexHull σ y).mp hy
  rw [eq_of_kleinLift_eq_affine (r j) (L j) (hL j) x (hj (hsub hx')),
    eq_of_kleinLift_eq_affine (r j) (L j) (hL j) y (hj (hsub hy'))]
  exact (r j).dist_eq x y

theorem plIsometry_hyperbolic_of_finite_pogorelov_selection
    {g : HyperbolicSpace n → HyperbolicSpace n} (hg : Continuous g)
    (R : Finset (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)))
    (hR : ∀ x, ∃ r ∈ R, g x = Pogorelov.affineMotion r x) :
    PLIsometry .hyperbolic n g := by
  apply plIsometry_hyperbolic_of_finite_lorentz_selection
    (fun r : R => Pogorelov.affineMotion r.val)
    (fun r : R => Pogorelov.motionLinear r.val.linearIsometryEquiv (r.val 0))
    (fun r x => Pogorelov.lift_affineMotion r.val x) hg
  intro x
  obtain ⟨r, hr, heq⟩ := hR x
  exact ⟨⟨r, hr⟩, heq⟩

/-- The hyperbolic component of the Brehm–Akopyan–Tarasov theorem. -/
theorem brehm_hyperbolic (n : ℕ)
    (A : Finset (Model .hyperbolic n)) (f : Model .hyperbolic n → Model .hyperbolic n)
    (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ dist x y) :
    ∃ F : Model .hyperbolic n → Model .hyperbolic n,
      LipschitzWith 1 F ∧ PLIsometry .hyperbolic n F ∧ ∀ x ∈ A, F x = f x := by
  classical
  by_cases hA : A.Nonempty
  · let : Nonempty A := hA.to_subtype
    obtain ⟨g, hg, ⟨R, hR⟩, hdata⟩ := Pogorelov.finite_hyperbolic_interpolation
      (fun i : A => i.val) (fun i : A => f i.val)
      (fun i j => hf i.val i.property j.val j.property)
    exact ⟨g, hg, plIsometry_hyperbolic_of_finite_pogorelov_selection hg.continuous R hR,
      fun x hx => hdata ⟨x, hx⟩⟩
  · have hPL : PLIsometry .hyperbolic n (id : HyperbolicSpace n → HyperbolicSpace n) := by
      apply plIsometry_hyperbolic_of_finite_lorentz_selection
        (fun _ : Unit => IsometryEquiv.refl _)
        (fun _ : Unit => LinearMap.id) (fun _ _ => rfl) continuous_id
      intro x
      exact ⟨(), rfl⟩
    exact ⟨id, LipschitzWith.id, hPL, fun x hx => (hA ⟨x, hx⟩).elim⟩

end ArchivePLGeometry
