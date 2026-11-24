module

public import PLGeometry.CompactTriangulation
public import PLGeometry.EuclideanApproximation
public import PLGeometry.HyperbolicApproximation
public import PLGeometry.SphericalApproximation
public import BrehmApprox.SmallFoldingFromBrehm

/-!
# Approximation from a genuine initial PL folding

Compactness makes every locally finite source triangulation finite. Model-cell
rigidity then constructs genuine folded simplex data. Finite Brehm interpolation
shrinks a supplied folding as much as required by the approximation argument.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

open BrehmApprox

universe u
variable {P : Type u} [MetricSpace P] {n : ℕ}

/-- One actual Euclidean PL folding suffices for arbitrary short-map approximation. -/
theorem euclidean_approximation_of_pl_folding
    (hP : IsFinitePolyhedron .euclidean n P)
    (q : P → Model .euclidean n) (hq : PLIsometry .euclidean n q)
    (f : P → Model .euclidean n) (hf : LipschitzWith 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → Model .euclidean n, LipschitzWith 1 g ∧
      PLIsometry .euclidean n g ∧ ∀ x, dist (g x) (f x) < ε := by
  let : CompactSpace P := hP.compactSpace
  obtain ⟨T, hfin, hiso⟩ := hq.exists_finite_triangulation
  let e := FaceEnumeration.ofFinite hfin
  let hT := hP.intrinsic_triangulation T
  exact euclidean_approximation_of_folded_geometry
    (T.euclideanFoldedGeometry e q hiso hT) (T.euclideanFoldedFaceData e q hiso hT) f hf hε

/-- A genuine hyperbolic PL folding admits arbitrarily small compatible refinements. -/
theorem hyperbolic_smallFoldable_of_pl_folding
    (hP : IsFinitePolyhedron .hyperbolic n P)
    (q : P → Model .hyperbolic n) (hq : PLIsometry .hyperbolic n q) :
    HyperbolicSmallFoldable P n := by
  classical
  let : CompactSpace P := hP.compactSpace
  obtain ⟨T, hfin, hiso⟩ := hq.exists_finite_triangulation
  let e := FaceEnumeration.ofFinite hfin
  let hT := hP.intrinsic_triangulation T
  let G := T.hyperbolicFoldedGeometry e q hiso hT
  let D := T.hyperbolicFoldedFaceData e q hiso hT
  intro ρ hρ _
  obtain ⟨H, _, hGood, hLip, _, hnear⟩ :=
    G.exists_small_postcomposition (hyperbolicBrehm n) ⟨0⟩ hρ
  have hm : G.RealizedByModelMaps (H ∘ G.fold) :=
    ⟨fun _ => H, fun _ => hGood, fun _ _ _ => rfl⟩
  have hPL := plIsometry_hyperbolic_of_model_maps G D hLip.continuous hm
  obtain ⟨U, hU, hu⟩ := hPL.exists_finite_triangulation
  let e' := FaceEnumeration.ofFinite hU
  let hUintr := hP.intrinsic_triangulation U
  let G' := U.hyperbolicFoldedGeometry e' (H ∘ G.fold) hu hUintr
  let D' := U.hyperbolicFoldedFaceData e' (H ∘ G.fold) hu hUintr
  refine ⟨e'.count, G', D', ?_⟩
  intro i v hv
  change v ∈ (e'.face i).val.image (H ∘ G.fold) at hv
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
  have hzero : HyperbolicSpace.klein (⟨0⟩ : HyperbolicSpace n) = 0 := by
    simp only [HyperbolicSpace.klein, smul_zero]
  have hd := HyperbolicSpace.klein_dist_le (H (G.fold x)) ⟨0⟩
  rw [hzero, dist_zero_right] at hd
  exact hd.trans (hnear x).le

/-- One actual hyperbolic PL folding suffices for the full approximation conclusion. -/
theorem hyperbolic_approximation_of_pl_folding
    (hP : IsFinitePolyhedron .hyperbolic n P)
    (q : P → Model .hyperbolic n) (hq : PLIsometry .hyperbolic n q)
    (f : P → Model .hyperbolic n) (hf : LipschitzWith 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → Model .hyperbolic n, LipschitzWith 1 g ∧
      PLIsometry .hyperbolic n g ∧ ∀ x, dist (g x) (f x) < ε :=
  hyperbolic_approximation_of_small_foldable
    (hyperbolic_smallFoldable_of_pl_folding hP q hq) f hf hε

/-- An initial spherical folding in one open hemisphere admits arbitrarily
small genuine spherical foldings, with compatible finite triangulations. -/
theorem spherical_smallFoldable_of_hemispherical_pl_folding
    (hP : IsFinitePolyhedron .spherical n P)
    (q : P → Model .spherical n) (hq : PLIsometry .spherical n q)
    (p : GeodesicSphere n) (hhem : ∀ x, q x ∈ GeodesicSphere.openHemisphere p) :
    SphericalSmallFoldable P n := by
  let : CompactSpace P := hP.compactSpace
  obtain ⟨T, hfin, hiso⟩ := hq.exists_finite_triangulation
  let e := FaceEnumeration.ofFinite hfin
  let hT := hP.intrinsic_triangulation T
  let G := T.sphericalFoldedGeometry e q hiso hT
  let D := T.sphericalFoldedFaceData e q hiso hT
  intro ρ hρ _
  obtain ⟨H, _, hGood, hLip, _, hnear⟩ :=
    G.exists_small_postcomposition (sphericalBrehm n) p hρ
  have hm : G.RealizedByModelMaps (H ∘ G.fold) :=
    ⟨fun _ => H, fun _ => hGood, fun _ _ _ => rfl⟩
  have hPL := plIsometry_spherical_of_model_maps G D p hhem hLip.continuous hm
  obtain ⟨U, hU, hu⟩ := hPL.exists_finite_triangulation
  let e' := FaceEnumeration.ofFinite hU
  let hUintr := hP.intrinsic_triangulation U
  let G' := U.sphericalFoldedGeometry e' (H ∘ G.fold) hu hUintr
  let D' := U.sphericalFoldedFaceData e' (H ∘ G.fold) hu hUintr
  refine ⟨e'.count, G', D', p, ?_⟩
  intro x
  exact (dist_comm _ _).trans_le (hnear x).le

/-- Spherical short maps with the standard strictness or hemisphere condition
are approximable once an initial hemispherical PL folding is supplied. -/
theorem spherical_approximation_of_hemispherical_pl_folding
    (hP : IsFinitePolyhedron .spherical n P)
    (q : P → Model .spherical n) (hq : PLIsometry .spherical n q)
    (p : GeodesicSphere n) (hhem : ∀ x, q x ∈ GeodesicSphere.openHemisphere p)
    (f : P → Model .spherical n) (hf : LipschitzWith 1 f)
    (hadm : StrictlyShort f ∨ ∃ c : Model .spherical n, ∀ x, dist c (f x) ≤ Real.pi / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → Model .spherical n, LipschitzWith 1 g ∧
      PLIsometry .spherical n g ∧ ∀ x, dist (g x) (f x) < ε := by
  have hsmall := spherical_smallFoldable_of_hemispherical_pl_folding hP q hq p hhem
  rcases hadm with ⟨K, hK, hLip⟩ | ⟨c, hc⟩
  · exact spherical_strict_approximation_of_small_foldable hsmall f hLip hK hε
  · apply spherical_hemisphere_approximation_of_small_foldable hsmall f hf c _ hε
    intro x
    have hx := hc x
    rw [GeodesicSphere.dist_eq_arccos_inner, Real.arccos_le_pi_div_two] at hx
    exact hx

end ArchivePLGeometry
