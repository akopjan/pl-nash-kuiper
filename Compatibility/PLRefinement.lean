module

public import Compatibility.RefinedPL
public import PLGeometry.FoldedFaceData

/-! Any finite metric PL isometry admits a finite subdivision refining an
already folded finite source. Ambient motions on pairwise cell intersections
give a finite motion selection, to which the proved arrangement applies. -/

@[expose] public section
noncomputable section

open Set BrehmApprox ArchivePLGeometry

namespace PLGeometry.Refined

universe u

variable {P : Type u} [MetricSpace P] {n N : ℕ}

theorem euclidean_of_plIsometry
    (G : FoldedGeometry (P := P) (euclideanPolytopeModel n) N)
    (D : SimplicialFaceData G.toPolyhedralFaceData)
    {g : P → EuclideanSpace ℝ (Fin n)}
    (hg : ArchivePLGeometry.PLIsometry .euclidean n g) :
    FinitePLRefinement .euclidean n G.cell g := by
  classical
  letI : CompactSpace P := G.compactSpace 0
  obtain ⟨V, hV, hgV⟩ := hg.exists_finite_triangulation
  letI : Finite V.simplices := hV.to_subtype
  let J := Fin N × V.simplices
  have hex (j : J) : ∃ r : E n ≃ᵃⁱ[ℝ] E n,
      ∀ x ∈ G.cell j.1 ∩ V.cell j.2.val, r (G.fold x) = g x := by
    let A := G.cell j.1 ∩ V.cell j.2.val
    obtain ⟨r, hr⟩ := SetRigidity.euclidean_motion
      (fun x : A => G.fold x.val) (fun x : A => g x.val) (by
        intro x y
        rw [G.isometry_cell j.1 x.val x.property.1 y.val y.property.1,
          hgV j.2.val j.2.property x.val x.property.2 y.val y.property.2])
    exact ⟨r, fun x hx => hr ⟨x, hx⟩⟩
  choose r hr using hex
  apply euclidean_of_motion_selection (G.euclideanPolytopeCover D)
    (G.compact_cell 0) ((G.constantSource 0).fold_lipschitz G.intrinsic).continuous
    G.isometry_cell r hg.1
  intro x
  obtain ⟨i, hi⟩ := G.cover x
  obtain ⟨σ, hσ, hx⟩ := V.cover x
  exact ⟨(i, ⟨σ, hσ⟩), (hr (i, ⟨σ, hσ⟩) x ⟨hi, hx⟩).symm⟩

theorem hyperbolic_of_plIsometry
    (G : FoldedGeometry (P := P) (hyperbolicPolytopeModel n) N)
    (D : HyperbolicSimplicialFaceData G.toPolyhedralFaceData)
    {g : P → HyperbolicSpace n}
    (hg : ArchivePLGeometry.PLIsometry .hyperbolic n g) :
    FinitePLRefinement .hyperbolic n G.cell g := by
  classical
  letI : CompactSpace P := G.compactSpace ⟨0⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_finite_triangulation
  letI : Finite V.simplices := hV.to_subtype
  let J := Fin N × V.simplices
  have hex (j : J) : ∃ r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n,
      ∀ x ∈ G.cell j.1 ∩ V.cell j.2.val, r (G.fold x) = g x := by
    let A := G.cell j.1 ∩ V.cell j.2.val
    obtain ⟨r, hr⟩ := SetRigidity.hyperbolic_motion
      (fun x : A => G.fold x.val) (fun x : A => g x.val) (by
        intro x y
        rw [G.isometry_cell j.1 x.val x.property.1 y.val y.property.1,
          hgV j.2.val j.2.property x.val x.property.2 y.val y.property.2])
    exact ⟨r, fun x hx => hr ⟨x, hx⟩⟩
  choose r hr using hex
  have hlinear := fun j : J => HyperbolicSpace.exists_lorentz_linear_lift (r j)
  choose L hL using hlinear
  apply hyperbolic_of_motion_selection (G.kleinPolytopeCover D)
    (G.compact_cell ⟨0⟩) ((G.constantSource ⟨0⟩).fold_lipschitz G.intrinsic).continuous
    G.isometry_cell r L (fun j x => (hL j x).symm) hg.1
  intro x
  obtain ⟨i, hi⟩ := G.cover x
  obtain ⟨σ, hσ, hx⟩ := V.cover x
  exact ⟨(i, ⟨σ, hσ⟩), (hr (i, ⟨σ, hσ⟩) x ⟨hi, hx⟩).symm⟩

theorem spherical_of_plIsometry
    (G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N)
    (D : SphericalSimplicialFaceData G.toPolyhedralFaceData)
    (p : GeodesicSphere n) (hhem : ∀ x, G.fold x ∈ GeodesicSphere.openHemisphere p)
    {g : P → GeodesicSphere n}
    (hg : ArchivePLGeometry.PLIsometry .spherical n g) :
    FinitePLRefinement .spherical n G.cell g := by
  classical
  letI : CompactSpace P := G.compactSpace p
  obtain ⟨V, hV, hgV⟩ := hg.exists_finite_triangulation
  letI : Finite V.simplices := hV.to_subtype
  let J := Fin N × V.simplices
  have hex (j : J) : ∃ r : E (n + 1) ≃ₗᵢ[ℝ] E (n + 1),
      ∀ x ∈ G.cell j.1 ∩ V.cell j.2.val, GeodesicSphere.mapEquiv r (G.fold x) = g x := by
    let A := G.cell j.1 ∩ V.cell j.2.val
    obtain ⟨r, hr⟩ := SetRigidity.spherical_motion
      (fun x : A => G.fold x.val) (fun x : A => g x.val) (by
        intro x y
        rw [G.isometry_cell j.1 x.val x.property.1 y.val y.property.1,
          hgV j.2.val j.2.property x.val x.property.2 y.val y.property.2])
    exact ⟨r, fun x hx => hr ⟨x, hx⟩⟩
  choose r hr using hex
  have hp : ∀ i, ∀ v ∈ D.vertices i, 0 < inner ℝ p.val v.val := by
    intro i v hv
    have hvcore : v ∈ G.core i := by
      rw [D.core_eq i]
      exact mem_sphericalCell_of_mem hv
    rw [← G.image_cell i] at hvcore
    obtain ⟨x, _, rfl⟩ := hvcore
    exact hhem x
  apply spherical_of_motion_selection p hhem (G.gnomonicPolytopeCover D p hp)
    (G.compact_cell p) ((G.constantSource p).fold_lipschitz G.intrinsic).continuous
    G.isometry_cell r hg.1
  intro x
  obtain ⟨i, hi⟩ := G.cover x
  obtain ⟨σ, hσ, hx⟩ := V.cover x
  exact ⟨(i, ⟨σ, hσ⟩), (hr (i, ⟨σ, hσ⟩) x ⟨hi, hx⟩).symm⟩

theorem FinitePLRefinement.mono {I J : Type*} {κ : ArchivePLGeometry.Geometry}
    {n : ℕ} {C : I → Set P} {D : J → Set P}
    {g : P → ArchivePLGeometry.Model κ n}
    (h : FinitePLRefinement κ n C g)
    (hCD : ∀ i, ∃ j, C i ⊆ D j) : FinitePLRefinement κ n D g := by
  obtain ⟨hg, U, hU, hsub, hiso⟩ := h
  refine ⟨hg, U, hU, ?_, hiso⟩
  intro σ hσ
  obtain ⟨i, hi⟩ := hsub σ hσ
  obtain ⟨j, hj⟩ := hCD i
  exact ⟨j, hi.trans hj⟩

/-- The public PL predicate can be refined compatibly with any finite
intrinsic triangulation carrying an initial small folding. -/
theorem refinement_of_plIsometry {κ : ArchivePLGeometry.Geometry}
    (T : ArchivePLGeometry.Triangulation κ n P) (hfin : T.simplices.Finite)
    (hT : ArchivePLGeometry.Intrinsic T)
    (q : P → ArchivePLGeometry.Model κ n)
    (hq : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist x y)
    (o : ArchivePLGeometry.Model κ n) (hsmall : ∀ x, dist (q x) o < Real.pi / 2)
    {g : P → ArchivePLGeometry.Model κ n}
    (hg : ArchivePLGeometry.PLIsometry κ n g) :
    FinitePLRefinement κ n (fun σ : T.simplices => T.cell σ.val) g := by
  let e := ArchivePLGeometry.FaceEnumeration.ofFinite hfin
  cases κ with
  | euclidean =>
    let G := T.euclideanFoldedGeometry e q hq hT
    let D := T.euclideanFoldedFaceData e q hq hT
    exact (euclidean_of_plIsometry G D hg).mono (fun i => ⟨e.face i, Set.Subset.rfl⟩)
  | hyperbolic =>
    let G := T.hyperbolicFoldedGeometry e q hq hT
    let D := T.hyperbolicFoldedFaceData e q hq hT
    exact (hyperbolic_of_plIsometry G D hg).mono (fun i => ⟨e.face i, Set.Subset.rfl⟩)
  | spherical =>
    let G := T.sphericalFoldedGeometry e q hq hT
    let D := T.sphericalFoldedFaceData e q hq hT
    have hh : ∀ x, G.fold x ∈ GeodesicSphere.openHemisphere o := by
      intro x
      apply (GeodesicSphere.dist_lt_pi_div_two_iff o (q x)).mp
      simpa only [dist_comm] using hsmall x
    exact (spherical_of_plIsometry G D o hh hg).mono
      (fun i => ⟨e.face i, Set.Subset.rfl⟩)

end PLGeometry.Refined
