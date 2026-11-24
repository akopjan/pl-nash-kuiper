module

public import PLGeometry.ProtectedVoronoi
public import BrehmApprox.AffineArrangement
public import BrehmApprox.PolytopeVertices
public import BrehmApprox.PullingPolytopeFamily

/-!
# Protected Voronoi cells in barycentric coordinates

A projective barycentric atlas turns distance comparisons in each constant
curvature simplex into affine halfspaces. Protected nearest sites then give
a finite face-to-face polytope family in one common coordinate space.
-/

@[expose] public section
noncomputable section

open Set Classical

namespace ArchivePLGeometry

open BrehmApprox

universe u v

local instance protectedVoronoiPolytopeDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The properties of canonical barycentric coordinates used by the Voronoi construction. -/
structure VoronoiAtlas where
  coord : P → E
  injective : Function.Injective coord
  continuous : Continuous coord
  cell_polytope : ∀ σ ∈ T.simplices, IsFinitePolytope (coord '' T.cell σ)
  face_extreme : ∀ σ ∈ T.simplices, ∀ τ ∈ T.simplices,
    _root_.IsExtreme ℝ (coord '' T.cell σ) (coord '' T.cell σ ∩ coord '' T.cell τ)
  distanceCut : ∀ σ ∈ T.simplices, ∀ a ∈ T.cell σ, ∀ b ∈ T.cell σ,
    ∃ ℓ : E →ₗ[ℝ] ℝ, ∃ c : ℝ, ∀ x ∈ T.cell σ,
      (dist (T.chart σ x) (T.chart σ a) ≤ dist (T.chart σ x) (T.chart σ b) ↔ ℓ (coord x) ≤ c) ∧
      (dist (T.chart σ x) (T.chart σ a) = dist (T.chart σ x) (T.chart σ b) ↔ ℓ (coord x) = c)

namespace VoronoiAtlas

variable {T E} (A : VoronoiAtlas T E)

/-- A Voronoi piece is an actual finite polytope in the common coordinates. -/
theorem voronoiPiece_polytope (S : Finset P) {σ : Finset P} (hσ : σ ∈ T.simplices) (a : P) :
    IsFinitePolytope (A.coord '' T.voronoiPiece S σ a) := by
  by_cases ha : a ∈ (S : Set P) ∩ T.cell σ
  · choose L c hc using fun b : T.cellSites S σ =>
      A.distanceCut σ hσ a ha.2 b.val (T.mem_cellSites.mp b.property).2
    have he : A.coord '' T.voronoiPiece S σ a =
        affineWeakCell (A.coord '' T.cell σ) L c (fun _ => .negative) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
        intro b
        exact (hc b x hx.1).1.mp (hx.2.2 b.val (T.mem_cellSites.mp b.property))
      · rintro ⟨⟨x, hx, rfl⟩, hz⟩
        refine ⟨x, ⟨hx, ha, ?_⟩, rfl⟩
        intro b hb
        exact (hc ⟨b, T.mem_cellSites.mpr hb⟩ x hx).1.mpr (hz ⟨b, T.mem_cellSites.mpr hb⟩)
    rw [he]
    obtain ⟨V, hV⟩ := A.cell_polytope σ hσ
    rw [hV]
    exact exists_finset_affineWeakCell V L c (fun _ => .negative)
  · refine ⟨∅, ?_⟩
    rw [Finset.coe_empty, convexHull_empty]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨x, hx, rfl⟩
    exact ha hx.2.1

/-- Protection makes all intersections of Voronoi pieces genuine faces. -/
theorem voronoiPiece_face_inter {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (hprotected : T.IsCellwiseProtected S)
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices) (a b : P) :
    _root_.IsExtreme ℝ (A.coord '' T.voronoiPiece S σ a)
      (A.coord '' T.voronoiPiece S σ a ∩ A.coord '' T.voronoiPiece S τ b) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨px, hpx, rfl⟩ := hx
  obtain ⟨py, hpy, rfl⟩ := hy
  obtain ⟨pz, hpza, rfl⟩ := hz.1
  obtain ⟨qz, hqzb, hqz⟩ := hz.2
  have hqzpz := A.injective hqz
  have hpzb : pz ∈ T.voronoiPiece S τ b := Eq.mp
    (congrArg (fun q : P => q ∈ T.voronoiPiece S τ b) hqzpz) hqzb
  have hpz : pz ∈ T.cell σ ∩ T.cell τ := ⟨hpza.1, hpzb.1⟩
  have hbσ : b ∈ T.cell σ := hprotected τ hτ σ hσ pz ⟨hpz.2, hpz.1⟩ b hpzb.2
  have hbase := (A.face_extreme σ hσ τ hτ).left_mem_of_mem_openSegment
    (show A.coord px ∈ A.coord '' T.cell σ from ⟨px, hpx.1, rfl⟩)
    (show A.coord py ∈ A.coord '' T.cell σ from ⟨py, hpy.1, rfl⟩)
    (show A.coord pz ∈ A.coord '' T.cell σ ∩ A.coord '' T.cell τ from
      ⟨⟨pz, hpz.1, rfl⟩, ⟨pz, hpz.2, rfl⟩⟩) hseg
  obtain ⟨qx, hqxτ, hqx⟩ := hbase.2
  have hqxp := A.injective hqx
  have hpxτ : px ∈ T.cell τ := Eq.mp (congrArg (fun q : P => q ∈ T.cell τ) hqxp) hqxτ
  obtain ⟨ℓ, c, hcut⟩ := A.distanceCut σ hσ a hpx.2.1.2 b hbσ
  have hxle : ℓ (A.coord px) ≤ c :=
    (hcut px hpx.1).1.mp (hpx.2.2 b ⟨hpzb.2.1.1, hbσ⟩)
  have hyle : ℓ (A.coord py) ≤ c :=
    (hcut py hpy.1).1.mp (hpy.2.2 b ⟨hpzb.2.1.1, hbσ⟩)
  have hpzbσ : T.IsNearestInCell S σ pz b :=
    (T.nearestInCell_iff hnet hprotected hσ hτ hpz).mpr hpzb.2
  have hzeq : ℓ (A.coord pz) = c := (hcut pz hpz.1).2.mp
    (le_antisymm (hpza.2.2 b hpzbσ.1) (hpzbσ.2 a hpza.2.1))
  have hxeq : ℓ (A.coord px) = c := by
    obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
    have hh := congrArg ℓ he
    simp only [map_add, map_smul, smul_eq_mul] at hh
    rw [hzeq] at hh
    apply le_antisymm hxle
    by_contra h
    have hlt := mul_pos hr (sub_pos.mpr (lt_of_not_ge h))
    have hnon := mul_nonneg hs.le (sub_nonneg.mpr hyle)
    have hsum := congrArg (fun t : ℝ => t * c) hrs
    nlinarith [hsum]
  have hdist : dist (T.chart σ px) (T.chart σ a) = dist (T.chart σ px) (T.chart σ b) :=
    (hcut px hpx.1).2.mpr hxeq
  have hbpx : T.IsNearestInCell S σ px b := by
    refine ⟨⟨hpzb.2.1.1, hbσ⟩, ?_⟩
    intro q hq
    change dist (T.chart σ px) (T.chart σ b) ≤ dist (T.chart σ px) (T.chart σ q)
    rw [← hdist]
    exact hpx.2.2 q hq
  refine ⟨⟨px, hpx, rfl⟩, px, ?_, rfl⟩
  exact ⟨hpxτ, (T.nearestInCell_iff hnet hprotected hσ hτ ⟨hpx.1, hpxτ⟩).mp hbpx⟩

/-- Finite indexing of all old-cell/site pairs. Empty pieces are retained. -/
abbrev PieceIndex (S : Finset P) := T.simplices × S

instance pieceIndexFinite (S : Finset P) : Finite (PieceIndex (T := T) S) := by
  let : Finite T.simplices := T.finite_simplices.to_subtype
  infer_instance

def piece (S : Finset P) (i : PieceIndex (T := T) S) : Set E :=
  A.coord '' T.voronoiPiece S i.1.val i.2.val

theorem piece_polytope (S : Finset P) (i : PieceIndex (T := T) S) : IsFinitePolytope (A.piece S i) :=
  A.voronoiPiece_polytope S i.1.property i.2.val

theorem piece_face_inter {S : Finset P} {η : ℝ}
    (hnet : T.IsCellwiseNet S η) (hprotected : T.IsCellwiseProtected S)
    (i j : PieceIndex (T := T) S) : _root_.IsExtreme ℝ (A.piece S i) (A.piece S i ∩ A.piece S j) :=
  A.voronoiPiece_face_inter hnet hprotected i.1.property j.1.property i.2.val j.2.val

theorem piece_cover {S : Finset P} {η : ℝ} (hnet : T.IsCellwiseNet S η) :
    (⋃ i, A.piece S i) = Set.range A.coord := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_range_self x
  · rintro ⟨x, rfl⟩
    obtain ⟨σ, hσ, hxσ⟩ := T.cover x
    obtain ⟨a, ha⟩ := T.exists_nearestInCell hnet hσ hxσ
    exact Set.mem_iUnion.mpr ⟨(⟨σ, hσ⟩, ⟨a, ha.1.1⟩), x, ⟨hxσ, ha⟩, rfl⟩

end VoronoiAtlas

end ArchivePLGeometry
