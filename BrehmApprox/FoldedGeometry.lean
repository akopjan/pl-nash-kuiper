module

public import BrehmApprox.IntrinsicChains
public import BrehmApprox.CellwiseLifting

/-!
# Folded source geometry independent of reference maps

The reference atlas is an output of the geometric preparation, not an input to
the definition of a polyhedral face system.  This file separates these data.
The structures in this module contain an initial folding. Its existence for
every finite intrinsic polyhedral source is proved separately in
`ArchivePLGeometry.FiniteFoldingExistence` and supplied by the final approximation
theorems.
-/

@[expose] public section

namespace BrehmApprox

universe u v
variable {X : Type u} [MetricSpace X]
variable {P : Type v} [MetricSpace P]
variable {Good : (X → X) → Prop} (M : PolytopeModel X Good) (N : ℕ)

namespace FoldedSource

variable {M N} {L : ℝ} {D : ReferenceAtlas M N L} (S : FoldedSource D P)

theorem compact_cell (i : Fin N) : IsCompact (S.cell i) := by
  let : CompactSpace (D.core i) :=
    isCompact_iff_compactSpace.mp (M.compact _ (D.polytope_core i))
  exact isCompact_iff_compactSpace.mpr (S.cellChart i).symm.toHomeomorph.compactSpace

theorem closed_cell (i : Fin N) : IsClosed (S.cell i) := (S.compact_cell i).isClosed

include S in
theorem compactSpace : CompactSpace P := by
  have hc : IsCompact (⋃ i, S.cell i) := isCompact_iUnion S.compact_cell
  have hu : (⋃ i, S.cell i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact S.cover x
  exact isCompact_univ_iff.mp (hu ▸ hc)

end FoldedSource

/-- A finite face system in one model. Only cofacial intersections are required
to have the expected image: unrelated sheets of a folding may overlap. -/
structure PolyhedralFaceData where
  faceLE : Fin N → Fin N → Prop
  le_refl : ∀ i, faceLE i i
  le_trans : ∀ i j k, faceLE i j → faceLE j k → faceLE i k
  index_strict : ∀ i j, faceLE i j → i ≠ j → i.val < j.val
  meet : Fin N → Fin N → Fin N
  meet_comm : ∀ i j, meet i j = meet j i
  meet_le_left : ∀ i j, faceLE (meet i j) i
  meet_le_right : ∀ i j, faceLE (meet i j) j
  core : Fin N → Set X
  polytope_core : ∀ i, M.Polytope (core i)
  core_mono : ∀ i j, faceLE i j → core i ⊆ core j
  core_inter : ∀ i j k, faceLE j i → faceLE k i → core j ∩ core k = core (meet j k)

/-- The actual folded source and its intrinsic chain metric.  No reference
map, strict contraction, approximation, or Brehm output occurs in this data. -/
structure FoldedGeometry extends PolyhedralFaceData M N where
  cell : Fin N → Set P
  cover : ∀ x : P, ∃ i, x ∈ cell i
  fold : P → X
  image_cell : ∀ i, fold '' cell i = core i
  isometry_cell : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i,
    dist (fold x) (fold y) = dist x y
  cell_mono : ∀ i j, faceLE i j → cell i ⊆ cell j
  intersection : ∀ i j, cell i ∩ cell j ⊆ cell (meet i j)
  intrinsic : ChainGenerated cell

namespace PolyhedralFaceData

variable {M N} (D : PolyhedralFaceData M N)

/-- The local reference maps to be constructed by flattening. Their conditions
are separate from the geometric source data. -/
structure LocalReferences (L : ℝ) where
  reference : Fin N → X → X
  domain : Fin N → Set X
  open_domain : ∀ i, IsOpen (domain i)
  core_domain : ∀ i, D.core i ⊆ domain i
  reference_short : ∀ i, ∀ x ∈ domain i, ∀ y ∈ domain i,
    dist (reference i x) (reference i y) ≤ L * dist x y
  agreement : ∀ i j, D.faceLE i j →
    ∃ U : Set X, IsOpen U ∧ D.core i ⊆ U ∧
      ∀ x ∈ U, reference i x = reference j x

def LocalReferences.toAtlas {L : ℝ} (R : D.LocalReferences L) : ReferenceAtlas M N L where
  faceLE := D.faceLE
  le_refl := D.le_refl
  le_trans := D.le_trans
  index_strict := D.index_strict
  meet := D.meet
  meet_comm := D.meet_comm
  meet_le_left := D.meet_le_left
  meet_le_right := D.meet_le_right
  core := D.core
  polytope_core := D.polytope_core
  core_mono := D.core_mono
  core_inter := D.core_inter
  reference := R.reference
  domain := R.domain
  open_domain := R.open_domain
  core_domain := R.core_domain
  reference_short := R.reference_short
  agreement := R.agreement

/-- A harmless constant atlas allows purely geometric lifting lemmas to be
used before the nonconstant reference maps have been constructed. -/
def constantReferences (o : X) : D.LocalReferences 0 where
  reference := fun _ _ => o
  domain := fun _ => Set.univ
  open_domain := fun _ => isOpen_univ
  core_domain := fun _ => Set.subset_univ _
  reference_short := by intros; simp
  agreement := fun _ _ _ => ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun _ _ => rfl⟩

end PolyhedralFaceData

namespace FoldedGeometry

variable {M N} (G : FoldedGeometry (P := P) M N)

def withReferences {L : ℝ} (R : G.toPolyhedralFaceData.LocalReferences L) :
    FoldedSource R.toAtlas P where
  cell := G.cell
  cover := G.cover
  fold := G.fold
  image_cell := G.image_cell
  isometry_cell := G.isometry_cell
  cell_mono := G.cell_mono
  intersection := G.intersection

/-- A geometric source usable by lifting and projection lemmas before any
approximation-related reference map exists. -/
def constantSource (o : X) :
    FoldedSource (G.toPolyhedralFaceData.constantReferences o).toAtlas P :=
  G.withReferences (G.toPolyhedralFaceData.constantReferences o)

theorem compact_cell (o : X) (i : Fin N) : IsCompact (G.cell i) :=
  (G.constantSource o).compact_cell i

theorem closed_cell (o : X) (i : Fin N) : IsClosed (G.cell i) :=
  (G.compact_cell o i).isClosed

include G in
theorem compactSpace (o : X) : CompactSpace P := (G.constantSource o).compactSpace

/-- Once the independently constructed reference maps are supplied, all
collars, numerical choices, Brehm applications and final gluing are derived. -/
theorem approximate {L : ℝ} (R : G.toPolyhedralFaceData.LocalReferences L)
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (f : P → X)
    (href : ∀ i, ∀ x ∈ G.cell i, R.reference i (G.fold x) = f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → X, LipschitzWith 1 g ∧
      PolyhedralPiecewiseIsometry M G.fold g ∧ ∀ x, dist (g x) (f x) < ε :=
  (G.withReferences R).approximate_short G.intrinsic hB hL0 hL1 f href hε

end FoldedGeometry
end BrehmApprox
