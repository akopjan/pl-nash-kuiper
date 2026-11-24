module

public import BrehmApprox.FoldedGeometry

/-!+# Transporting actual folded geometry through a chart

The face poset, source cells, and incidence are preserved. Model cores are the
actual chart images. Injectivity on each coface proves the required intersection
identities. A supplied chain metric with the actual chart distances on cells
then gives a new folded geometry on the same underlying source type.
-/

@[expose] public section

namespace BrehmApprox

universe u v w

variable {X : Type u} [MetricSpace X] {E : Type v} [MetricSpace E]
variable {GoodX : (X → X) → Prop} {GoodE : (E → E) → Prop}
variable {MX : PolytopeModel X GoodX} {ME : PolytopeModel E GoodE} {N : ℕ}

namespace PolyhedralFaceData

variable (D : PolyhedralFaceData MX N)

/-- Actual chart transport of a finite model face system. Only injectivity on
one coface at a time is needed; disjoint folded sheets may overlap. -/
def mapChart (Φ : X → E) (hpoly : ∀ i, ME.Polytope (Φ '' D.core i))
    (hinj : ∀ i, Set.InjOn Φ (D.core i)) : PolyhedralFaceData ME N where
  faceLE := D.faceLE
  le_refl := D.le_refl
  le_trans := D.le_trans
  index_strict := D.index_strict
  meet := D.meet
  meet_comm := D.meet_comm
  meet_le_left := D.meet_le_left
  meet_le_right := D.meet_le_right
  core := fun i => Φ '' D.core i
  polytope_core := hpoly
  core_mono := fun i j hij => Set.image_mono (D.core_mono i j hij)
  core_inter := by
    intro i j k hji hki
    rw [← D.core_inter i j k hji hki]
    apply Set.Subset.antisymm
    · rintro z ⟨⟨x, hx, hΦx⟩, ⟨y, hy, hΦy⟩⟩
      have hxy : x = y := hinj i (D.core_mono j i hji hx) (D.core_mono k i hki hy)
        (hΦx.trans hΦy.symm)
      exact ⟨x, ⟨hx, hxy.symm ▸ hy⟩, hΦx⟩
    · rintro z ⟨x, hx, hΦx⟩
      exact ⟨⟨x, hx.1, hΦx⟩, ⟨x, hx.2, hΦx⟩⟩

lemma mapChart_core (Φ : X → E) (hpoly : ∀ i, ME.Polytope (Φ '' D.core i))
    (hinj : ∀ i, Set.InjOn Φ (D.core i)) (i : Fin N) :
    (D.mapChart Φ hpoly hinj).core i = Φ '' D.core i := rfl

lemma mapChart_faceLE (Φ : X → E) (hpoly : ∀ i, ME.Polytope (Φ '' D.core i))
    (hinj : ∀ i, Set.InjOn Φ (D.core i)) (i j : Fin N) :
    (D.mapChart Φ hpoly hinj).faceLE i j ↔ D.faceLE i j := Iff.rfl

end PolyhedralFaceData

namespace FoldedGeometry

variable {P : Type w} [mP : MetricSpace P] (G : FoldedGeometry (P := P) MX N)

/-- The same source transport with independently constructed model face data.
This form preserves their definitional identity, so their proved simplex
structure can be used directly. -/
def rechartWithData (D : PolyhedralFaceData ME N) (Φ : X → E)
    (hface : ∀ i j, D.faceLE i j ↔ G.faceLE i j)
    (hmeet : ∀ i j, D.meet i j = G.meet i j)
    (hcore : ∀ i, D.core i = Φ '' G.core i) (m : MetricSpace P)
    (hcell : letI : MetricSpace P := mP
      ∀ i, ∀ x ∈ G.cell i, ∀ y ∈ G.cell i,
      dist (Φ (G.fold x)) (Φ (G.fold y)) =
        (letI : MetricSpace P := m; dist x y))
    (hchain : letI : MetricSpace P := mP
      @ChainGenerated P m (Fin N) G.cell) :
    @FoldedGeometry E _ P m GoodE ME N := by
  letI : MetricSpace P := mP
  refine @FoldedGeometry.mk E _ P m GoodE ME N D G.cell G.cover
    (fun x => Φ (G.fold x)) ?_ hcell ?_ ?_ hchain
  · intro i
    rw [hcore i, ← Set.image_image, G.image_cell i]
  · exact fun i j hij => G.cell_mono i j ((hface i j).mp hij)
  · intro i j
    rw [hmeet i j]
    exact G.intersection i j


/-- Change the source metric only after the chart-cell distance equalities and
intrinsic chain property have been established. -/
def rechart (Φ : X → E) (hpoly : ∀ i, ME.Polytope (Φ '' G.core i))
    (hinj : ∀ i, Set.InjOn Φ (G.core i)) (m : MetricSpace P)
    (hcell : letI : MetricSpace P := mP
      ∀ i, ∀ x ∈ G.cell i, ∀ y ∈ G.cell i,
      dist (Φ (G.fold x)) (Φ (G.fold y)) =
        (letI : MetricSpace P := m; dist x y))
    (hchain : letI : MetricSpace P := mP
      @ChainGenerated P m (Fin N) G.cell) :
    @FoldedGeometry E _ P m GoodE ME N := by
  letI : MetricSpace P := mP
  exact G.rechartWithData (G.toPolyhedralFaceData.mapChart Φ hpoly hinj) Φ
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ => rfl) m hcell hchain

end FoldedGeometry
end BrehmApprox
