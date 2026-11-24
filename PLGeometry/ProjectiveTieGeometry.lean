module

public import PLGeometry.ProjectiveVoronoiAtlas
public import PLGeometry.ProtectedVoronoiTieComplex

/-!
# Geometry of the triangulated tie bases

Every base simplex lies in one old chart and in the bisector of two
distinct sites. Its radii and edge lengths agree in all incident charts.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.VoronoiAtlas

universe u v

local instance projectiveTieGeometryDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : VoronoiAtlas T E) (S : Finset P)

local instance projectiveTieGeometryEDecidableEq : DecidableEq E := Classical.decEq E

def tieChart {σ : Finset (A.TieVertex S)} (hσ : σ ∈ (A.tieComplex S).faces) :
    P → Model κ n := T.chart (A.tieFaceIndex S σ hσ).val.1.val

def tieCenter {σ : Finset (A.TieVertex S)} (hσ : σ ∈ (A.tieComplex S).faces) : P :=
  (A.tieFaceIndex S σ hσ).val.2.1.val

def tieOtherCenter {σ : Finset (A.TieVertex S)} (hσ : σ ∈ (A.tieComplex S).faces) : P :=
  (A.tieFaceIndex S σ hσ).val.2.2.val

theorem tie_centers_distinct {σ : Finset (A.TieVertex S)}
    (hσ : σ ∈ (A.tieComplex S).faces) :
    A.tieChart S hσ (A.tieCenter S hσ) ≠ A.tieChart S hσ (A.tieOtherCenter S hσ) := by
  let i := A.tieFaceIndex S σ hσ
  intro he
  exact i.property.1 (T.chart_injectiveOn i.val.1.val i.val.1.property
    i.property.2.1 i.property.2.2 he)

theorem tie_vertex_bisector {σ : Finset (A.TieVertex S)}
    (hσ : σ ∈ (A.tieComplex S).faces) {v : A.TieVertex S} (hv : v ∈ σ) :
    dist (A.tieChart S hσ (A.tieCenter S hσ)) (A.tieChart S hσ (A.tieSource S v)) =
      dist (A.tieChart S hσ (A.tieOtherCenter S hσ)) (A.tieChart S hσ (A.tieSource S v)) := by
  obtain ⟨ha, hb⟩ := A.tieFace_source_mem S hσ hv
  simpa only [tieChart, tieCenter, tieOtherCenter, dist_comm] using T.voronoiPiece_tie ha hb

theorem tie_vertex_radius_pos {σ : Finset (A.TieVertex S)}
    (hσ : σ ∈ (A.tieComplex S).faces) {v : A.TieVertex S} (hv : v ∈ σ) :
    0 < dist (A.tieChart S hσ (A.tieCenter S hσ)) (A.tieChart S hσ (A.tieSource S v)) := by
  have htri := dist_triangle (A.tieChart S hσ (A.tieCenter S hσ))
    (A.tieChart S hσ (A.tieSource S v)) (A.tieChart S hσ (A.tieOtherCenter S hσ))
  have hbis := A.tie_vertex_bisector S hσ hv
  rw [dist_comm (A.tieChart S hσ (A.tieSource S v))] at htri
  rw [← hbis] at htri
  have hpos := dist_pos.mpr (A.tie_centers_distinct S hσ)
  linarith

theorem tie_vertex_radius_lt {η : ℝ} (hnet : T.IsCellwiseNet S η)
    {σ : Finset (A.TieVertex S)} (hσ : σ ∈ (A.tieComplex S).faces)
    {v : A.TieVertex S} (hv : v ∈ σ) :
    dist (A.tieChart S hσ (A.tieCenter S hσ)) (A.tieChart S hσ (A.tieSource S v)) < η := by
  have h := T.voronoiPiece_radius_lt hnet (A.tieFaceIndex S σ hσ).val.1.property
    (A.tieFace_source_mem S hσ hv).1
  simpa only [tieChart, tieCenter, dist_comm] using h

theorem tie_vertex_radius_eq {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S)
    {σ τ : Finset (A.TieVertex S)} (hσ : σ ∈ (A.tieComplex S).faces)
    (hτ : τ ∈ (A.tieComplex S).faces) {v : A.TieVertex S} (hv : v ∈ σ ∩ τ) :
    dist (A.tieChart S hσ (A.tieCenter S hσ)) (A.tieChart S hσ (A.tieSource S v)) =
      dist (A.tieChart S hτ (A.tieCenter S hτ)) (A.tieChart S hτ (A.tieSource S v)) := by
  let i := A.tieFaceIndex S σ hσ
  let j := A.tieFaceIndex S τ hτ
  have hvi := (A.tieFace_source_mem S hσ (Finset.mem_inter.mp hv).1).1
  have hvj := (A.tieFace_source_mem S hτ (Finset.mem_inter.mp hv).2).1
  have hb := (T.nearestInCell_iff hnet hp i.val.1.property j.val.1.property
    ⟨hvi.1, hvj.1⟩).mpr hvj.2
  have heq := le_antisymm (hvi.2.2 j.val.2.1.val hb.1) (hb.2 i.val.2.1.val hvi.2.1)
  change dist (T.chart i.val.1.val i.val.2.1.val) (T.chart i.val.1.val (A.tieSource S v)) =
    dist (T.chart j.val.1.val j.val.2.1.val) (T.chart j.val.1.val (A.tieSource S v))
  calc
    _ = dist (T.chart i.val.1.val (A.tieSource S v)) (T.chart i.val.1.val i.val.2.1.val) := dist_comm _ _
    _ = dist (T.chart i.val.1.val (A.tieSource S v)) (T.chart i.val.1.val j.val.2.1.val) := heq
    _ = dist (T.chart j.val.1.val (A.tieSource S v)) (T.chart j.val.1.val j.val.2.1.val) :=
      T.metric_coherence i.val.1.val i.val.1.property j.val.1.val j.val.1.property
        (A.tieSource S v) ⟨hvi.1, hvj.1⟩ j.val.2.1.val ⟨hb.1.2, hvj.2.1.2⟩
    _ = _ := dist_comm _ _

theorem tie_edge_distance_eq
    {σ τ : Finset (A.TieVertex S)} (hσ : σ ∈ (A.tieComplex S).faces)
    (hτ : τ ∈ (A.tieComplex S).faces) {v w : A.TieVertex S}
    (hv : v ∈ σ ∩ τ) (hw : w ∈ σ ∩ τ) :
    dist (A.tieChart S hσ (A.tieSource S v)) (A.tieChart S hσ (A.tieSource S w)) =
      dist (A.tieChart S hτ (A.tieSource S v)) (A.tieChart S hτ (A.tieSource S w)) := by
  exact T.metric_coherence _ (A.tieFaceIndex S σ hσ).val.1.property
    _ (A.tieFaceIndex S τ hτ).val.1.property _
    ⟨(A.tieFace_source_mem S hσ (Finset.mem_inter.mp hv).1).1.1,
      (A.tieFace_source_mem S hτ (Finset.mem_inter.mp hv).2).1.1⟩ _
    ⟨(A.tieFace_source_mem S hσ (Finset.mem_inter.mp hw).1).1.1,
      (A.tieFace_source_mem S hτ (Finset.mem_inter.mp hw).2).1.1⟩

end ArchivePLGeometry.VoronoiAtlas

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v

local instance projectiveTieSimplexDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance projectiveTieSimplexEDecidableEq : DecidableEq E := Classical.decEq E

theorem tieFace_simplex {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    simplexVertices κ n ((A.toVoronoiAtlas.tieSourceFace S σ).image
      (A.toVoronoiAtlas.tieChart S hσ)) := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  apply A.simplex_transfer i.val.1.val i.val.1.property
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (B.tieFace_source_mem S hσ hv).1.1
  · have he : (B.tieSourceFace S σ).image A.coord = B.tieCoordinateFace S σ := by
      ext z
      simp only [VoronoiAtlas.tieSourceFace, Finset.mem_image,
        VoronoiAtlas.tieCoordinateFace]
      constructor
      · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, (B.coord_tieSource S v).symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨B.tieSource S v, ⟨v, hv, rfl⟩, B.coord_tieSource S v⟩
    rw [he]
    exact Pulling.family_face_independent (B.tiePiece S) (B.tiePiece_polytope S) hσ

end ArchivePLGeometry.ProjectiveVoronoiAtlas
