module

public import PLGeometry.VoronoiAngularData
public import PLGeometry.AngularRefinedBaseFamily

/-! # A globally consistent assignment to the refined cone vertices -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ (n + 1) P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance voronoiConeVertexMapDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def coneVertexMap {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    (q : (A.toVoronoiAtlas.tieComplex S).Space → GeodesicSphere n)
    (o : Model κ (n + 1)) (x : P) : Model κ (n + 1) :=
  if hx : x ∈ A.tieLocus S then
    conePoint κ n o (q ((A.angularTieHomeomorph S hnet hp hsmall).symm ⟨x, hx⟩))
      (T.nearestRadius hnet x)
  else o

theorem coneVertexMap_angularTiePoint {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    (q : (A.toVoronoiAtlas.tieComplex S).Space → GeodesicSphere n)
    (o : Model κ (n + 1)) (x : (A.toVoronoiAtlas.tieComplex S).Space) :
    A.coneVertexMap S hnet hp hsmall q o (A.angularTiePoint S hnet hp hsmall x) =
      conePoint κ n o (q x) (T.nearestRadius hnet (A.angularTiePoint S hnet hp hsmall x)) := by
  have hx : A.angularTiePoint S hnet hp hsmall x ∈ A.tieLocus S :=
    (A.angularTieHomeomorph S hnet hp hsmall x).property
  rw [coneVertexMap, dif_pos hx]
  have he : (A.angularTieHomeomorph S hnet hp hsmall).symm
      ⟨A.angularTiePoint S hnet hp hsmall x, hx⟩ = x :=
    (A.angularTieHomeomorph S hnet hp hsmall).symm_apply_apply x
  rw [he]

theorem coneVertexMap_site {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    (q : (A.toVoronoiAtlas.tieComplex S).Space → GeodesicSphere n)
    (o : Model κ (n + 1)) {a : P} (ha : a ∈ S) :
    A.coneVertexMap S hnet hp hsmall q o a = o := by
  by_cases h : a ∈ A.tieLocus S
  · rw [coneVertexMap, dif_pos h, T.nearestRadius_site hnet hp ha, conePoint_zero]
  · rw [coneVertexMap, dif_neg h]

theorem coneVertexMap_angular_dist_pole {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    (q : (A.toVoronoiAtlas.tieComplex S).Space → GeodesicSphere n)
    (o : Model κ (n + 1)) (x : (A.toVoronoiAtlas.tieComplex S).Space) :
    dist (A.coneVertexMap S hnet hp hsmall q o (A.angularTiePoint S hnet hp hsmall x)) o =
      T.nearestRadius hnet (A.angularTiePoint S hnet hp hsmall x) := by
  rw [A.coneVertexMap_angularTiePoint S hnet hp hsmall q o x]
  exact conePoint_dist_pole κ o (q x) (T.nearestRadius_nonneg hnet _) fun h =>
    ((T.nearestRadius_lt hnet _).trans (hsmall h)).le

theorem coneVertexMap_angular_cell_metric {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2)
    (hsmall : κ = .spherical → η < Real.pi)
    (U : FiniteChartedComplex .spherical n (A.toVoronoiAtlas.tieComplex S).Space)
    (hU : U.Refines (A.angularData S hnet hp hη).toChartedComplex)
    (q : (A.toVoronoiAtlas.tieComplex S).Space → GeodesicSphere n)
    (hq : ∀ V ∈ U.simplices, ∀ x ∈ U.cell V, ∀ y ∈ U.cell V,
      dist (q x) (q y) = dist (U.chart V x) (U.chart V y))
    (o : Model κ (n + 1)) {V : Finset (A.toVoronoiAtlas.tieComplex S).Space}
    (hV : V ∈ U.simplices) {x y : (A.toVoronoiAtlas.tieComplex S).Space}
    (hx : x ∈ U.cell V) (hy : y ∈ U.cell V)
    {τ : Finset P} (hτ : τ ∈ T.simplices)
    (hxτ : A.angularTiePoint S hnet hp hsmall x ∈ T.cell τ)
    (hyτ : A.angularTiePoint S hnet hp hsmall y ∈ T.cell τ) :
    dist (A.coneVertexMap S hnet hp hsmall q o (A.angularTiePoint S hnet hp hsmall x))
      (A.coneVertexMap S hnet hp hsmall q o (A.angularTiePoint S hnet hp hsmall y)) =
      dist (T.chart τ (A.angularTiePoint S hnet hp hsmall x))
        (T.chart τ (A.angularTiePoint S hnet hp hsmall y)) := by
  let D := A.angularData S hnet hp hη
  obtain ⟨W, hW, hc, hm⟩ := hU.cell V hV
  let σ := (A.toVoronoiAtlas.tieComplex S).labels W
  have hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces := D.labels_mem hW
  have hxσ : x.val ∈ Barycentric.weightsOn σ := hc hx
  have hyσ : y.val ∈ Barycentric.weightsOn σ := hc hy
  have hangle : dist (q x) (q y) =
      dist (Barycentric.chartPoint (D.vertex σ) x.val)
        (Barycentric.chartPoint (D.vertex σ) y.val) :=
    (hq V hV x hx y hy).trans (hm x hx y hy)
  rw [A.coneVertexMap_angularTiePoint S hnet hp hsmall q o x,
    A.coneVertexMap_angularTiePoint S hnet hp hsmall q o y]
  refine (A.cone_metric_of_angularTiePoint S hnet hp hη hsmall hσ x y hxσ hyσ o
    (q x) (q y) hangle).trans ?_
  exact T.metric_coherence _ (A.toVoronoiAtlas.tieFaceIndex S σ hσ).val.1.property τ hτ
    _ ⟨A.tieCell_subset_old S hσ
      ((A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ x).mpr hxσ), hxτ⟩
    _ ⟨A.tieCell_subset_old S hσ
      ((A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ y).mpr hyσ), hyτ⟩

end ArchivePLGeometry.ProjectiveVoronoiAtlas
