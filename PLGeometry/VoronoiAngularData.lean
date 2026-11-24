module

public import PLGeometry.AngularTieDirections
public import PLGeometry.VoronoiRadius

/-! # Uniform angular data and cone metric identities in all three geometries -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ (n + 1) P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance voronoiAngularDataDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance voronoiAngularDataEDecidableEq : DecidableEq E := Classical.decEq E

def angularData {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2) :
    Barycentric.SphericalData (A.toVoronoiAtlas.tieComplex S) n := by
  cases κ with
  | euclidean => exact A.euclideanAngularData S hnet hp
  | spherical => exact A.sphericalAngularData S hnet hp hη
  | hyperbolic => exact A.hyperbolicAngularData S hnet hp

theorem angularTiePoint_direction {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2)
    {hsmall : κ = .spherical → η < Real.pi}
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ)
    (h0 : 0 < dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x)))
    (hπ : κ = .spherical →
      dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
        (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x)) < Real.pi) :
    coneDirection κ n
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x)) h0 hπ =
        Barycentric.chartPoint ((A.angularData S hnet hp hη).vertex σ) x.val := by
  cases κ with
  | euclidean => exact A.euclidean_angularTiePoint_direction S hnet hp hσ x hx h0
  | spherical => exact A.spherical_angularTiePoint_direction S hnet hp hη hσ x hx h0 (hπ rfl)
  | hyperbolic => exact A.hyperbolic_angularTiePoint_direction S hnet hp hσ x hx h0

theorem nearestRadius_angularTiePoint {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ) :
    T.nearestRadius hnet (A.angularTiePoint S hnet hp hsmall x) =
      dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
        (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x)) := by
  have hpoint := (A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ x).mpr hx
  have h := T.nearestRadius_eq hnet hp (A.toVoronoiAtlas.tieFaceIndex S σ hσ).val.1.property
    (A.tieCell_subset_voronoiPieces S hσ hpoint).1
  simpa only [VoronoiAtlas.tieChart, VoronoiAtlas.tieCenter, dist_comm] using h

theorem angularTiePoint_not_mem_sites {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) : A.angularTiePoint S hnet hp hsmall x ∉ S := by
  obtain ⟨σ, hσ, hx⟩ := Set.mem_iUnion₂.mp x.property
  intro hs
  have hp0 := A.tieCell_radius_pos S hσ
    ((A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ x).mpr hx)
  rw [← A.nearestRadius_angularTiePoint S hnet hp hsmall hσ x hx,
    T.nearestRadius_site hnet hp hs] at hp0
  exact lt_irrefl _ hp0

/-- An isometry of an angular simplex preserves all cone vertex distances
when the common nearest-site radii are retained. -/
theorem cone_metric_of_angularTiePoint {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2)
    (hsmall : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x y : (A.toVoronoiAtlas.tieComplex S).Space)
    (hx : x.val ∈ Barycentric.weightsOn σ) (hy : y.val ∈ Barycentric.weightsOn σ)
    (o : Model κ (n + 1)) (u v : GeodesicSphere n)
    (hangle : dist u v =
      dist (Barycentric.chartPoint ((A.angularData S hnet hp hη).vertex σ) x.val)
        (Barycentric.chartPoint ((A.angularData S hnet hp hη).vertex σ) y.val)) :
    dist (conePoint κ n o u (T.nearestRadius hnet (A.angularTiePoint S hnet hp hsmall x)))
      (conePoint κ n o v (T.nearestRadius hnet (A.angularTiePoint S hnet hp hsmall y))) =
      dist (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x))
        (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall y)) := by
  have hxC := (A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ x).mpr hx
  have hyC := (A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ y).mpr hy
  have hx0 := A.tieCell_radius_pos S hσ hxC
  have hy0 := A.tieCell_radius_pos S hσ hyC
  have hxπ : κ = .spherical →
      dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
        (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x)) < Real.pi :=
    fun h => (A.tieCell_radius_lt S hnet hσ hxC).trans (hsmall h)
  have hyπ : κ = .spherical →
      dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
        (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall y)) < Real.pi :=
    fun h => (A.tieCell_radius_lt S hnet hσ hyC).trans (hsmall h)
  rw [A.nearestRadius_angularTiePoint S hnet hp hsmall hσ x hx,
    A.nearestRadius_angularTiePoint S hnet hp hsmall hσ y hy]
  apply conePoint_dist_of_directions κ _ o _ _ hx0 hy0 hxπ hyπ u v
  rw [A.angularTiePoint_direction S hnet hp hη hσ x hx hx0 hxπ,
    A.angularTiePoint_direction S hnet hp hη hσ y hy hy0 hyπ]
  exact hangle

end ArchivePLGeometry.ProjectiveVoronoiAtlas
