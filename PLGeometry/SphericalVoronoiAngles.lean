module

public import PLGeometry.ProjectiveTieGeometry
public import BrehmApprox.SphericalFoldingGeometry

/-!
# Tangent geometry of the protected spherical Voronoi ties

The angular simplex is formed in the actual tangent plane of its chosen
site. The shared-face Gram identities use only nearest radii and base
distances, hence do not depend on that choice of site or chart.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v

local instance sphericalVoronoiAnglesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex .spherical n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance sphericalVoronoiAnglesEDecidableEq : DecidableEq E := Classical.decEq E
local instance sphericalVoronoiAnglesLabelDecidableEq :
    DecidableEq (A.toVoronoiAtlas.TieVertex S) := Classical.decEq _
local instance sphericalVoronoiAnglesModelDecidableEq :
    DecidableEq (Model .spherical n) := Classical.decEq _

theorem sphericalTieBase_independent {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    LinearIndependent ℝ (fun v : σ =>
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val)).val) := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  let W := (B.tieSourceFace S σ).image (B.tieChart S hσ)
  have hW : LinearIndependent ℝ (fun x : W => x.val.val) := (A.tieFace_simplex S hσ).2
  let e : σ → W := fun v => ⟨B.tieChart S hσ (B.tieSource S v.val),
    Finset.mem_image.mpr ⟨B.tieSource S v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩, rfl⟩⟩
  have he : Function.Injective e := by
    intro v w h
    have hq := congrArg (fun z : W => z.val) h
    have hs := T.chart_injectiveOn i.val.1.val i.val.1.property
      (B.tieFace_source_mem S hσ v.property).1.1
      (B.tieFace_source_mem S hσ w.property).1.1 hq
    exact Subtype.ext (B.tieSource_injective S hs)
  exact hW.comp e he

theorem sphericalTie_radius_lt_halfPi {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : η ≤ Real.pi / 2)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ) :
    dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v)) < Real.pi / 2 :=
  (A.toVoronoiAtlas.tie_vertex_radius_lt S hnet hσ hv).trans_le hη

theorem sphericalTie_radius_lt_pi {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : η ≤ Real.pi / 2)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ) :
    dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v)) < Real.pi := by
  have hh := A.sphericalTie_radius_lt_halfPi S hnet hη hσ hv
  linarith [Real.pi_pos]

def sphericalTieDirection {η : ℝ} (hnet : T.IsCellwiseNet S η) (hη : η ≤ Real.pi / 2)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (v : σ) : GeodesicSphere.tangentPlane
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ)) :=
  GeodesicSphere.radialDirection
    (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
    (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val))
    (A.toVoronoiAtlas.tie_vertex_radius_pos S hσ v.property)
    (A.sphericalTie_radius_lt_pi S hnet hη hσ v.property)

theorem sphericalTieDirection_norm {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : η ≤ Real.pi / 2)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) (v : σ) :
    ‖A.sphericalTieDirection S hnet hη hσ v‖ = 1 :=
  GeodesicSphere.radialDirection_norm _ _ _ _

theorem sphericalTieDirection_independent {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : η ≤ Real.pi / 2)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    LinearIndependent ℝ (A.sphericalTieDirection S hnet hη hσ) := by
  let B := A.toVoronoiAtlas
  apply GeodesicSphere.radialDirection_linearIndependent _ _ _ _
    (A.sphericalTieBase_independent S hσ)
  exact GeodesicSphere.center_not_mem_span_of_equidistant
    (B.tieChart S hσ (B.tieCenter S hσ)) (B.tieChart S hσ (B.tieOtherCenter S hσ))
    (B.tie_centers_distinct S hσ) (fun v : σ => B.tieChart S hσ (B.tieSource S v.val))
    (fun v => B.tie_vertex_bisector S hσ v.property)

theorem sphericalTieDirection_hemisphere {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : η ≤ Real.pi / 2)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) [Nonempty σ] :
    ∃ p : GeodesicSphere.tangentPlane
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ)),
      ‖p‖ = 1 ∧ ∀ v : σ, 0 < inner ℝ p (A.sphericalTieDirection S hnet hη hσ v) := by
  let B := A.toVoronoiAtlas
  exact GeodesicSphere.bisector_radialDirections_hemispherical
    (B.tieChart S hσ (B.tieCenter S hσ)) (B.tieChart S hσ (B.tieOtherCenter S hσ))
    (B.tie_centers_distinct S hσ) (fun v : σ => B.tieChart S hσ (B.tieSource S v.val))
    (fun v => B.tie_vertex_radius_pos S hσ v.property)
    (fun v => A.sphericalTie_radius_lt_halfPi S hnet hη hσ v.property)
    (fun v => B.tie_vertex_bisector S hσ v.property)

theorem sphericalTieDirection_gram {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2)
    {σ τ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (hτ : τ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (v w : A.toVoronoiAtlas.TieVertex S) (hvσ : v ∈ σ) (hvτ : v ∈ τ)
    (hwσ : w ∈ σ) (hwτ : w ∈ τ) :
    inner ℝ (A.sphericalTieDirection S hnet hη hσ ⟨v, hvσ⟩)
      (A.sphericalTieDirection S hnet hη hσ ⟨w, hwσ⟩) =
    inner ℝ (A.sphericalTieDirection S hnet hη hτ ⟨v, hvτ⟩)
      (A.sphericalTieDirection S hnet hη hτ ⟨w, hwτ⟩) := by
  let B := A.toVoronoiAtlas
  unfold sphericalTieDirection
  rw [GeodesicSphere.radial_gram_formula, GeodesicSphere.radial_gram_formula,
    B.tie_vertex_radius_eq S hnet hp hσ hτ (by simpa only [Finset.mem_inter] using And.intro hvσ hvτ),
    B.tie_vertex_radius_eq S hnet hp hσ hτ (by simpa only [Finset.mem_inter] using And.intro hwσ hwτ),
    B.tie_edge_distance_eq S hσ hτ (by simpa only [Finset.mem_inter] using And.intro hvσ hvτ)
      (by simpa only [Finset.mem_inter] using And.intro hwσ hwτ)]

end ArchivePLGeometry.ProjectiveVoronoiAtlas
