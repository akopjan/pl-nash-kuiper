module

public import PLGeometry.ProjectiveTieGeometry
public import BrehmApprox.EuclideanFoldingGeometry

/-!
# The angular complex of a protected Euclidean Voronoi decomposition

Each triangulated tie base is viewed from its nearest site. The cosine law
shows that these angular simplices agree on their labelled common faces.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v

local instance euclideanVoronoiAngularDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex .euclidean (n + 1) P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance euclideanVoronoiAngularEDecidableEq : DecidableEq E := Classical.decEq E
local instance euclideanVoronoiAngularLabelDecidableEq :
    DecidableEq (A.toVoronoiAtlas.TieVertex S) := Classical.decEq _
local instance euclideanVoronoiAngularModelDecidableEq :
    DecidableEq (Model .euclidean (n + 1)) := Classical.decEq _

def euclideanAngularVertex (σ : Finset (A.toVoronoiAtlas.TieVertex S))
    (v : A.toVoronoiAtlas.TieVertex S) : GeodesicSphere n :=
  if hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces then
    CrossPolytope.sphereNormalize
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v) -
        A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
  else GeodesicSphere.northPole n

theorem euclideanAngularVertex_val {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ) :
    (A.euclideanAngularVertex S σ v).val = EuclideanFolding.radialDirection
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v)) := by
  rw [euclideanAngularVertex, dite_eq_left hσ, CrossPolytope.sphereNormalize_val]
  · rfl
  · exact sub_ne_zero.mpr (dist_pos.mp
      (A.toVoronoiAtlas.tie_vertex_radius_pos S hσ hv)).symm

theorem euclideanTieBase_independent {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    AffineIndependent ℝ (fun v : σ =>
      A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val)) := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  let W := (B.tieSourceFace S σ).image (B.tieChart S hσ)
  have hW : AffineIndependent ℝ ((↑) : W → EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using A.tieFace_simplex S hσ
  let e : σ ↪ W :=
    { toFun := fun v => ⟨B.tieChart S hσ (B.tieSource S v.val),
        Finset.mem_image.mpr ⟨B.tieSource S v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩, rfl⟩⟩
      inj' := by
        intro v w h
        have he := congrArg (fun z : W => z.val) h
        have hs := T.chart_injectiveOn i.val.1.val i.val.1.property
          (B.tieFace_source_mem S hσ v.property).1.1
          (B.tieFace_source_mem S hσ w.property).1.1 he
        exact Subtype.ext (B.tieSource_injective S hs) }
  exact hW.comp_embedding e

theorem euclideanAngularVertex_independent {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    LinearIndependent ℝ (fun v : σ => (A.euclideanAngularVertex S σ v.val).val) := by
  let B := A.toVoronoiAtlas
  have h := EuclideanFolding.radialDirection_linearIndependent
    (B.tieChart S hσ (B.tieCenter S hσ)) (B.tieChart S hσ (B.tieOtherCenter S hσ))
    (fun v : σ => B.tieChart S hσ (B.tieSource S v.val))
    (B.tie_centers_distinct S hσ) (fun v => B.tie_vertex_bisector S hσ v.property)
    (A.euclideanTieBase_independent S hσ)
  convert h using 1
  funext v
  exact A.euclideanAngularVertex_val S hσ v.property

theorem euclideanAngularVertex_hemisphere {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    InOpenHemisphere (σ.image (A.euclideanAngularVertex S σ)) := by
  let B := A.toVoronoiAtlas
  let a := B.tieChart S hσ (B.tieCenter S hσ)
  let b := B.tieChart S hσ (B.tieOtherCenter S hσ)
  let p : GeodesicSphere n := ⟨EuclideanFolding.radialDirection a b,
    EuclideanFolding.radialDirection_norm a b (B.tie_centers_distinct S hσ)⟩
  refine ⟨p, ?_⟩
  intro z hz
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  rw [A.euclideanAngularVertex_val S hσ hv]
  exact EuclideanFolding.bisector_direction_in_open_hemisphere a b
    (B.tieChart S hσ (B.tieSource S v)) (B.tie_centers_distinct S hσ)
    (B.tie_vertex_bisector S hσ hv)

theorem euclideanAngularVertex_gram {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S)
    {σ τ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (hτ : τ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v w : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ ∩ τ) (hw : w ∈ σ ∩ τ) :
    inner ℝ (A.euclideanAngularVertex S σ v).val (A.euclideanAngularVertex S σ w).val =
      inner ℝ (A.euclideanAngularVertex S τ v).val (A.euclideanAngularVertex S τ w).val := by
  let B := A.toVoronoiAtlas
  rw [A.euclideanAngularVertex_val S hσ (Finset.mem_inter.mp hv).1,
    A.euclideanAngularVertex_val S hσ (Finset.mem_inter.mp hw).1,
    A.euclideanAngularVertex_val S hτ (Finset.mem_inter.mp hv).2,
    A.euclideanAngularVertex_val S hτ (Finset.mem_inter.mp hw).2,
    EuclideanFolding.radial_gram_formula _ _ _
      (B.tie_vertex_radius_pos S hσ (Finset.mem_inter.mp hv).1)
      (B.tie_vertex_radius_pos S hσ (Finset.mem_inter.mp hw).1),
    EuclideanFolding.radial_gram_formula _ _ _
      (B.tie_vertex_radius_pos S hτ (Finset.mem_inter.mp hv).2)
      (B.tie_vertex_radius_pos S hτ (Finset.mem_inter.mp hw).2),
    B.tie_vertex_radius_eq S hnet hp hσ hτ (by simpa only [Finset.mem_inter] using hv),
    B.tie_vertex_radius_eq S hnet hp hσ hτ (by simpa only [Finset.mem_inter] using hw),
    B.tie_edge_distance_eq S hσ hτ (by simpa only [Finset.mem_inter] using hv)
      (by simpa only [Finset.mem_inter] using hw)]

/-- The actual finite spherical angular complex; no gluing hypothesis is assumed. -/
def euclideanAngularData {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) :
    Barycentric.SphericalData (A.toVoronoiAtlas.tieComplex S) n where
  vertex := A.euclideanAngularVertex S
  independent := fun _ hσ => A.euclideanAngularVertex_independent S hσ
  hemisphere := fun _ hσ => A.euclideanAngularVertex_hemisphere S hσ
  gram := by
    intro σ hσ τ hτ v hv w hw
    apply A.euclideanAngularVertex_gram S hnet hp hσ hτ
    · simpa only [Finset.mem_inter] using hv
    · simpa only [Finset.mem_inter] using hw

def euclideanAngularComplex {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) :
    FiniteChartedComplex .spherical n (A.toVoronoiAtlas.tieComplex S).Space :=
  (A.euclideanAngularData S hnet hp).toChartedComplex

end ArchivePLGeometry.ProjectiveVoronoiAtlas
