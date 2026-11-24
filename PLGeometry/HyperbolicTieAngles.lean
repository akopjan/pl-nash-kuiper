module

public import PLGeometry.ProjectiveTieGeometry
public import BrehmApprox.HyperbolicAngularSimplex
public import BrehmApprox.SimplexRadialLink

/-! # The spherical angular complex of hyperbolic Voronoi tie bases -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox
open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

open HyperbolicSpace CrossPolytope RadialLink

universe u v

local instance hyperbolicTieAnglesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex .hyperbolic (n + 1) P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

def hyperbolicTieVector (σ : Finset (A.toVoronoiAtlas.TieVertex S))
    (v : A.toVoronoiAtlas.TieVertex S) : EuclideanSpace ℝ (Fin (n + 1)) :=
  if hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces then
    radialVector
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v))
  else 0

def hyperbolicTiePoint (σ : Finset (A.toVoronoiAtlas.TieVertex S))
    (v : A.toVoronoiAtlas.TieVertex S) : GeodesicSphere n :=
  sphereNormalize (A.hyperbolicTieVector S σ v)

theorem hyperbolicTieVector_independent {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    LinearIndependent ℝ (fun v : σ => A.hyperbolicTieVector S σ v.val) := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  let C := B.tieChart S hσ
  let a := C (B.tieCenter S hσ)
  let b := C (B.tieOtherCenter S hσ)
  let W := (B.tieSourceFace S σ).image C
  have hW : LinearIndependent ℝ (fun v : W => lift v.val) := A.tieFace_simplex S hσ
  have hbis : ∀ x ∈ W, dist a x = dist b x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact B.tie_vertex_bisector S hσ hv
  have hab : a ≠ b := B.tie_centers_distinct S hσ
  let e : σ ↪ W :=
    { toFun := fun v => ⟨C (B.tieSource S v.val),
        Finset.mem_image.mpr ⟨B.tieSource S v.val,
          Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩, rfl⟩⟩
      inj' := by
        intro v w he
        apply Subtype.ext
        apply B.tieSource_injective S
        exact T.chart_injectiveOn i.val.1.val i.val.1.property
          (B.tieFace_source_mem S hσ v.property).1.1
          (B.tieFace_source_mem S hσ w.property).1.1
          (congrArg (fun z : W => z.val) he) }
  have hfamily : LinearIndependent ℝ
      (fun v : σ => lift (C (B.tieSource S v.val))) := hW.comp e e.injective
  have hspan : Set.range (fun v : σ => lift (C (B.tieSource S v.val))) ⊆
      lift '' (W : Set (HyperbolicSpace (n + 1))) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨e v, (e v).property, rfl⟩
  have ha : lift a ∉ Submodule.span ℝ
      (Set.range (fun v : σ => lift (C (B.tieSource S v.val)))) := by
    intro h
    exact center_not_mem_span_bisector_vertices a b hab W hbis (Submodule.span_mono hspan h)
  have h := linearIndependent_radialVector a (fun v : σ => C (B.tieSource S v.val)) hfamily ha
  simpa only [hyperbolicTieVector, dite_eq_left hσ] using h

theorem hyperbolicTiePoint_independent {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    LinearIndependent ℝ (fun v : σ => (A.hyperbolicTiePoint S σ v.val).val) :=
  normalized_family_independent (A.hyperbolicTieVector_independent S hσ)

theorem hyperbolicTiePoint_hemisphere {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    InOpenHemisphere (σ.image (A.hyperbolicTiePoint S σ)) := by
  have h := normalized_family_hemisphere (A.hyperbolicTieVector_independent S hσ)
  have he : Finset.univ.image (fun v : σ => sphereNormalize (A.hyperbolicTieVector S σ v.val)) =
      σ.image (A.hyperbolicTiePoint S σ) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hyperbolicTiePoint]
    constructor
    · rintro ⟨v, hz⟩
      exact ⟨v.val, v.property, hz⟩
    · rintro ⟨v, hv, hz⟩
      exact ⟨⟨v, hv⟩, hz⟩
  rwa [he] at h

theorem hyperbolicTiePoint_val {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ) :
    (A.hyperbolicTiePoint S σ v).val = radialDirection
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v)) := by
  have hn := (A.hyperbolicTieVector_independent S hσ).ne_zero ⟨v, hv⟩
  rw [hyperbolicTiePoint, sphereNormalize_val hn]
  simp only [hyperbolicTieVector, dite_eq_left hσ, NormedSpace.normalize,
    norm_radialVector, radialDirection]

theorem hyperbolicTiePoint_gram {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S)
    {σ τ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (hτ : τ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v w : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ ∩ τ) (hw : w ∈ σ ∩ τ) :
    inner ℝ (A.hyperbolicTiePoint S σ v).val (A.hyperbolicTiePoint S σ w).val =
      inner ℝ (A.hyperbolicTiePoint S τ v).val (A.hyperbolicTiePoint S τ w).val := by
  let B := A.toVoronoiAtlas
  obtain ⟨hvσ, hvτ⟩ := Finset.mem_inter.mp hv
  obtain ⟨hwσ, hwτ⟩ := Finset.mem_inter.mp hw
  rw [A.hyperbolicTiePoint_val S hσ hvσ, A.hyperbolicTiePoint_val S hσ hwσ,
    A.hyperbolicTiePoint_val S hτ hvτ, A.hyperbolicTiePoint_val S hτ hwτ]
  rw [radial_gram_formula _ _ _ (B.tie_vertex_radius_pos S hσ hvσ)
      (B.tie_vertex_radius_pos S hσ hwσ),
    radial_gram_formula _ _ _ (B.tie_vertex_radius_pos S hτ hvτ)
      (B.tie_vertex_radius_pos S hτ hwτ),
    B.tie_vertex_radius_eq S hnet hp hσ hτ hv,
    B.tie_vertex_radius_eq S hnet hp hσ hτ hw,
    B.tie_edge_distance_eq S hσ hτ hv hw]

/-- The true angular simplices used in the hyperbolic radial folding construction. -/
def hyperbolicAngularData {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) : Barycentric.SphericalData (A.toVoronoiAtlas.tieComplex S) n where
  vertex := A.hyperbolicTiePoint S
  independent := fun _ hσ => A.hyperbolicTiePoint_independent S hσ
  hemisphere := fun _ hσ => A.hyperbolicTiePoint_hemisphere S hσ
  gram := by
    intro σ hσ τ hτ v hv w hw
    apply A.hyperbolicTiePoint_gram S hnet hp hσ hτ
    · simpa only [Finset.mem_inter] using hv
    · simpa only [Finset.mem_inter] using hw

end ArchivePLGeometry.ProjectiveVoronoiAtlas
