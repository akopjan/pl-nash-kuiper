module

public import PLGeometry.SphericalVoronoiAngles
public import BrehmApprox.SphericalTangentDimension

/-! # The actual lower-dimensional spherical Voronoi angular complex -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v

local instance sphericalVoronoiAngularDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex .spherical (n + 1) P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance sphericalVoronoiAngularEDecidableEq : DecidableEq E := Classical.decEq E
local instance sphericalVoronoiAngularLabelDecidableEq :
    DecidableEq (A.toVoronoiAtlas.TieVertex S) := Classical.decEq _

def sphericalAngularVertex {η : ℝ} (hnet : T.IsCellwiseNet S η) (hη : η ≤ Real.pi / 2)
    (σ : Finset (A.toVoronoiAtlas.TieVertex S))
    (v : A.toVoronoiAtlas.TieVertex S) : GeodesicSphere n :=
  if hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces then
    if hv : v ∈ σ then
      ⟨GeodesicSphere.tangentEuclideanEquiv
        (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
        (A.sphericalTieDirection S hnet hη hσ ⟨v, hv⟩), by
          rw [LinearIsometryEquiv.norm_map]
          exact A.sphericalTieDirection_norm S hnet hη hσ ⟨v, hv⟩⟩
    else GeodesicSphere.northPole n
  else GeodesicSphere.northPole n

theorem sphericalAngularVertex_val {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : η ≤ Real.pi / 2) {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ) :
    (A.sphericalAngularVertex S hnet hη σ v).val =
      GeodesicSphere.tangentEuclideanEquiv
        (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
        (A.sphericalTieDirection S hnet hη hσ ⟨v, hv⟩) := by
  simp only [sphericalAngularVertex, dite_eq_left hσ, dite_eq_left hv]

theorem sphericalAngularVertex_independent {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : η ≤ Real.pi / 2) {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    LinearIndependent ℝ (fun v : σ => (A.sphericalAngularVertex S hnet hη σ v.val).val) := by
  let U := GeodesicSphere.tangentEuclideanEquiv
    (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
  have h := (A.sphericalTieDirection_independent S hnet hη hσ).map' U.toLinearMap
    (LinearMap.ker_eq_bot.mpr U.injective)
  convert h using 1
  funext v
  exact A.sphericalAngularVertex_val S hnet hη hσ v.property

theorem sphericalAngularVertex_hemisphere {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : η ≤ Real.pi / 2) {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    InOpenHemisphere (σ.image (A.sphericalAngularVertex S hnet hη σ)) := by
  by_cases hσe : σ = ∅
  · rw [hσe, Finset.image_empty]
    exact ⟨GeodesicSphere.northPole n, by simp⟩
  · obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hσe
    let : Nonempty σ := ⟨⟨v₀, hv₀⟩⟩
    obtain ⟨p, hp, hpos⟩ := A.sphericalTieDirection_hemisphere S hnet hη hσ
    let U := GeodesicSphere.tangentEuclideanEquiv
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
    refine ⟨⟨U p, by rw [U.norm_map]; exact hp⟩, ?_⟩
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    rw [A.sphericalAngularVertex_val S hnet hη hσ hv]
    change 0 < inner ℝ (U p) (U (A.sphericalTieDirection S hnet hη hσ ⟨v, hv⟩))
    rw [U.inner_map_map]
    exact hpos ⟨v, hv⟩

theorem sphericalAngularVertex_gram {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2)
    {σ τ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (hτ : τ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v w : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ ∩ τ) (hw : w ∈ σ ∩ τ) :
    inner ℝ (A.sphericalAngularVertex S hnet hη σ v).val
      (A.sphericalAngularVertex S hnet hη σ w).val =
    inner ℝ (A.sphericalAngularVertex S hnet hη τ v).val
      (A.sphericalAngularVertex S hnet hη τ w).val := by
  rw [A.sphericalAngularVertex_val S hnet hη hσ (Finset.mem_inter.mp hv).1,
    A.sphericalAngularVertex_val S hnet hη hσ (Finset.mem_inter.mp hw).1,
    A.sphericalAngularVertex_val S hnet hη hτ (Finset.mem_inter.mp hv).2,
    A.sphericalAngularVertex_val S hnet hη hτ (Finset.mem_inter.mp hw).2,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  exact A.sphericalTieDirection_gram S hnet hp hη hσ hτ v w
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2
    (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2

def sphericalAngularData {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2) :
    Barycentric.SphericalData (A.toVoronoiAtlas.tieComplex S) n where
  vertex := A.sphericalAngularVertex S hnet hη
  independent := fun _ hσ => A.sphericalAngularVertex_independent S hnet hη hσ
  hemisphere := fun _ hσ => A.sphericalAngularVertex_hemisphere S hnet hη hσ
  gram := by
    intro σ hσ τ hτ v hv w hw
    apply A.sphericalAngularVertex_gram S hnet hp hη hσ hτ
    · simpa only [Finset.mem_inter] using hv
    · simpa only [Finset.mem_inter] using hw

def sphericalAngularComplex {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2) :
    FiniteChartedComplex .spherical n (A.toVoronoiAtlas.tieComplex S).Space :=
  (A.sphericalAngularData S hnet hp hη).toChartedComplex

end ArchivePLGeometry.ProjectiveVoronoiAtlas
