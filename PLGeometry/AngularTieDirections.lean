module

public import PLGeometry.AngularTieRealization
public import PLGeometry.EuclideanVoronoiAngular
public import PLGeometry.SphericalVoronoiAngular
public import PLGeometry.HyperbolicTieAngles
public import PLGeometry.ModelConeDirections

/-! # Angular realization agrees with the actual radial direction -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox
open scoped BigOperators

namespace ArchivePLGeometry

theorem normalize_sum_of_common_scale {ι : Type*} [Fintype ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : ι → F) (a b : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (hab : ∀ i, a i = c * b i) :
    NormedSpace.normalize (∑ i, a i • v i) = NormedSpace.normalize (∑ i, b i • v i) := by
  have he : (∑ i, a i • v i) = c • ∑ i, b i • v i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hab i, mul_smul]
  rw [he, NormedSpace.normalize_smul_of_pos hc]

namespace ProjectiveVoronoiAtlas

universe u v
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E]

local instance angularTieDirectionsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance angularTieDirectionsEDecidableEq : DecidableEq E := Classical.decEq E

section Euclidean

variable {T : FiniteChartedComplex .euclidean (n + 1) P}
    (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

theorem euclidean_angularTiePoint_direction {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ)
    (h0 : 0 < dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp (by intro h; cases h) x))) :
    coneDirection .euclidean n
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp (by intro h; cases h) x))
      h0 (by intro h; cases h) = Barycentric.chartPoint (A.euclideanAngularVertex S σ) x.val := by
  let B := A.toVoronoiAtlas
  let a := B.tieChart S hσ (B.tieCenter S hσ)
  let z := B.tieChart S hσ (A.angularTiePoint S hnet hp (by intro h; cases h) x)
  let v : σ → Model .euclidean (n + 1) := fun j => B.tieChart S hσ (B.tieSource S j.val)
  let w := A.angularWeights S hnet (by intro h; cases h) x hx
  have hrep : (∑ j : σ, w.val j • v j) = z := A.angularTiePoint_represents S hnet hp
    (by intro h; cases h) hσ x hx
  apply GeodesicSphere.ext
  rw [Barycentric.chartPoint_restrict σ (A.euclideanAngularVertex S σ)
    (A.euclideanAngularVertex_independent S hσ) ⟨x.val, hx⟩]
  change EuclideanFolding.radialDirection a z = NormedSpace.normalize
    (∑ j : σ, x.val j.val • (A.euclideanAngularVertex S σ j.val).val)
  rw [EuclideanFolding.radial_direction_barycentric a z v w.val w.property.2 hrep]
  have hv (j : σ) : EuclideanFolding.radialDirection a (v j) =
      (A.euclideanAngularVertex S σ j.val).val :=
    (A.euclideanAngularVertex_val S hσ j.property).symm
  simp only [hv]
  apply normalize_sum_of_common_scale _ _ _
    (inv_pos.mpr (A.angularWeightTotal_pos S hnet (by intro h; cases h) x))
  intro j
  exact A.angularWeights_mul_radialSine S hnet hp (by intro h; cases h) hσ x hx j

end Euclidean

section Hyperbolic

variable {T : FiniteChartedComplex .hyperbolic (n + 1) P}
    (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

theorem hyperbolic_angularTiePoint_direction {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ)
    (h0 : 0 < dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp (by intro h; cases h) x))) :
    coneDirection .hyperbolic n
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp (by intro h; cases h) x))
      h0 (by intro h; cases h) = Barycentric.chartPoint (A.hyperbolicTiePoint S σ) x.val := by
  let B := A.toVoronoiAtlas
  let a := B.tieChart S hσ (B.tieCenter S hσ)
  let z := B.tieChart S hσ (A.angularTiePoint S hnet hp (by intro h; cases h) x)
  let v : σ → HyperbolicSpace (n + 1) := fun j => B.tieChart S hσ (B.tieSource S j.val)
  let w := A.angularWeights S hnet (by intro h; cases h) x hx
  obtain ⟨c, hc, hrep⟩ := A.angularTiePoint_represents S hnet hp
    (by intro h; cases h) hσ x hx
  change (∑ j : σ, w.val j • HyperbolicSpace.lift (v j)) = c • HyperbolicSpace.lift z at hrep
  let L := (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin (n + 1)))).comp
    (Hyperboloid.boostLinear a.point)
  have hcoord (y : HyperbolicSpace (n + 1)) : L (HyperbolicSpace.lift y) =
      HyperbolicSpace.radialVector a y := rfl
  have hvec := congrArg L hrep
  simp only [map_sum, map_smul, hcoord] at hvec
  have hsum : (∑ j : σ, (w.val j * Real.sinh (dist a (v j))) •
      HyperbolicSpace.radialDirection a (v j)) = c • HyperbolicSpace.radialVector a z := by
    simpa only [mul_smul, HyperbolicSpace.sinh_smul_radialDirection] using hvec
  have hd : HyperbolicSpace.radialDirection a z = NormedSpace.normalize
      (∑ j : σ, (w.val j * Real.sinh (dist a (v j))) •
        HyperbolicSpace.radialDirection a (v j)) := by
    rw [hsum, NormedSpace.normalize_smul_of_pos hc]
    rw [NormedSpace.normalize, HyperbolicSpace.norm_radialVector, HyperbolicSpace.radialDirection]
  apply GeodesicSphere.ext
  rw [Barycentric.chartPoint_restrict σ (A.hyperbolicTiePoint S σ)
    (A.hyperbolicTiePoint_independent S hσ) ⟨x.val, hx⟩]
  change HyperbolicSpace.radialDirection a z = NormedSpace.normalize
    (∑ j : σ, x.val j.val • (A.hyperbolicTiePoint S σ j.val).val)
  rw [hd]
  have hv (j : σ) : HyperbolicSpace.radialDirection a (v j) =
      (A.hyperbolicTiePoint S σ j.val).val :=
    (A.hyperbolicTiePoint_val S hσ j.property).symm
  simp only [hv]
  apply normalize_sum_of_common_scale _ _ _
    (inv_pos.mpr (A.angularWeightTotal_pos S hnet (by intro h; cases h) x))
  intro j
  exact A.angularWeights_mul_radialSine S hnet hp (by intro h; cases h) hσ x hx j

end Hyperbolic

section Spherical

variable {T : FiniteChartedComplex .spherical (n + 1) P}
    (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

theorem spherical_angularTiePoint_direction {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : η ≤ Real.pi / 2)
    {hsmall : Geometry.spherical = .spherical → η < Real.pi}
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ)
    (h0 : 0 < dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x)))
    (hπ : dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x)) < Real.pi) :
    coneDirection .spherical n
      (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x))
      h0 (fun _ => hπ) =
        Barycentric.chartPoint (A.sphericalAngularVertex S hnet hη σ) x.val := by
  let B := A.toVoronoiAtlas
  let a := B.tieChart S hσ (B.tieCenter S hσ)
  let z := B.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x)
  let v : σ → GeodesicSphere (n + 1) := fun j => B.tieChart S hσ (B.tieSource S j.val)
  let w := A.angularWeights S hnet hsmall x hx
  let U := GeodesicSphere.tangentEuclideanEquiv a
  have hv0 (j : σ) : 0 < dist a (v j) := B.tie_vertex_radius_pos S hσ j.property
  have hvπ (j : σ) : dist a (v j) < Real.pi := A.sphericalTie_radius_lt_pi S hnet hη hσ j.property
  obtain ⟨c, hc, hrep⟩ := A.angularTiePoint_represents S hnet hp hsmall hσ x hx
  change (∑ j : σ, w.val j • (v j).val) = c • z.val at hrep
  have hd := GeodesicSphere.radialDirection_positive_combination_tangent a z v w.val
    h0 hπ hv0 hvπ hc hrep
  apply GeodesicSphere.ext
  rw [Barycentric.chartPoint_restrict σ (A.sphericalAngularVertex S hnet hη σ)
    (A.sphericalAngularVertex_independent S hnet hη hσ) ⟨x.val, hx⟩]
  change U (GeodesicSphere.radialDirection a z h0 hπ) = NormedSpace.normalize
    (∑ j : σ, x.val j.val • (A.sphericalAngularVertex S hnet hη σ j.val).val)
  rw [hd]
  have hmap : U (NormedSpace.normalize
      (∑ j : σ, (w.val j * Real.sin (dist a (v j))) •
        GeodesicSphere.radialDirection a (v j) (hv0 j) (hvπ j))) =
      NormedSpace.normalize (∑ j : σ, (w.val j * Real.sin (dist a (v j))) •
        U (GeodesicSphere.radialDirection a (v j) (hv0 j) (hvπ j))) := by
    have hh := linearIsometry_map_normalize U.toLinearIsometry
      (∑ j : σ, (w.val j * Real.sin (dist a (v j))) •
        GeodesicSphere.radialDirection a (v j) (hv0 j) (hvπ j))
    change U (NormedSpace.normalize _) = NormedSpace.normalize (U _) at hh
    rw [hh]
    simp only [map_sum, map_smul]
  rw [hmap]
  have hv (j : σ) : U (GeodesicSphere.radialDirection a (v j) (hv0 j) (hvπ j)) =
      (A.sphericalAngularVertex S hnet hη σ j.val).val :=
    (A.sphericalAngularVertex_val S hnet hη hσ j.property).symm
  simp only [hv]
  apply normalize_sum_of_common_scale _ _ _
    (inv_pos.mpr (A.angularWeightTotal_pos S hnet hsmall x))
  intro j
  exact A.angularWeights_mul_radialSine S hnet hp hsmall hσ x hx j

end Spherical

end ProjectiveVoronoiAtlas
end ArchivePLGeometry
