module

public import BrehmApprox.CoordinateSphericalCells
public import Mathlib.Data.Fintype.EquivFin

/-!
# Actual model charts for signed-coordinate spherical cells

An injective coordinate map followed by coordinate sign changes is a genuine
linear isometric embedding. Its induced round-sphere map sends the standard
positive spherical simplex onto the desired signed-coordinate cell.
-/

@[expose] public section
noncomputable section

namespace BrehmApprox.CoordinateCellCharts

open GeodesicSphere CoordinateSphericalCells
open scoped BigOperators

variable {m n : ℕ}

local instance coordinateCellChartsLocalInstance1 {k : ℕ} : DecidableEq (GeodesicSphere k) := Classical.decEq _

def signIsometry (σ : Fin (n + 1) → Bool) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i =>
    if σ i then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)

theorem signIsometry_coordinate (σ : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    signIsometry σ (coordinatePole n i).val = (signedPole σ i).val := by
  rw [signIsometry, coordinatePole_val, LinearIsometryEquiv.piLpCongrRight_single]
  unfold signedPole
  cases σ i <;> simp [coordinatePole_val, antipode]
  ext j
  by_cases h : j = i <;> simp [h]

def linearChart (e : Fin (m + 1) ↪ Fin (n + 1)) (σ : Fin (n + 1) → Bool) :
    EuclideanSpace ℝ (Fin (m + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (signIsometry σ).toLinearIsometry.comp (LinearIsometry.piLpExtendByZero 2 ℝ ℝ e)

def sphereChart (e : Fin (m + 1) ↪ Fin (n + 1)) (σ : Fin (n + 1) → Bool) :
    GeodesicSphere m → GeodesicSphere n := GeodesicSphere.map (linearChart e σ)

theorem sphereChart_isometry (e : Fin (m + 1) ↪ Fin (n + 1))
    (σ : Fin (n + 1) → Bool) : Isometry (sphereChart e σ) :=
  GeodesicSphere.isometry_map _

theorem sphereChart_coordinate (e : Fin (m + 1) ↪ Fin (n + 1))
    (σ : Fin (n + 1) → Bool) (i : Fin (m + 1)) :
    sphereChart e σ (coordinatePole m i) = signedPole σ (e i) := by
  apply GeodesicSphere.ext
  change signIsometry σ (LinearIsometry.piLpExtendByZero 2 ℝ ℝ e
    (coordinatePole m i).val) = _
  rw [coordinatePole_val, LinearIsometry.piLpExtendByZero_apply_single]
  exact signIsometry_coordinate σ (e i)

/-- A linear isometric embedding transports the actual positive spherical
hull exactly, including every point of every face. -/
theorem map_sphericalCell_image
    (A : EuclideanSpace ℝ (Fin (m + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (V : Finset (GeodesicSphere m)) :
    GeodesicSphere.map A '' sphericalCell V =
      sphericalCell (V.image (GeodesicSphere.map A)) := by
  classical
  let f := GeodesicSphere.map A
  have hf : Function.Injective f := (GeodesicSphere.isometry_map A).injective
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, a, ha, hrep⟩, rfl⟩
    let w' : GeodesicSphere n → ℝ := fun v => w (Function.invFun f v)
    refine ⟨w', ?_, a, ha, ?_⟩
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      change 0 ≤ w (Function.invFun f (f u))
      rw [Function.leftInverse_invFun hf u]
      exact hw u hu
    · rw [Finset.sum_image (fun u _ v _ h => hf h)]
      have hinv (u : GeodesicSphere m) : w' (f u) = w u := by
        simp only [w', Function.leftInverse_invFun hf u]
      change (∑ u ∈ V, w' (f u) • A u.val) = a • A y.val
      simp_rw [hinv, ← A.map_smul]
      rw [← map_sum, hrep, A.map_smul]
  · rintro ⟨w, hw, a, ha, hrep⟩
    let v : EuclideanSpace ℝ (Fin (m + 1)) := ∑ u ∈ V, w (f u) • u.val
    have hAv : A v = a • x.val := by
      rw [Finset.sum_image (fun u _ v _ h => hf h)] at hrep
      simpa only [v, map_sum, A.map_smul, f, GeodesicSphere.map] using hrep
    have hnorm : ‖v‖ = a := by
      have h := congrArg norm hAv
      rw [A.norm_map, norm_smul, x.norm_val, Real.norm_eq_abs, abs_of_pos ha, mul_one] at h
      exact h
    have hv : v ≠ 0 := norm_pos_iff.mp (hnorm ▸ ha)
    let y : GeodesicSphere m := normalizeVector v hv
    refine ⟨y, ?_, ?_⟩
    · refine ⟨fun u => w (f u), ?_, ‖v‖, hnorm ▸ ha, ?_⟩
      · intro u hu
        exact hw _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      · exact (NormedSpace.norm_smul_normalize v).symm
    · apply GeodesicSphere.ext
      change A (NormedSpace.normalize v) = x.val
      rw [NormedSpace.normalize, A.map_smul, hAv, smul_smul, hnorm,
        inv_mul_cancel₀ ha.ne', one_smul]

def standardVertices (m : ℕ) : Finset (GeodesicSphere m) :=
  vertices Finset.univ (fun _ => true)

def standardSimplex (m : ℕ) : Set (GeodesicSphere m) := sphericalCell (standardVertices m)

theorem standardVertices_hemispherical (m : ℕ) : InOpenHemisphere (standardVertices m) :=
  hemispherical Finset.univ (fun _ => true)

theorem sphereChart_image (e : Fin (m + 1) ↪ Fin (n + 1))
    (σ : Fin (n + 1) → Bool) :
    sphereChart e σ '' standardSimplex m =
      sphericalCell (vertices (Finset.univ.image e) σ) := by
  classical
  rw [standardSimplex, sphereChart, map_sphericalCell_image]
  congr 1
  simp only [standardVertices, vertices, Finset.image_image]
  apply Finset.image_congr
  intro i _
  change sphereChart e σ (coordinatePole m i) = signedPole σ (e i)
  exact sphereChart_coordinate e σ i

def restrictedChart (e : Fin (m + 1) ↪ Fin (n + 1)) (σ : Fin (n + 1) → Bool) :
    standardSimplex m → sphericalCell (vertices (Finset.univ.image e) σ) :=
  fun x => ⟨sphereChart e σ x.val, by
    rw [← sphereChart_image]
    exact Set.mem_image_of_mem _ x.property⟩

theorem restrictedChart_isometry (e : Fin (m + 1) ↪ Fin (n + 1))
    (σ : Fin (n + 1) → Bool) : Isometry (restrictedChart e σ) := by
  apply Isometry.of_dist_eq
  intro x y
  exact (sphereChart_isometry e σ).dist_eq x.val y.val

theorem restrictedChart_surjective (e : Fin (m + 1) ↪ Fin (n + 1))
    (σ : Fin (n + 1) → Bool) : Function.Surjective (restrictedChart e σ) := by
  intro y
  have hy := (Set.ext_iff.mp (sphereChart_image e σ) y.val).mpr y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- An actual isometry equivalence of metric subspaces, with both source and
target carrying the round angular distance. -/
def coordinateChart (e : Fin (m + 1) ↪ Fin (n + 1)) (σ : Fin (n + 1) → Bool) :
    standardSimplex m ≃ᵢ sphericalCell (vertices (Finset.univ.image e) σ) where
  toEquiv := Equiv.ofBijective (restrictedChart e σ)
    ⟨(restrictedChart_isometry e σ).injective, restrictedChart_surjective e σ⟩
  isometry_toFun := restrictedChart_isometry e σ

/-- A signed-coordinate cell with `m+1` independent axes has a genuine chart
from the standard `m`-dimensional spherical simplex. -/
theorem exists_model_chart (I : Finset (Fin (n + 1)))
    (σ : Fin (n + 1) → Bool) (hI : I.card = m + 1) :
    Nonempty (standardSimplex m ≃ᵢ sphericalCell (vertices I σ)) := by
  classical
  let t : Fin (m + 1) ≃ I := Fintype.equivOfCardEq (by simpa using hI.symm)
  let e : Fin (m + 1) ↪ Fin (n + 1) :=
    ⟨fun i => (t i).val, fun i j h => t.injective (Subtype.ext h)⟩
  have he : Finset.univ.image e = I := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact (t i).property
    · intro hj
      obtain ⟨i, hi⟩ := t.surjective ⟨j, hj⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, congrArg Subtype.val hi⟩
  have hsets : sphericalCell (vertices (Finset.univ.image e) σ) =
      sphericalCell (vertices I σ) := congrArg (fun J => sphericalCell (vertices J σ)) he
  let c : sphericalCell (vertices (Finset.univ.image e) σ) ≃ᵢ
      sphericalCell (vertices I σ) :=
    { toEquiv := Set.equivOfEq hsets
      isometry_toFun := by intro x y; rfl }
  exact ⟨(coordinateChart e σ).trans c⟩

/-- In particular, the three-axis cells in the explicit source are actual
two-dimensional spherical triangles, not merely sets with three vertices. -/
theorem exists_triangle_chart (I : Finset (Fin 4)) (σ : Fin 4 → Bool)
    (hI : I.card = 3) :
    Nonempty (standardSimplex 2 ≃ᵢ sphericalCell (vertices I σ)) :=
  exists_model_chart I σ hI

theorem exists_triangle_chart_of_coordinates (V : Finset (GeodesicSphere 3))
    (hV : ∃ I : Finset (Fin 4), ∃ σ : Fin 4 → Bool,
      V = vertices I σ ∧ I.card = 3) :
    Nonempty (standardSimplex 2 ≃ᵢ sphericalCell V) := by
  obtain ⟨I, σ, hV, hI⟩ := hV
  subst V
  exact exists_triangle_chart I σ hI

end BrehmApprox.CoordinateCellCharts
