module

public import PLGeometry.Basic
public import BrehmApprox.CoordinateCellCharts
public import Mathlib.Data.Fin.Embedding

/-!
# Increasing the ambient dimension

Canonical coordinate embeddings preserve model distances, geodesic hulls,
and simplex independence in all three geometries. They transport each chart
of a concrete triangulation and leave its intrinsic source metric unchanged.
-/

@[expose] public section
noncomputable section

open scoped BigOperators InnerProductSpace

namespace ArchivePLGeometry

universe u

local instance dimensionLocalInstance1 (α : Type*) : DecidableEq α := Classical.decEq α

/-- An isometric model embedding preserving genuine simplices and their hulls. -/
structure ModelEmbedding (κ : Geometry) (d n : ℕ) where
  toFun : Model κ d → Model κ n
  isometry : Isometry toFun
  image_hull : ∀ V : Finset (Model κ d),
    toFun '' hull κ d V = hull κ n (V.image toFun)
  simplex_image : ∀ V : Finset (Model κ d),
    simplexVertices κ d V → simplexVertices κ n (V.image toFun)

/-- Inclusion of Euclidean coordinate spaces by appending zero coordinates. -/
def coordinateEmbedding {d n : ℕ} (hdn : d ≤ n) :
    EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hdn)

def euclideanModelEmbedding {d n : ℕ} (hdn : d ≤ n) : ModelEmbedding .euclidean d n where
  toFun := coordinateEmbedding hdn
  isometry := (coordinateEmbedding hdn).isometry
  image_hull V := by
    simpa only [hull, Finset.coe_image, LinearIsometry.coe_toLinearMap] using
      (coordinateEmbedding hdn).toLinearMap.image_convexHull (V : Set _)
  simplex_image V hV := by
    have hV' : AffineIndepOn ℝ id (V : Set (EuclideanSpace ℝ (Fin d))) := by
      simpa only [simplexVertices, AffineIndepOn, id_eq] using hV
    have hmap := hV'.map' (coordinateEmbedding hdn).toLinearMap.toAffineMap
      (coordinateEmbedding hdn).injective
    dsimp only [simplexVertices]
    rw [@Finset.coe_image _ _ (Classical.decEq _) (coordinateEmbedding hdn) V]
    simpa only [AffineIndepOn,
      LinearMap.coe_toAffineMap, LinearIsometry.coe_toLinearMap, Function.comp_def,
      id_eq] using hmap.id_image

def sphericalModelEmbedding {d n : ℕ} (hdn : d ≤ n) : ModelEmbedding .spherical d n where
  toFun := GeodesicSphere.map (coordinateEmbedding (Nat.succ_le_succ hdn))
  isometry := GeodesicSphere.isometry_map _
  image_hull V := BrehmApprox.CoordinateCellCharts.map_sphericalCell_image _ V
  simplex_image V hV := by
    let A := coordinateEmbedding (Nat.succ_le_succ hdn)
    change BrehmApprox.InOpenHemisphere (V.image (GeodesicSphere.map A)) ∧ _
    obtain ⟨⟨p, hp⟩, hlin⟩ := hV
    constructor
    · refine ⟨GeodesicSphere.map A p, ?_⟩
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      change 0 < inner ℝ (A p.val) (A x.val)
      rw [A.inner_map_map]
      exact hp x hx
    · change LinearIndepOn ℝ GeodesicSphere.val
        (↑(V.image (GeodesicSphere.map A)) : Set (GeodesicSphere n))
      rw [Finset.coe_image]
      have hmap : LinearIndepOn ℝ (GeodesicSphere.val ∘ GeodesicSphere.map A)
          (V : Set (GeodesicSphere d)) :=
        hlin.map_injOn A.toLinearMap A.injective.injOn
      exact hmap.image_of_comp (GeodesicSphere.map A) GeodesicSphere.val

end ArchivePLGeometry

namespace BrehmApprox.HyperbolicSpace

variable {d n : ℕ}

local instance dimensionLocalInstance2 (α : Type*) : DecidableEq α := Classical.decEq α
local instance dimensionLocalInstance3 {k : ℕ} : Nonempty (HyperbolicSpace k) := ⟨⟨0⟩⟩

/-- A linear isometric embedding of the spatial coordinates acts isometrically
on the corresponding future hyperboloids. -/
def map (A : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : HyperbolicSpace d) : HyperbolicSpace n := ⟨A x.point⟩

theorem isometry_map (A : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Isometry (map A) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [HyperbolicSpace.dist_eq, map, A.norm_map, A.inner_map_map]

/-- The induced linear inclusion of Lorentz homogeneous coordinates. -/
def liftMap (A : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (ℝ × EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) :=
  LinearMap.id.prodMap A.toLinearMap

@[simp] theorem lift_map (A : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : HyperbolicSpace d) : lift (map A x) = liftMap A (lift x) := by
  simp [lift, map, liftMap, Hyperboloid.height, A.norm_map]

theorem liftMap_injective (A : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Function.Injective (liftMap A) := by
  intro x y h
  apply Prod.ext
  · simpa only [liftMap, LinearMap.prodMap_apply, LinearMap.id_apply] using congrArg Prod.fst h
  · apply A.injective
    exact congrArg Prod.snd h

/-- Spatial coordinate inclusions transport every hyperbolic hull exactly. -/
theorem map_hyperbolicCell_image
    (A : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (V : Finset (HyperbolicSpace d)) :
    map A '' hyperbolicCell V = hyperbolicCell (V.image (map A)) := by
  classical
  let f := map A
  have hf : Function.Injective f := (isometry_map A).injective
  ext y
  constructor
  · rintro ⟨x, ⟨w, hw, a, ha, hrep⟩, rfl⟩
    let w' : HyperbolicSpace n → ℝ := fun v => w (Function.invFun f v)
    refine ⟨w', ?_, a, ha, ?_⟩
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      change 0 ≤ w (Function.invFun f (f u))
      rw [Function.leftInverse_invFun hf u]
      exact hw u hu
    · rw [Finset.sum_image (fun u _ v _ h => hf h)]
      have hinv (u : HyperbolicSpace d) : w' (f u) = w u := by
        simp only [w', Function.leftInverse_invFun hf u]
      change (∑ u ∈ V, w' (f u) • lift (map A u)) = a • lift (map A x)
      simp_rw [hinv, lift_map, ← map_smul]
      rw [← map_sum, hrep, map_smul]
  · rintro ⟨w, hw, a, ha, hrep⟩
    rw [Finset.sum_image (fun u _ v _ h => hf h)] at hrep
    let v : EuclideanSpace ℝ (Fin d) := ∑ u ∈ V, w (f u) • u.point
    have hAv : A v = a • y.point := by
      have hh := congrArg (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) hrep
      simpa only [v, map_sum, map_smul, lift, map, f, LinearMap.snd_apply] using hh
    let x : HyperbolicSpace d := ⟨a⁻¹ • v⟩
    have hfx : f x = y := by
      apply HyperbolicSpace.ext
      change A (a⁻¹ • v) = y.point
      rw [A.map_smul, hAv, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    refine ⟨x, ?_, hfx⟩
    refine ⟨fun u => w (f u), ?_, a, ha, ?_⟩
    · intro u hu
      exact hw _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    · apply liftMap_injective A
      simp only [map_sum, map_smul, ← lift_map]
      change (∑ u ∈ V, w (f u) • lift (f u)) = a • lift (f x)
      rw [hfx]
      exact hrep

end BrehmApprox.HyperbolicSpace

namespace ArchivePLGeometry

local instance dimensionLocalInstance4 (α : Type*) : DecidableEq α := Classical.decEq α

def hyperbolicModelEmbedding {d n : ℕ} (hdn : d ≤ n) : ModelEmbedding .hyperbolic d n where
  toFun := BrehmApprox.HyperbolicSpace.map (coordinateEmbedding hdn)
  isometry := BrehmApprox.HyperbolicSpace.isometry_map _
  image_hull V := BrehmApprox.HyperbolicSpace.map_hyperbolicCell_image _ V
  simplex_image V hV := by
    let A := coordinateEmbedding hdn
    let f := BrehmApprox.HyperbolicSpace.map A
    change LinearIndepOn ℝ BrehmApprox.HyperbolicSpace.lift
      (↑(V.image f) : Set (BrehmApprox.HyperbolicSpace n))
    rw [Finset.coe_image]
    have hm := hV.map_injOn (BrehmApprox.HyperbolicSpace.liftMap A)
      (BrehmApprox.HyperbolicSpace.liftMap_injective A).injOn
    have hmap : LinearIndepOn ℝ (BrehmApprox.HyperbolicSpace.lift ∘ f)
        (V : Set (BrehmApprox.HyperbolicSpace d)) := by
      simpa only [LinearIndepOn, Function.comp_def, f,
        BrehmApprox.HyperbolicSpace.lift_map] using hm
    exact hmap.image_of_comp f BrehmApprox.HyperbolicSpace.lift

/-- The canonical inclusion of one constant-curvature model into a larger one. -/
def modelEmbedding (κ : Geometry) {d n : ℕ} (hdn : d ≤ n) : ModelEmbedding κ d n :=
  match κ with
  | .euclidean => euclideanModelEmbedding hdn
  | .spherical => sphericalModelEmbedding hdn
  | .hyperbolic => hyperbolicModelEmbedding hdn

namespace Triangulation

variable {κ : Geometry} {d n : ℕ} {P : Type u} [MetricSpace P]

/-- Enlarge the model of each local chart without changing the source cells. -/
def mapModel (T : Triangulation κ d P) (e : ModelEmbedding κ d n) :
    Triangulation κ n P where
  simplices := T.simplices
  cell := T.cell
  chart σ := e.toFun ∘ T.chart σ
  cover := T.cover
  locallyFinite := T.locallyFinite
  vertices_mem := T.vertices_mem
  simplex σ hσ := by
    rw [← Finset.image_image]
    exact e.simplex_image _ (T.simplex σ hσ)
  image_cell σ hσ := by
    simp only [Function.comp_def]
    rw [← Set.image_image e.toFun (T.chart σ) (T.cell σ), T.image_cell σ hσ,
      e.image_hull, Finset.image_image]
    simp only [Function.comp_def]
  isometry_cell σ hσ x hx y hy :=
    (e.isometry.dist_eq _ _).trans (T.isometry_cell σ hσ x hx y hy)
  faces := T.faces
  image_face σ hσ τ hτ := by
    simp only [Function.comp_def]
    rw [← Set.image_image e.toFun (T.chart σ) (T.cell τ), T.image_face σ hσ τ hτ,
      e.image_hull, Finset.image_image]
    simp only [Function.comp_def]
  intersection := T.intersection

theorem intrinsic_mapModel (T : Triangulation κ d P) (e : ModelEmbedding κ d n)
    (hT : Intrinsic T) : Intrinsic (T.mapModel e) := hT

end Triangulation

/-- A dimension bound on a finite intrinsic polyhedron may be increased. -/
theorem IsFinitePolyhedron.mono {κ : Geometry} {d n : ℕ}
    {P : Type u} [MetricSpace P] (hP : IsFinitePolyhedron κ d P) (hdn : d ≤ n) :
    IsFinitePolyhedron κ n P := by
  obtain ⟨T, hfin, hT⟩ := hP
  exact ⟨T.mapModel (modelEmbedding κ hdn), hfin,
    T.intrinsic_mapModel (modelEmbedding κ hdn) hT⟩

/-- Postcomposition with a model inclusion preserves a genuine PL-isometry. -/
theorem PLIsometry.mapModel {κ : Geometry} {d n : ℕ}
    {P : Type u} [MetricSpace P] {f : P → Model κ d}
    (hf : PLIsometry κ d f) (e : ModelEmbedding κ d n) :
    PLIsometry κ n (e.toFun ∘ f) := by
  obtain ⟨hcont, T, hT⟩ := hf
  refine ⟨e.isometry.continuous.comp hcont, T.mapModel e, ?_⟩
  intro σ hσ x hx y hy
  exact (e.isometry.dist_eq _ _).trans (hT σ hσ x hx y hy)

end ArchivePLGeometry
