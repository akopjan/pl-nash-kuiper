module

public import PLGeometry.ModelMotions
public import BrehmApprox.FiniteDistanceIsometry
public import BrehmApprox.ModelPointRigidity
public import BrehmApprox.HyperbolicFiniteDistanceIsometry

/-!
# Cellwise isometries preserve simplex geometry

A metric isometry on one genuine model simplex is the restriction of an
ambient motion. Consequently it maps the cell onto the hull of its vertex
images and preserves simplex nondegeneracy. These facts are proved from
finite vertex distances and are not extra folding hypotheses.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.Triangulation

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]

local instance cellRigidityDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance cellRigidityModelDecidableEq : DecidableEq (Model κ n) := Classical.decEq _
local instance cellRigidityEDecidableEq : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
local instance cellRigiditySDecidableEq : DecidableEq (GeodesicSphere n) := Classical.decEq _
local instance cellRigidityHDecidableEq : DecidableEq (HyperbolicSpace n) := Classical.decEq _

def vertexChartEmbedding (T : Triangulation κ n P) (σ : Finset P) (hσ : σ ∈ T.simplices) :
    σ ↪ σ.image (T.chart σ) where
  toFun v := ⟨T.chart σ v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
  inj' := by
    intro v w hvw
    apply Subtype.ext
    apply dist_eq_zero.mp
    rw [← T.isometry_cell σ hσ v.val (T.vertices_mem σ hσ v.property)
      w.val (T.vertices_mem σ hσ w.property)]
    have he := congrArg (fun z : σ.image (T.chart σ) => z.val) hvw
    change T.chart σ v.val = T.chart σ w.val at he
    rw [he, dist_self]

theorem exists_euclidean_cell_motion (T : Triangulation .euclidean n P)
    (σ : Finset P) (hσ : σ ∈ T.simplices) (q : P → Model .euclidean n)
    (hq : ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ, dist (q x) (q y) = dist x y) :
    ∃ r : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x ∈ T.cell σ, r (T.chart σ x) = q x := by
  have hverts : AffineIndependent ℝ
      ((↑) : σ.image (T.chart σ) → EuclideanSpace ℝ (Fin n)) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using T.simplex σ hσ
  have hv := hverts.comp_embedding (T.vertexChartEmbedding σ hσ)
  obtain ⟨r, hr⟩ := exists_ambient_distance_isometry
    (fun v : σ => T.chart σ v.val) (fun v : σ => q v.val) hv (by
      intro v w
      rw [T.isometry_cell σ hσ v.val (T.vertices_mem σ hσ v.property)
        w.val (T.vertices_mem σ hσ w.property),
        hq v.val (T.vertices_mem σ hσ v.property) w.val (T.vertices_mem σ hσ w.property)])
  refine ⟨r, fun x hx => ?_⟩
  apply affineIsometry_eq_of_vertex_distances r (T.chart_mem_hull hσ hx)
  intro v hv
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  rw [hr ⟨z, hz⟩, hq x hx z (T.vertices_mem σ hσ hz),
    T.isometry_cell σ hσ x hx z (T.vertices_mem σ hσ hz)]

theorem exists_spherical_cell_motion (T : Triangulation .spherical n P)
    (σ : Finset P) (hσ : σ ∈ T.simplices) (q : P → Model .spherical n)
    (hq : ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ, dist (q x) (q y) = dist x y) :
    ∃ r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      ∀ x ∈ T.cell σ, GeodesicSphere.mapEquiv r (T.chart σ x) = q x := by
  have hverts : LinearIndependent ℝ
      (fun v : σ.image (T.chart σ) => v.val.val) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using (T.simplex σ hσ).2
  have hv := hverts.comp (T.vertexChartEmbedding σ hσ) (T.vertexChartEmbedding σ hσ).injective
  obtain ⟨r, hr⟩ := exists_spherical_vertex_motion
    (fun v : σ => T.chart σ v.val) (fun v : σ => q v.val) hv (by
      intro v w
      rw [T.isometry_cell σ hσ v.val (T.vertices_mem σ hσ v.property)
        w.val (T.vertices_mem σ hσ w.property),
        hq v.val (T.vertices_mem σ hσ v.property) w.val (T.vertices_mem σ hσ w.property)])
  refine ⟨r, fun x hx => ?_⟩
  apply sphericalMotion_eq_of_vertex_distances r (T.chart_mem_hull hσ hx)
  intro v hv
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  rw [hr ⟨z, hz⟩, hq x hx z (T.vertices_mem σ hσ hz),
    T.isometry_cell σ hσ x hx z (T.vertices_mem σ hσ hz)]

theorem exists_hyperbolic_cell_motion (T : Triangulation .hyperbolic n P)
    (σ : Finset P) (hσ : σ ∈ T.simplices) (q : P → Model .hyperbolic n)
    (hq : ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ, dist (q x) (q y) = dist x y) :
    ∃ r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n,
      ∀ x ∈ T.cell σ, r (T.chart σ x) = q x := by
  have hverts : LinearIndependent ℝ
      (fun v : σ.image (T.chart σ) => HyperbolicSpace.lift v.val) := by
    simpa only [simplexVertices, Finset.coe_sort_coe] using T.simplex σ hσ
  have hv := hverts.comp (T.vertexChartEmbedding σ hσ) (T.vertexChartEmbedding σ hσ).injective
  obtain ⟨r, hr⟩ := HyperbolicSpace.exists_vertex_motion
    (fun v : σ => T.chart σ v.val) (fun v : σ => q v.val) hv (by
      intro v w
      rw [T.isometry_cell σ hσ v.val (T.vertices_mem σ hσ v.property)
        w.val (T.vertices_mem σ hσ w.property),
        hq v.val (T.vertices_mem σ hσ v.property) w.val (T.vertices_mem σ hσ w.property)])
  refine ⟨r, fun x hx => ?_⟩
  apply hyperbolicMotion_eq_of_vertex_distances r (T.chart_mem_hull hσ hx)
  intro v hv
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  rw [hr ⟨z, hz⟩, hq x hx z (T.vertices_mem σ hσ hz),
    T.isometry_cell σ hσ x hx z (T.vertices_mem σ hσ hz)]

theorem exists_cell_model_embedding (T : Triangulation κ n P)
    (σ : Finset P) (hσ : σ ∈ T.simplices) (q : P → Model κ n)
    (hq : ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ, dist (q x) (q y) = dist x y) :
    ∃ R : ModelEmbedding κ n n, ∀ x ∈ T.cell σ, R.toFun (T.chart σ x) = q x := by
  cases κ with
  | euclidean =>
    obtain ⟨r, hr⟩ := T.exists_euclidean_cell_motion σ hσ q hq
    exact ⟨euclideanMotionEmbedding r, hr⟩
  | spherical =>
    obtain ⟨r, hr⟩ := T.exists_spherical_cell_motion σ hσ q hq
    exact ⟨sphericalMotionEmbedding r, hr⟩
  | hyperbolic =>
    obtain ⟨r, hr⟩ := T.exists_hyperbolic_cell_motion σ hσ q hq
    exact ⟨hyperbolicMotionEmbedding r, hr⟩

/-- A cellwise metric isometry has the genuine simplex images required for
finite folded face data. -/
theorem folding_cell_geometry (T : Triangulation κ n P)
    (σ : Finset P) (hσ : σ ∈ T.simplices) (q : P → Model κ n)
    (hq : ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ, dist (q x) (q y) = dist x y) :
    simplexVertices κ n (σ.image q) ∧ q '' T.cell σ = hull κ n (σ.image q) := by
  obtain ⟨R, hR⟩ := T.exists_cell_model_embedding σ hσ q hq
  have hv : (σ.image (T.chart σ)).image R.toFun = σ.image q := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    exact hR x (T.vertices_mem σ hσ hx)
  refine ⟨?_, ?_⟩
  · rw [← hv]
    exact R.simplex_image _ (T.simplex σ hσ)
  · calc
      q '' T.cell σ = R.toFun '' (T.chart σ '' T.cell σ) := by
        rw [Set.image_image]
        apply Set.image_congr
        intro x hx
        exact (hR x hx).symm
      _ = R.toFun '' hull κ n (σ.image (T.chart σ)) := by rw [T.image_cell σ hσ]
      _ = hull κ n ((σ.image (T.chart σ)).image R.toFun) := R.image_hull _
      _ = hull κ n (σ.image q) := by rw [hv]

end ArchivePLGeometry.Triangulation
