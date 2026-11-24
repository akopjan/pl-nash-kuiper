module

public import Compatibility.Models
public import PLGeometry.Dimension

/-! # Dimension enlargement for the original Challenge

The coordinate inclusions from the completed proof are transported through
the exact model equivalences. The underlying geometric simplicial complex,
its intrinsic extended distance, and its PL-isometry predicate are unchanged.
-/

@[expose] public section
noncomputable section

namespace PLGeometry

local instance modelDimensionDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def modelEmbedding (κ : Geometry) {d n : ℕ} (hdn : d ≤ n)
    (x : Model κ d) : Model κ n :=
  (modelEquiv κ n).symm
    ((ArchivePLGeometry.modelEmbedding κ.toArchive hdn).toFun (modelEquiv κ d x))

@[simp]
theorem modelEmbedding_dist (κ : Geometry) {d n : ℕ} (hdn : d ≤ n)
    (x y : Model κ d) :
    modelDist κ n (modelEmbedding κ hdn x) (modelEmbedding κ hdn y) =
      modelDist κ d x y := by
  unfold modelEmbedding
  rw [modelDist_modelEquiv_symm,
    (ArchivePLGeometry.modelEmbedding κ.toArchive hdn).isometry.dist_eq,
    modelEquiv_dist]

theorem modelEmbedding_continuous (κ : Geometry) {d n : ℕ} (hdn : d ≤ n) :
    Continuous (modelEmbedding κ hdn) :=
  (continuous_modelEquiv_symm κ n).comp
    ((ArchivePLGeometry.modelEmbedding κ.toArchive hdn).isometry.continuous.comp
      (continuous_modelEquiv κ d))

theorem modelEmbedding_injective (κ : Geometry) {d n : ℕ} (hdn : d ≤ n) :
    Function.Injective (modelEmbedding κ hdn) :=
  (modelEquiv κ n).symm.injective.comp
    ((ArchivePLGeometry.modelEmbedding κ.toArchive hdn).isometry.injective.comp
      (modelEquiv κ d).injective)

theorem modelEmbedding_image_hull (κ : Geometry) {d n : ℕ} (hdn : d ≤ n)
    (V : Finset (Model κ d)) :
    modelEmbedding κ hdn '' hull κ d (V : Set (Model κ d)) =
      hull κ n (V.image (modelEmbedding κ hdn) : Set (Model κ n)) := by
  apply (modelEquiv κ n).injective.image_injective
  calc
    modelEquiv κ n '' (modelEmbedding κ hdn '' hull κ d (V : Set (Model κ d))) =
        (ArchivePLGeometry.modelEmbedding κ.toArchive hdn).toFun ''
          (modelEquiv κ d '' hull κ d (V : Set (Model κ d))) := by
      simp only [Set.image_image, Function.comp_def, modelEmbedding, Equiv.apply_symm_apply]
    _ = ArchivePLGeometry.hull κ.toArchive n
        ((V.image (modelEquiv κ d)).image
          (ArchivePLGeometry.modelEmbedding κ.toArchive hdn).toFun) := by
      rw [modelEquiv_image_hull,
        (ArchivePLGeometry.modelEmbedding κ.toArchive hdn).image_hull]
    _ = modelEquiv κ n ''
        hull κ n (V.image (modelEmbedding κ hdn) : Set (Model κ n)) := by
      rw [modelEquiv_image_hull]
      simp only [Finset.image_image, Function.comp_def, modelEmbedding, Equiv.apply_symm_apply]

namespace Simplex

abbrev raiseDimension {κ : Geometry} {d m n : ℕ} {σ : Finset (E m)}
    (S : Simplex κ d m σ) (hdn : d ≤ n) : Simplex κ n m σ where
  toModel := modelEmbedding κ hdn ∘ S.toModel
  continuous := (modelEmbedding_continuous κ hdn).comp_continuousOn S.continuous
  injective := fun _ hx _ hy h =>
    S.injective hx hy ((modelEmbedding_injective κ hdn) h)
  convex V hV := by
    change (fun x => modelEmbedding κ hdn (S.toModel x)) ''
      convexHull ℝ (V : Set (E m)) =
      hull κ n ((fun x => modelEmbedding κ hdn (S.toModel x)) '' (V : Set (E m)))
    rw [← Set.image_image (modelEmbedding κ hdn) S.toModel,
      S.convex V hV, ← Finset.coe_image,
      modelEmbedding_image_hull, Finset.coe_image, Finset.coe_image, Set.image_image]

end Simplex

namespace Polyhedron

abbrev raiseDimension {κ : Geometry} {d m n : ℕ}
    (K : Polyhedron κ d m) (hdn : d ≤ n) : Polyhedron κ n m where
  K := K.K
  finite := K.finite
  simplex σ hσ := (K.simplex σ hσ).raiseDimension hdn
  compatible := by
    intro σ τ hσ hτ x hx y hy
    change modelDist κ n (modelEmbedding κ hdn ((K.simplex σ hσ).toModel x))
        (modelEmbedding κ hdn ((K.simplex σ hσ).toModel y)) =
      modelDist κ n (modelEmbedding κ hdn ((K.simplex τ hτ).toModel x))
        (modelEmbedding κ hdn ((K.simplex τ hτ).toModel y))
    rw [modelEmbedding_dist, modelEmbedding_dist]
    exact K.compatible σ τ hσ hτ x hx y hy

@[simp]
theorem segmentEDist_raiseDimension {κ : Geometry} {d m n : ℕ}
    (K : Polyhedron κ d m) (hdn : d ≤ n) (x y : ↥K.K.space) :
    segmentEDist (K.raiseDimension hdn) x y = segmentEDist K x y := by
  simp only [segmentEDist, raiseDimension, Simplex.raiseDimension,
    Function.comp_apply, modelEmbedding_dist]

@[simp]
theorem intrinsicEDist_raiseDimension {κ : Geometry} {d m n : ℕ}
    (K : Polyhedron κ d m) (hdn : d ≤ n) (x y : ↥K.K.space) :
    intrinsicEDist (K.raiseDimension hdn) x y = intrinsicEDist K x y := by
  simp only [intrinsicEDist, segmentEDist_raiseDimension]

theorem lipschitz_raiseDimension_iff {κ : Geometry} {d m n r : ℕ}
    (K : Polyhedron κ d m) (hdn : d ≤ n)
    (f : ↥K.K.space → Model κ r) (L : NNReal) :
    Lipschitz (K.raiseDimension hdn) f L ↔ Lipschitz K f L := by
  simp only [Lipschitz, intrinsicEDist_raiseDimension]

theorem plIsometry_raiseDimension_iff {κ : Geometry} {d m n r : ℕ}
    (K : Polyhedron κ d m) (hdn : d ≤ n) (f : ↥K.K.space → Model κ r) :
    PLIsometry (K.raiseDimension hdn) f ↔ PLIsometry K f := by
  simp only [PLIsometry, raiseDimension, Simplex.raiseDimension,
    Function.comp_apply, modelEmbedding_dist]

end Polyhedron
end PLGeometry
