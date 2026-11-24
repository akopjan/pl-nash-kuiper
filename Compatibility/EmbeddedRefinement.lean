module

public import Compatibility.SourceAtlas
public import Compatibility.GeometricRealization

/-! A charted refinement of a component is realized inside the original
Euclidean ambient space. This works for any injective component embedding
and retains exactly the original simplex metrics. -/

@[expose] public section
noncomputable section

open Set

namespace PLGeometry.Polyhedron

universe u

variable {κ : Geometry} {n m : ℕ} (K : Polyhedron κ n m)
    {P : Type u} [TopologicalSpace P] [T2Space P]
    (U : ArchivePLGeometry.FiniteChartedComplex κ.toArchive n P)
    (e : P → ↥K.K.space) (he : Function.Injective e)
    (href : ∀ σ ∈ U.simplices, ∃ (τ : Finset (E m)) (hτ : τ ∈ K.K.faces),
      (∀ x ∈ U.cell σ, (e x).val ∈ cell τ) ∧
      ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
        dist (U.chart σ x) (U.chart σ y) =
          modelDist κ n ((K.simplex τ hτ).toModel (e x).val)
            ((K.simplex τ hτ).toModel (e y).val))

include href in
theorem embedded_refinement_hull (σ : Finset P) (hσ : σ ∈ U.simplices) :
    (fun x => (e x).val) '' U.cell σ =
      convexHull ℝ ((fun x => (e x).val) '' (σ : Set P)) := by
  classical
  obtain ⟨τ, hτ, hsub, hmetric⟩ := href σ hσ
  let a : P → E m := fun x => (e x).val
  let f : E m → ArchivePLGeometry.Model κ.toArchive n :=
    fun x => modelEquiv κ n ((K.simplex τ hτ).toModel x)
  have hf : Set.InjOn f (cell τ) := by
    intro x hx y hy hxy
    exact (K.simplex τ hτ).injective hx hy ((modelEquiv κ n).injective hxy)
  have hverts : (σ.image a : Set (E m)) ⊆ cell τ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hsub y (U.vertices_mem σ hσ hy)
  have hleft : a '' U.cell σ ⊆ cell τ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsub x hx
  have hright : convexHull ℝ (a '' (σ : Set P)) ⊆ cell τ := by
    apply convexHull_min ?_ (convex_convexHull ℝ _)
    simpa only [cell, Finset.coe_image] using hverts
  have hfold : ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (f (a x)) (f (a y)) = dist (U.chart σ x) (U.chart σ y) := by
    intro x hx y hy
    rw [hmetric x hx y hy]
    exact modelEquiv_dist κ n _ _
  have himage := (U.folding_cell_geometry σ hσ (f ∘ a) hfold).2
  have hconv := (K.simplex τ hτ).archive_image_hull (σ.image a) hverts
  apply (hf.image_eq_image_iff hleft hright).mp
  rw [Set.image_image]
  change (f ∘ a) '' U.cell σ = f '' convexHull ℝ (a '' (σ : Set P))
  rw [himage]
  simpa only [cell, Finset.coe_image, Finset.image_image, Function.comp_def,
    Set.image_image, f, a] using hconv.symm

include he href in
/-- The original PL condition, restricted to one embedded component. -/
theorem geometric_piece {r : ℕ} (g : ↥K.K.space → Model κ r)
    (hg : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      modelDist κ r (g (e x)) (g (e y)) = dist (U.chart σ x) (U.chart σ y)) :
    ∃ C : _root_.Geometry.SimplicialComplex ℝ (E m),
      C.faces.Finite ∧ C.space = Set.range (fun x => (e x).val) ∧
      ∀ σ ∈ C.faces, ∃ (τ : Finset (E m)) (hτ : τ ∈ K.K.faces),
        cell σ ⊆ cell τ ∧
        ∀ x y : ↥K.K.space, x.val ∈ cell σ → y.val ∈ cell σ →
          modelDist κ r (g x) (g y) =
            modelDist κ n ((K.simplex τ hτ).toModel x.val)
              ((K.simplex τ hτ).toModel y.val) := by
  classical
  let a : P → E m := fun x => (e x).val
  have ha : Function.Injective a := Subtype.val_injective.comp he
  have hhull := K.embedded_refinement_hull U e href
  let C := ChartedRealization.complex U a ha hhull
  refine ⟨C, ChartedRealization.complex_finite U a ha hhull,
    ChartedRealization.complex_space U a ha hhull, ?_⟩
  intro σ hσ
  obtain ⟨V, hV, rfl⟩ := ChartedRealization.face_origin U a ha hhull hσ
  obtain ⟨τ, hτ, hsub, hmetric⟩ := href V hV
  have hgeo : a '' U.cell V = cell (V.image a) := by
    simpa only [cell, Finset.coe_image] using hhull V hV
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro x hx
    rw [← hgeo] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hsub y hy
  · intro x y hx hy
    rw [← hgeo] at hx hy
    obtain ⟨x', hx', hxx'⟩ := hx
    obtain ⟨y', hy', hyy'⟩ := hy
    have hexx : e x' = x := Subtype.ext hxx'
    have heyy : e y' = y := Subtype.ext hyy'
    rw [← hexx, ← heyy, hg V hV x' hx' y' hy', hmetric x' hx' y' hy']

end PLGeometry.Polyhedron
