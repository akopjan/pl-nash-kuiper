module

public import Compatibility.Models

/-!
# Continuity of the original PL-isometry predicate

A finite geometric subdivision is a finite closed cover. On each of its
cells, preservation of the original chart distance implies continuity in
the original model topology. Finite closed gluing gives global continuity.
-/

@[expose] public section
noncomputable section

namespace PLGeometry

theorem PLIsometry.continuous {κ : Geometry} {d m n : ℕ}
    {K : Polyhedron κ d m} {g : ↥K.K.space → Model κ n}
    (hg : PLIsometry K g) : Continuous g := by
  classical
  obtain ⟨T, hfinite, hspace, hcell⟩ := hg
  let : Finite T.faces := hfinite.to_subtype
  let C : T.faces → Set ↥K.K.space := fun σ =>
    {x | x.val ∈ cell σ.val}
  let F : ↥K.K.space → ArchivePLGeometry.Model κ.toArchive n :=
    fun x => modelEquiv κ n (g x)
  have hcover : (⋃ σ, C σ) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx : x.val ∈ T.space := hspace.symm ▸ x.property
    obtain ⟨σ, hσ, hxσ⟩ := _root_.Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨⟨σ, hσ⟩, hxσ⟩
  have hclosed : ∀ σ, IsClosed (C σ) := by
    intro σ
    exact (σ.val.finite_toSet.isCompact_convexHull ℝ).isClosed.preimage
      continuous_subtype_val
  have hF : Continuous F := by
    apply (locallyFinite_of_finite C).continuous hcover hclosed
    intro σ
    obtain ⟨τ, hτ, hsub, hiso⟩ := hcell σ.val σ.property
    let H : ↥K.K.space → ArchivePLGeometry.Model κ.toArchive d :=
      fun x => modelEquiv κ d ((K.simplex τ hτ).toModel x.val)
    have hH : ContinuousOn H (C σ) := by
      apply (continuous_modelEquiv κ d).comp_continuousOn
      exact (K.simplex τ hτ).continuous.comp continuous_subtype_val.continuousOn
        (fun x hx => hsub hx)
    have hmetric : ∀ x ∈ C σ, ∀ y ∈ C σ,
        dist (F x) (F y) = dist (H x) (H y) := by
      intro x hx y hy
      simpa only [F, H, modelEquiv_dist] using hiso x y hx hy
    rw [Metric.continuousOn_iff'] at hH ⊢
    intro x hx ε hε
    filter_upwards [hH x hx ε hε, self_mem_nhdsWithin] with y hy hyC
    rw [hmetric y hyC x hx]
    exact hy
  simpa only [F, Function.comp_def, Equiv.symm_apply_apply] using
    (continuous_modelEquiv_symm κ n).comp hF

end PLGeometry
