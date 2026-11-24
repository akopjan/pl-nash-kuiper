module

public import Compatibility.ComponentApproximation
public import Compatibility.ComponentRefinement
public import Compatibility.SourceRefinementShortness
public import Compatibility.GeometricUnion
public import Compatibility.ModelDimension
public import PLGeometry.FiniteFoldingExistence

/-!
# Transfer to the original embedded-polyhedron formulation

The original finite simplicial complex is first folded into a small model
ball. Its finitely many cell components receive their intrinsic metrics.
Approximation on each component is followed by a refinement of its original
cells. These refinements are realized in the original Euclidean ambient
space and united into the geometric subdivision required by the Challenge.
-/

@[expose] public section
noncomputable section

open scoped NNReal

namespace PLGeometry.Compatibility

theorem approximation_equal_dimension (κ : Geometry) {m n : ℕ}
    (K : Polyhedron κ n m) (f : ↥K.K.space → Model κ n)
    (hf : Lipschitz K f 1)
    (hsphere : κ = .spherical →
      ((∃ L : ℝ≥0, L < 1 ∧ Lipschitz K f L) ∨
       ∃ o : Model κ n, ∀ x, modelDist κ n (f x) o < Real.pi / 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ↥K.K.space → Model κ n,
      PLIsometry K g ∧ ∀ x, modelDist κ n (g x) (f x) < ε := by
  classical
  cases isEmpty_or_nonempty ↥K.K.space with
  | inl hEmpty =>
    letI := hEmpty
    refine ⟨f, ⟨K.K, K.finite, rfl, ?_⟩, fun x => isEmptyElim x⟩
    intro σ hσ
    obtain ⟨v, hv⟩ := K.K.nonempty_of_mem_faces hσ
    exact isEmptyElim (⟨v, K.K.subset_space hσ hv⟩ : ↥K.K.space)
  | inr hNonempty =>
    obtain ⟨x₀⟩ := hNonempty
    obtain ⟨τ₀, hτ₀, _⟩ :=
      _root_.Geometry.SimplicialComplex.mem_space_iff.mp x₀.property
    let o := archiveBasepoint κ n
    obtain ⟨U, hU, q, hq, hiso, hsmall⟩ :=
      K.toArchiveChartedComplex.hasSmallFiniteFolding o (Real.pi / 2)
        (by positivity)
    let F : ↥K.K.space → ArchivePLGeometry.Model κ.toArchive n :=
      fun x => modelEquiv κ n (f x)
    have hF : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
        dist (F x) (F y) ≤ dist (U.chart σ x) (U.chart σ y) := by
      intro σ hσ x hx y hy
      simpa only [NNReal.coe_one, one_mul] using
        hf.archive_refinement_cellwise hU σ hσ x hx y hy
    have hFsphere : κ.toArchive = .spherical →
        ((∃ L : NNReal, L < 1 ∧
          ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
            dist (F x) (F y) ≤ (L : ℝ) * dist (U.chart σ x) (U.chart σ y)) ∨
          ∃ c : ArchivePLGeometry.Model κ.toArchive n,
            ∀ x, dist (F x) c < Real.pi / 2) := by
      intro hk
      have hk' : κ = .spherical := by cases κ <;> simp_all [Geometry.toArchive]
      rcases hsphere hk' with ⟨L, hL, hshort⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨L, hL, hshort.archive_refinement_cellwise hU⟩
      · refine Or.inr ⟨modelEquiv κ n c, ?_⟩
        intro x
        simpa only [F, modelEquiv_dist] using hc x
    have happ : ∀ c : U.ComponentIndex,
        ∃ g : U.IndexedComponent c → ArchivePLGeometry.Model κ.toArchive n,
          Continuous g ∧
          ∃ V : ArchivePLGeometry.FiniteChartedComplex κ.toArchive n
              (U.IndexedComponent c),
            V.Refines (U.componentChartedComplex c.out) ∧
            (∀ σ ∈ V.simplices, ∀ x ∈ V.cell σ, ∀ y ∈ V.cell σ,
              dist (g x) (g y) = dist (V.chart σ x) (V.chart σ y)) ∧
            ∀ x, dist (g x) (F x.val) < ε := by
      intro c
      exact approximate_component U q hq hiso o hsmall F hF hFsphere c hε
    choose gs hgs Vs hVs hisos hnears using happ
    let g : ↥K.K.space → Model κ n :=
      fun x => (modelEquiv κ n).symm (U.glueComponents gs x)
    have hnear : ∀ x, modelDist κ n (g x) (f x) < ε := by
      intro x
      rw [← modelEquiv_dist κ n (g x) (f x)]
      simpa only [g, Equiv.apply_symm_apply, F,
        ArchivePLGeometry.FiniteChartedComplex.glueComponents,
        ArchivePLGeometry.FiniteChartedComplex.pointInComponent] using
        hnears (U.componentIndex x) (U.pointInComponent x)
    have hpieces : ∀ c : U.ComponentIndex,
        ∃ C : _root_.Geometry.SimplicialComplex ℝ (E m),
          C.faces.Finite ∧
          C.space = Set.range (fun x : U.IndexedComponent c => x.val.val) ∧
          ∀ σ ∈ C.faces, ∃ (τ : Finset (E m)) (hτ : τ ∈ K.K.faces),
            cell σ ⊆ cell τ ∧
            ∀ x y : ↥K.K.space, x.val ∈ cell σ → y.val ∈ cell σ →
              modelDist κ n (g x) (g y) =
                modelDist κ n ((K.simplex τ hτ).toModel x.val)
                  ((K.simplex τ hτ).toModel y.val) := by
      intro c
      apply K.geometric_piece (Vs c) Subtype.val Subtype.val_injective
        (K.component_refinement U hU c (Vs c) (hVs c) τ₀ hτ₀) g
      intro σ hσ x hx y hy
      change modelDist κ n ((modelEquiv κ n).symm (U.glueComponents gs x.val))
        ((modelEquiv κ n).symm (U.glueComponents gs y.val)) = _
      rw [modelDist_modelEquiv_symm, U.glueComponents_apply gs c x,
        U.glueComponents_apply gs c y]
      exact hisos c σ hσ x hx y hy
    choose Cs hfin hspace hfaces using hpieces
    have hdisj : Pairwise (fun c d => Disjoint (Cs c).space (Cs d).space) := by
      intro c d hcd
      apply Set.disjoint_left.mpr
      intro x hx hy
      rw [hspace c] at hx
      rw [hspace d] at hy
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      have huv : u.val = v.val := Subtype.ext (hu.trans hv.symm)
      have hind := congrArg U.componentIndex huv
      rw [U.componentIndex_eq c u, U.componentIndex_eq d v] at hind
      exact hcd hind
    let C := GeometricUnion.complex Cs hdisj
    have hCspace : C.space = K.K.space := by
      rw [GeometricUnion.complex_space]
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
        rw [hspace c] at hc
        obtain ⟨y, rfl⟩ := hc
        exact y.val.property
      · intro hx
        obtain ⟨c, y, hy⟩ := U.indexedComponent_cover (⟨x, hx⟩ : ↥K.K.space)
        apply Set.mem_iUnion.mpr
        refine ⟨c, ?_⟩
        rw [hspace c]
        exact ⟨y, congrArg Subtype.val hy⟩
    refine ⟨g, ⟨C, GeometricUnion.complex_finite Cs hdisj hfin, hCspace, ?_⟩,
      hnear⟩
    intro σ hσ
    obtain ⟨c, hc⟩ := GeometricUnion.face_origin Cs hdisj hσ
    exact hfaces c σ hc

end PLGeometry.Compatibility
