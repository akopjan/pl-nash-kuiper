module

public import PLGeometry.Definitions
public import BrehmApprox.SphericalCells
public import BrehmApprox.HyperbolicTopology
public import BrehmApprox.IntrinsicChains
public import Mathlib.Analysis.Convex.Topology

/-!
# Consequences of the concrete polyhedral definitions

The cells are compact genuine model simplices. A finite triangulation makes
the source compact, and its intrinsic metric turns cellwise metric estimates
into global estimates. None of these results assumes an initial folding.
-/

@[expose] public section
noncomputable section

namespace ArchivePLGeometry

universe u v

local instance basicLocalInstance1 (α : Type*) : DecidableEq α := Classical.decEq α

theorem compact_hull (κ : Geometry) (n : ℕ) (V : Finset (Model κ n))
    (hV : simplexVertices κ n V) : IsCompact (hull κ n V) := by
  cases κ with
  | euclidean => exact V.finite_toSet.isCompact_convexHull ℝ
  | spherical => exact BrehmApprox.isCompact_sphericalCell V hV.1
  | hyperbolic => exact BrehmApprox.isCompact_hyperbolicCell V

namespace Triangulation

variable {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]
    (T : Triangulation κ n P)

theorem chart_mem_hull {σ : Finset P} (hσ : σ ∈ T.simplices)
    {x : P} (hx : x ∈ T.cell σ) :
    T.chart σ x ∈ hull κ n (σ.image (T.chart σ)) := by
  rw [← T.image_cell σ hσ]
  exact Set.mem_image_of_mem _ hx

/-- The bundled metric identification of one source simplex with its model. -/
def cellChart (σ : Finset P) (hσ : σ ∈ T.simplices) :
    T.cell σ ≃ᵢ hull κ n (σ.image (T.chart σ)) := by
  let q : T.cell σ → hull κ n (σ.image (T.chart σ)) :=
    fun x => ⟨T.chart σ x, T.chart_mem_hull hσ x.property⟩
  have hq : Isometry q := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    exact T.isometry_cell σ hσ x x.property y y.property
  have hsurj : Function.Surjective q := by
    intro y
    have hy : (y : Model κ n) ∈ T.chart σ '' T.cell σ := by
      rw [T.image_cell σ hσ]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact { Equiv.ofBijective q ⟨hq.injective, hsurj⟩ with isometry_toFun := hq }

@[simp] theorem cellChart_apply (σ : Finset P) (hσ : σ ∈ T.simplices)
    (x : T.cell σ) : (T.cellChart σ hσ x : Model κ n) = T.chart σ x := rfl

theorem compact_cell (σ : Finset P) (hσ : σ ∈ T.simplices) :
    IsCompact (T.cell σ) := by
  let : CompactSpace (hull κ n (σ.image (T.chart σ))) :=
    isCompact_iff_compactSpace.mp (compact_hull κ n _ (T.simplex σ hσ))
  exact isCompact_iff_compactSpace.mpr (T.cellChart σ hσ).symm.toHomeomorph.compactSpace

theorem closed_cell (σ : Finset P) (hσ : σ ∈ T.simplices) :
    IsClosed (T.cell σ) := (T.compact_cell σ hσ).isClosed

theorem cell_mono {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτσ : τ ⊆ σ) :
    T.cell τ ⊆ T.cell σ := by
  have ht := T.faces σ hσ τ hτσ
  have he := T.intersection τ ht σ hσ
  rw [Finset.inter_eq_left.mpr hτσ] at he
  exact Set.inter_eq_left.mp he

theorem compactSpace (hfin : T.simplices.Finite) : CompactSpace P := by
  have hc : IsCompact (⋃ σ ∈ T.simplices, T.cell σ) :=
    hfin.isCompact_biUnion (fun σ hσ => T.compact_cell σ hσ)
  have he : (⋃ σ ∈ T.simplices, T.cell σ) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨σ, hσ, hx⟩ := T.cover x
    exact ⟨σ, hσ, hx⟩
  exact isCompact_univ_iff.mp (he ▸ hc)

/-- The explicit source definition has precisely the cell-chain metric used
by the metric gluing lemmas. -/
theorem intrinsic_iff_chainGenerated :
    Intrinsic T ↔ BrehmApprox.ChainGenerated (fun σ : T.simplices => T.cell σ.val) := by
  constructor <;> intro h x y ε hε
  · obtain ⟨m, z, h0, hm, hc, hcost⟩ := h x y ε hε
    refine ⟨m, z, h0, hm, ?_, hcost⟩
    intro j hj
    obtain ⟨σ, hσ, hx, hy⟩ := hc j hj
    exact ⟨⟨σ, hσ⟩, hx, hy⟩
  · obtain ⟨m, z, h0, hm, hc, hcost⟩ := h x y ε hε
    refine ⟨m, z, h0, hm, ?_, hcost⟩
    intro j hj
    obtain ⟨σ, hx, hy⟩ := hc j hj
    exact ⟨σ.val, σ.property, hx, hy⟩

theorem lipschitzWith_of_cellwise {Y : Type v} [MetricSpace Y]
    (hT : Intrinsic T) {f : P → Y} {L : NNReal}
    (hf : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (f x) (f y) ≤ L * dist x y) : LipschitzWith L f := by
  exact BrehmApprox.lipschitzWith_of_cellwise
    (T.intrinsic_iff_chainGenerated.mp hT) (fun σ => hf σ.val σ.property)

theorem short_of_isometric_cells {Y : Type v} [MetricSpace Y]
    (hT : Intrinsic T) {f : P → Y}
    (hf : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (f x) (f y) = dist x y) : LipschitzWith 1 f := by
  apply T.lipschitzWith_of_cellwise hT
  intro σ hσ x hx y hy
  simp only [NNReal.coe_one, one_mul, hf σ hσ x hx y hy, le_refl]

end Triangulation

theorem IsFinitePolyhedron.compactSpace {κ : Geometry} {n : ℕ}
    {P : Type u} [MetricSpace P] (hP : IsFinitePolyhedron κ n P) : CompactSpace P := by
  obtain ⟨T, hfin, _⟩ := hP
  exact T.compactSpace hfin

end ArchivePLGeometry
