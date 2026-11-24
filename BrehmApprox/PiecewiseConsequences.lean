module

public import BrehmApprox.GluedApproximation
public import Mathlib.Topology.Compactness.Compact

/-!
# Consequences of the actual finite polyhedral isometry certificate

The certificate has genuine compact isometric pieces. In particular its fibers
are finite, and near each point the map preserves distance from that point.
These facts require no triangulation convention or additional geometric axiom.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace BrehmApprox

universe u v
variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good} {q f : P → X}

/-- Each actual source piece is compact, by its isometry to a compact model
polytope. -/
theorem compact_of_polyhedral_isometric_piece {B : Set P}
    (hB : M.Polytope (q '' B))
    (hq : ∀ x ∈ B, ∀ y ∈ B, dist (q x) (q y) = dist x y) : IsCompact B := by
  let qB : B → X := fun x => q x
  have hi : Isometry qB := Isometry.of_dist_eq (fun x y => hq x x.property y y.property)
  have himage : qB '' (Set.univ : Set B) = q '' B := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have hc : IsCompact (Set.univ : Set B) := hi.isEmbedding.isCompact_iff.mpr
    (himage.symm ▸ M.compact _ hB)
  exact isCompact_iff_isCompact_univ.mpr hc

namespace PolyhedralPiecewiseIsometry

/-- A finite polyhedral piecewise isometry cannot collapse an infinite set
to one point. -/
theorem finite_fiber (hf : PolyhedralPiecewiseIsometry M q f) (y : X) :
    (f ⁻¹' {y}).Finite := by
  classical
  obtain ⟨S, hcover, hpieces⟩ := hf
  have hfinite : (⋃ B ∈ S, B ∩ f ⁻¹' {y}).Finite := by
    apply S.finite_toSet.biUnion
    intro B hB
    apply Set.Subsingleton.finite
    intro a ha b hb
    apply eq_of_dist_eq_zero
    have hfa : f a = y := ha.2
    have hfb : f b = y := hb.2
    have he := (hpieces B hB).2 a ha.1 b hb.1
    simpa only [hfa, hfb, dist_self] using he.2.symm
  apply hfinite.subset
  intro x hx
  obtain ⟨B, hB, hxB⟩ := hcover x
  exact Set.mem_iUnion₂.mpr ⟨B, hB, hxB, hx⟩

/-- A finite compact piece cover gives exact local preservation of distance
from each fixed source point. No claim of local injectivity is made. -/
theorem eventually_dist_eq (hf : PolyhedralPiecewiseIsometry M q f) (x : P) :
    ∀ᶠ y in 𝓝 x, dist (f y) (f x) = dist y x := by
  classical
  obtain ⟨S, hcover, hpieces⟩ := hf
  have hnear : ∀ᶠ y in 𝓝 x, ∀ B ∈ S, y ∈ B → x ∈ B := by
    apply (Filter.eventually_all_finset S).mpr
    intro B hB
    by_cases hx : x ∈ B
    · exact Filter.Eventually.of_forall (fun _ _ => hx)
    · have hclosed : IsClosed B := (compact_of_polyhedral_isometric_piece
        (hpieces B hB).1 (fun a ha b hb => ((hpieces B hB).2 a ha b hb).1)).isClosed
      have he : ∀ᶠ y in 𝓝 x, y ∈ Bᶜ := hclosed.isOpen_compl.mem_nhds hx
      exact he.mono (fun _ hy hmem => (hy hmem).elim)
  filter_upwards [hnear] with y hy
  obtain ⟨B, hB, hyB⟩ := hcover y
  exact ((hpieces B hB).2 y hyB x (hy B hB hyB)).2

/-- In particular, an isometrically parametrized nondegenerate interval
cannot be sent to a single point. -/
theorem not_constant_on_isometric_interval
    (hf : PolyhedralPiecewiseIsometry M q f) {a b : ℝ} (hab : a < b)
    (γ : Set.Icc a b → P) (hγ : Isometry γ) (y : X) :
    ¬ ∀ t, f (γ t) = y := by
  intro hconst
  have hfinite : (Set.range γ).Finite := (hf.finite_fiber y).subset (by
    rintro x ⟨t, rfl⟩
    exact hconst t)
  let : Fintype (Set.range γ) := hfinite.fintype
  let : Finite (Set.Icc a b) :=
    Finite.of_injective (fun t => (⟨γ t, Set.mem_range_self t⟩ : Set.range γ)) (by
      intro s t hst
      exact hγ.injective (congrArg Subtype.val hst))
  have hinfinite : (Set.Icc a b).Infinite := Set.Icc_infinite hab
  exact hinfinite (Set.toFinite _)

end PolyhedralPiecewiseIsometry
end BrehmApprox
