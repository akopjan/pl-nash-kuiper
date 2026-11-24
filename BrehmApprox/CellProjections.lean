module

public import BrehmApprox.CellwiseLifting
public import BrehmApprox.ConvexProjection

/-!+# Actual source retractions and ambient reference maps

An inverse folding chart turns a model projection into a source retraction.
Composing a source map with that chart and projection gives an ambient reference
map, with a proved Lipschitz estimate. Compatibility of references from different
faces is not assumed by these constructions and must be proved separately.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

universe u v w

section Metric

variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
variable {Y : Type w} [MetricSpace Y]
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

/-- The source-valued inverse chart of a model map into one core. -/
def sourceFromCore (i : Fin N) (r : X → D.core i) (z : X) : P :=
  (S.cellChart i).symm (r z)

lemma sourceFromCore_mem (i : Fin N) (r : X → D.core i) (z : X) :
    S.sourceFromCore i r z ∈ S.cell i := ((S.cellChart i).symm (r z)).property

lemma fold_sourceFromCore (i : Fin N) (r : X → D.core i) (z : X) :
    S.fold (S.sourceFromCore i r z) = (r z : X) := S.cellChart_symm_apply i (r z)

lemma sourceFromCore_dist (i : Fin N) (r : X → D.core i) (z w : X) :
    dist (S.sourceFromCore i r z) (S.sourceFromCore i r w) = dist (r z) (r w) :=
  (S.cellChart i).symm.dist_eq (r z) (r w)

lemma sourceFromCore_lipschitz (i : Fin N) (r : X → D.core i) {C : NNReal}
    (hr : LipschitzWith C r) : LipschitzWith C (S.sourceFromCore i r) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [S.sourceFromCore_dist]
  exact hr.dist_le_mul z w

lemma sourceFromCore_continuous (i : Fin N) (r : X → D.core i) (hr : Continuous r) :
    Continuous (S.sourceFromCore i r) := by
  change Continuous (fun z => ((S.cellChart i).symm (r z) : P))
  exact continuous_subtype_val.comp ((S.cellChart i).symm.continuous.comp hr)

/-- Pull the model projection back to the source through its initial folding. -/
def retractFromCore (i : Fin N) (r : X → D.core i) (x : P) : P :=
  S.sourceFromCore i r (S.fold x)

lemma retractFromCore_mem (i : Fin N) (r : X → D.core i) (x : P) :
    S.retractFromCore i r x ∈ S.cell i := S.sourceFromCore_mem i r (S.fold x)

lemma fold_retractFromCore (i : Fin N) (r : X → D.core i) (x : P) :
    S.fold (S.retractFromCore i r x) = (r (S.fold x) : X) :=
  S.fold_sourceFromCore i r (S.fold x)

lemma retractFromCore_fix (i : Fin N) (r : X → D.core i)
    (hr : ∀ z ∈ D.core i, (r z : X) = z) {x : P} (hx : x ∈ S.cell i) :
    S.retractFromCore i r x = x := by
  apply S.fold_injective_cell i (S.retractFromCore_mem i r x) hx
  rw [S.fold_retractFromCore, hr _ (S.fold_mem_core hx)]

lemma retractFromCore_idempotent (i : Fin N) (r : X → D.core i)
    (hr : ∀ z ∈ D.core i, (r z : X) = z) (x : P) :
    S.retractFromCore i r (S.retractFromCore i r x) = S.retractFromCore i r x :=
  S.retractFromCore_fix i r hr (S.retractFromCore_mem i r x)

lemma retractFromCore_lipschitz (i : Fin N) (r : X → D.core i)
    (hintrinsic : ChainGenerated S.cell) {C : NNReal} (hr : LipschitzWith C r) :
    LipschitzWith C (S.retractFromCore i r) := by
  have h := (S.sourceFromCore_lipschitz i r hr).comp (S.fold_lipschitz hintrinsic)
  change LipschitzWith C (fun x => S.sourceFromCore i r (S.fold x))
  simpa only [mul_one, Function.comp_def] using h

/-- The ambient reference map defined from the actual source map. -/
def referenceFromCore (i : Fin N) (r : X → D.core i) (f : P → Y) (z : X) : Y :=
  f (S.sourceFromCore i r z)

omit [MetricSpace Y] in
lemma referenceFromCore_on_cell (i : Fin N) (r : X → D.core i)
    (hr : ∀ z ∈ D.core i, (r z : X) = z) (f : P → Y)
    {x : P} (hx : x ∈ S.cell i) : S.referenceFromCore i r f (S.fold x) = f x := by
  change f (S.retractFromCore i r x) = f x
  rw [S.retractFromCore_fix i r hr hx]

/-- A local estimate for the model projection suffices; this form also applies
to spherical projections on a small collar. -/
theorem referenceFromCore_lipschitzOn (i : Fin N) (r : X → D.core i) (f : P → Y)
    {U : Set X} {κ μ : ℝ} (hκ : 0 ≤ κ)
    (hf : ∀ x ∈ S.cell i, ∀ y ∈ S.cell i, dist (f x) (f y) ≤ κ * dist x y)
    (hr : ∀ z ∈ U, ∀ w ∈ U, dist (r z) (r w) ≤ μ * dist z w) :
    ∀ z ∈ U, ∀ w ∈ U,
      dist (S.referenceFromCore i r f z) (S.referenceFromCore i r f w) ≤
        (κ * μ) * dist z w := by
  intro z hz w hw
  calc
    _ ≤ κ * dist (S.sourceFromCore i r z) (S.sourceFromCore i r w) :=
      hf _ (S.sourceFromCore_mem i r z) _ (S.sourceFromCore_mem i r w)
    _ = κ * dist (r z) (r w) := by rw [S.sourceFromCore_dist]
    _ ≤ κ * (μ * dist z w) := mul_le_mul_of_nonneg_left (hr z hz w hw) hκ
    _ = (κ * μ) * dist z w := by ring

theorem referenceFromCore_lipschitz (i : Fin N) (r : X → D.core i) (f : P → Y)
    {κ μ : NNReal} (hf : LipschitzWith κ f) (hr : LipschitzWith μ r) :
    LipschitzWith (κ * μ) (S.referenceFromCore i r f) :=
  hf.comp (S.sourceFromCore_lipschitz i r hr)

end FoldedSource
end Metric

section Convex

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {P : Type v} [MetricSpace P] {Y : Type w} [MetricSpace Y]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

/-- The actual nearest-point map into a compact convex model core. -/
def convexCoreProjection (_S : FoldedSource D P) (i : Fin N) (hne : (D.core i).Nonempty)
    (hconvex : Convex ℝ (D.core i)) (z : E) : D.core i :=
  ⟨convexProjection (D.core i) hne (M.compact _ (D.polytope_core i)).isComplete hconvex z,
    convexProjection_mem _ _ _ _ z⟩

lemma convexCoreProjection_fix (i : Fin N) (hne : (D.core i).Nonempty)
    (hconvex : Convex ℝ (D.core i)) {z : E} (hz : z ∈ D.core i) :
    (S.convexCoreProjection i hne hconvex z : E) = z :=
  convexProjection_fix (D.core i) hne (M.compact _ (D.polytope_core i)).isComplete hconvex hz

lemma convexCoreProjection_short (i : Fin N) (hne : (D.core i).Nonempty)
    (hconvex : Convex ℝ (D.core i)) : LipschitzWith 1 (S.convexCoreProjection i hne hconvex) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  exact convexProjection_short (D.core i) hne (M.compact _ (D.polytope_core i)).isComplete
    hconvex z w

/-- A globally short source retraction, once the initial folding is given. -/
theorem convex_core_retraction (i : Fin N) (hne : (D.core i).Nonempty)
    (hconvex : Convex ℝ (D.core i)) (hintrinsic : ChainGenerated S.cell) :
    ∃ ρ : P → P, LipschitzWith 1 ρ ∧
      (∀ x, ρ x ∈ S.cell i) ∧ (∀ x ∈ S.cell i, ρ x = x) ∧
      (∀ x, ρ (ρ x) = ρ x) ∧
      ∀ x, S.fold (ρ x) = (S.convexCoreProjection i hne hconvex (S.fold x) : E) := by
  let r := S.convexCoreProjection i hne hconvex
  have hr : ∀ z ∈ D.core i, (r z : E) = z := fun z hz =>
    S.convexCoreProjection_fix i hne hconvex hz
  refine ⟨S.retractFromCore i r,
    S.retractFromCore_lipschitz i r hintrinsic (S.convexCoreProjection_short i hne hconvex),
    S.retractFromCore_mem i r, ?_, S.retractFromCore_idempotent i r hr,
    S.fold_retractFromCore i r⟩
  intro x hx
  exact S.retractFromCore_fix i r hr hx

/-- The Euclidean ambient reference has exactly the source Lipschitz constant.
No strict-constant Kirszbraun extension is required. -/
theorem convex_core_reference (i : Fin N) (hne : (D.core i).Nonempty)
    (hconvex : Convex ℝ (D.core i)) (f : P → Y) {κ : NNReal}
    (hf : LipschitzWith κ f) :
    ∃ u : E → Y, LipschitzWith κ u ∧ ∀ x ∈ S.cell i, u (S.fold x) = f x := by
  let r := S.convexCoreProjection i hne hconvex
  refine ⟨S.referenceFromCore i r f, ?_, ?_⟩
  · simpa only [mul_one] using
      S.referenceFromCore_lipschitz i r f hf (S.convexCoreProjection_short i hne hconvex)
  · intro x hx
    exact S.referenceFromCore_on_cell i r
      (fun z hz => S.convexCoreProjection_fix i hne hconvex hz) f hx

end FoldedSource
end Convex

end BrehmApprox
