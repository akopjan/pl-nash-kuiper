module

public import BrehmApprox.FoldedGeometry
public import BrehmApprox.GluedModelMaps
public import Mathlib.Topology.ContinuousOn

/-!+# Pulling actual reference maps back through one common chart

Euclidean reference maps may have any metric target. Composing them with a
Lipschitz chart on an open domain gives the local references in the original
model, with the exact product constant. Whole-face agreement pulls back to an
open neighborhood; the chart need not be continuous outside its domain.
-/

@[expose] public section

namespace BrehmApprox

universe u v w

variable {X : Type u} [MetricSpace X] {E : Type v} [MetricSpace E]
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good} {N : ℕ}

namespace PolyhedralFaceData

variable (D : PolyhedralFaceData M N)

/-- Explicit pullback construction; no collar or approximation data are
inserted into this definition. -/
def referencesFromChart (coreE : Fin N → Set E) (Φ : X → E) (V : Set X)
    (hV : IsOpen V) (hcoreV : ∀ i, D.core i ⊆ V) (hΦ : ContinuousOn Φ V)
    {A B : NNReal}
    (hΦLip : ∀ x ∈ V, ∀ y ∈ V, dist (Φ x) (Φ y) ≤ A * dist x y)
    (hcore : ∀ i, Set.MapsTo Φ (D.core i) (coreE i))
    (u : Fin N → E → X) (hu : ∀ i, LipschitzWith B (u i))
    (hagree : ∀ i j, D.faceLE i j → ∃ U : Set E, IsOpen U ∧ coreE i ⊆ U ∧
      ∀ z ∈ U, u i z = u j z) : D.LocalReferences ((B : ℝ) * A) where
  reference := fun i x => u i (Φ x)
  domain := fun _ => V
  open_domain := fun _ => hV
  core_domain := hcoreV
  reference_short := by
    intro i x hx y hy
    calc
      dist (u i (Φ x)) (u i (Φ y)) ≤ B * dist (Φ x) (Φ y) := (hu i).dist_le_mul _ _
      _ ≤ B * (A * dist x y) := mul_le_mul_of_nonneg_left (hΦLip x hx y hy) B.coe_nonneg
      _ = ((B : ℝ) * A) * dist x y := by ring
  agreement := by
    intro i j hij
    obtain ⟨U, hU, hcoreU, huij⟩ := hagree i j hij
    refine ⟨V ∩ Φ ⁻¹' U, hΦ.isOpen_inter_preimage hV hU, ?_, ?_⟩
    · intro x hx
      exact ⟨hcoreV i hx, hcoreU (hcore i hx)⟩
    · intro x hx
      exact huij (Φ x) hx.2

end PolyhedralFaceData

namespace FoldedGeometry

variable {P : Type w} [MetricSpace P] (G : FoldedGeometry (P := P) M N)

/-- All remaining collar, finite Brehm, and final gluing steps apply directly
to references constructed in a common auxiliary chart. -/
theorem approximate_from_chart (coreE : Fin N → Set E) (Φ : X → E) (V : Set X)
    (hV : IsOpen V) (hcoreV : ∀ i, G.core i ⊆ V) (hΦ : ContinuousOn Φ V)
    {A B : NNReal}
    (hΦLip : ∀ x ∈ V, ∀ y ∈ V, dist (Φ x) (Φ y) ≤ A * dist x y)
    (hcore : ∀ i, Set.MapsTo Φ (G.core i) (coreE i))
    (u : Fin N → E → X) (hu : ∀ i, LipschitzWith B (u i))
    (hagree : ∀ i j, G.faceLE i j → ∃ U : Set E, IsOpen U ∧ coreE i ⊆ U ∧
      ∀ z ∈ U, u i z = u j z)
    (hBrehm : FiniteExtension Good) (hshort : (B : ℝ) * A < 1)
    (f : P → X) (hexact : ∀ i, ∀ x ∈ G.cell i, u i (Φ (G.fold x)) = f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → X, LipschitzWith 1 g ∧ PolyhedralPiecewiseIsometry M G.fold g ∧
      ∀ x, dist (g x) (f x) < ε := by
  let R := G.toPolyhedralFaceData.referencesFromChart coreE Φ V hV hcoreV hΦ
    hΦLip hcore u hu hagree
  exact G.approximate R hBrehm (mul_nonneg B.coe_nonneg A.coe_nonneg) hshort f hexact hε

/-- The same construction retaining its ambient model maps. -/
theorem approximate_from_chart_with_maps (coreE : Fin N → Set E) (Φ : X → E) (V : Set X)
    (hV : IsOpen V) (hcoreV : ∀ i, G.core i ⊆ V) (hΦ : ContinuousOn Φ V)
    {A B : NNReal}
    (hΦLip : ∀ x ∈ V, ∀ y ∈ V, dist (Φ x) (Φ y) ≤ A * dist x y)
    (hcore : ∀ i, Set.MapsTo Φ (G.core i) (coreE i))
    (u : Fin N → E → X) (hu : ∀ i, LipschitzWith B (u i))
    (hagree : ∀ i j, G.faceLE i j → ∃ U : Set E, IsOpen U ∧ coreE i ⊆ U ∧
      ∀ z ∈ U, u i z = u j z)
    (hBrehm : FiniteExtension Good) (hshort : (B : ℝ) * A < 1)
    (f : P → X) (hexact : ∀ i, ∀ x ∈ G.cell i, u i (Φ (G.fold x)) = f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : P → X, LipschitzWith 1 g ∧ G.RealizedByModelMaps g ∧
      ∀ x, dist (g x) (f x) < ε := by
  let R := G.toPolyhedralFaceData.referencesFromChart coreE Φ V hV hcoreV hΦ
    hΦLip hcore u hu hagree
  exact G.approximate_with_maps R hBrehm
    (mul_nonneg B.coe_nonneg A.coe_nonneg) hshort f hexact hε

end FoldedGeometry
end BrehmApprox
