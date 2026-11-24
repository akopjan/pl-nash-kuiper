module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# The metric part of the Brehm approximation argument

`FiniteExtension Good` is the exact finite interpolation property used from
Brehm. The abstract lemmas take it as a hypothesis; the concrete instances
are proved in the three model geometries. `DeterminedOn` is the finite
rigidity property used in the relative extension argument, with its concrete
instances proved from model-isometric polyhedral pieces.
-/

@[expose] public section

namespace BrehmApprox

universe u
variable {X : Type u} [MetricSpace X]

/-- A distance nonincreasing map. -/
def Short (f : X → X) : Prop :=
  ∀ x y, dist (f x) (f y) ≤ dist x y

/-- Distance nonincrease on a specified subset. -/
def ShortOn (f : X → X) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ dist x y

/-- The finite interpolation conclusion of Brehm, with the regularity property
kept as a parameter. No interpolation on an arbitrary polyhedral source is
assumed. Both source and target here are the *same model metric space*. -/
def FiniteExtension (Good : (X → X) → Prop) : Prop :=
  ∀ (s : Finset X) (f : X → X), ShortOn f (s : Set X) →
    ∃ h : X → X, Short h ∧ Good h ∧ ∀ x ∈ s, h x = f x

/-- A finite collection of points determines a given map on a subset among
all short maps. This is proved for finite unions of Euclidean polyhedra. -/
def DeterminedOn (A : Set X) (g : X → X) : Prop :=
  ∃ V : Finset X, (V : Set X) ⊆ A ∧
    ∀ h : X → X, Short h → (∀ v ∈ V, h v = g v) →
      ∀ x ∈ A, h x = g x

lemma Short.shortOn {f : X → X} (hf : Short f) (s : Set X) : ShortOn f s :=
  fun x _ y _ => hf x y

lemma short_iff_lipschitz {f : X → X} : Short f ↔ LipschitzWith 1 f := by
  constructor
  · intro h
    exact LipschitzWith.of_dist_le_mul (by simpa [Short] using h)
  · intro h x y
    simpa using h.dist_le_mul x y

lemma Short.continuous {f : X → X} (hf : Short f) : Continuous f :=
  (short_iff_lipschitz.mp hf).continuous

lemma determinedOn_empty (g : X → X) : DeterminedOn (∅ : Set X) g := by
  refine ⟨∅, by simp, ?_⟩
  simp

end BrehmApprox
