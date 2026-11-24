module

public import BrehmApprox.CellProjections
public import BrehmApprox.NearestFaceSelection

/-!+# Whole-face agreement of references from local flattening

Actual inverse source charts are used throughout. Near each point of a face,
local constancy on fibers of one lower-face retraction and the proved local
nearest-projection identities imply equality of two ambient references.
Taking the interior of their equality set gives one open neighborhood of the
entire closed face. No uniform neighborhood radius is assumed.
-/

@[expose] public section

open scoped Topology
open Filter

namespace BrehmApprox

universe u v w

variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
variable {Y : Type w}
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

lemma retract_sourceFromCore (k i : Fin N) (rk : X → D.core k) (ri : X → D.core i)
    {z : X} (hcomm : (rk (ri z) : X) = (rk z : X)) :
    S.retractFromCore k rk (S.sourceFromCore i ri z) = S.sourceFromCore k rk z := by
  apply S.fold_injective_cell k (S.retractFromCore_mem k rk _)
    (S.sourceFromCore_mem k rk z)
  rw [S.fold_retractFromCore, S.fold_sourceFromCore, S.fold_sourceFromCore]
  exact hcomm

/-- One reference agrees locally with the lower-face reference whenever the
source map is flat along that retraction and the model projections commute
locally. All maps in the conclusion are the explicitly constructed references. -/
theorem referenceFromCore_eventuallyEq_of_flat
    (k i : Fin N) (rk : X → D.core k) (ri : X → D.core i) (f : P → Y)
    (hri : Continuous ri) (hfix : ∀ z ∈ D.core i, (ri z : X) = z)
    {p : P} (hp : p ∈ S.cell i)
    (hflat : f =ᶠ[𝓝 p] (fun x => f (S.retractFromCore k rk x)))
    (hcomm : (fun z => (rk (ri z) : X)) =ᶠ[𝓝 (S.fold p)] (fun z => (rk z : X))) :
    S.referenceFromCore i ri f =ᶠ[𝓝 (S.fold p)] S.referenceFromCore k rk f := by
  have hgp : S.sourceFromCore i ri (S.fold p) = p := S.retractFromCore_fix i ri hfix hp
  have hgt : Tendsto (S.sourceFromCore i ri) (𝓝 (S.fold p)) (𝓝 p) := by
    have hcont : ContinuousAt (S.sourceFromCore i ri) (S.fold p) :=
      (S.sourceFromCore_continuous i ri hri).continuousAt
    simpa only [hgp] using hcont.tendsto
  have hsource :
      (fun z => S.retractFromCore k rk (S.sourceFromCore i ri z)) =ᶠ[𝓝 (S.fold p)]
        S.sourceFromCore k rk := by
    filter_upwards [hcomm] with z hz
    exact S.retract_sourceFromCore k i rk ri hz
  change (fun z => f (S.sourceFromCore i ri z)) =ᶠ[𝓝 (S.fold p)]
    (fun z => f (S.sourceFromCore k rk z))
  exact (hflat.comp_tendsto hgt).trans (hsource.fun_comp f)

/-- Two references agree near a source point after both are reduced to the
same local lower-face retraction. -/
theorem references_eventuallyEq_of_common_flat_projection
    (k i j : Fin N) (rk : X → D.core k) (ri : X → D.core i) (rj : X → D.core j)
    (f : P → Y) (hri : Continuous ri) (hrj : Continuous rj)
    (hfixi : ∀ z ∈ D.core i, (ri z : X) = z)
    (hfixj : ∀ z ∈ D.core j, (rj z : X) = z)
    {p : P} (hpi : p ∈ S.cell i) (hpj : p ∈ S.cell j)
    (hflat : f =ᶠ[𝓝 p] (fun x => f (S.retractFromCore k rk x)))
    (hcommi : (fun z => (rk (ri z) : X)) =ᶠ[𝓝 (S.fold p)] (fun z => (rk z : X)))
    (hcommj : (fun z => (rk (rj z) : X)) =ᶠ[𝓝 (S.fold p)] (fun z => (rk z : X))) :
    S.referenceFromCore i ri f =ᶠ[𝓝 (S.fold p)] S.referenceFromCore j rj f :=
  (S.referenceFromCore_eventuallyEq_of_flat k i rk ri f hri hfixi hpi hflat hcommi).trans
    (S.referenceFromCore_eventuallyEq_of_flat k j rk rj f hrj hfixj hpj hflat hcommj).symm

/-- Local agreements at all points give one open neighborhood of the whole
closed face. No compactness or unstated uniform choice of local radii is needed. -/
theorem whole_face_agreement_of_eventuallyEq (i : Fin N) (u v : X → Y)
    (hlocal : ∀ p ∈ S.cell i, u =ᶠ[𝓝 (S.fold p)] v) :
    ∃ U : Set X, IsOpen U ∧ D.core i ⊆ U ∧ ∀ z ∈ U, u z = v z := by
  refine ⟨interior {z | u z = v z}, isOpen_interior, ?_, ?_⟩
  · intro z hz
    rw [← S.image_cell i] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact mem_interior_iff_mem_nhds.mpr (hlocal p hp)
  · intro z hz
    exact interior_subset hz

/-- A finite family of local flat retractions suffices for the reference
agreement required by the final collar and Brehm induction. The projection
commutation hypotheses are supplied by geometric nearest-face selection. -/
theorem whole_face_reference_agreement
    (i j : Fin N) (hij : D.faceLE i j)
    (ri : X → D.core i) (rj : X → D.core j) (f : P → Y)
    (hri : Continuous ri) (hrj : Continuous rj)
    (hfixi : ∀ z ∈ D.core i, (ri z : X) = z)
    (hfixj : ∀ z ∈ D.core j, (rj z : X) = z)
    (hlocal : ∀ p ∈ S.cell i, ∃ k : Fin N, ∃ rk : X → D.core k,
      f =ᶠ[𝓝 p] (fun x => f (S.retractFromCore k rk x)) ∧
      (fun z => (rk (ri z) : X)) =ᶠ[𝓝 (S.fold p)] (fun z => (rk z : X)) ∧
      (fun z => (rk (rj z) : X)) =ᶠ[𝓝 (S.fold p)] (fun z => (rk z : X))) :
    ∃ U : Set X, IsOpen U ∧ D.core i ⊆ U ∧
      ∀ z ∈ U, S.referenceFromCore i ri f z = S.referenceFromCore j rj f z := by
  apply S.whole_face_agreement_of_eventuallyEq
  intro p hp
  obtain ⟨k, rk, hflat, hcommi, hcommj⟩ := hlocal p hp
  exact S.references_eventuallyEq_of_common_flat_projection k i j rk ri rj f
    hri hrj hfixi hfixj hp (S.cell_mono i j hij hp) hflat hcommi hcommj

end FoldedSource
end BrehmApprox
