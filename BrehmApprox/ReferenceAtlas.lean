module

public import BrehmApprox.CollarConstruction
public import BrehmApprox.PolytopeModels

/-!
# Approximation from compatible local reference maps

This theorem constructs the collars, proves their positive separation, chooses
all error budgets, and carries out the entire finite Brehm induction.

Its geometric input is a family of strictly short reference maps that agree
in open neighborhoods of common faces. Initial folding and compatible
flattening construct these maps. The final theorems in
`ArchivePLGeometry.PLNashKuiper` supply these data for arbitrary finite intrinsic
polyhedral sources.
-/

@[expose] public section

namespace BrehmApprox

universe u
variable {X : Type u} [MetricSpace X]

/-- A finite face system equipped with the local reference maps used after
flattening. There are no approximating maps or collar choices in this input. -/
structure ReferenceAtlas {Good : (X → X) → Prop} (M : PolytopeModel X Good)
    (N : ℕ) (L : ℝ) where
  faceLE : Fin N → Fin N → Prop
  le_refl : ∀ i, faceLE i i
  le_trans : ∀ i j k, faceLE i j → faceLE j k → faceLE i k
  index_strict : ∀ i j, faceLE i j → i ≠ j → i.val < j.val
  meet : Fin N → Fin N → Fin N
  meet_comm : ∀ i j, meet i j = meet j i
  meet_le_left : ∀ i j, faceLE (meet i j) i
  meet_le_right : ∀ i j, faceLE (meet i j) j
  core : Fin N → Set X
  polytope_core : ∀ i, M.Polytope (core i)
  core_mono : ∀ i j, faceLE i j → core i ⊆ core j
  core_inter : ∀ i j k, faceLE j i → faceLE k i → core j ∩ core k = core (meet j k)
  reference : Fin N → X → X
  domain : Fin N → Set X
  open_domain : ∀ i, IsOpen (domain i)
  core_domain : ∀ i, core i ⊆ domain i
  reference_short : ∀ i, ∀ x ∈ domain i, ∀ y ∈ domain i,
    dist (reference i x) (reference i y) ≤ L * dist x y
  agreement : ∀ i j, faceLE i j →
    ∃ U : Set X, IsOpen U ∧ core i ⊆ U ∧
      ∀ x ∈ U, reference i x = reference j x

namespace ReferenceAtlas

variable {N : ℕ} {Good : (X → X) → Prop} {L : ℝ}
variable {M : PolytopeModel X Good} (D : ReferenceAtlas M N L)

/-- The complete approximation result for a finite prepared reference atlas.
The three model-space specializations use proved polytope interfaces and the
corresponding proved finite Brehm extension theorem. -/
theorem approximate
    (hB : FiniteExtension Good) (hL0 : 0 ≤ L) (hL1 : L < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Fin N → X → X,
      (∀ i, Short (H i) ∧ Good (H i) ∧
        ∀ x ∈ D.core i, dist (H i x) (D.reference i x) < ε) ∧
      (∀ i j, D.faceLE i j → ∀ x ∈ D.core i, H j x = H i x) := by
  classical
  have hneighborhoods : ∀ i j, ∃ U : Set X,
      IsOpen U ∧ D.core i ⊆ U ∧
        (D.faceLE i j → ∀ x ∈ U, D.reference i x = D.reference j x) := by
    intro i j
    by_cases hij : D.faceLE i j
    · obtain ⟨U, hU, hKU, hagree⟩ := D.agreement i j hij
      exact ⟨U, hU, hKU, fun _ => hagree⟩
    · exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun h => (hij h).elim⟩
  choose U hU hKU hagree using hneighborhoods
  let allowed : Fin N → Set X := fun i =>
    ⋂ j, if D.faceLE i j then U i j ∩ D.domain j else Set.univ
  have hopen (i : Fin N) : IsOpen (allowed i) := by
    apply isOpen_iInter_of_finite
    intro j
    by_cases hij : D.faceLE i j
    · simpa [hij] using (hU i j).inter (D.open_domain j)
    · simp [hij]
  have hallowed (i : Fin N) : D.core i ⊆ allowed i := by
    intro x hx
    apply Set.mem_iInter.mpr
    intro j
    by_cases hij : D.faceLE i j
    · simp only [ite_eq_left hij, Set.mem_inter_iff]
      exact ⟨hKU i j hx, D.core_domain j (D.core_mono i j hij hx)⟩
    · simp [hij]
  let K : CoreNeighborhoodData X N M.Polytope := {
    faceLE := D.faceLE
    le_refl := D.le_refl
    index_strict := D.index_strict
    meet := D.meet
    meet_comm := D.meet_comm
    meet_le_left := D.meet_le_left
    meet_le_right := D.meet_le_right
    core := D.core
    compact_core := fun i => M.compact _ (D.polytope_core i)
    core_inter := D.core_inter
    allowed := allowed
    open_allowed := hopen
    core_allowed := hallowed
    basis := fun i T hT hKT => M.neighborhoods _ T (D.polytope_core i) hT hKT }
  obtain ⟨W, hW, hinter⟩ := K.exists_collars
  have hWallowed (i j : Fin N) (hij : D.faceLE i j) {x : X} (hx : x ∈ W i) :
      x ∈ U i j ∩ D.domain j := by
    have h := Set.mem_iInter.mp ((hW i).2.2.2 hx) j
    simpa only [ite_eq_left hij] using h
  let C : CollarData X N Good L := {
    faceLE := D.faceLE
    le_refl := D.le_refl
    le_trans := D.le_trans
    index_strict := D.index_strict
    meet := D.meet
    meet_le_left := D.meet_le_left
    meet_le_right := D.meet_le_right
    W := W
    compact_W := fun i => (hW i).2.1
    reference := D.reference
    reference_agree := fun i j hij x hx => hagree i j hij x (hWallowed i j hij hx).1
    reference_short := by
      intro i x y hx hy
      obtain ⟨j, hji, hxj⟩ := hx
      obtain ⟨k, hki, hyk⟩ := hy
      exact D.reference_short i x (hWallowed j i hji hxj).2
        y (hWallowed k i hki hyk).2
    determined := fun i f hf => M.determined _ f (hW i).1 hf
    interior_overlap := by
      intro i j k hji hki hjk hkj
      exact hinter j k ⟨⟨i, hji, hki⟩, hjk, hkj⟩ }
  obtain ⟨H, hH, hcompat⟩ := C.compatible_approximations hB hL0 hL1 hε
  have hcoreW (i : Fin N) : D.core i ⊆ W i :=
    fun x hx => interior_subset ((hW i).2.2.1 hx)
  exact ⟨H, fun i => ⟨(hH i).1, (hH i).2.1,
    fun x hx => (hH i).2.2 x (hcoreW i hx)⟩,
    fun i j hij x hx => hcompat i j hij x (hcoreW i hx)⟩

end ReferenceAtlas
end BrehmApprox
