module

public import BrehmApprox.IntrinsicChains
public import Mathlib.Topology.MetricSpace.Isometry

/-!+# Lifting compatible model maps to the actual polyhedral source

The maps are lifted through the inverse isometric charts of the given folding.
Only actual common faces are used for compatibility; extra intersections of
unrelated folded images impose no condition. The initial folding is an input,
and no claim of constructing that folding is hidden in this module.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

universe u v

variable {X : Type u} [MetricSpace X] {P : Type v} [MetricSpace P]
variable {Good : (X → X) → Prop} {M : PolytopeModel X Good}
variable {N : ℕ} {L : ℝ} {D : ReferenceAtlas M N L}

namespace FoldedSource

variable (S : FoldedSource D P)

lemma fold_injective_cell (i : Fin N) {x y : P}
    (hx : x ∈ S.cell i) (hy : y ∈ S.cell i) (hxy : S.fold x = S.fold y) : x = y := by
  apply dist_eq_zero.mp
  rw [← S.isometry_cell i x hx y hy, hxy, dist_self]

/-- The genuine isometric chart carried by one cell of the initial folding. -/
def cellChart (i : Fin N) : S.cell i ≃ᵢ D.core i := by
  let q : S.cell i → D.core i := fun x => ⟨S.fold x, S.fold_mem_core x.property⟩
  have hq : Isometry q := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    exact S.isometry_cell i x x.property y y.property
  have hsurj : Function.Surjective q := by
    intro y
    have hy : (y : X) ∈ S.fold '' S.cell i := by
      rw [S.image_cell i]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact { Equiv.ofBijective q ⟨hq.injective, hsurj⟩ with isometry_toFun := hq }

lemma cellChart_apply (i : Fin N) (x : S.cell i) :
    (S.cellChart i x : X) = S.fold x := rfl

lemma cellChart_symm_apply (i : Fin N) (y : D.core i) :
    S.fold ((S.cellChart i).symm y) = y := by
  exact congrArg Subtype.val ((S.cellChart i).apply_symm_apply y)

/-- Lift a core-preserving model map through a single actual source chart. -/
def liftOnCell (i : Fin N) (F : X → X) (hF : Set.MapsTo F (D.core i) (D.core i))
    (x : S.cell i) : S.cell i :=
  (S.cellChart i).symm ⟨F (S.fold x), hF (S.fold_mem_core x.property)⟩

lemma fold_liftOnCell (i : Fin N) (F : X → X)
    (hF : Set.MapsTo F (D.core i) (D.core i)) (x : S.cell i) :
    S.fold (S.liftOnCell i F hF x) = F (S.fold x) :=
  S.cellChart_symm_apply i _

/-- Compatibility is needed on the model of the actual common face, not on
every accidental intersection of two folded cell images. -/
def LiftCompatible (_S : FoldedSource D P) (F : Fin N → X → X) : Prop :=
  ∀ i j, ∀ x ∈ D.core (D.meet i j),
    F i x = F j x ∧ F i x ∈ D.core (D.meet i j)

lemma liftOnCell_agree (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i))
    (hcompat : S.LiftCompatible F) (i j : Fin N) {x : P}
    (hxi : x ∈ S.cell i) (hxj : x ∈ S.cell j) :
    (S.liftOnCell i (F i) (hF i) ⟨x, hxi⟩ : P) =
      S.liftOnCell j (F j) (hF j) ⟨x, hxj⟩ := by
  have hxm : x ∈ S.cell (D.meet i j) := S.intersection i j ⟨hxi, hxj⟩
  have hco := hcompat i j (S.fold x) (S.fold_mem_core hxm)
  have hzmem : F i (S.fold x) ∈ S.fold '' S.cell (D.meet i j) := by
    rw [S.image_cell (D.meet i j)]
    exact hco.2
  obtain ⟨z, hzm, hz⟩ := hzmem
  have hzi : z ∈ S.cell i := S.cell_mono _ _ (D.meet_le_left i j) hzm
  have hzj : z ∈ S.cell j := S.cell_mono _ _ (D.meet_le_right i j) hzm
  have hi : (S.liftOnCell i (F i) (hF i) ⟨x, hxi⟩ : P) = z := by
    apply S.fold_injective_cell i (S.liftOnCell i (F i) (hF i) ⟨x, hxi⟩).property hzi
    rw [S.fold_liftOnCell, hz]
  have hj : (S.liftOnCell j (F j) (hF j) ⟨x, hxj⟩ : P) = z := by
    apply S.fold_injective_cell j (S.liftOnCell j (F j) (hF j) ⟨x, hxj⟩).property hzj
    rw [S.fold_liftOnCell, hz, hco.1]
  exact hi.trans hj.symm

/-- The actual globally defined lift, chosen through a covering source cell. -/
def cellwiseLift (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i)) (x : P) : P :=
  S.liftOnCell (S.cover x).choose (F (S.cover x).choose) (hF (S.cover x).choose)
    ⟨x, (S.cover x).choose_spec⟩

lemma cellwiseLift_eq (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i))
    (hcompat : S.LiftCompatible F) (i : Fin N) {x : P} (hx : x ∈ S.cell i) :
    S.cellwiseLift F hF x = S.liftOnCell i (F i) (hF i) ⟨x, hx⟩ :=
  S.liftOnCell_agree F hF hcompat _ i (S.cover x).choose_spec hx

theorem cellwiseLift_mapsTo (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i))
    (hcompat : S.LiftCompatible F) (i : Fin N) :
    Set.MapsTo (S.cellwiseLift F hF) (S.cell i) (S.cell i) := by
  intro x hx
  rw [S.cellwiseLift_eq F hF hcompat i hx]
  exact (S.liftOnCell i (F i) (hF i) ⟨x, hx⟩).property

theorem fold_cellwiseLift (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i))
    (hcompat : S.LiftCompatible F) (i : Fin N) {x : P} (hx : x ∈ S.cell i) :
    S.fold (S.cellwiseLift F hF x) = F i (S.fold x) := by
  rw [S.cellwiseLift_eq F hF hcompat i hx]
  exact S.fold_liftOnCell i (F i) (hF i) ⟨x, hx⟩

theorem cellwiseLift_lipschitz (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i))
    (hcompat : S.LiftCompatible F) (hintrinsic : ChainGenerated S.cell)
    {C : NNReal} (hLip : ∀ i, ∀ x ∈ D.core i, ∀ y ∈ D.core i,
      dist (F i x) (F i y) ≤ C * dist x y) :
    LipschitzWith C (S.cellwiseLift F hF) := by
  apply lipschitzWith_of_cellwise hintrinsic
  intro i x hx y hy
  rw [← S.isometry_cell i _ (S.cellwiseLift_mapsTo F hF hcompat i hx)
    _ (S.cellwiseLift_mapsTo F hF hcompat i hy),
    S.fold_cellwiseLift F hF hcompat i hx, S.fold_cellwiseLift F hF hcompat i hy]
  exact (hLip i _ (S.fold_mem_core hx) _ (S.fold_mem_core hy)).trans_eq
    (congrArg (fun t => (C : ℝ) * t) (S.isometry_cell i x hx y hy))

theorem cellwiseLift_displacement (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i))
    (hcompat : S.LiftCompatible F) {δ : ℝ}
    (hdisp : ∀ i, ∀ x ∈ D.core i, dist (F i x) x ≤ δ) :
    ∀ x, dist (S.cellwiseLift F hF x) x ≤ δ := by
  intro x
  obtain ⟨i, hx⟩ := S.cover x
  rw [← S.isometry_cell i _ (S.cellwiseLift_mapsTo F hF hcompat i hx) x hx,
    S.fold_cellwiseLift F hF hcompat i hx]
  exact hdisp i _ (S.fold_mem_core hx)

lemma cellwiseLift_fix (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i))
    (hcompat : S.LiftCompatible F) {i : Fin N} {x : P} (hx : x ∈ S.cell i)
    (hfix : F i (S.fold x) = S.fold x) : S.cellwiseLift F hF x = x := by
  apply S.fold_injective_cell i (S.cellwiseLift_mapsTo F hF hcompat i hx) hx
  rw [S.fold_cellwiseLift F hF hcompat i hx, hfix]

theorem lift_cellwise_maps (F : Fin N → X → X)
    (hF : ∀ i, Set.MapsTo (F i) (D.core i) (D.core i))
    (hcompat : S.LiftCompatible F) (hintrinsic : ChainGenerated S.cell)
    {C : NNReal} (hLip : ∀ i, ∀ x ∈ D.core i, ∀ y ∈ D.core i,
      dist (F i x) (F i y) ≤ C * dist x y)
    {δ : ℝ} (hdisp : ∀ i, ∀ x ∈ D.core i, dist (F i x) x ≤ δ) :
    ∃ Q : P → P, LipschitzWith C Q ∧
      (∀ i, Set.MapsTo Q (S.cell i) (S.cell i)) ∧
      (∀ i, ∀ x ∈ S.cell i, S.fold (Q x) = F i (S.fold x)) ∧
      ∀ x, dist (Q x) x ≤ δ :=
  ⟨S.cellwiseLift F hF, S.cellwiseLift_lipschitz F hF hcompat hintrinsic hLip,
    S.cellwiseLift_mapsTo F hF hcompat, S.fold_cellwiseLift F hF hcompat,
    S.cellwiseLift_displacement F hF hcompat hdisp⟩

lemma fold_lipschitz (hintrinsic : ChainGenerated S.cell) : LipschitzWith 1 S.fold := by
  apply lipschitzWith_of_cellwise hintrinsic
  intro i x hx y hy
  simpa only [NNReal.coe_one, one_mul] using (S.isometry_cell i x hx y hy).le

end FoldedSource
end BrehmApprox
