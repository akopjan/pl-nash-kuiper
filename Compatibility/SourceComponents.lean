module

public import Compatibility.IntrinsicMetric
public import PLGeometry.ChartedIncidence

/-! # The finitely many connected cell components of a finite charted complex -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set BrehmApprox

namespace PLGeometry.Compatibility.CellComponents

universe u v
variable {P : Type u} {ι : Type v} (cell : ι → Set P)

/-- Two points are joined when a finite chain of source cells connects them. -/
def Joined (x y : P) : Prop := Nonempty (CellChain cell x y)

theorem joined_refl (x : P) : Joined cell x x := ⟨.nil x⟩
theorem joined_symm {x y : P} : Joined cell x y → Joined cell y x :=
  fun ⟨a⟩ => ⟨a.reverse⟩
theorem joined_trans {x y z : P} : Joined cell x y → Joined cell y z → Joined cell x z :=
  fun ⟨a⟩ ⟨b⟩ => ⟨a.append b⟩
theorem joined_of_cell (i : ι) {x y : P} (hx : x ∈ cell i) (hy : y ∈ cell i) :
    Joined cell x y := ⟨CellChain.single i hx hy⟩

def setoid : Setoid P where
  r := Joined cell
  iseqv := ⟨joined_refl cell, joined_symm cell, joined_trans cell⟩

abbrev Component (p : P) := {x : P // Joined cell p x}

def restrictedCell (p : P) (i : ι) : Set (Component cell p) :=
  {x | x.val ∈ cell i}

/-- Every chain stays in the component containing either endpoint. -/
def restrictChain (p : P) : {x y : P} → (a : CellChain cell x y) →
    (hx : Joined cell p x) → (hy : Joined cell p y) →
    CellChain (restrictedCell cell p) ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil x, hx, hy => CellChain.nil (cell := restrictedCell cell p) (⟨x, hx⟩ : Component cell p)
  | _, _, .cons i hx hy tail, hp, hz =>
    .cons i hx hy (restrictChain p tail (joined_trans cell hp (joined_of_cell cell i hx hy)) hz)

theorem restricted_connected (p : P) : ConnectedCellMetric.Connected (restrictedCell cell p) := by
  intro x y
  obtain ⟨a⟩ := joined_trans cell (joined_symm cell x.property) y.property
  exact ⟨restrictChain cell p a x.property y.property⟩

include cell in
theorem component_eq_union (hcover : ∀ x, ∃ i, x ∈ cell i) (p : P) :
    {x | Joined cell p x} = ⋃ (i : ι) (_ : ∃ x ∈ cell i, Joined cell p x), cell i := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨⟨x, hi, hx⟩, hi⟩⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨⟨y, hy, hpy⟩, hxi⟩ := mem_iUnion.mp hi
    exact joined_trans cell hpy (joined_of_cell cell i hy hxi)

variable [Finite ι]

theorem finite_components (hcover : ∀ x, ∃ i, x ∈ cell i) : Finite (Quotient (setoid cell)) := by
  classical
  let J := {i : ι // (cell i).Nonempty}
  let f : J → Quotient (setoid cell) := fun i => Quotient.mk _ i.property.choose
  apply Finite.of_surjective f
  intro a
  induction a using Quotient.inductionOn with
  | _ x =>
    obtain ⟨i, hi⟩ := hcover x
    let j : J := ⟨i, ⟨x, hi⟩⟩
    refine ⟨j, ?_⟩
    apply Quotient.sound
    exact joined_of_cell cell i j.property.choose_spec hi

variable [TopologicalSpace P] [T2Space P]
variable (hcompact : ∀ i, IsCompact (cell i)) (hcover : ∀ x, ∃ i, x ∈ cell i)

include hcompact hcover in
theorem compact_component (p : P) : IsCompact {x | Joined cell p x} := by
  rw [component_eq_union cell hcover p]
  exact isCompact_iUnion fun i => isCompact_iUnion fun _ => hcompact i

include hcompact hcover in
theorem compact_restrictedCell (p : P) (i : ι) : IsCompact (restrictedCell cell p i) :=
  (compact_component cell hcompact hcover p).isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hcompact i)

include hcover in
theorem restricted_cover (p : P) : ∀ x : Component cell p, ∃ i, x ∈ restrictedCell cell p i := by
  intro x
  exact hcover x.val

end PLGeometry.Compatibility.CellComponents

namespace ArchivePLGeometry.FiniteChartedComplex

open PLGeometry.Compatibility.CellComponents

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (U : FiniteChartedComplex κ n P)

abbrev CellComponent (p : P) := Component (fun σ : U.simplices => U.cell σ.val) p

local instance componentDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- Every cell whose vertices belong to one component belongs to it entirely. -/
theorem cell_subset_component (p : P) (σ : Finset (U.CellComponent p))
    (hσ : σ.image Subtype.val ∈ U.simplices) :
    ∀ x ∈ U.cell (σ.image Subtype.val),
      Joined (fun τ : U.simplices => U.cell τ.val) p x := by
  intro x hx
  have hne : σ.Nonempty := by
    by_contra h
    have he : σ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.image_empty, U.cell_empty (by simpa [he] using hσ)] at hx
    exact hx
  obtain ⟨v, hv⟩ := hne
  exact joined_trans _ v.property (joined_of_cell _ ⟨σ.image Subtype.val, hσ⟩
    (U.vertices_mem _ hσ (Finset.mem_image_of_mem Subtype.val hv)) hx)

/-- Forgetting the component subtype is a homeomorphism on every component cell. -/
def componentCellHomeomorph (p : P) (σ : Finset (U.CellComponent p))
    (hσ : σ.image Subtype.val ∈ U.simplices) :
    {x : U.CellComponent p // x.val ∈ U.cell (σ.image Subtype.val)} ≃ₜ
      U.cell (σ.image Subtype.val) where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, U.cell_subset_component p σ hσ x.val x.property⟩, x.property⟩
  left_inv x := by cases x; rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Restriction of the finite charted complex to one cell component. -/
def componentChartedComplex (p : P) : FiniteChartedComplex κ n (U.CellComponent p) where
  simplices := {σ | σ.image Subtype.val ∈ U.simplices}
  finite_simplices := U.finite_simplices.preimage
    (Finset.image_injective Subtype.val_injective).injOn
  cell σ := {x | x.val ∈ U.cell (σ.image Subtype.val)}
  chart σ x := U.chart (σ.image Subtype.val) x.val
  cover x := by
    classical
    obtain ⟨σ, hσ, hx⟩ := U.cover x.val
    have hvertices : ∀ v ∈ σ, Joined (fun τ : U.simplices => U.cell τ.val) p v := by
      intro v hv
      exact joined_trans _ x.property (joined_of_cell _ ⟨σ, hσ⟩ hx
        (U.vertices_mem σ hσ hv))
    let S := σ.subtype (Joined (fun τ : U.simplices => U.cell τ.val) p)
    have he : S.image Subtype.val = σ := by
      ext v
      constructor
      · rintro hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_subtype.mp hw
      · intro hv
        exact Finset.mem_image.mpr ⟨⟨v, hvertices v hv⟩, Finset.mem_subtype.mpr hv, rfl⟩
    exact ⟨S, by simpa [he] using hσ, by simpa [he] using hx⟩
  vertices_mem σ hσ x hx :=
    U.vertices_mem _ hσ (Finset.mem_image_of_mem Subtype.val hx)
  simplex σ hσ := by
    simpa only [Finset.image_image, Function.comp_def] using U.simplex _ hσ
  image_cell σ hσ := by
    calc
      _ = U.chart (σ.image Subtype.val) '' U.cell (σ.image Subtype.val) := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.val, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, U.cell_subset_component p σ hσ x hx⟩, hx, rfl⟩
      _ = _ := by
        simpa only [Finset.image_image, Function.comp_def] using U.image_cell _ hσ
  cellHomeomorph σ hσ :=
    (U.componentCellHomeomorph p σ hσ).trans
      ((U.cellHomeomorph _ hσ).trans (Homeomorph.setCongr (by
        simp only [Finset.image_image, Function.comp_def])))
  cellHomeomorph_apply σ hσ x := by
    exact U.cellHomeomorph_apply _ hσ ⟨x.val.val, x.property⟩
  faces σ hσ τ hτσ := U.faces _ hσ _ (Finset.image_subset_image hτσ)
  image_face σ hσ τ hτσ := by
    calc
      _ = U.chart (σ.image Subtype.val) '' U.cell (τ.image Subtype.val) := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.val, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, U.cell_subset_component p τ
            (U.faces _ hσ _ (Finset.image_subset_image hτσ)) x hx⟩, hx, rfl⟩
      _ = _ := by
        simpa only [Finset.image_image, Function.comp_def] using
          U.image_face _ hσ _ (Finset.image_subset_image hτσ)
  intersection σ hσ τ hτ := by
    letI : DecidableEq (U.CellComponent p) := Classical.decEq _
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    have hi : (σ ∩ τ).image (Subtype.val : U.CellComponent p → P) =
        σ.image Subtype.val ∩ τ.image Subtype.val :=
      Finset.image_inter σ τ Subtype.val_injective
    have hmem := congrArg (fun S : Finset P => x.val ∈ U.cell S) hi
    exact (Set.ext_iff.mp (U.intersection _ hσ _ hτ) x.val).trans (Iff.of_eq hmem.symm)
  metric_coherence σ hσ τ hτ x hx y hy :=
    U.metric_coherence _ hσ _ hτ x.val hx y.val hy

/-- An original cell meeting a component gives a cell of the restricted complex. -/
theorem exists_component_face (p : P) (σ : U.simplices)
    (x : U.CellComponent p) (hx : x.val ∈ U.cell σ.val) :
    ∃ τ ∈ (U.componentChartedComplex p).simplices,
      τ.image Subtype.val = σ.val := by
  classical
  have hvertices : ∀ v ∈ σ.val, Joined (fun τ : U.simplices => U.cell τ.val) p v := by
    intro v hv
    exact joined_trans _ x.property (joined_of_cell _ σ hx
      (U.vertices_mem σ.val σ.property hv))
  let S := σ.val.subtype (Joined (fun τ : U.simplices => U.cell τ.val) p)
  have he : S.image Subtype.val = σ.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_subtype.mp hw
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v, hvertices v hv⟩, Finset.mem_subtype.mpr hv, rfl⟩
  exact ⟨S, by simpa only [componentChartedComplex, Set.mem_setOf_eq, he] using σ.property, he⟩

theorem componentChartedComplex_connected (p : P) :
    ConnectedCellMetric.Connected (fun σ : (U.componentChartedComplex p).simplices =>
      (U.componentChartedComplex p).cell σ.val) := by
  intro x y
  obtain ⟨a⟩ := restricted_connected (fun σ : U.simplices => U.cell σ.val) p x y
  induction a with
  | nil x => exact ⟨.nil x⟩
  | @cons x y z i hx hy tail ih =>
    obtain ⟨σ, hσ, he⟩ := U.exists_component_face p i x hx
    obtain ⟨b⟩ := ih
    refine ⟨CellChain.cons ⟨σ, hσ⟩ ?_ ?_ b⟩
    · change x.val ∈ U.cell (σ.image Subtype.val)
      rwa [he]
    · change y.val ∈ U.cell (σ.image Subtype.val)
      rwa [he]

/-- The finite quotient indexing the cell components. -/
abbrev ComponentIndex := Quotient (setoid (fun σ : U.simplices => U.cell σ.val))

instance componentIndex_finite : Finite U.ComponentIndex := by
  letI : Finite U.simplices := U.finite_simplices.to_subtype
  exact finite_components (fun σ : U.simplices => U.cell σ.val)
    (fun x => by obtain ⟨σ, hσ, hx⟩ := U.cover x; exact ⟨⟨σ, hσ⟩, hx⟩)

def componentIndex (x : P) : U.ComponentIndex := Quotient.mk _ x

abbrev IndexedComponent (c : U.ComponentIndex) := U.CellComponent c.out

def pointInComponent (x : P) : U.IndexedComponent (U.componentIndex x) :=
  ⟨x, Quotient.mk_out (s := setoid (fun σ : U.simplices => U.cell σ.val)) x⟩

theorem componentIndex_eq (c : U.ComponentIndex) (x : U.IndexedComponent c) :
    U.componentIndex x.val = c :=
  (Quotient.sound x.property).symm.trans (Quotient.out_eq c)

theorem componentIndex_eq_iff (c : U.ComponentIndex) (x : P) :
    U.componentIndex x = c ↔ Joined (fun σ : U.simplices => U.cell σ.val) c.out x := by
  constructor
  · intro h
    exact Quotient.exact ((Quotient.out_eq c).trans h.symm)
  · intro h
    exact (Quotient.sound h).symm.trans (Quotient.out_eq c)

theorem compact_indexedComponent (c : U.ComponentIndex) :
    IsCompact {x : P | Joined (fun σ : U.simplices => U.cell σ.val) c.out x} := by
  letI : Finite U.simplices := U.finite_simplices.to_subtype
  exact compact_component (fun σ : U.simplices => U.cell σ.val)
    (fun σ => U.compact_cell σ.val σ.property)
    (fun x => by obtain ⟨σ, hσ, hx⟩ := U.cover x; exact ⟨⟨σ, hσ⟩, hx⟩) c.out

theorem indexedComponent_cover (x : P) :
    ∃ (c : U.ComponentIndex) (y : U.IndexedComponent c), y.val = x :=
  ⟨U.componentIndex x, U.pointInComponent x, rfl⟩

theorem indexedComponent_disjoint {c d : U.ComponentIndex} (hcd : c ≠ d) :
    Disjoint (Set.range (Subtype.val : U.IndexedComponent c → P))
      (Set.range (Subtype.val : U.IndexedComponent d → P)) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, hz⟩ := hx'
  have hcy : U.componentIndex x = c := by rw [← hy]; exact U.componentIndex_eq c y
  have hdz : U.componentIndex x = d := by rw [← hz]; exact U.componentIndex_eq d z
  exact hcd (hcy.symm.trans hdz)

variable {Y : Type*}

/-- Gluing arbitrary functions on the disjoint cell components. -/
def glueComponents (f : ∀ c : U.ComponentIndex, U.IndexedComponent c → Y) : P → Y :=
  fun x => f (U.componentIndex x) (U.pointInComponent x)

@[simp]
theorem glueComponents_apply (f : ∀ c : U.ComponentIndex, U.IndexedComponent c → Y)
    (c : U.ComponentIndex) (x : U.IndexedComponent c) :
    U.glueComponents f x.val = f c x := by
  rcases x with ⟨x, hx⟩
  have he : U.componentIndex x = c := U.componentIndex_eq c ⟨x, hx⟩
  subst c
  rfl

variable [TopologicalSpace Y]

theorem continuous_glueComponents
    (f : ∀ c : U.ComponentIndex, U.IndexedComponent c → Y)
    (hf : ∀ c, Continuous (f c)) : Continuous (U.glueComponents f) := by
  let C : U.ComponentIndex → Set P := fun c =>
    {x | Joined (fun σ : U.simplices => U.cell σ.val) c.out x}
  have hcover : (⋃ c, C c) = univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨U.componentIndex x, (U.pointInComponent x).property⟩
  apply (locallyFinite_of_finite C).continuous hcover
    (fun c => (U.compact_indexedComponent c).isClosed)
  intro c
  rw [continuousOn_iff_continuous_domRestrict]
  exact (hf c).congr (fun x => (U.glueComponents_apply f c x).symm)

variable (q : P → Model κ n) (hq : Continuous q)
    (hiso : ∀ σ ∈ U.simplices, ∀ x ∈ U.cell σ, ∀ y ∈ U.cell σ,
      dist (q x) (q y) = dist (U.chart σ x) (U.chart σ y))

include hiso in
theorem component_folding_isometric (p : P) :
    ∀ σ ∈ (U.componentChartedComplex p).simplices,
      ∀ x ∈ (U.componentChartedComplex p).cell σ,
      ∀ y ∈ (U.componentChartedComplex p).cell σ,
      dist (q x.val) (q y.val) =
        dist ((U.componentChartedComplex p).chart σ x)
          ((U.componentChartedComplex p).chart σ y) := by
  intro σ hσ x hx y hy
  exact hiso _ hσ x.val hx y.val hy

/-- The actual intrinsic metric on one finite cell component. -/
@[instance_reducible]
def componentIntrinsicMetric (p : P) : MetricSpace (U.CellComponent p) :=
  (U.componentChartedComplex p).foldedIntrinsicMetric (q ∘ Subtype.val)
    (hq.comp continuous_subtype_val) (U.component_folding_isometric q hiso p)
    (U.componentChartedComplex_connected p)

theorem component_isFinitePolyhedron (p : P) :
    letI := U.componentIntrinsicMetric q hq hiso p
    IsFinitePolyhedron κ n (U.CellComponent p) :=
  (U.componentChartedComplex p).isFinitePolyhedron_foldedIntrinsicMetric
    (q ∘ Subtype.val) (hq.comp continuous_subtype_val)
    (U.component_folding_isometric q hiso p) (U.componentChartedComplex_connected p)

theorem componentMetric_on_cell (p : P) (σ : U.simplices)
    (x : U.CellComponent p) (hx : x.val ∈ U.cell σ.val)
    (y : U.CellComponent p) (hy : y.val ∈ U.cell σ.val) :
    @dist (U.CellComponent p) (U.componentIntrinsicMetric q hq hiso p).toDist x y =
      dist (q x.val) (q y.val) := by
  obtain ⟨τ, hτ, he⟩ := U.exists_component_face p σ x hx
  have hx' : x ∈ (U.componentChartedComplex p).cell τ := by
    change x.val ∈ U.cell (τ.image Subtype.val)
    rwa [he]
  have hy' : y ∈ (U.componentChartedComplex p).cell τ := by
    change y.val ∈ U.cell (τ.image Subtype.val)
    rwa [he]
  exact ((U.componentChartedComplex p).foldedIntrinsicMetric_on_cell (q ∘ Subtype.val)
    (hq.comp continuous_subtype_val) (U.component_folding_isometric q hiso p)
    (U.componentChartedComplex_connected p) τ hτ x hx' y hy').trans
      (U.component_folding_isometric q hiso p τ hτ x hx' y hy').symm

theorem component_lipschitzWith_of_cellwise
    {Y : Type*} [MetricSpace Y] (p : P) (f : U.CellComponent p → Y) {L : NNReal}
    (hf : ∀ σ ∈ U.simplices, ∀ x : U.CellComponent p, x.val ∈ U.cell σ →
      ∀ y : U.CellComponent p, y.val ∈ U.cell σ →
      dist (f x) (f y) ≤ L * dist (U.chart σ x.val) (U.chart σ y.val)) :
    letI := U.componentIntrinsicMetric q hq hiso p
    LipschitzWith L f := by
  apply (U.componentChartedComplex p).foldedIntrinsicMetric_lipschitzWith_of_cellwise
    (q ∘ Subtype.val) (hq.comp continuous_subtype_val)
    (U.component_folding_isometric q hiso p) (U.componentChartedComplex_connected p) f
  intro σ hσ x hx y hy
  exact hf (σ.image Subtype.val) hσ x hx y hy

end ArchivePLGeometry.FiniteChartedComplex

