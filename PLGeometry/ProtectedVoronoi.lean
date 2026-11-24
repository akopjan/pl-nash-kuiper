module

public import PLGeometry.ProtectedNets

/-!
# The Voronoi decomposition of a protected cellwise net

Protection makes nearest-site sets independent of the incident simplex
chart. Thus the individual cell diagrams glue to a finite closed cover of
the source, with every piece contained in the corresponding site's star.
-/

@[expose] public section
noncomputable section

open Set Classical

namespace ArchivePLGeometry.FiniteChartedComplex

open BrehmApprox

universe u

local instance protectedVoronoiDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

def cellSites (S : Finset P) (σ : Finset P) : Finset P := S.filter (fun a => a ∈ T.cell σ)

@[simp]
theorem mem_cellSites {S σ : Finset P} {a : P} :
    a ∈ T.cellSites S σ ↔ a ∈ S ∧ a ∈ T.cell σ := Finset.mem_filter

def IsNearestInCell (S : Finset P) (σ : Finset P) (x a : P) : Prop :=
  IsNearestFor (fun z w => dist (T.chart σ z) (T.chart σ w)) ((S : Set P) ∩ T.cell σ) x a

theorem exists_nearestInCell {S : Finset P} {η : ℝ} (hnet : T.IsCellwiseNet S η)
    {σ : Finset P} (hσ : σ ∈ T.simplices) {x : P} (hx : x ∈ T.cell σ) :
    ∃ a, T.IsNearestInCell S σ x a := by
  obtain ⟨b, hb, hbσ, _⟩ := hnet σ hσ x hx
  have hne : (T.cellSites S σ).Nonempty := ⟨b, T.mem_cellSites.mpr ⟨hb, hbσ⟩⟩
  obtain ⟨a, ha, hmin⟩ := (T.cellSites S σ).exists_min_image
    (fun a => dist (T.chart σ x) (T.chart σ a)) hne
  exact ⟨a, T.mem_cellSites.mp ha, fun c hc => hmin c (T.mem_cellSites.mpr hc)⟩

/-- Nearest-site membership agrees in any two charts containing the query point. -/
theorem nearestInCell_iff {S : Finset P} {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hprotected : T.IsCellwiseProtected S)
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
    {x a : P} (hx : x ∈ T.cell σ ∩ T.cell τ) :
    T.IsNearestInCell S σ x a ↔ T.IsNearestInCell S τ x a := by
  have hforward (σ τ : Finset P) (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
      (hx : x ∈ T.cell σ ∩ T.cell τ) (ha : T.IsNearestInCell S σ x a) :
      T.IsNearestInCell S τ x a := by
    have haτ := hprotected σ hσ τ hτ x hx a ha
    obtain ⟨b, hb⟩ := T.exists_nearestInCell hnet hτ hx.2
    have hbσ := hprotected τ hτ σ hσ x ⟨hx.2, hx.1⟩ b hb
    refine ⟨⟨ha.1.1, haτ⟩, ?_⟩
    intro c hc
    calc
      dist (T.chart τ x) (T.chart τ a) = dist (T.chart σ x) (T.chart σ a) :=
        (T.metric_coherence σ hσ τ hτ x hx a ⟨ha.1.2, haτ⟩).symm
      _ ≤ dist (T.chart σ x) (T.chart σ b) := ha.2 b ⟨hb.1.1, hbσ⟩
      _ = dist (T.chart τ x) (T.chart τ b) :=
        T.metric_coherence σ hσ τ hτ x hx b ⟨hbσ, hb.1.2⟩
      _ ≤ dist (T.chart τ x) (T.chart τ c) := hb.2 c hc
  exact ⟨hforward σ τ hσ hτ hx, hforward τ σ hτ hσ ⟨hx.2, hx.1⟩⟩

def voronoiPiece (S : Finset P) (σ : Finset P) (a : P) : Set P :=
  {x | x ∈ T.cell σ ∧ T.IsNearestInCell S σ x a}

def voronoiCell (S : Finset P) (a : P) : Set P :=
  ⋃ σ ∈ T.simplices, T.voronoiPiece S σ a

theorem voronoiPiece_inter_cell {S : Finset P} {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hprotected : T.IsCellwiseProtected S)
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices) (a : P) :
    T.voronoiPiece S σ a ∩ T.cell τ = T.cell σ ∩ T.voronoiPiece S τ a := by
  ext x
  constructor
  · rintro ⟨⟨hxσ, ha⟩, hxτ⟩
    exact ⟨hxσ, hxτ, (T.nearestInCell_iff hnet hprotected hσ hτ ⟨hxσ, hxτ⟩).mp ha⟩
  · rintro ⟨hxσ, hxτ, ha⟩
    exact ⟨⟨hxσ, (T.nearestInCell_iff hnet hprotected hσ hτ ⟨hxσ, hxτ⟩).mpr ha⟩, hxτ⟩

/-- The global Voronoi cell restricts to the local diagram in every old simplex. -/
theorem voronoiCell_inter_cell {S : Finset P} {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hprotected : T.IsCellwiseProtected S)
    {σ : Finset P} (hσ : σ ∈ T.simplices) (a : P) :
    T.voronoiCell S a ∩ T.cell σ = T.voronoiPiece S σ a := by
  ext x
  constructor
  · rintro ⟨hx, hxσ⟩
    obtain ⟨τ, hτ, hxτ, haτ⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨hxσ, (T.nearestInCell_iff hnet hprotected hτ hσ ⟨hxτ, hxσ⟩).mp haτ⟩
  · intro hx
    exact ⟨Set.mem_iUnion₂.mpr ⟨σ, hσ, hx⟩, hx.1⟩

theorem voronoi_cover {S : Finset P} {η : ℝ} (hnet : T.IsCellwiseNet S η) (x : P) :
    ∃ a ∈ S, x ∈ T.voronoiCell S a := by
  obtain ⟨σ, hσ, hxσ⟩ := T.cover x
  obtain ⟨a, ha⟩ := T.exists_nearestInCell hnet hσ hxσ
  exact ⟨a, ha.1.1, Set.mem_iUnion₂.mpr ⟨σ, hσ, hxσ, ha⟩⟩

theorem voronoiPiece_radius_lt {S : Finset P} {η : ℝ} (hnet : T.IsCellwiseNet S η)
    {σ : Finset P} (hσ : σ ∈ T.simplices) {a x : P} (hx : x ∈ T.voronoiPiece S σ a) :
    dist (T.chart σ x) (T.chart σ a) < η := by
  obtain ⟨b, hb, hbσ, hxb⟩ := hnet σ hσ x hx.1
  exact (hx.2.2 b ⟨hb, hbσ⟩).trans_lt hxb

theorem voronoiPiece_site_mem {S : Finset P} {σ : Finset P} {a x : P}
    (hx : x ∈ T.voronoiPiece S σ a) : a ∈ T.voronoiPiece S σ a := by
  refine ⟨hx.2.1.2, hx.2.1, ?_⟩
  intro b hb
  simpa only [dist_self] using dist_nonneg (x := T.chart σ a) (y := T.chart σ b)

theorem voronoiPiece_tie {S : Finset P} {σ : Finset P} {a b x : P}
    (ha : x ∈ T.voronoiPiece S σ a) (hb : x ∈ T.voronoiPiece S σ b) :
    dist (T.chart σ x) (T.chart σ a) = dist (T.chart σ x) (T.chart σ b) :=
  le_antisymm (ha.2.2 b hb.2.1) (hb.2.2 a ha.2.1)

/-- A Voronoi cell cannot touch an old face which does not contain its site. -/
theorem voronoiPiece_disjoint_cell {S : Finset P} (hprotected : T.IsCellwiseProtected S)
    {σ τ : Finset P} (hσ : σ ∈ T.simplices) (hτ : τ ∈ T.simplices)
    {a : P} (ha : a ∉ T.cell τ) : Disjoint (T.voronoiPiece S σ a) (T.cell τ) := by
  apply Set.disjoint_left.mpr
  intro x hx hxτ
  exact ha (hprotected σ hσ τ hτ x ⟨hx.1, hxτ⟩ a hx.2)

theorem isCompact_voronoiPiece (S : Finset P) {σ : Finset P} (hσ : σ ∈ T.simplices) (a : P) :
    IsCompact (T.voronoiPiece S σ a) := by
  by_cases ha : a ∈ (S : Set P) ∩ T.cell σ
  · let : CompactSpace (T.cell σ) := isCompact_iff_compactSpace.mp (T.compact_cell σ hσ)
    let C : Set (T.cell σ) := {x | ∀ b ∈ (S : Set P) ∩ T.cell σ,
      dist (T.chart σ x.val) (T.chart σ a) ≤ dist (T.chart σ x.val) (T.chart σ b)}
    have hc : Continuous (fun x : T.cell σ => T.chart σ x.val) :=
      (T.chart_continuousOn σ hσ).domRestrict
    have hC : IsClosed C := by
      have he : C = ⋂ b, ⋂ (_ : b ∈ (S : Set P) ∩ T.cell σ),
          {x : T.cell σ | dist (T.chart σ x.val) (T.chart σ a) ≤
            dist (T.chart σ x.val) (T.chart σ b)} := by ext x; simp [C]
      rw [he]
      exact isClosed_iInter (fun b => isClosed_iInter (fun _ =>
        isClosed_le (hc.dist continuous_const) (hc.dist continuous_const)))
    have he : T.voronoiPiece S σ a = (Subtype.val : T.cell σ → P) '' C := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨x, hx.1⟩, hx.2.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.property, ha, hx⟩
    rw [he]
    exact hC.isCompact.image continuous_subtype_val
  · have he : T.voronoiPiece S σ a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact ha hx.2.1
    rw [he]
    exact isCompact_empty

theorem isCompact_voronoiCell (S : Finset P) (a : P) : IsCompact (T.voronoiCell S a) :=
  T.finite_simplices.isCompact_biUnion (fun σ hσ => T.isCompact_voronoiPiece S hσ a)

end ArchivePLGeometry.FiniteChartedComplex
