module

public import PLGeometry.AngularTieProjective
public import PLGeometry.ChartedProjectiveConverse
public import PLGeometry.ChartedProjectiveTransport
public import PLGeometry.VoronoiBaseTransport

/-! # Source coordinate polytopes of transported angular simplices -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}

local instance angularTieCoordinateDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

section General

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance angularTieCoordinateEDecidableEq : DecidableEq E := Classical.decEq E

theorem coord_image_tieCell {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) :
    A.coord '' A.tieCell S σ =
      convexHull ℝ (A.toVoronoiAtlas.tieCoordinateFace S σ : Set E) := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hz
    have hv : (B.tieCoordinateFace S σ : Set E) ⊆ A.coord '' T.cell i.val.1.val := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨B.tieSource S v, (B.tieFace_source_mem S hσ hv).1.1, B.coord_tieSource S v⟩
    obtain ⟨y, _, he⟩ := convexHull_min hv (A.cell_polytope _ i.val.1.property).convex hz
    refine ⟨y, ?_, he⟩
    change A.coord y ∈ convexHull ℝ (B.tieCoordinateFace S σ : Set E)
    rwa [he]

end General

section Canonical

variable [LinearOrder (T.Vertex → ℝ)]
    (A : ProjectiveVoronoiAtlas T (T.Vertex → ℝ)) (S : Finset P)
    (hA : A.coord = T.barycentricCoords)

include hA

local instance angularTieCoordinateCanonicalEq : DecidableEq (T.Vertex → ℝ) := Classical.decEq _

theorem angularTiePoint_coord_hull_iff {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (V : Finset (A.toVoronoiAtlas.tieComplex S).Space)
    (hV : ∀ v ∈ V, v.val ∈ Barycentric.weightsOn σ)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ) :
    A.coord (A.angularTiePoint S hnet hp hsmall x) ∈
      convexHull ℝ (V.image (A.coord ∘ A.angularTiePoint S hnet hp hsmall) : Set (T.Vertex → ℝ)) ↔
      x.val ∈ convexHull ℝ (V.image Subtype.val : Set _) := by
  let B := A.toVoronoiAtlas
  let f := A.angularTiePoint S hnet hp hsmall
  let i := B.tieFaceIndex S σ hσ
  have hverts : (V.image f : Set P) ⊆ T.cell i.val.1.val := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact A.tieCell_subset_old S hσ ((A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ v).mpr (hV v hv))
  have hxold := A.tieCell_subset_old S hσ ((A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ x).mpr hx)
  have hb := T.barycentric_hull_iff i.val.1.property (V.image f) hverts ⟨f x, hxold⟩
  rw [← hA, composed_image A f V] at hb
  have hm := A.angularTiePoint_model_hull_iff S hnet hp hsmall hσ
    (fun v : V => v.val) Subtype.val_injective (fun v => hV v.val v.property) x hx
  have hfin : Finset.univ.image (fun v : V => B.tieChart S hσ (f v.val)) =
      (V.image f).image (T.chart i.val.1.val) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨f v.val, ⟨v.val, v.property, rfl⟩, hv⟩
    · rintro ⟨y, ⟨v, hv, rfl⟩, he⟩
      exact ⟨⟨v, hv⟩, he⟩
  have hset : Set.range (fun v : V => v.val.val) = (V.image Subtype.val : Set _) := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩
    · intro hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨⟨v, hv⟩, rfl⟩
  rw [hfin, hset] at hm
  exact hb.symm.trans hm

theorem angularTiePoint_coord_independent {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (V : Finset (A.toVoronoiAtlas.tieComplex S).Space)
    (hV : ∀ v ∈ V, v.val ∈ Barycentric.weightsOn σ)
    (hi : AffineIndependent ℝ (fun v : V => v.val.val)) :
    AffineIndependent ℝ ((↑) :
      V.image (A.coord ∘ A.angularTiePoint S hnet hp hsmall) → (T.Vertex → ℝ)) := by
  let B := A.toVoronoiAtlas
  let f := A.angularTiePoint S hnet hp hsmall
  let i := B.tieFaceIndex S σ hσ
  let v : V → T.cell i.val.1.val := fun v =>
    ⟨f v.val, A.tieCell_subset_old S hσ
      ((A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ v.val).mpr (hV v.val v.property))⟩
  have hm := A.angularTiePoint_model_independent S hnet hp hsmall hσ
    (fun v : V => v.val) (fun v => hV v.val v.property) hi
  have hc := T.barycentricCoords_independent_of_model i.val.1.property v hm
  have hrange := hc.range
  have he : Set.range (fun j : V => T.barycentricCoords (v j).val) =
      (V.image (A.coord ∘ f) : Set (T.Vertex → ℝ)) := by
    rw [← hA]
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩
    · intro hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨⟨j, hj⟩, rfl⟩
  rw [he] at hrange
  exact hrange

theorem angularTiePoint_coord_image_cell {κ' : Geometry} {m : ℕ}
    (U : FiniteChartedComplex κ' m (A.toVoronoiAtlas.tieComplex S).Space)
    {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hsmall : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {V : Finset (A.toVoronoiAtlas.tieComplex S).Space} (hV : V ∈ U.simplices)
    (hcell : ∀ x ∈ U.cell V, x.val ∈ Barycentric.weightsOn σ)
    (hcoords : (Subtype.val : (A.toVoronoiAtlas.tieComplex S).Space → _) '' U.cell V =
      convexHull ℝ (V.image Subtype.val : Set _)) :
    (A.coord ∘ A.angularTiePoint S hnet hp hsmall) '' U.cell V =
      convexHull ℝ (V.image (A.coord ∘ A.angularTiePoint S hnet hp hsmall) : Set _) := by
  let f := A.angularTiePoint S hnet hp hsmall
  have hv (v) (hv : v ∈ V) := hcell v (U.vertices_mem V hV hv)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (A.angularTiePoint_coord_hull_iff S hA hnet hp hsmall hσ V hv x (hcell x hx)).mpr
    rw [← hcoords]
    exact ⟨x, hx, rfl⟩
  · intro hz
    have hzc : z ∈ A.coord '' A.tieCell S σ := by
      apply convexHull_min ?_ ?_ hz
      · intro y hy
        obtain ⟨v, hvV, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨f v, (A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ v).mpr (hv v hvV), rfl⟩
      · rw [A.coord_image_tieCell S hσ]
        exact convex_convexHull ℝ _
    obtain ⟨y, hy, rfl⟩ := hzc
    have hyl : y ∈ A.tieLocus S := Set.mem_iUnion₂.mpr ⟨σ, hσ, hy⟩
    let x := (A.angularTieHomeomorph S hnet hp hsmall).symm ⟨y, hyl⟩
    have hfx : f x = y := congrArg Subtype.val
      ((A.angularTieHomeomorph S hnet hp hsmall).apply_symm_apply ⟨y, hyl⟩)
    have hfxC : f x ∈ A.tieCell S σ := by rw [hfx]; exact hy
    have hxσ : x.val ∈ Barycentric.weightsOn σ :=
      (A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ x).mp hfxC
    have hxcoord : x.val ∈ convexHull ℝ (V.image Subtype.val : Set _) :=
      (A.angularTiePoint_coord_hull_iff S hA hnet hp hsmall hσ V hv x hxσ).mp
        (by simpa only [← hfx] using hz)
    rw [← hcoords] at hxcoord
    obtain ⟨w, hw, he⟩ := hxcoord
    have hwx : w = x := Subtype.ext he
    refine ⟨x, hwx ▸ hw, ?_⟩
    exact congrArg A.coord hfx

end Canonical
end ArchivePLGeometry.ProjectiveVoronoiAtlas
