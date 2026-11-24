module

public import PLGeometry.TieRealization

/-!
# Angular coordinates on the source tie locus

The positive weights converting angular barycentric coordinates to model
barycentric coordinates are the reciprocals of `r`, `sin r`, and `sinh r`.
The vertex radii are intrinsic to the protected tie complex, so this
reweighting is global and preserves every face.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry

def radialSine (κ : Geometry) (r : ℝ) : ℝ :=
  match κ with
  | .euclidean => r
  | .spherical => Real.sin r
  | .hyperbolic => Real.sinh r

theorem radialSine_pos (κ : Geometry) {r : ℝ} (hr : 0 < r)
    (hπ : κ = .spherical → r < Real.pi) : 0 < radialSine κ r := by
  cases κ with
  | euclidean => exact hr
  | spherical => exact Real.sin_pos_of_pos_of_lt_pi hr (hπ rfl)
  | hyperbolic => exact Real.sinh_pos_iff.mpr hr

namespace ProjectiveVoronoiAtlas

universe u v
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance angularTieRealizationDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance angularTieRealizationEDecidableEq : DecidableEq E := Classical.decEq E

def tieVertexRadius (v : A.toVoronoiAtlas.TieVertex S) : ℝ :=
  let h := (A.toVoronoiAtlas.tieComplex S).singleton v
  dist (A.toVoronoiAtlas.tieChart S h (A.toVoronoiAtlas.tieCenter S h))
    (A.toVoronoiAtlas.tieChart S h (A.toVoronoiAtlas.tieSource S v))

theorem tieVertexRadius_pos (v : A.toVoronoiAtlas.TieVertex S) : 0 < A.tieVertexRadius S v :=
  A.toVoronoiAtlas.tie_vertex_radius_pos S
    ((A.toVoronoiAtlas.tieComplex S).singleton v) (Finset.mem_singleton_self v)

theorem tieVertexRadius_lt {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (v : A.toVoronoiAtlas.TieVertex S) : A.tieVertexRadius S v < η :=
  A.toVoronoiAtlas.tie_vertex_radius_lt S hnet
    ((A.toVoronoiAtlas.tieComplex S).singleton v) (Finset.mem_singleton_self v)

theorem tieVertexRadius_eq {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    {v : A.toVoronoiAtlas.TieVertex S} (hv : v ∈ σ) :
    A.tieVertexRadius S v =
      dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
        (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v)) :=
  A.toVoronoiAtlas.tie_vertex_radius_eq S hnet hp
    ((A.toVoronoiAtlas.tieComplex S).singleton v) hσ
    (Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, hv⟩)

def angularTieWeight (v : A.toVoronoiAtlas.TieVertex S) : ℝ :=
  (radialSine κ (A.tieVertexRadius S v))⁻¹

theorem angularTieWeight_pos {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : κ = .spherical → η < Real.pi) (v : A.toVoronoiAtlas.TieVertex S) :
    0 < A.angularTieWeight S v :=
  inv_pos.mpr (radialSine_pos κ (A.tieVertexRadius_pos S v)
    (fun h => (A.tieVertexRadius_lt S hnet v).trans (hη h)))

theorem tieRealization_mem_cell_iff {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) :
    A.tieRealization S x ∈ A.tieCell S σ ↔ x.val ∈ Barycentric.weightsOn σ := by
  constructor
  · intro hx
    let w := (A.tieWeightsHomeomorph S hσ).symm ⟨A.tieRealization S x, hx⟩
    let z : (A.toVoronoiAtlas.tieComplex S).Space :=
      ⟨w.val, Set.mem_iUnion₂.mpr ⟨σ, hσ, w.property⟩⟩
    have hz : A.tieRealization S z = A.tieRealization S x := by
      rw [A.tieRealization_eq S hσ z w.property]
      exact congrArg Subtype.val ((A.tieWeightsHomeomorph S hσ).apply_symm_apply _)
    have he := A.tieRealization_injective S hnet hp hz
    rw [← he]
    exact w.property
  · intro hx
    rw [A.tieRealization_eq S hσ x hx]
    exact A.tieLocalPoint_mem S hσ _

@[simp] theorem tieRealizationHomeomorph_apply {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (x : (A.toVoronoiAtlas.tieComplex S).Space) :
    (A.tieRealizationHomeomorph S hnet hp x).val = A.tieRealization S x := rfl

def angularTieHomeomorph {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : κ = .spherical → η < Real.pi) :
    (A.toVoronoiAtlas.tieComplex S).Space ≃ₜ A.tieLocus S :=
  ((A.toVoronoiAtlas.tieComplex S).reweightHomeomorph
    (A.angularTieWeight S) (A.angularTieWeight_pos S hnet hη)).trans
      (A.tieRealizationHomeomorph S hnet hp)

def angularTiePoint {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : κ = .spherical → η < Real.pi)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) : P :=
  (A.angularTieHomeomorph S hnet hp hη x).val

theorem angularTiePoint_mem_cell_iff {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) :
    A.angularTiePoint S hnet hp hη x ∈ A.tieCell S σ ↔
      x.val ∈ Barycentric.weightsOn σ := by
  change A.tieRealization S ((A.toVoronoiAtlas.tieComplex S).reweight
    (A.angularTieWeight S) (A.angularTieWeight_pos S hnet hη) x) ∈ A.tieCell S σ ↔ _
  rw [A.tieRealization_mem_cell_iff S hnet hp hσ]
  exact (A.toVoronoiAtlas.tieComplex S).reweight_mem_weightsOn_iff _ _ x σ

theorem continuous_angularTiePoint {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : κ = .spherical → η < Real.pi) :
    Continuous (A.angularTiePoint S hnet hp hη) :=
  continuous_subtype_val.comp (A.angularTieHomeomorph S hnet hp hη).continuous

theorem angularTiePoint_injective {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : κ = .spherical → η < Real.pi) :
    Function.Injective (A.angularTiePoint S hnet hp hη) := by
  intro x y he
  exact (A.angularTieHomeomorph S hnet hp hη).injective (Subtype.ext he)

theorem angularTiePoint_represents {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ) :
    ModelBarycentric.Represents κ n (fun v : σ =>
      A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val))
      (fun v => A.angularTieWeight S v.val * x.val v.val /
        BarycentricReweighting.total (A.angularTieWeight S) x.val)
      (A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hη x)) := by
  let K := A.toVoronoiAtlas.tieComplex S
  let y := K.reweight (A.angularTieWeight S) (A.angularTieWeight_pos S hnet hη) x
  have hy : y.val ∈ Barycentric.weightsOn σ :=
    (K.reweight_mem_weightsOn_iff _ _ x σ).mpr hx
  change ModelBarycentric.Represents κ n _ (Barycentric.restrict σ ⟨y.val, hy⟩).val
    (A.toVoronoiAtlas.tieChart S hσ (A.tieRealization S y))
  rw [A.tieRealization_eq S hσ y hy]
  exact A.tieLocalPoint_represents S hσ _

def angularWeights {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ) :
    ModelBarycentric.Weights σ :=
  Barycentric.restrict σ
    ⟨((A.toVoronoiAtlas.tieComplex S).reweight (A.angularTieWeight S)
      (A.angularTieWeight_pos S hnet hη) x).val,
      ((A.toVoronoiAtlas.tieComplex S).reweight_mem_weightsOn_iff _ _ x σ).mpr hx⟩

@[simp] theorem angularWeights_apply {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ)
    (v : σ) :
    (A.angularWeights S hnet hη x hx).val v = A.angularTieWeight S v.val * x.val v.val /
      BarycentricReweighting.total (A.angularTieWeight S) x.val := rfl

theorem angularWeightTotal_pos {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hη : κ = .spherical → η < Real.pi) (x : (A.toVoronoiAtlas.tieComplex S).Space) :
    0 < BarycentricReweighting.total (A.angularTieWeight S) x.val :=
  BarycentricReweighting.total_pos _ (A.angularTieWeight_pos S hnet hη)
    ⟨x.val, (A.toVoronoiAtlas.tieComplex S).weight_nonneg x,
      (A.toVoronoiAtlas.tieComplex S).weight_sum x⟩

theorem angularWeights_mul_radialSine {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hη : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ)
    (v : σ) :
    (A.angularWeights S hnet hη x hx).val v *
      radialSine κ (dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
        (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieSource S v.val))) =
      (BarycentricReweighting.total (A.angularTieWeight S) x.val)⁻¹ * x.val v.val := by
  rw [angularWeights_apply, ← A.tieVertexRadius_eq S hnet hp hσ v.property]
  have hs : radialSine κ (A.tieVertexRadius S v.val) ≠ 0 :=
    (radialSine_pos κ (A.tieVertexRadius_pos S v.val)
      (fun h => (A.tieVertexRadius_lt S hnet v.val).trans (hη h))).ne'
  unfold angularTieWeight
  field_simp [hs, (A.angularWeightTotal_pos S hnet hη x).ne']

theorem tieCell_subset_voronoiPieces {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) {y : P}
    (hy : y ∈ A.tieCell S σ) :
    y ∈ T.voronoiPiece S (A.toVoronoiAtlas.tieFaceIndex S σ hσ).val.1.val
      (A.toVoronoiAtlas.tieCenter S hσ) ∧
    y ∈ T.voronoiPiece S (A.toVoronoiAtlas.tieFaceIndex S σ hσ).val.1.val
      (A.toVoronoiAtlas.tieOtherCenter S hσ) := by
  let B := A.toVoronoiAtlas
  let i := B.tieFaceIndex S σ hσ
  have hz : A.coord y ∈ B.tiePiece S i :=
    Pulling.family_face_subset_cell (B.tiePiece S) (B.tiePiece_polytope S)
      (B.tieFaceIndex_spec S σ hσ) hy
  obtain ⟨z, he, hza, hzb⟩ := B.tiePiece_source S i hz
  have hzy := A.injective he
  subst z
  exact ⟨hza, hzb⟩

theorem tieCell_radius_pos {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) {y : P}
    (hy : y ∈ A.tieCell S σ) :
    0 < dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ y) := by
  let B := A.toVoronoiAtlas
  obtain ⟨ha, hb⟩ := A.tieCell_subset_voronoiPieces S hσ hy
  have hbis := T.voronoiPiece_tie ha hb
  have htri := dist_triangle (B.tieChart S hσ (B.tieCenter S hσ))
    (B.tieChart S hσ y) (B.tieChart S hσ (B.tieOtherCenter S hσ))
  have hpos := dist_pos.mpr (B.tie_centers_distinct S hσ)
  change dist (B.tieChart S hσ y) (B.tieChart S hσ (B.tieCenter S hσ)) =
    dist (B.tieChart S hσ y) (B.tieChart S hσ (B.tieOtherCenter S hσ)) at hbis
  rw [← hbis, dist_comm (B.tieChart S hσ y)] at htri
  linarith

theorem tieCell_radius_lt {η : ℝ} (hnet : T.IsCellwiseNet S η)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces) {y : P}
    (hy : y ∈ A.tieCell S σ) :
    dist (A.toVoronoiAtlas.tieChart S hσ (A.toVoronoiAtlas.tieCenter S hσ))
      (A.toVoronoiAtlas.tieChart S hσ y) < η := by
  have h := T.voronoiPiece_radius_lt hnet
    (A.toVoronoiAtlas.tieFaceIndex S σ hσ).val.1.property
    (A.tieCell_subset_voronoiPieces S hσ hy).1
  simpa only [VoronoiAtlas.tieChart, VoronoiAtlas.tieCenter, dist_comm] using h

end ProjectiveVoronoiAtlas
end ArchivePLGeometry
