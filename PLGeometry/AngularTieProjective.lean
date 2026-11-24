module

public import PLGeometry.AngularTieRealization
public import PLGeometry.BarycentricRestrictionGeometry
public import PLGeometry.ModelProjectiveGeometry
public import BrehmApprox.ReweightingProjectiveGeometry

/-! # Projective transport from angular simplices to source tie bases -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.ProjectiveVoronoiAtlas

universe u v
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)

local instance angularTieProjectiveDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance angularTieProjectiveEDecidableEq : DecidableEq E := Classical.decEq E

theorem angularTiePoint_model_hull_iff {J : Type*} [Fintype J]
    {η : ℝ} (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S)
    (hsmall : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (v : J → (A.toVoronoiAtlas.tieComplex S).Space) (hinj : Function.Injective v)
    (hv : ∀ j, (v j).val ∈ Barycentric.weightsOn σ)
    (x : (A.toVoronoiAtlas.tieComplex S).Space) (hx : x.val ∈ Barycentric.weightsOn σ) :
    A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall x) ∈
      hull κ n (Finset.univ.image (fun j =>
        A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall (v j)))) ↔
      x.val ∈ convexHull ℝ (Set.range (fun j => (v j).val)) := by
  let B := A.toVoronoiAtlas
  let K := B.tieComplex S
  let f := A.angularTiePoint S hnet hp hsmall
  let u : J → Model κ n := fun j => B.tieChart S hσ (f (v j))
  let b : J → ModelBarycentric.Weights σ := fun j => A.angularWeights S hnet hsmall (v j) (hv j)
  let b₀ := A.angularWeights S hnet hsmall x hx
  have hui : Function.Injective u := by
    intro j k he
    apply hinj
    apply A.angularTiePoint_injective S hnet hp hsmall
    exact T.chart_injectiveOn _ (B.tieFaceIndex S σ hσ).val.1.property
      (A.tieCell_subset_old S hσ ((A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ (v j)).mpr (hv j)))
      (A.tieCell_subset_old S hσ ((A.angularTiePoint_mem_cell_iff S hnet hp hsmall hσ (v k)).mpr (hv k))) he
  have hmodel := ModelBarycentric.represents_hull_iff
    (fun i : σ => B.tieChart S hσ (B.tieSource S i.val)) (A.tie_vertex_independent S hσ)
    u hui b (fun j => A.angularTiePoint_represents S hnet hp hsmall hσ (v j) (hv j))
    b₀ (B.tieChart S hσ (f x)) (A.angularTiePoint_represents S hnet hp hsmall hσ x hx)
  let a := A.angularTieWeight S
  let ha := A.angularTieWeight_pos S hnet hsmall
  let rwv : J → Barycentric.weightsOn σ := fun j =>
    ⟨(K.reweight a ha (v j)).val, (K.reweight_mem_weightsOn_iff a ha (v j) σ).mpr (hv j)⟩
  let rwx : Barycentric.weightsOn σ :=
    ⟨(K.reweight a ha x).val, (K.reweight_mem_weightsOn_iff a ha x σ).mpr hx⟩
  have hrestrict := Barycentric.restrict_mem_convexHull_iff σ rwv rwx
  let w : J → BarycentricReweighting.Weights (B.TieVertex S) :=
    fun j => ⟨(v j).val, K.weight_nonneg (v j), K.weight_sum (v j)⟩
  let w₀ : BarycentricReweighting.Weights (B.TieVertex S) :=
    ⟨x.val, K.weight_nonneg x, K.weight_sum x⟩
  have hrw := BarycentricReweighting.reweight_mem_convexHull_iff a ha w w₀
  exact hmodel.trans (hrestrict.trans hrw)

theorem angularTiePoint_model_independent {J : Type*} [Fintype J]
    {η : ℝ} (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S)
    (hsmall : κ = .spherical → η < Real.pi)
    {σ : Finset (A.toVoronoiAtlas.TieVertex S)}
    (hσ : σ ∈ (A.toVoronoiAtlas.tieComplex S).faces)
    (v : J → (A.toVoronoiAtlas.tieComplex S).Space)
    (hv : ∀ j, (v j).val ∈ Barycentric.weightsOn σ)
    (hi : AffineIndependent ℝ (fun j => (v j).val)) :
    ModelBarycentric.Independent κ n (fun j =>
      A.toVoronoiAtlas.tieChart S hσ (A.angularTiePoint S hnet hp hsmall (v j))) := by
  let B := A.toVoronoiAtlas
  let K := B.tieComplex S
  let a := A.angularTieWeight S
  let ha := A.angularTieWeight_pos S hnet hsmall
  let w : J → BarycentricReweighting.Weights (B.TieVertex S) :=
    fun j => ⟨(v j).val, K.weight_nonneg (v j), K.weight_sum (v j)⟩
  have hirw := BarycentricReweighting.affineIndependent_reweight a ha w hi
  let rwv : J → Barycentric.weightsOn σ := fun j =>
    ⟨(K.reweight a ha (v j)).val, (K.reweight_mem_weightsOn_iff a ha (v j) σ).mpr (hv j)⟩
  have hir := (Barycentric.affineIndependent_restrict_iff σ rwv).mpr hirw
  exact ModelBarycentric.independent_of_barycentric
    (fun i : σ => B.tieChart S hσ (B.tieSource S i.val)) (A.tie_vertex_independent S hσ)
    _ (fun j => A.angularWeights S hnet hsmall (v j) (hv j))
    (fun j => A.angularTiePoint_represents S hnet hp hsmall hσ (v j) (hv j)) hir

end ArchivePLGeometry.ProjectiveVoronoiAtlas
