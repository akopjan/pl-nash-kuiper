module

public import PLGeometry.Basic
public import PLGeometry.FaceEnumeration
public import BrehmApprox.FoldedGeometry
public import BrehmApprox.SimplexFaces
public import BrehmApprox.SphericalFaceTransport
public import BrehmApprox.HyperbolicFaceTransport

/-!
# Finite folded triangulations as ordered face systems

A finite geodesic triangulation is enumerated with proper subfaces first.
A cellwise isometric folding then gives the ordered face system used by the
approximation argument. Cofacial intersections are inherited from the source,
so overlaps of unrelated folded sheets do not impose extra identifications.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.Triangulation

universe u
variable {κ : Geometry} {n : ℕ} {P : Type u} [MetricSpace P]
    (T : Triangulation κ n P)

local instance foldedTransportDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance foldedTransportSourceDecidableEq : DecidableEq P := Classical.decEq _
local instance foldedTransportModelDecidableEq : DecidableEq (Model κ n) := Classical.decEq _

def meetIndex (e : FaceEnumeration T.simplices) (i j : Fin e.count) : Fin e.count :=
  e.face.symm ⟨(e.face i).val ∩ (e.face j).val,
    T.faces _ (e.face i).property _ Finset.inter_subset_left⟩

@[simp] theorem face_meetIndex (e : FaceEnumeration T.simplices) (i j : Fin e.count) :
    (e.face (T.meetIndex e i j)).val = (e.face i).val ∩ (e.face j).val :=
  congrArg Subtype.val (e.face.apply_symm_apply _)

theorem folding_injective_cell (q : P → Model κ n)
    (hq : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist x y)
    {σ : Finset P} (hσ : σ ∈ T.simplices) : Set.InjOn q (T.cell σ) := by
  intro x hx y hy he
  apply dist_eq_zero.mp
  rw [← hq σ hσ x hx y hy, he, dist_self]

def toFoldedGeometry {Good : (Model κ n → Model κ n) → Prop}
    (M : PolytopeModel (Model κ n) Good)
    (e : FaceEnumeration T.simplices) (q : P → Model κ n)
    (hq : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist x y)
    (hpoly : ∀ σ ∈ T.simplices, M.Polytope (q '' T.cell σ))
    (hT : Intrinsic T) : FoldedGeometry (P := P) M e.count where
  faceLE i j := (e.face i).val ⊆ (e.face j).val
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  index_strict i j hij hne := e.index_strict i j hij hne
  meet := T.meetIndex e
  meet_comm i j := by
    apply e.face.injective
    apply Subtype.ext
    simp only [T.face_meetIndex, Finset.inter_comm]
  meet_le_left i j := by simp only [T.face_meetIndex]; exact Finset.inter_subset_left
  meet_le_right i j := by simp only [T.face_meetIndex]; exact Finset.inter_subset_right
  core i := q '' T.cell (e.face i).val
  polytope_core i := hpoly _ (e.face i).property
  core_mono i j hij := Set.image_mono (T.cell_mono (e.face j).property hij)
  core_inter i j k hji hki := by
    rw [T.face_meetIndex, ← T.intersection _ (e.face j).property _ (e.face k).property]
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
      have he : y = x := T.folding_injective_cell q hq (e.face i).property
        (T.cell_mono (e.face i).property hki hy)
        (T.cell_mono (e.face i).property hji hx) hyx
      subst y
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, x, hy, rfl⟩
  cell i := T.cell (e.face i).val
  cover x := by
    obtain ⟨σ, hσ, hx⟩ := T.cover x
    refine ⟨e.face.symm ⟨σ, hσ⟩, ?_⟩
    simpa only [e.face.apply_symm_apply] using hx
  fold := q
  image_cell _ := rfl
  isometry_cell i := hq _ (e.face i).property
  cell_mono i j hij := T.cell_mono (e.face j).property hij
  intersection i j := by
    rw [T.face_meetIndex, T.intersection _ (e.face i).property _ (e.face j).property]
  intrinsic := by
    intro x y ε hε
    obtain ⟨m, z, h0, hm, hc, hcost⟩ := hT x y ε hε
    refine ⟨m, z, h0, hm, ?_, hcost⟩
    intro j hj
    obtain ⟨σ, hσ, hx, hy⟩ := hc j hj
    exact ⟨e.face.symm ⟨σ, hσ⟩, by simpa using hx, by simpa using hy⟩

/-- Every subfamily of folded vertices comes from an actual source face. -/
theorem folded_vertices_all_subfaces (e : FaceEnumeration T.simplices)
    (q : P → Model κ n) (i : Fin e.count) (W : Finset (Model κ n))
    (hW : W ⊆ (e.face i).val.image q) :
    ∃ j : Fin e.count, (e.face j).val ⊆ (e.face i).val ∧ (e.face j).val.image q = W := by
  let σ := (e.face i).val.filter (fun x => q x ∈ W)
  have hσ : σ ∈ T.simplices := T.faces _ (e.face i).property σ (Finset.filter_subset _ _)
  refine ⟨e.face.symm ⟨σ, hσ⟩, ?_, ?_⟩
  · simp only [e.face.apply_symm_apply]
    exact Finset.filter_subset _ _
  · simp only [e.face.apply_symm_apply]
    ext x
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hW hx)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hx⟩, rfl⟩

/-- In one source simplex, inclusion of folded vertex sets detects face inclusion. -/
theorem face_of_folded_vertices (e : FaceEnumeration T.simplices)
    (q : P → Model κ n)
    (hq : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist x y)
    (i j k : Fin e.count)
    (hik : (e.face i).val ⊆ (e.face k).val)
    (hjk : (e.face j).val ⊆ (e.face k).val)
    (hij : (e.face i).val.image q ⊆ (e.face j).val.image q) :
    (e.face i).val ⊆ (e.face j).val := by
  intro x hx
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp (hij (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  have hyx : y = x := T.folding_injective_cell q hq (e.face k).property
    (T.vertices_mem _ (e.face k).property (hjk hy))
    (T.vertices_mem _ (e.face k).property (hik hx)) he
  exact hyx ▸ hy

end ArchivePLGeometry.Triangulation
