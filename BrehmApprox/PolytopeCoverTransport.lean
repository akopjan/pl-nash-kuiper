module

public import BrehmApprox.PolytopeArrangementCover
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Transport of polyhedral covers by linear coordinates
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology

namespace BrehmApprox

variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isExtreme_linear_preimage {C D : Set E}
    (h : _root_.IsExtreme ℝ C D) (L : F →ₗ[ℝ] E) :
    _root_.IsExtreme ℝ (L ⁻¹' C) (L ⁻¹' D) := by
  refine ⟨Set.preimage_mono h.subset, ?_⟩
  intro x hx y hy z hz hseg
  apply h.left_mem_of_mem_openSegment hx hy hz
  obtain ⟨a, d, ha, hd, had, rfl⟩ := hseg
  exact ⟨a, d, ha, hd, had, by simp⟩

theorem locallyFinite_preimage_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : I → Set X} (hC : LocallyFinite C) {f : Y → X} (hf : Continuous f) :
    LocallyFinite (fun i => f ⁻¹' C i) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := hC (f x)
  refine ⟨f ⁻¹' U, hf.continuousAt.preimage_mem_nhds hU, hfin.subset ?_⟩
  rintro i ⟨y, hyC, hyU⟩
  exact ⟨f y, hyC, hyU⟩

def PolytopeCover.map (K : PolytopeCover E I) (e : E ≃L[ℝ] F) : PolytopeCover F I where
  cell i := e.symm ⁻¹' K.cell i
  polytope i := by
    classical
    obtain ⟨V, hV⟩ := K.polytope i
    refine ⟨V.image e, ?_⟩
    have himage : e.symm ⁻¹' K.cell i = e '' K.cell i := by
      ext x
      constructor
      · intro hx
        exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        change e.symm (e y) ∈ K.cell i
        simpa only [e.symm_apply_apply] using hy
    rw [himage, hV, Finset.coe_image]
    exact e.toLinearMap.image_convexHull _
  cover x := K.cover (e.symm x)
  locallyFinite := locallyFinite_preimage_continuous K.locallyFinite e.symm.continuous
  face_inter i j := isExtreme_linear_preimage (K.face_inter i j) e.symm.toLinearMap

def euclideanCubeCover (n : ℕ) :
    PolytopeCover (EuclideanSpace ℝ (Fin n)) (Fin n → ℤ) :=
  (integerCubeCover (Fin n)).map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

end BrehmApprox
