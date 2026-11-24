module

public import PLGeometry.VoronoiConeRefinement
public import BrehmApprox.ExtremeHullRestriction

/-! # Transporting a refined tie complex to every Voronoi base -/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry

universe u v w
variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [LinearOrder E] (A : ProjectiveVoronoiAtlas T E) (S : Finset P)
    {κ' : Geometry} {m : ℕ} {Q : Type w} [TopologicalSpace Q] [T2Space Q]
    (U : FiniteChartedComplex κ' m Q) (f : Q → P)

local instance voronoiBaseTransportDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance voronoiBaseTransportEDecidableEq : DecidableEq E := Classical.decEq E

def TransportedTieIndex :=
  {j : VoronoiAtlas.TieIndex (T := T) S × U.simplices |
    convexHull ℝ (j.2.val.image (A.coord ∘ f) : Set E) ⊆ A.toVoronoiAtlas.tiePiece S j.1}

instance transportedTieIndexFinite : Finite (TransportedTieIndex A S U f) := by
  let : Finite U.simplices := U.finite_simplices.to_subtype
  unfold TransportedTieIndex
  infer_instance

theorem composed_image (V : Finset Q) :
    (V.image f).image A.coord = V.image (A.coord ∘ f) := by
  ext z
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨f v, ⟨v, hv, rfl⟩, rfl⟩

def transportedVoronoiBaseFamily {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (hf : Function.Injective f)
    (hgeometry : ∀ V ∈ U.simplices,
      AffineIndependent ℝ ((↑) : V.image (A.coord ∘ f) → E) ∧
      (A.coord ∘ f) '' U.cell V = convexHull ℝ (V.image (A.coord ∘ f) : Set E))
    (hcoface : ∀ V ∈ U.simplices, ∃ i : VoronoiAtlas.TieIndex (T := T) S,
      convexHull ℝ (V.image (A.coord ∘ f) : Set E) ⊆ A.toVoronoiAtlas.tiePiece S i)
    (hcover : ∀ i : VoronoiAtlas.TieIndex (T := T) S,
      ∀ z ∈ A.toVoronoiAtlas.tiePiece S i, ∃ x : Q, A.coord (f x) = z) :
    VoronoiBaseFamily A S (TransportedTieIndex A S U f) where
  vertices j := j.val.2.val.image f
  index j := j.val.1
  independent j := by
    rw [composed_image A f]
    exact (hgeometry _ j.val.2.property).1
  subset_tie j := by
    rw [composed_image A f]
    exact j.property
  intersection i j := by
    let V := i.val.2.val
    let W := j.val.2.val
    have hV := i.val.2.property
    have hW := j.val.2.property
    have hVW := U.faces V hV (V ∩ W) Finset.inter_subset_left
    have hG : Function.Injective (A.coord ∘ f) := A.injective.comp hf
    have hfVW : (V.image f ∩ W.image f) = (V ∩ W).image f :=
      (Finset.image_inter V W hf).symm
    change convexHull ℝ ((V.image f).image A.coord : Set E) ∩
      convexHull ℝ ((W.image f).image A.coord : Set E) =
      convexHull ℝ ((V.image f ∩ W.image f).image A.coord : Set E)
    rw [hfVW, composed_image A f V, composed_image A f W,
      composed_image A f (V ∩ W), ← (hgeometry V hV).2, ← (hgeometry W hW).2,
      ← (hgeometry (V ∩ W) hVW).2, ← Set.image_inter hG, U.intersection V hV W hW]
  cover i z hz := by
    let G := A.coord ∘ f
    obtain ⟨x, hx⟩ := hcover i z hz
    obtain ⟨V, hV, hxV⟩ := U.cover x
    obtain ⟨j, hVj⟩ := hcoface V hV
    have hzV : z ∈ convexHull ℝ (V.image G : Set E) := by
      rw [← (hgeometry V hV).2]
      exact ⟨x, hxV, hx⟩
    let C := A.toVoronoiAtlas.tiePiece S j
    let D := C ∩ A.toVoronoiAtlas.tiePiece S i
    have hC : Convex ℝ C := (A.toVoronoiAtlas.tiePiece_polytope S j).convex
    have hD : Convex ℝ D := hC.inter (A.toVoronoiAtlas.tiePiece_polytope S i).convex
    have hCD : _root_.IsExtreme ℝ C D :=
      A.toVoronoiAtlas.tiePiece_face_inter hnet hp j i
    have hvertices : (V.image G : Set E) ⊆ C :=
      fun y hy => hVj (subset_convexHull ℝ _ hy)
    have hh := convexHull_inter_extreme (V.image G) hC hD hCD hvertices
    have hzD : z ∈ D := ⟨hVj hzV, hz⟩
    have hzfilter : z ∈ convexHull ℝ ((V.image G).filter (fun y => y ∈ D) : Set E) := by
      simpa only [Finset.coe_filter] using hh.subset ⟨hzV, hzD⟩
    let W := V.filter (fun y => G y ∈ D)
    have hWV : W ⊆ V := Finset.filter_subset _ _
    have hW := U.faces V hV W hWV
    have he : W.image G = (V.image G).filter (fun y => y ∈ D) := by
      ext y
      simp only [W, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨q, ⟨hq, hqD⟩, rfl⟩
        exact ⟨⟨q, hq, rfl⟩, hqD⟩
      · rintro ⟨⟨q, hq, rfl⟩, hqD⟩
        exact ⟨q, ⟨hq, hqD⟩, rfl⟩
    have hWi : convexHull ℝ (W.image G : Set E) ⊆ A.toVoronoiAtlas.tiePiece S i := by
      intro y hy
      have hyD : y ∈ D := by
        apply convexHull_min ?_ hD hy
        intro q hq
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
        exact (Finset.mem_filter.mp hr).2
      exact hyD.2
    refine ⟨⟨⟨i, ⟨W, hW⟩⟩, hWi⟩, rfl, ?_⟩
    rw [composed_image A f W, he]
    exact hzfilter

end ArchivePLGeometry
