module

public import PLGeometry.EuclideanLinkCoverage
public import PLGeometry.LinkRegionCells
public import PLGeometry.AngularRegions

/-! # The complete angular region of an old Euclidean simplex -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex .euclidean (n + 1) P)

local instance euclideanAngularRegionDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def euclideanAngularRegion {p : P} {σ : Finset P}
    (hσ : σ ∈ T.simplices) (hpσ : p ∈ T.cell σ) : AngularRegion (T.euclideanLink p) where
  carrier := T.linkRegion p σ
  pieces := T.linkRegionPieces p σ
  valid := fun _ h => T.linkRegionPieces_valid h
  contained := fun _ h => T.linkRegionPieces_contained h
  cover := fun _ h => T.linkRegionPieces_cover h
  coordinate := T.euclideanAngularChart p σ
  continuous := T.continuousOn_euclideanAngularChart hσ hpσ
  injective := T.euclideanAngularChart_injectiveOn hσ hpσ
  metric := by
    intro S hS x hx y hy
    obtain ⟨τ, hτ, hsub, rfl⟩ := T.mem_linkRegionPieces.mp hS
    change x.val ∈ Barycentric.weightsOn ((T.linkComplex p).labels ((T.linkComplex p).vertices τ)) at hx
    change y.val ∈ Barycentric.weightsOn ((T.linkComplex p).labels ((T.linkComplex p).vertices τ)) at hy
    rw [(T.linkComplex p).labels_vertices] at hx hy
    change dist _ _ = dist (Barycentric.chartPoint
      (T.euclideanLinkPoint p ((T.linkComplex p).labels ((T.linkComplex p).vertices τ))) x.val)
      (Barycentric.chartPoint
      (T.euclideanLinkPoint p ((T.linkComplex p).labels ((T.linkComplex p).vertices τ))) y.val)
    rw [(T.linkComplex p).labels_vertices]
    exact T.euclideanAngularChart_dist_on_face hτ hσ hpσ hsub x y hx hy
  arcs := fun _ hx _ hy hπ _ ht =>
    T.geodesic_mem_image_euclideanAngularChart hσ hpσ hx hy hπ ht

end ArchivePLGeometry.FiniteChartedComplex
