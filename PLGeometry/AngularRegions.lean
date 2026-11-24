module

public import PLGeometry.ProtectedAngularRegions

/-! # Embedded unions of spherical cells -/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry

universe u
variable {m : ℕ} {L : Type u} [TopologicalSpace L] [T2Space L]

structure AngularRegion (A : FiniteChartedComplex .spherical m L) where
  carrier : Set L
  pieces : Finset (Finset L)
  valid : ∀ σ ∈ pieces, σ ∈ A.simplices
  contained : ∀ σ ∈ pieces, A.cell σ ⊆ carrier
  cover : ∀ x ∈ carrier, ∃ σ ∈ pieces, x ∈ A.cell σ
  coordinate : L → GeodesicSphere m
  continuous : ContinuousOn coordinate carrier
  injective : Set.InjOn coordinate carrier
  metric : ∀ σ ∈ pieces, ∀ x ∈ A.cell σ, ∀ y ∈ A.cell σ,
    dist (coordinate x) (coordinate y) = dist (A.chart σ x) (A.chart σ y)
  arcs : ∀ a ∈ carrier, ∀ x ∈ carrier, ∀ hπ : dist (coordinate a) (coordinate x) < Real.pi,
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      GeodesicSphere.geodesic (coordinate a) (coordinate x) hπ t ∈ coordinate '' carrier

namespace AngularRegion

variable {A : FiniteChartedComplex .spherical m L} (R : AngularRegion A)

theorem net {S : Finset L} {δ : ℝ} (hnet : A.IsCellwiseNet S δ)
    {x : L} (hx : x ∈ R.carrier) :
    ∃ a ∈ S, a ∈ R.carrier ∧ dist (R.coordinate x) (R.coordinate a) < δ := by
  obtain ⟨σ, hσ, hxσ⟩ := R.cover x hx
  obtain ⟨a, ha, haσ, hdist⟩ := hnet σ (R.valid σ hσ) x hxσ
  exact ⟨a, ha, R.contained σ hσ haσ, by rwa [R.metric σ hσ x hxσ a haσ]⟩

theorem protected_nearest {S : Finset L} {δ : ℝ} (hnet : A.IsCellwiseNet S δ)
    (hprotected : A.IsCellwiseProtected S) (hδ : δ < Real.pi)
    {x a : L} (hx : x ∈ R.carrier)
    (ha : IsNearestFor (fun z w => dist (R.coordinate z) (R.coordinate w))
      ((S : Set L) ∩ R.carrier) x a) :
    ∀ τ ∈ A.simplices, x ∈ A.cell τ → a ∈ A.cell τ :=
  A.protected_nearest_in_spherical_region R.pieces R.carrier R.valid R.contained R.cover
    R.coordinate R.continuous R.injective R.metric R.arcs hnet hprotected hδ hx ha

end AngularRegion
end ArchivePLGeometry
