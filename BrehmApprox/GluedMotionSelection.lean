module

public import BrehmApprox.GluedModelMaps

/-! # Finite rigid-motion branches of the glued approximation -/

@[expose] public section
noncomputable section

open Set

namespace BrehmApprox.FoldedGeometry

variable {P : Type*} [MetricSpace P] {n N : ℕ}

theorem RealizedByModelMaps.euclidean_motions
    {G : FoldedGeometry (P := P) (euclideanPolytopeModel n) N}
    {g : P → EuclideanSpace ℝ (Fin n)} (h : G.RealizedByModelMaps g) :
    ∃ R : Finset (EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)),
      ∀ x, ∃ r ∈ R, g x = r (G.fold x) := by
  classical
  obtain ⟨H, hH, hg⟩ := h
  have hpoly : ∀ i, ∃ V : Finset (EuclideanSpace ℝ (Fin n)),
      G.core i = convexHull ℝ (V : Set _) := G.polytope_core
  choose V hV using hpoly
  have hp := fun i => hH i (V i)
  choose C hC hr using hp
  let J := Σ i : Fin N, C i
  let r : J → EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun j => (hr j.1 j.2.val j.2.property).choose
  refine ⟨Finset.univ.image r, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := G.cover x
  have hx : G.fold x ∈ G.core i := by
    rw [← G.image_cell i]
    exact Set.mem_image_of_mem G.fold hxi
  rw [hV i, hC i] at hx
  obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.mp hx
  let j : J := ⟨i, ⟨D, hD⟩⟩
  refine ⟨r j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
  exact (hg i x hxi).trans ((hr i D hD).choose_spec (G.fold x) hxD)

theorem RealizedByModelMaps.spherical_motions
    {G : FoldedGeometry (P := P) (sphericalPolytopeModel n) N}
    {g : P → GeodesicSphere n} (h : G.RealizedByModelMaps g) :
    ∃ R : Finset (EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))),
      ∀ x, ∃ r ∈ R, g x = GeodesicSphere.mapEquiv r (G.fold x) := by
  classical
  obtain ⟨H, hH, hg⟩ := h
  have hpoly : ∀ i, ∃ V : Finset (GeodesicSphere n),
      InOpenHemisphere V ∧ G.core i = sphericalCell V := G.polytope_core
  choose V hhem hV using hpoly
  have hp := fun i => hH i (V i) (hhem i)
  choose C hC hr using hp
  let J := Σ i : Fin N, C i
  let r : J → EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    fun j => ((hr j.1 j.2.val j.2.property).2).choose
  refine ⟨Finset.univ.image r, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := G.cover x
  have hx : G.fold x ∈ G.core i := by
    rw [← G.image_cell i]
    exact Set.mem_image_of_mem G.fold hxi
  rw [hV i, hC i] at hx
  obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.mp hx
  let j : J := ⟨i, ⟨D, hD⟩⟩
  refine ⟨r j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
  exact (hg i x hxi).trans (((hr i D hD).2).choose_spec (G.fold x) hxD)

theorem RealizedByModelMaps.hyperbolic_motions
    {G : FoldedGeometry (P := P) (hyperbolicPolytopeModel n) N}
    {g : P → HyperbolicSpace n} (h : G.RealizedByModelMaps g) :
    ∃ R : Finset (HyperbolicSpace n ≃ᵢ HyperbolicSpace n),
      ∀ x, ∃ r ∈ R, g x = r (G.fold x) := by
  classical
  obtain ⟨H, hH, hg⟩ := h
  have hpoly : ∀ i, ∃ V : Finset (HyperbolicSpace n),
      G.core i = hyperbolicCell V := G.polytope_core
  choose V hV using hpoly
  have hp := fun i => hH i (V i)
  choose C hC hr using hp
  let J := Σ i : Fin N, C i
  let r : J → HyperbolicSpace n ≃ᵢ HyperbolicSpace n :=
    fun j => (hr j.1 j.2.val j.2.property).choose
  refine ⟨Finset.univ.image r, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := G.cover x
  have hx : G.fold x ∈ G.core i := by
    rw [← G.image_cell i]
    exact Set.mem_image_of_mem G.fold hxi
  rw [hV i, hC i] at hx
  obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.mp hx
  let j : J := ⟨i, ⟨D, hD⟩⟩
  refine ⟨r j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
  exact (hg i x hxi).trans ((hr i D hD).choose_spec (G.fold x) hxD)

end BrehmApprox.FoldedGeometry
