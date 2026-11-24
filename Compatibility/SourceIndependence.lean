module

public import Compatibility.Original

/-! Independence transported by injective maps preserving finite convex hulls. -/

@[expose] public section
noncomputable section

namespace PLGeometry

theorem affineIndependent_of_hull_preserving
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (σ : Finset V) (hσ : AffineIndependent ℝ (fun x : σ => (x : V)))
    (f : V → W) (hinj : Set.InjOn f (convexHull ℝ (σ : Set V)))
    (hhull : ∀ τ : Finset V, τ ⊆ σ →
      f '' convexHull ℝ (τ : Set V) = convexHull ℝ (f '' (τ : Set V))) :
    AffineIndependent ℝ (fun x : σ => f x.val) := by
  classical
  by_contra h
  obtain ⟨I, z, hzI, hzJ⟩ := Convex.radon_partition h
  let A : Finset V := I.toFinset.image Subtype.val
  let B : Finset V := Iᶜ.toFinset.image Subtype.val
  have hA : (A : Set V) = Subtype.val '' I := by
    simp only [A, Finset.coe_image, Set.coe_toFinset]
  have hB : (B : Set V) = Subtype.val '' Iᶜ := by
    simp only [B, Finset.coe_image, Set.coe_toFinset]
  have hAs : A ⊆ σ := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact v.property
  have hBs : B ⊆ σ := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact v.property
  have hzA : z ∈ f '' convexHull ℝ (A : Set V) := by
    rw [hhull A hAs, hA, Set.image_image]
    exact hzI
  have hzB : z ∈ f '' convexHull ℝ (B : Set V) := by
    rw [hhull B hBs, hB, Set.image_image]
    exact hzJ
  obtain ⟨a, ha, hfa⟩ := hzA
  obtain ⟨b, hb, hfb⟩ := hzB
  have hab : a = b := hinj
    (convexHull_mono (Finset.coe_subset.mpr hAs) ha)
    (convexHull_mono (Finset.coe_subset.mpr hBs) hb) (hfa.trans hfb.symm)
  have haI : a ∈ affineSpan ℝ (Subtype.val '' I) := by
    rw [← hA]
    exact convexHull_subset_affineSpan _ ha
  have haJ : a ∈ affineSpan ℝ (Subtype.val '' Iᶜ) := by
    rw [← hB, hab]
    exact convexHull_subset_affineSpan _ hb
  obtain ⟨i, hi, hni⟩ := hσ.exists_mem_inter_of_exists_mem_inter_affineSpan haI haJ
  exact hni hi

theorem Simplex.euclidean_vertex_independent {d m : ℕ} {σ : Finset (E m)}
    (S : Simplex .euclidean d m σ)
    (hσ : AffineIndependent ℝ (fun x : σ => (x : E m))) :
    AffineIndependent ℝ (fun x : σ => S.toModel x.val) := by
  apply affineIndependent_of_hull_preserving σ hσ S.toModel S.injective
  intro τ hτ
  exact S.convex τ ((Finset.coe_subset.mpr hτ).trans (subset_convexHull ℝ _))

end PLGeometry
