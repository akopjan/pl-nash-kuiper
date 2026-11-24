module

public import Compatibility.Models
public import PLGeometry.ChartedCellRigidity
public import PLGeometry.ChartedIncidence

/-! A charted triangulation whose cells are actual convex hulls in the
original ambient space gives a geometric simplicial complex there. -/

@[expose] public section
noncomputable section

namespace PLGeometry

open Set

universe u

namespace ChartedRealization

variable {κ : ArchivePLGeometry.Geometry} {n m : ℕ}
    {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : ArchivePLGeometry.FiniteChartedComplex κ n P)
    (e : P → E m) (he : Function.Injective e)
    (hhull : ∀ σ ∈ T.simplices,
      e '' T.cell σ = convexHull ℝ (e '' (σ : Set P)))

include he hhull in
theorem vertex_independent (σ : Finset P) (hσ : σ ∈ T.simplices) :
    AffineIndependent ℝ (fun v : σ => e v.val) := by
  classical
  by_contra h
  obtain ⟨I, z, hzI, hzJ⟩ := Convex.radon_partition h
  let A : Finset P := I.toFinset.image Subtype.val
  let B : Finset P := Iᶜ.toFinset.image Subtype.val
  have hA : (A : Set P) = Subtype.val '' I := by
    simp only [A, Finset.coe_image, Set.coe_toFinset]
  have hB : (B : Set P) = Subtype.val '' Iᶜ := by
    simp only [B, Finset.coe_image, Set.coe_toFinset]
  have hAs : A ⊆ σ := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  have hBs : B ⊆ σ := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  have hAm := T.faces σ hσ A hAs
  have hBm := T.faces σ hσ B hBs
  have hzA : z ∈ e '' T.cell A := by
    rw [hhull A hAm, hA, Set.image_image]
    exact hzI
  have hzB : z ∈ e '' T.cell B := by
    rw [hhull B hBm, hB, Set.image_image]
    exact hzJ
  obtain ⟨a, ha, hea⟩ := hzA
  obtain ⟨b, hb, heb⟩ := hzB
  have hab := he (hea.trans heb.symm)
  have hAB : A ∩ B = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hv
    obtain ⟨a, ha, hva⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb, hvb⟩ := Finset.mem_image.mp hb
    have heq : a = b := Subtype.ext (hva.trans hvb.symm)
    have hai : a ∈ I := Set.mem_toFinset.mp ha
    have hbi : b ∉ I := Set.mem_toFinset.mp hb
    exact hbi (heq ▸ hai)
  have hm : a ∈ T.cell (A ∩ B) := by
    rw [← T.intersection A hAm B hBm]
    exact ⟨ha, hab ▸ hb⟩
  rw [hAB, T.cell_empty (T.faces σ hσ ∅ (Finset.empty_subset σ))] at hm
  exact hm

include he hhull in
theorem image_vertex_independent (σ : Finset P) (hσ : σ ∈ T.simplices) :
    AffineIndependent ℝ ((↑) : σ.image e → E m) := by
  classical
  let q : σ ≃ σ.image e := Equiv.ofBijective
    (fun v => ⟨e v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩) (by
      constructor
      · intro v w h
        exact Subtype.ext (he (congrArg Subtype.val h))
      · intro z
        obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp z.property
        exact ⟨⟨v, hv⟩, Subtype.ext heq⟩)
  have hi := (vertex_independent T e he hhull σ hσ).comp_embedding q.symm.toEmbedding
  convert hi using 1
  funext z
  exact (congrArg Subtype.val (q.apply_symm_apply z)).symm

def faces : Set (Finset (E m)) :=
  (fun σ : Finset P => σ.image e) '' T.simplices

theorem finite_faces : (faces T e).Finite :=
  T.finite_simplices.image _

theorem faces_lower : IsLowerSet (faces T e) := by
  classical
  intro s t hst ht
  obtain ⟨σ, hσ, rfl⟩ := ht
  obtain ⟨τ, hτσ, hτ⟩ := Finset.subset_image_iff.mp hst
  exact ⟨τ, T.faces σ hσ τ hτσ, hτ⟩

include he hhull in
theorem hull_inter (σ : Finset P) (hσ : σ ∈ T.simplices)
    (τ : Finset P) (hτ : τ ∈ T.simplices) :
    convexHull ℝ (σ.image e : Set (E m)) ∩
      convexHull ℝ (τ.image e : Set (E m)) =
    convexHull ℝ ((σ.image e ∩ τ.image e : Finset (E m)) : Set (E m)) := by
  classical
  have hστ := T.faces σ hσ (σ ∩ τ) Finset.inter_subset_left
  rw [← Finset.image_inter σ τ he]
  simp only [Finset.coe_image]
  rw [← hhull σ hσ, ← hhull τ hτ, ← hhull (σ ∩ τ) hστ,
    ← Set.image_inter he, T.intersection σ hσ τ hτ]

def complex : _root_.Geometry.SimplicialComplex ℝ (E m) :=
  _root_.Geometry.SimplicialComplex.ofErase (faces T e)
    (by
      rintro s ⟨σ, hσ, rfl⟩
      exact image_vertex_independent T e he hhull σ hσ)
    (faces_lower T e)
    (by
      rintro s ⟨σ, hσ, rfl⟩ t ⟨τ, hτ, rfl⟩
      simpa only [Finset.coe_inter] using (hull_inter T e he hhull σ hσ τ hτ).subset)

theorem complex_finite : (complex T e he hhull).faces.Finite :=
  (finite_faces T e).subset (fun _ h => h.1)

theorem complex_space : (complex T e he hhull).space = Set.range e := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs, hz⟩ := _root_.Geometry.SimplicialComplex.mem_space_iff.mp hz
    obtain ⟨σ, hσ, rfl⟩ := hs.1
    rw [Finset.coe_image, ← hhull σ hσ] at hz
    obtain ⟨x, _, rfl⟩ := hz
    exact Set.mem_range_self x
  · rintro ⟨x, rfl⟩
    obtain ⟨σ, hσ, hx⟩ := T.cover x
    have hσne : σ ≠ ∅ := by
      intro heq
      subst σ
      rw [T.cell_empty hσ] at hx
      exact hx
    refine _root_.Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨σ.image e, ⟨⟨σ, hσ, rfl⟩, ?_⟩, ?_⟩
    · simpa only [Set.mem_singleton_iff, Finset.image_eq_empty] using hσne
    · rw [Finset.coe_image, ← hhull σ hσ]
      exact Set.mem_image_of_mem e hx

theorem face_origin {s : Finset (E m)}
    (hs : s ∈ (complex T e he hhull).faces) :
    ∃ σ ∈ T.simplices, σ.image e = s := hs.1

end ChartedRealization

end PLGeometry
