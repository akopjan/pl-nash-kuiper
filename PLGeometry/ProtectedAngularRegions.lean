module

public import PLGeometry.ProtectedNets
public import BrehmApprox.SphericalGeodesics

/-!
# Protected nearest sites in larger spherical regions

A cellwise protected net remains protected in a union of cells that embeds
as a short-arc-convex spherical region. Propagation takes place along an
actual minimizing arc; no global angular metric on the whole complex is used.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u
variable {P : Type u} [TopologicalSpace P] [T2Space P] {n : ℕ}
    (T : FiniteChartedComplex .spherical n P)

local instance protectedAngularRegionsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- Fine-cell protection propagates to every nearest site in a larger
spherical region whose angular chart preserves the fine-cell metrics. -/
theorem protected_nearest_in_spherical_region
    (I : Finset (Finset P)) (R : Set P)
    (hI : ∀ σ ∈ I, σ ∈ T.simplices)
    (hcell : ∀ σ ∈ I, T.cell σ ⊆ R)
    (hcover : ∀ x ∈ R, ∃ σ ∈ I, x ∈ T.cell σ)
    (q : P → GeodesicSphere n) (hq : ContinuousOn q R) (hinj : Set.InjOn q R)
    (hmetric : ∀ σ ∈ I, ∀ x ∈ T.cell σ, ∀ y ∈ T.cell σ,
      dist (q x) (q y) = dist (T.chart σ x) (T.chart σ y))
    (harc : ∀ a ∈ R, ∀ x ∈ R, ∀ hπ : dist (q a) (q x) < Real.pi,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        GeodesicSphere.geodesic (q a) (q x) hπ t ∈ q '' R)
    {S : Finset P} {δ : ℝ} (hnet : T.IsCellwiseNet S δ)
    (hprotected : T.IsCellwiseProtected S) (hδ : δ < Real.pi)
    {x a : P} (hx : x ∈ R)
    (ha : IsNearestFor (fun z w => dist (q z) (q w)) ((S : Set P) ∩ R) x a) :
    ∀ τ ∈ T.simplices, x ∈ T.cell τ → a ∈ T.cell τ := by
  have hR : IsCompact R := by
    have he : R = ⋃ σ ∈ I, T.cell σ := by
      ext z
      exact ⟨fun hz => by
        obtain ⟨σ, hσ, hzσ⟩ := hcover z hz
        exact Set.mem_iUnion₂.mpr ⟨σ, hσ, hzσ⟩, fun hz => by
        obtain ⟨σ, hσ, hz⟩ := Set.mem_iUnion₂.mp hz
        exact hcell σ hσ hz⟩
    rw [he]
    exact I.finite_toSet.isCompact_biUnion (fun σ hσ => T.compact_cell σ (hI σ hσ))
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let e₀ : R ≃ q '' R := Equiv.ofBijective
    (fun z => ⟨q z.val, Set.mem_image_of_mem q z.property⟩)
    ⟨fun z w he => Subtype.ext (hinj z.property w.property (congrArg Subtype.val he)),
      fun y => by
        obtain ⟨z, hz, he⟩ := y.property
        exact ⟨⟨z, hz⟩, Subtype.ext he⟩⟩
  let e : R ≃ₜ q '' R := Continuous.homeoOfEquivCompactToT2
    (f := e₀) (hq.domRestrict.subtype_mk _)
  have he_apply (z : R) : (e z).val = q z.val := rfl
  have hsmall : dist (q x) (q a) < δ := by
    obtain ⟨σ, hσ, hxσ⟩ := hcover x hx
    obtain ⟨b, hb, hbσ, hxb⟩ := hnet σ (hI σ hσ) x hxσ
    have hn := ha.2 b ⟨hb, hcell σ hσ hbσ⟩
    change dist (q x) (q a) ≤ dist (q x) (q b) at hn
    rw [hmetric σ hσ x hxσ b hbσ] at hn
    exact hn.trans_lt hxb
  have hπ : dist (q a) (q x) < Real.pi := by
    rw [dist_comm]
    exact hsmall.trans hδ
  let aR : R := ⟨a, ha.1.2⟩
  let xR : R := ⟨x, hx⟩
  let arc : Set.Icc (0 : ℝ) 1 → q '' R := fun t =>
    ⟨GeodesicSphere.geodesic (q a) (q x) hπ t.val, harc a ha.1.2 x hx hπ t.val t.property⟩
  let γ : Set.Icc (0 : ℝ) 1 → R := fun t => e.symm (arc t)
  have hγ : Continuous γ := e.symm.continuous.comp
    (((GeodesicSphere.geodesic_lipschitzOn (q a) (q x) hπ).continuousOn.domRestrict).subtype_mk _)
  have hqγ (t : Set.Icc (0 : ℝ) 1) :
      q (γ t).val = GeodesicSphere.geodesic (q a) (q x) hπ t.val := by
    have he := congrArg Subtype.val (e.apply_symm_apply (arc t))
    exact he
  have hγ0 : γ ⟨0, by constructor <;> norm_num⟩ = aR := by
    apply e.injective
    apply Subtype.ext
    rw [he_apply, hqγ, GeodesicSphere.geodesic_zero, he_apply]
  have hγ1 : γ ⟨1, by constructor <;> norm_num⟩ = xR := by
    apply e.injective
    apply Subtype.ext
    rw [he_apply, hqγ, GeodesicSphere.geodesic_one, he_apply]
  let C : Set R := Set.range γ
  have hC : IsPreconnected C := isPreconnected_range hγ
  have haC : aR ∈ C := ⟨⟨0, by constructor <;> norm_num⟩, hγ0⟩
  have hxC : xR ∈ C := ⟨⟨1, by constructor <;> norm_num⟩, hγ1⟩
  let d : R → R → ℝ := fun y z => dist (q y.val) (q z.val)
  let sites : Set R := {z | z.val ∈ S}
  have hnearest : ∀ y ∈ C, IsNearestFor d sites y aR := by
    rintro y ⟨t, rfl⟩
    apply isNearestFor_chart_along_minimizing (fun z : R => q z.val)
      (x := xR) (a := aR)
    · exact ⟨ha.1.1, fun b hb => ha.2 b.val ⟨hb, b.property⟩⟩
    · change dist (q x) (q a) = dist (q x) (q (γ t).val) + dist (q (γ t).val) (q a)
      rw [hqγ]
      have h₁ := GeodesicSphere.geodesic_dist (q a) (q x) hπ
        (s := 1) (t := t.val) (by constructor <;> norm_num) t.property
      have h₀ := GeodesicSphere.geodesic_dist (q a) (q x) hπ
        (s := t.val) (t := 0) t.property (by constructor <;> norm_num)
      rw [GeodesicSphere.geodesic_one, abs_of_nonneg (sub_nonneg.mpr t.property.2)] at h₁
      rw [GeodesicSphere.geodesic_zero, sub_zero, abs_of_nonneg t.property.1] at h₀
      rw [h₁, h₀, dist_comm (q x) (q a)]
      ring
  let cells : Finset P → Set R := fun σ => (Subtype.val : R → P) ⁻¹' T.cell σ
  have hprotect : ∀ σ ∈ I, ∀ τ ∈ I, ∀ z ∈ cells σ ∩ cells τ, ∀ b,
      IsNearestFor d (sites ∩ cells σ) z b → b ∈ cells τ := by
    intro σ hσ τ hτ z hz b hb
    apply hprotected σ (hI σ hσ) τ (hI τ hτ) z.val hz b.val
    refine ⟨⟨hb.1.1, hb.1.2⟩, ?_⟩
    intro c hc
    have hn := hb.2 ⟨c, hcell σ hσ hc.2⟩ ⟨hc.1, hc.2⟩
    change dist (q z.val) (q b.val) ≤ dist (q z.val) (q c) at hn
    rw [hmetric σ hσ z.val hz.1 b.val hb.1.2,
      hmetric σ hσ z.val hz.1 c hc.2] at hn
    exact hn
  have hall := protected_nearest_of_preconnected_locus I cells
    (fun σ hσ => (T.closed_cell σ (hI σ hσ)).preimage continuous_subtype_val)
    (fun z => hcover z.val z.property) d sites hprotect hC haC hnearest
  intro τ hτ hxτ
  obtain ⟨σ, hσ, hxσ⟩ := hcover x hx
  have haσ : a ∈ T.cell σ := hall xR hxC σ hσ hxσ
  apply hprotected σ (hI σ hσ) τ hτ x ⟨hxσ, hxτ⟩ a
  refine ⟨⟨ha.1.1, haσ⟩, ?_⟩
  intro b hb
  have hn := ha.2 b ⟨hb.1, hcell σ hσ hb.2⟩
  change dist (q x) (q a) ≤ dist (q x) (q b) at hn
  rw [hmetric σ hσ x hxσ a haσ, hmetric σ hσ x hxσ b hb.2] at hn
  exact hn

end ArchivePLGeometry.FiniteChartedComplex
