module

public import PLGeometry.AngularRegions
public import BrehmApprox.RadialProductGrids

/-!
# Local polar geometry for protected nets

The data record actual polar coordinates near one source point: embedded
angular regions, source radial points, incidence, a uniform metric modulus,
and the strict angular comparison furnished by the cosine laws.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox

namespace ArchivePLGeometry

universe u v
variable {κ : Geometry} {n m : ℕ} {P : Type u} {L : Type v}
    [TopologicalSpace P] [T2Space P] [TopologicalSpace L] [T2Space L]

structure PolarNetData (T : FiniteChartedComplex κ n P) (p : P)
    (A : FiniteChartedComplex .spherical m L) where
  radius : ℝ
  radius_pos : 0 < radius
  region : ∀ σ, σ ∈ T.simplices → p ∈ T.cell σ → AngularRegion A
  point : ℝ → L → P
  point_zero : ∀ u, point 0 u = p
  point_mem : ∀ σ, ∀ hσ : σ ∈ T.simplices, ∀ hpσ : p ∈ T.cell σ,
    ∀ r : ℝ, 0 < r → r ≤ 2 * radius → ∀ u,
      point r u ∈ T.cell σ ↔ u ∈ (region σ hσ hpσ).carrier
  point_radius : ∀ r : ℝ, 0 ≤ r → r ≤ radius → ∀ u,
    T.radialDistance p (point r u) = r
  point_star : ∀ r : ℝ, 0 ≤ r → r ≤ radius → ∀ u,
    point r u ∈ T.openStar p
  reconstruct : ∀ σ, ∀ hσ : σ ∈ T.simplices, ∀ hpσ : p ∈ T.cell σ,
    ∀ x ∈ T.cell σ, 0 < T.radialDistance p x → T.radialDistance p x < 2 * radius →
      ∃ u ∈ (region σ hσ hpσ).carrier, point (T.radialDistance p x) u = x
  metric_modulus : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ σ, ∀ hσ : σ ∈ T.simplices, ∀ hpσ : p ∈ T.cell σ,
    ∀ u ∈ (region σ hσ hpσ).carrier, ∀ v ∈ (region σ hσ hpσ).carrier,
    ∀ r ∈ Set.Icc (0 : ℝ) (2 * radius), ∀ s ∈ Set.Icc (0 : ℝ) (2 * radius),
      |r - s| < δ → dist ((region σ hσ hpσ).coordinate u)
        ((region σ hσ hpσ).coordinate v) < δ →
      dist (T.chart σ (point r u)) (T.chart σ (point s v)) < ε
  strict_comparison : ∀ σ, ∀ hσ : σ ∈ T.simplices, ∀ hpσ : p ∈ T.cell σ,
    ∀ u ∈ (region σ hσ hpσ).carrier, ∀ v ∈ (region σ hσ hpσ).carrier,
    ∀ w ∈ (region σ hσ hpσ).carrier,
    ∀ r : ℝ, 0 < r → r < 2 * radius → ∀ s : ℝ, 0 < s → s ≤ radius →
      dist ((region σ hσ hpσ).coordinate u) ((region σ hσ hpσ).coordinate v) <
        dist ((region σ hσ hpσ).coordinate u) ((region σ hσ hpσ).coordinate w) →
      dist (T.chart σ (point r u)) (T.chart σ (point s v)) <
        dist (T.chart σ (point r u)) (T.chart σ (point s w))

structure LocalProtectedGrid (T : FiniteChartedComplex κ n P) (p : P) (r δ : ℝ) where
  sites : Finset P
  center_mem : p ∈ sites
  star : ∀ a ∈ sites, a ∈ T.openStar p
  radius : ∀ a ∈ sites, T.radialDistance p a ≤ r
  net : ∀ σ ∈ T.simplices, ∀ x ∈ T.cell σ, x ∈ T.starBall p r →
    ∃ a ∈ sites, a ∈ T.cell σ ∧ dist (T.chart σ x) (T.chart σ a) < δ
  protection : ∀ σ ∈ T.simplices, ∀ τ ∈ T.simplices, p ∈ T.cell σ → p ∈ T.cell τ →
    ∀ x ∈ T.cell σ ∩ T.cell τ, T.radialDistance p x < 2 * r → ∀ a,
      IsNearestFor (fun z w => dist (T.chart σ z) (T.chart σ w))
        ((sites : Set P) ∩ T.cell σ) x a → a ∈ T.cell τ

namespace PolarNetData

variable {T : FiniteChartedComplex κ n P} {p : P}
    {A : FiniteChartedComplex .spherical m L} (D : PolarNetData T p A)

local instance polarNetDataDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

include D in
theorem radialDistance_pos {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) {x : P} (hxσ : x ∈ T.cell σ) (hxp : x ≠ p) :
    0 < T.radialDistance p x := by
  rw [T.radialDistance_eq p hσ hpσ hxσ]
  apply dist_pos.mpr
  exact fun h => hxp (T.chart_injectiveOn σ hσ hxσ hpσ h.symm)

theorem point_mem_of_nonneg {σ : Finset P} (hσ : σ ∈ T.simplices)
    (hpσ : p ∈ T.cell σ) {r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ D.radius)
    {u : L} (hu : u ∈ (D.region σ hσ hpσ).carrier) : D.point r u ∈ T.cell σ := by
  rcases hr.eq_or_lt with rfl | hr
  · simpa only [D.point_zero] using hpσ
  · exact (D.point_mem σ hσ hpσ r hr (by linarith [D.radius_pos]) u).mpr hu

/-- A protected angular net and a common radial mesh give an actual finite
protected grid in the source open star. -/
theorem exists_localProtectedGrid
    (hangular : ∀ ε : ℝ, 0 < ε → ∃ S : Finset L,
      A.IsCellwiseNet S ε ∧ A.IsCellwiseProtected S)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (LocalProtectedGrid T p D.radius ε) := by
  obtain ⟨δ, hδ, hmesh⟩ := D.metric_modulus ε hε
  let η : ℝ := min δ Real.pi / 2
  have hη : 0 < η := div_pos (lt_min hδ Real.pi_pos) (by norm_num)
  have hηδ : η < δ := by
    have hh := min_le_left δ Real.pi
    have hhpos := lt_min hδ Real.pi_pos
    dsimp only [η]
    linarith
  have hηπ : η < Real.pi := by
    have hh := min_le_right δ Real.pi
    have hhpos := lt_min hδ Real.pi_pos
    dsimp only [η]
    linarith
  obtain ⟨S, hSnet, hSprotected⟩ := hangular η hη
  obtain ⟨R, hRsub, hRfin, hRcover⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) D.radius)).finite_cover_balls hδ
  let radii : Finset ℝ := hRfin.toFinset
  have hradii (r : ℝ) (hr : r ∈ radii) : r ∈ Set.Icc (0 : ℝ) D.radius :=
    hRsub ((Set.Finite.mem_toFinset hRfin).mp hr)
  let G : Finset P := radialProductGrid p radii S D.point
  have hcenter : p ∈ G := Finset.mem_insert_self _ _
  have hpoint {r : ℝ} (hr : r ∈ radii) {u : L} (hu : u ∈ S) : D.point r u ∈ G :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(r, u), Finset.mem_product.mpr ⟨hr, hu⟩, rfl⟩)
  refine ⟨{ sites := G, center_mem := hcenter, star := ?_, radius := ?_, net := ?_, protection := ?_ }⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact T.mem_openStar_self _
    · obtain ⟨⟨r, u⟩, hru, rfl⟩ := Finset.mem_image.mp ha
      have hr := hradii r (Finset.mem_product.mp hru).1
      exact D.point_star r hr.1 hr.2 u
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rw [T.radialDistance_self]
      exact D.radius_pos.le
    · obtain ⟨⟨r, u⟩, hru, rfl⟩ := Finset.mem_image.mp ha
      have hr := hradii r (Finset.mem_product.mp hru).1
      rw [D.point_radius r hr.1 hr.2 u]
      exact hr.2
  · intro σ hσ x hxσ hxstar
    have hpσ : p ∈ T.cell σ := hxstar.1 σ hσ hxσ
    by_cases hxp : x = p
    · subst x
      exact ⟨p, hcenter, hpσ, by simpa only [dist_self] using hε⟩
    have hx0 := D.radialDistance_pos hσ hpσ hxσ hxp
    have hxR : T.radialDistance p x < D.radius := hxstar.2
    obtain ⟨u, hu, hux⟩ := D.reconstruct σ hσ hpσ x hxσ hx0 (by linarith [D.radius_pos])
    obtain ⟨v, hv, hvR, huv⟩ := (D.region σ hσ hpσ).net hSnet hu
    obtain ⟨r, hrR, hrx⟩ := Set.mem_iUnion₂.mp (hRcover ⟨hx0.le, hxR.le⟩)
    have hr : r ∈ radii := (Set.Finite.mem_toFinset hRfin).mpr hrR
    have hrI := hradii r hr
    refine ⟨D.point r v, hpoint hr hv, D.point_mem_of_nonneg hσ hpσ hrI.1 hrI.2 hvR, ?_⟩
    rw [← hux]
    apply hmesh σ hσ hpσ u hu v hvR (T.radialDistance p x)
      ⟨hx0.le, by linarith [D.radius_pos]⟩ r ⟨hrI.1, by linarith [D.radius_pos, hrI.2]⟩
    · simpa only [Metric.mem_ball, Real.dist_eq] using hrx
    · exact huv.trans hηδ
  · intro σ hσ τ hτ hpσ hpτ x hx hxR a ha
    by_cases hap : a = p
    · exact hap ▸ hpτ
    have hxp : x ≠ p := by
      intro he
      have hm := ha.2 p ⟨hcenter, hpσ⟩
      dsimp only at hm
      rw [he, dist_self] at hm
      have hax : T.chart σ a = T.chart σ p :=
        (dist_eq_zero.mp (le_antisymm hm dist_nonneg)).symm
      exact hap (T.chart_injectiveOn σ hσ ha.1.2 hpσ hax)
    have hx0 := D.radialDistance_pos hσ hpσ hx.1 hxp
    obtain ⟨u, huσ, hux⟩ := D.reconstruct σ hσ hpσ x hx.1 hx0 hxR
    have huτ : u ∈ (D.region τ hτ hpτ).carrier :=
      (D.point_mem τ hτ hpτ _ hx0 hxR.le u).mp (hux.symm ▸ hx.2)
    rcases Finset.mem_insert.mp ha.1.1 with hap' | ha'
    · exact (hap hap').elim
    obtain ⟨⟨s, v⟩, hsv, hsva⟩ := Finset.mem_image.mp ha'
    have hs := hradii s (Finset.mem_product.mp hsv).1
    have hvS := (Finset.mem_product.mp hsv).2
    have hs0 : 0 < s := by
      apply lt_of_le_of_ne hs.1
      intro he
      exact hap (hsva.symm.trans (by rw [← he, D.point_zero]))
    have hvσ : v ∈ (D.region σ hσ hpσ).carrier :=
      (D.point_mem σ hσ hpσ s hs0 (by linarith [D.radius_pos, hs.2]) v).mp (hsva.symm ▸ ha.1.2)
    have hvnear : IsNearestFor
        (fun z w => dist ((D.region σ hσ hpσ).coordinate z) ((D.region σ hσ hpσ).coordinate w))
        ((S : Set L) ∩ (D.region σ hσ hpσ).carrier) u v := by
      refine ⟨⟨hvS, hvσ⟩, ?_⟩
      intro w hw
      by_contra hn
      have hlt := D.strict_comparison σ hσ hpσ u huσ w hw.2 v hvσ
        _ hx0 hxR s hs0 hs.2 (lt_of_not_ge hn)
      rw [hux, hsva] at hlt
      have hm := ha.2 (D.point s w) ⟨hpoint (Finset.mem_product.mp hsv).1 hw.1,
        D.point_mem_of_nonneg hσ hpσ hs.1 hs.2 hw.2⟩
      exact (not_lt_of_ge hm) hlt
    obtain ⟨K, hK, huK⟩ := (D.region τ hτ hpτ).cover u huτ
    have hvK := (D.region σ hσ hpσ).protected_nearest hSnet hSprotected hηπ huσ hvnear
      K ((D.region τ hτ hpτ).valid K hK) huK
    have hvτ := (D.region τ hτ hpτ).contained K hK hvK
    rw [← hsva]
    exact D.point_mem_of_nonneg hτ hpτ hs.1 hs.2 hvτ

end PolarNetData
end ArchivePLGeometry
