module

public import BrehmApprox.RadialBoundaryEmbedding
public import BrehmApprox.SphericalGeodesics
public import Mathlib.Analysis.Convex.Join

/-! # Angular domains of convex sets -/

@[expose] public section
noncomputable section

open Set
open scoped BigOperators

namespace BrehmApprox

variable {n : ℕ}

local instance radialDomainsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance radialDomainsEuclideanDecidableEq :
    DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _

def radialDirections (C : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p : EuclideanSpace ℝ (Fin (n + 1))) : Set (GeodesicSphere n) :=
  {u | ∃ r : ℝ, 0 < r ∧ p + r • u.val ∈ C}

theorem sphericalCell_subset_radialDirections
    {C : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hC : Convex ℝ C)
    {p : EuclideanSpace ℝ (Fin (n + 1))} {V : Finset (GeodesicSphere n)}
    (hV : ∀ v ∈ V, v ∈ radialDirections C p) :
    sphericalCell V ⊆ radialDirections C p := by
  intro u hu
  choose r hrpos hrC using (fun v : V => hV v.val v.property)
  obtain ⟨w, hw, c, hc, hrep⟩ := hu
  have hrep' : ∑ v : V, w v.val • v.val.val = c • u.val := by
    rw [Finset.sum_coe_sort V (fun v => w v • v.val)]
    exact hrep
  let a : V → ℝ := fun v => w v.val / r v
  have ha (v : V) : 0 ≤ a v := div_nonneg (hw v.val v.property) (hrpos v).le
  have ha0 : 0 < ∑ v : V, a v := by
    apply lt_of_le_of_ne (Finset.sum_nonneg (fun v _ => ha v))
    intro he
    have hz : ∀ v : V, a v = 0 := fun v =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => ha v)).mp he.symm v (Finset.mem_univ _)
    have hwz (v : V) : w v.val = 0 :=
      (div_eq_zero_iff.mp (hz v)).resolve_right (hrpos v).ne'
    have hzero : c • u.val = 0 := by
      rw [← hrep']
      exact Finset.sum_eq_zero (fun v _ => by rw [hwz v, zero_smul])
    exact smul_ne_zero hc.ne' u.val_ne_zero hzero
  let d : ℝ := ∑ v : V, a v
  have hsum : ∑ v : V, a v / d = 1 := by
    rw [← Finset.sum_div]
    exact div_self ha0.ne'
  have hy : (∑ v : V, (a v / d) • (p + r v • v.val.val)) ∈ C :=
    hC.sum_mem (fun v _ => div_nonneg (ha v) ha0.le) hsum (fun v _ => hrC v)
  refine ⟨c / d, div_pos hc ha0, ?_⟩
  have he : (∑ v : V, (a v / d) • (p + r v • v.val.val)) = p + (c / d) • u.val := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
    congr 1
    calc
      (∑ v : V, (a v / d) • (r v • v.val.val)) = d⁻¹ • ∑ v : V, w v.val • v.val.val := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro v _
        simp only [smul_smul, a]
        congr 1
        field_simp [(hrpos v).ne']
      _ = (c / d) • u.val := by rw [hrep', smul_smul]; congr 1; ring
  rwa [he] at hy

theorem geodesic_mem_radialDirections
    {C : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hC : Convex ℝ C)
    {p : EuclideanSpace ℝ (Fin (n + 1))} {a b : GeodesicSphere n}
    (ha : a ∈ radialDirections C p) (hb : b ∈ radialDirections C p)
    (hπ : dist a b < Real.pi) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    GeodesicSphere.geodesic a b hπ t ∈ radialDirections C p := by
  apply sphericalCell_subset_radialDirections hC
    (V := {a, b}) (fun v hv => by
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ha
      · exact Finset.mem_singleton.mp hv ▸ hb)
  exact geodesic_mem_sphericalCell
    (mem_sphericalCell_of_mem (Finset.mem_insert_self _ _))
    (mem_sphericalCell_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    hπ ht.1 ht.2

theorem exists_visibleBoundary_same_direction
    (V : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (hV : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))))
    {p x : EuclideanSpace ℝ (Fin (n + 1))}
    (hp : p ∈ convexHull ℝ (V : Set _)) (hx : x ∈ convexHull ℝ (V : Set _))
    (hxp : x ≠ p) :
    ∃ y ∈ visibleBoundary V p,
      NormedSpace.normalize (y - p) = NormedSpace.normalize (x - p) := by
  obtain ⟨U, hUV, hpU, hxU⟩ := exists_stellar_face_avoiding_center V hV hp hx
  have hU : (U : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty := by
    by_contra h
    have he : U = ∅ := Finset.coe_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h)
    have hxp' : x = p := by simpa [he] using hxU
    exact hxp hxp'
  rw [Finset.coe_insert, convexHull_insert hU, convexJoin_singleton_left] at hxU
  obtain ⟨y, hy, hseg⟩ := Set.mem_iUnion₂.mp hxU
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have hbpos : 0 < b := by
    apply lt_of_le_of_ne hb
    intro hb0
    have hb' : b = 0 := hb0.symm
    have ha' : a = 1 := by linarith
    have hpx : p = x := by simpa only [ha', hb', one_smul, zero_smul, add_zero] using he
    exact hxp hpx.symm
  have hv : x - p = b • (y - p) := by
    rw [← he, smul_sub, show a = 1 - b by linarith, sub_smul, one_smul]
    abel
  refine ⟨y, ⟨U, hUV, hpU, hy⟩, ?_⟩
  rw [hv, NormedSpace.normalize_smul_of_pos hbpos]

end BrehmApprox
