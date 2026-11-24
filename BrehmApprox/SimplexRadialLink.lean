module

public import BrehmApprox.SphericalRadialTransfer

/-!
# Radial links of Euclidean simplices

At a vertex of a nondegenerate simplex, a sufficiently small metric sphere
cuts out the spherical simplex of normalized edge vectors.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.RadialLink

open GeodesicSphere CrossPolytope

variable {n : ℕ}

local instance radialLinkDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- A finite independent family lies in an affine hyperplane away from zero. -/
theorem exists_functional_one
    {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}
    {v : ι → E} (hv : LinearIndependent ℝ v) :
    ∃ ℓ : E →ₗ[ℝ] ℝ, ∀ i, ℓ (v i) = 1 := by
  obtain ⟨ℓ, hℓ⟩ := (Module.Basis.span hv).sumCoords.exists_extend
  refine ⟨ℓ, ?_⟩
  intro i
  have h := LinearMap.congr_fun hℓ (Module.Basis.span hv i)
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coe_span_apply,
    Module.Basis.sumCoords_self_apply] using h

/-- Arbitrary values on independent vectors extend to a linear functional. -/
theorem exists_functional_values
    {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}
    {v : ι → E} (hv : LinearIndependent ℝ v) (w : ι → ℝ) :
    ∃ ℓ : E →ₗ[ℝ] ℝ, ∀ i, ℓ (v i) = w i := by
  obtain ⟨ℓ, hℓ⟩ := ((Module.Basis.span hv).constr ℝ w).exists_extend
  refine ⟨ℓ, ?_⟩
  intro i
  have h := LinearMap.congr_fun hℓ (Module.Basis.span hv i)
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coe_span_apply,
    Module.Basis.constr_basis] using h

def hyperplaneSection (ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (x : GeodesicSphere n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (ℓ x.val)⁻¹ • x.val

theorem nonzero_of_functional_one
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ℓ v = 1) : v ≠ 0 := by
  intro hz
  rw [hz, map_zero] at hv
  exact zero_ne_one hv

theorem section_sphereNormalize
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ℓ v = 1) :
    hyperplaneSection ℓ (sphereNormalize v) = v := by
  rw [hyperplaneSection, sphereNormalize_val (nonzero_of_functional_one hv)]
  simp only [NormedSpace.normalize, map_smul, smul_eq_mul, hv, mul_one,
    inv_inv]
  exact NormedSpace.norm_smul_normalize v

theorem sphereNormalize_injOn_section
    (ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ) :
    Set.InjOn sphereNormalize {v | ℓ v = 1} := by
  intro v hv w hw h
  have hh := congrArg (hyperplaneSection ℓ) h
  simpa only [section_sphereNormalize hv, section_sphereNormalize hw] using hh

theorem functional_one_on_hull
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : ∀ v ∈ V, ℓ v = 1) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1))))) : ℓ z = 1 := by
  obtain ⟨w, hw, hw1, hrep⟩ := Finset.mem_convexHull'.mp hz
  rw [← hrep, map_sum]
  simp only [map_smul, smul_eq_mul]
  convert hw1 using 1
  apply Finset.sum_congr rfl
  intro v hv
  rw [hV v hv, mul_one]

theorem radialVertices_hemisphere_of_functional
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))} (hV : ∀ v ∈ V, ℓ v = 1) :
    InOpenHemisphere (radialVertices V) := by
  by_cases he : V = ∅
  · subst V
    exact ⟨northPole n, by simp [radialVertices]⟩
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let a := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
    ℓ.toContinuousLinearMap
  have ha (z : EuclideanSpace ℝ (Fin (n + 1))) : inner ℝ a z = ℓ z :=
    InnerProductSpace.toDual_symm_apply
  have ha0 : a ≠ 0 := by
    intro hz
    have hv' := ha v
    rw [hz, inner_zero_left, hV v hv] at hv'
    exact zero_ne_one hv'
  refine ⟨sphereNormalize a, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  rw [sphereNormalize_val ha0,
    sphereNormalize_val (nonzero_of_functional_one (hV z hz))]
  simp only [NormedSpace.normalize, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, ha, hV z hz, mul_one]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (nonzero_of_functional_one (hV z hz))))
    (inv_pos.mpr (norm_pos_iff.mpr ha0))

theorem sphericalCell_radialVertices_of_functional
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : ∀ v ∈ V, ℓ v = 1) :
    sphericalCell (radialVertices V) = sphereNormalize '' convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hnon (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ∈ V) : v ≠ 0 :=
    nonzero_of_functional_one (hV v hv)
  have hinj : Set.InjOn sphereNormalize (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    (sphereNormalize_injOn_section ℓ).mono (fun v hv => hV v hv)
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨w, hw, a, ha, hrep⟩ := hx
    rw [radialVertices, Finset.sum_image hinj] at hrep
    let α : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun v => w (sphereNormalize v) / ‖v‖
    have hα (v) (hv : v ∈ V) : 0 ≤ α v :=
      div_nonneg (hw _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)) (norm_nonneg _)
    have hvec : ∑ v ∈ V, α v • v = a • x.val := by
      calc
        ∑ v ∈ V, α v • v = ∑ v ∈ V, w (sphereNormalize v) • (sphereNormalize v).val := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [sphereNormalize_val (hnon v hv)]
          simp only [α, NormedSpace.normalize, div_eq_mul_inv, smul_smul]
        _ = a • x.val := hrep
    let d : ℝ := ∑ v ∈ V, α v
    have hdnon : 0 ≤ d := Finset.sum_nonneg hα
    have hd : 0 < d := by
      apply lt_of_le_of_ne hdnon
      intro heq
      have hzero : ∀ v ∈ V, α v = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hα).mp heq.symm
      have hz : a • x.val = 0 := by
        rw [← hvec]
        exact Finset.sum_eq_zero (fun v hv => by rw [hzero v hv, zero_smul])
      exact smul_ne_zero ha.ne' x.val_ne_zero hz
    let z : EuclideanSpace ℝ (Fin (n + 1)) := (a / d) • x.val
    have hz : z ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
      apply Finset.mem_convexHull'.mpr
      refine ⟨fun v => α v / d, fun v hv => div_nonneg (hα v hv) hd.le, ?_, ?_⟩
      · simp only [div_eq_mul_inv, ← Finset.sum_mul]
        exact mul_inv_cancel₀ hd.ne'
      · calc
          ∑ v ∈ V, (α v / d) • v = d⁻¹ • ∑ v ∈ V, α v • v := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro v _
            simp only [div_eq_mul_inv, smul_smul, mul_comm]
          _ = z := by rw [hvec, smul_smul]; simp only [z, div_eq_mul_inv, mul_comm]
    exact ⟨z, hz, sphereNormalize_pos_smul x (div_pos ha hd)⟩
  · rintro x ⟨z, hz, rfl⟩
    obtain ⟨α, hα, hsum, hvec⟩ := Finset.mem_convexHull'.mp hz
    let w : GeodesicSphere n → ℝ := fun x => α (hyperplaneSection ℓ x) * ‖hyperplaneSection ℓ x‖
    have hw (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ∈ V) :
        w (sphereNormalize v) = α v * ‖v‖ := by
      dsimp [w]
      rw [section_sphereNormalize (hV v hv)]
    refine ⟨w, ?_, ‖z‖, norm_pos_iff.mpr (nonzero_of_functional_one (functional_one_on_hull hV hz)), ?_⟩
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      rw [hw v hv]
      exact mul_nonneg (hα v hv) (norm_nonneg v)
    · rw [radialVertices, Finset.sum_image hinj,
        norm_smul_sphereNormalize (nonzero_of_functional_one (functional_one_on_hull hV hz))]
      calc
        ∑ v ∈ V, w (sphereNormalize v) • (sphereNormalize v).val = ∑ v ∈ V, α v • v := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hw v hv, mul_smul, norm_smul_sphereNormalize (hnon v hv)]
        _ = z := hvec

theorem radialVertices_linearIndependent_of_functional
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : ∀ v ∈ V, ℓ v = 1)
    (hlin : LinearIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1)))) :
    LinearIndependent ℝ (fun x : radialVertices V => x.val.val) := by
  let units : V → ℝˣ := fun v => Units.mk0 (‖v.val‖⁻¹)
    (inv_ne_zero (norm_ne_zero_iff.mpr (nonzero_of_functional_one (hV v.val v.property))))
  have hnormalized : LinearIndependent ℝ (fun v : V => (sphereNormalize v.val).val) := by
    have h := hlin.units_smul units
    have heq : (units • ((↑) : V → EuclideanSpace ℝ (Fin (n + 1)))) =
        (fun v : V => (sphereNormalize v.val).val) := by
      funext v
      rw [sphereNormalize_val (nonzero_of_functional_one (hV v.val v.property))]
      rfl
    rw [heq] at h
    exact h
  let e : radialVertices V ↪ V :=
    { toFun := fun x => ⟨hyperplaneSection ℓ x.val, by
        obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp x.property
        rw [← hveq, section_sphereNormalize (hV v hv)]
        exact hv⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        have hh := congrArg (fun v : V => sphereNormalize v.val) h
        change sphereNormalize (hyperplaneSection ℓ x.val) =
          sphereNormalize (hyperplaneSection ℓ y.val) at hh
        obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp x.property
        obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp y.property
        rw [← hvx, ← hwy, section_sphereNormalize (hV v hv),
          section_sphereNormalize (hV w hw)] at hh
        exact hvx.symm.trans (hh.trans hwy) }
  have h := hnormalized.comp e e.injective
  convert h using 1
  funext x
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp x.property
  change x.val.val = (sphereNormalize (hyperplaneSection ℓ x.val)).val
  rw [← hvx, section_sphereNormalize (hV v hv)]


/-- The opposite-face hull stays a positive distance from the cone vertex. -/
theorem exists_radius_below_opposite_face
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))} (hV : ∀ v ∈ V, ℓ v = 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ρ < ‖z‖ := by
  have hc : IsClosed (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (show IsFinitePolytope (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1))))) from
      ⟨V, rfl⟩).isCompact.isClosed
  have hz : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∉ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    intro h
    have hh := functional_one_on_hull hV h
    exact zero_ne_one (by simpa only [map_zero] using hh)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hc.isOpen_compl.mem_nhds hz)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  have hnorm : ε ≤ ‖z‖ := by
    by_contra! h
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using h) hz
  linarith

/-- Directions in the cone over a hyperplane simplex are exactly its
normalized spherical cell, uniformly at every sufficiently small radius. -/
theorem radial_mem_cone_iff
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))} (hV : ∀ v ∈ V, ℓ v = 1)
    {ρ r : ℝ} (hρ : ∀ z ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ρ < ‖z‖) (hr : 0 < r) (hrρ : r ≤ ρ) (u : GeodesicSphere n) :
    r • u.val ∈ convexHull ℝ ((insert 0 V : Finset (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1)))) ↔
      u ∈ sphericalCell (radialVertices V) := by
  rw [sphericalCell_radialVertices_of_functional hV]
  constructor
  · intro hx
    by_cases hempty : V = ∅
    · subst V
      have hz : r • u.val = 0 := by simpa using hx
      exact False.elim (smul_ne_zero hr.ne' u.val_ne_zero hz)
    have hne : (V : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    rw [Finset.coe_insert, convexHull_insert hne, convexJoin_singleton_left] at hx
    obtain ⟨q, hq, hseg⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨a, b, ha, hb, hab, hrep⟩ := hseg
    simp only [smul_zero, zero_add] at hrep
    have hbpos : 0 < b := by
      apply lt_of_le_of_ne hb
      intro heq
      have hz : r • u.val = 0 := by rw [← hrep, ← heq, zero_smul]
      exact smul_ne_zero hr.ne' u.val_ne_zero hz
    refine ⟨q, hq, ?_⟩
    apply GeodesicSphere.ext
    rw [sphereNormalize_val (nonzero_of_functional_one (functional_one_on_hull hV hq))]
    have h := congrArg NormedSpace.normalize hrep
    rw [NormedSpace.normalize_smul_of_pos hbpos, NormedSpace.normalize_smul_of_pos hr,
      NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_val] at h
    exact h
  · rintro ⟨q, hq, rfl⟩
    have hq0 := nonzero_of_functional_one (functional_one_on_hull hV hq)
    have hqn := norm_pos_iff.mpr hq0
    have ht : r / ‖q‖ ≤ 1 := (div_le_one hqn).mpr (hrρ.trans (hρ q hq).le)
    have h0 : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈
        convexHull ℝ ((insert 0 V : Finset (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
      subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
    have hqc : q ∈ convexHull ℝ ((insert 0 V : Finset (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
      convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hq
    have hc := (convex_convexHull ℝ ((insert 0 V : Finset (EuclideanSpace ℝ (Fin (n + 1)))) : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      h0 hqc (sub_nonneg.mpr ht) (div_nonneg hr.le hqn.le)
      (show (1 - r / ‖q‖) + r / ‖q‖ = 1 by ring)
    simpa only [smul_zero, zero_add, sphereNormalize_val hq0,
      NormedSpace.normalize, smul_smul, div_eq_mul_inv] using hc


/-- The edge vectors based at a chosen vertex. -/
def edgeVectors (V : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (p : EuclideanSpace ℝ (Fin (n + 1))) : Finset (EuclideanSpace ℝ (Fin (n + 1))) :=
  (V.erase p).image (fun v => v - p)

/-- The vertices of the spherical link at `p`. -/
def linkVertices (V : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (p : EuclideanSpace ℝ (Fin (n + 1))) : Finset (GeodesicSphere n) :=
  radialVertices (edgeVectors V p)

theorem edgeVectors_linearIndependent
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))))
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ V) :
    LinearIndependent ℝ ((↑) : edgeVectors V p → EuclideanSpace ℝ (Fin (n + 1))) := by
  have h := (affineIndependent_set_iff_linearIndependent_vsub ℝ hp).mp hV
  have hset : ((fun v : EuclideanSpace ℝ (Fin (n + 1)) => v -ᵥ p) '' ((V : Set (EuclideanSpace ℝ (Fin (n + 1)))) \ {p})) =
      (edgeVectors V p : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    simp only [edgeVectors, Finset.coe_image, Finset.coe_erase, vsub_eq_sub]
  rw [hset] at h
  exact h

theorem linkVertices_simplex
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))))
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ V) :
    InOpenHemisphere (linkVertices V p) ∧
      LinearIndependent ℝ (fun u : linkVertices V p => u.val.val) := by
  have he := edgeVectors_linearIndependent hV hp
  obtain ⟨ℓ, hℓ⟩ := exists_functional_one he
  have hℓ' : ∀ v ∈ edgeVectors V p, ℓ v = 1 := fun v hv => hℓ ⟨v, hv⟩
  exact ⟨radialVertices_hemisphere_of_functional hℓ',
    radialVertices_linearIndependent_of_functional hℓ' he⟩

theorem sub_mem_hull_edgeVectors_iff
    (V : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ V)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    x - p ∈ convexHull ℝ ((insert 0 (edgeVectors V p) : Finset _) : Set (EuclideanSpace ℝ (Fin (n + 1)))) ↔
      x ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let T := (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin (n + 1))) (-p)).toAffineMap
  have hT (y : EuclideanSpace ℝ (Fin (n + 1))) : T y = y - p := by
    simp [T, sub_eq_add_neg, add_comm]
  have hs : T '' (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      ((insert 0 (edgeVectors V p) : Finset _) : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hT]
      by_cases hvp : v = p
      · simp [hvp]
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v,
          Finset.mem_erase.mpr ⟨hvp, hv⟩, rfl⟩)
    · intro hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨p, hp, by rw [hT, sub_self]⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨v, Finset.mem_of_mem_erase hv, hT v⟩
  rw [← hs, ← T.image_convexHull]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [hT] at hxy
    exact sub_left_injective hxy ▸ hy
  · intro hx
    exact ⟨x, hx, hT x⟩

/-- A small sphere around a simplex vertex is precisely its spherical link.
The same radius works for every smaller positive concentric sphere. -/
theorem exists_radial_link_radius
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))))
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ u : GeodesicSphere n,
      p + r • u.val ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ↔
        u ∈ sphericalCell (linkVertices V p) := by
  have he := edgeVectors_linearIndependent hV hp
  obtain ⟨ℓ, hℓ⟩ := exists_functional_one he
  have hℓ' : ∀ v ∈ edgeVectors V p, ℓ v = 1 := fun v hv => hℓ ⟨v, hv⟩
  obtain ⟨ρ, hρ, hsmall⟩ := exists_radius_below_opposite_face hℓ'
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ u
  rw [← sub_mem_hull_edgeVectors_iff V hp (p + r • u.val)]
  have heq : p + r • u.val - p = r • u.val := by abel
  rw [heq]
  exact radial_mem_cone_iff hℓ' hsmall hr hrρ u


theorem sub_mem_hull_edgeVectors_of_mem_opposite
    (V : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (p : EuclideanSpace ℝ (Fin (n + 1)))
    {q : EuclideanSpace ℝ (Fin (n + 1))}
    (hq : q ∈ convexHull ℝ (V.erase p : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    q - p ∈ convexHull ℝ (edgeVectors V p : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let T := (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin (n + 1))) (-p)).toAffineMap
  have hT (y : EuclideanSpace ℝ (Fin (n + 1))) : T y = y - p := by
    simp [T, sub_eq_add_neg, add_comm]
  have hs : (edgeVectors V p : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      T '' (V.erase p : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    simp only [edgeVectors, Finset.coe_image, hT]
  rw [hs, ← T.image_convexHull]
  exact ⟨q, hq, hT q⟩

/-- The link radius may be chosen strictly below the whole opposite face. -/
theorem exists_radial_link_radius_with_boundary
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))))
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ q ∈ convexHull ℝ (V.erase p : Set (EuclideanSpace ℝ (Fin (n + 1)))), ρ < dist q p) ∧
      ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ u : GeodesicSphere n,
        p + r • u.val ∈ convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ↔
          u ∈ sphericalCell (linkVertices V p) := by
  have he := edgeVectors_linearIndependent hV hp
  obtain ⟨ℓ, hℓ⟩ := exists_functional_one he
  have hℓ' : ∀ v ∈ edgeVectors V p, ℓ v = 1 := fun v hv => hℓ ⟨v, hv⟩
  obtain ⟨ρ, hρ, hsmall⟩ := exists_radius_below_opposite_face hℓ'
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro q hq
    simpa only [dist_eq_norm] using hsmall (q - p)
      (sub_mem_hull_edgeVectors_of_mem_opposite V p hq)
  · intro r hr hrρ u
    rw [← sub_mem_hull_edgeVectors_iff V hp (p + r • u.val)]
    have heq : p + r • u.val - p = r • u.val := by abel
    rw [heq]
    exact radial_mem_cone_iff hℓ' hsmall hr hrρ u

theorem radial_dist (p : EuclideanSpace ℝ (Fin (n + 1)))
    {r : ℝ} (hr : 0 ≤ r) (u v : GeodesicSphere n) :
    dist (p + r • u.val) (p + r • v.val) = r * dist u.val v.val := by
  rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hr, dist_eq_norm]

/-- Equal chord lengths on two fixed-radius spheres give equal link angles. -/
theorem angular_dist_eq_of_radial_dist_eq
    (p q : EuclideanSpace ℝ (Fin (n + 1))) {r : ℝ} (hr : 0 < r)
    (u v u' v' : GeodesicSphere n)
    (h : dist (p + r • u.val) (p + r • v.val) =
      dist (q + r • u'.val) (q + r • v'.val)) : dist u v = dist u' v' := by
  rw [radial_dist p hr.le, radial_dist q hr.le] at h
  have hc := mul_left_cancel₀ hr.ne' h
  have hs := congrArg (fun t : ℝ => t ^ 2) hc
  simp only [dist_eq_norm, norm_sub_sq_real, u.norm_val, v.norm_val,
    u'.norm_val, v'.norm_val] at hs
  have hi : inner ℝ u.val v.val = inner ℝ u'.val v'.val := by linarith
  rw [GeodesicSphere.dist_eq_arccos_inner, GeodesicSphere.dist_eq_arccos_inner, hi]


/-- Any nonzero positive linear combination determines a point of the
normalized spherical hull. -/
theorem mem_radialCell_of_positive_combination
    {ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ}
    {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))} (hV : ∀ v ∈ V, ℓ v = 1)
    (w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (u : GeodesicSphere n) {a : ℝ} (ha : 0 < a)
    (hrep : ∑ v ∈ V, w v • v = a • u.val) : u ∈ sphericalCell (radialVertices V) := by
  let d : ℝ := ∑ v ∈ V, w v
  have hd : 0 < d := by
    have hd0 : 0 ≤ d := Finset.sum_nonneg hw
    apply lt_of_le_of_ne hd0
    intro hd'
    have hw0 : ∀ v ∈ V, w v = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hd'.symm
    have hz : a • u.val = 0 := by
      rw [← hrep]
      exact Finset.sum_eq_zero (fun v hv => by rw [hw0 v hv, zero_smul])
    exact smul_ne_zero ha.ne' u.val_ne_zero hz
  rw [sphericalCell_radialVertices_of_functional hV]
  refine ⟨(a / d) • u.val, ?_, sphereNormalize_pos_smul u (div_pos ha hd)⟩
  apply Finset.mem_convexHull'.mpr
  refine ⟨fun v => w v / d, fun v hv => div_nonneg (hw v hv) hd.le, ?_, ?_⟩
  · simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hd.ne'
  · calc
      ∑ v ∈ V, (w v / d) • v = d⁻¹ • ∑ v ∈ V, w v • v := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro v _
        simp only [div_eq_mul_inv, smul_smul, mul_comm]
      _ = (a / d) • u.val := by rw [hrep, smul_smul]; congr 1; ring


theorem normalized_family_independent {ι : Type*}
    {v : ι → EuclideanSpace ℝ (Fin (n + 1))} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun i => (sphereNormalize (v i)).val) := by
  let units : ι → ℝˣ := fun i => Units.mk0 (‖v i‖⁻¹) (inv_ne_zero (norm_ne_zero_iff.mpr (hv.ne_zero i)))
  have h := hv.units_smul units
  convert h using 1
  funext i
  rw [sphereNormalize_val (hv.ne_zero i)]
  rfl

theorem normalized_family_hemisphere {ι : Type*} [Fintype ι]
    {v : ι → EuclideanSpace ℝ (Fin (n + 1))} (hv : LinearIndependent ℝ v) :
    InOpenHemisphere (Finset.univ.image (fun i => sphereNormalize (v i))) := by
  obtain ⟨ℓ, hℓ⟩ := exists_functional_one hv
  have hone : ∀ z ∈ Finset.univ.image v, ℓ z = 1 := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact hℓ i
  have h := radialVertices_hemisphere_of_functional hone
  simpa only [radialVertices, Finset.image_image, Function.comp_def] using h

end BrehmApprox.RadialLink
