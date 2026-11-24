module

public import BrehmApprox.SphericalCrossPolytope
public import PLGeometry.Definitions

/-!
# Radial transport of simplices from the crosspolytope

Normalization takes each affine simplex in a signed facet to a genuine
hemispherical geodesic simplex. It preserves finite hulls and common faces.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.CrossPolytope

open GeodesicSphere CoordinateSphericalCells

variable {n : ℕ}

local instance sphericalRadialTransferLocalInstance1 : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
local instance sphericalRadialTransferLocalInstance2 : DecidableEq (GeodesicSphere n) := Classical.decEq _

def radialVertices (V : Finset (EuclideanSpace ℝ (Fin (n + 1)))) : Finset (GeodesicSphere n) :=
  V.image sphereNormalize

theorem hull_subset_facet {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    {σ : Fin (n + 1) → Bool} (hV : ∀ v ∈ V, v ∈ facet σ) :
    convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ facet σ :=
  convexHull_min hV (convex_convexHull ℝ _)

theorem sphereNormalize_mem_coordinate_cell {σ : Fin (n + 1) → Bool}
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : v ∈ facet σ) :
    sphereNormalize v ∈ sphericalCell (vertices Finset.univ σ) := by
  apply (mem_cell_iff Finset.univ σ _).mpr
  refine ⟨by simp, ?_⟩
  intro i _
  have hpos := ((facet_mem_iff σ v).mp hv).1 i
  rw [sphereNormalize_val (nonzero_of_mem_facet hv)]
  change 0 ≤ sign (σ i) * (‖v‖⁻¹ * v i)
  nlinarith [mul_nonneg (inv_nonneg.mpr (norm_nonneg v)) hpos]

theorem radialVertices_hemisphere {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    {σ : Fin (n + 1) → Bool} (hV : ∀ v ∈ V, v ∈ facet σ) :
    InOpenHemisphere (radialVertices V) := by
  obtain ⟨p, hp⟩ := hemispherical Finset.univ σ
  refine ⟨p, ?_⟩
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  exact sphericalCell_inner_pos (vertices Finset.univ σ) p hp
    (sphereNormalize_mem_coordinate_cell (hV v hv))

theorem norm_smul_sphereNormalize {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : v ≠ 0) :
    ‖v‖ • (sphereNormalize v).val = v := by
  rw [sphereNormalize_val hv]
  exact NormedSpace.norm_smul_normalize v

theorem sphereNormalize_pos_smul (x : GeodesicSphere n) {a : ℝ} (ha : 0 < a) :
    sphereNormalize (a • x.val) = x := by
  apply GeodesicSphere.ext
  rw [sphereNormalize_val (smul_ne_zero ha.ne' x.val_ne_zero),
    NormedSpace.normalize_smul_of_pos ha, NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val]

theorem sphericalCell_radialVertices {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    {σ : Fin (n + 1) → Bool} (hV : ∀ v ∈ V, v ∈ facet σ) :
    sphericalCell (radialVertices V) = sphereNormalize '' convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hnon (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ∈ V) : v ≠ 0 :=
    nonzero_of_mem_facet (hV v hv)
  have hinj : Set.InjOn sphereNormalize (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    sphereNormalize_injOn.mono (fun v hv => gauge_eq_one_of_mem_facet (hV v hv))
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
    let w : GeodesicSphere n → ℝ := fun x => α (radialSection x) * ‖radialSection x‖
    have hw (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ∈ V) :
        w (sphereNormalize v) = α v * ‖v‖ := by
      dsimp [w]
      rw [radialSection_sphereNormalize (gauge_eq_one_of_mem_facet (hV v hv))]
    refine ⟨w, ?_, ‖z‖, norm_pos_iff.mpr (nonzero_of_mem_facet (hull_subset_facet hV hz)), ?_⟩
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      rw [hw v hv]
      exact mul_nonneg (hα v hv) (norm_nonneg v)
    · rw [radialVertices, Finset.sum_image hinj,
        norm_smul_sphereNormalize (nonzero_of_mem_facet (hull_subset_facet hV hz))]
      calc
        ∑ v ∈ V, w (sphereNormalize v) • (sphereNormalize v).val = ∑ v ∈ V, α v • v := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hw v hv, mul_smul, norm_smul_sphereNormalize (hnon v hv)]
        _ = z := hvec

theorem radialVertices_linearIndependent {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    {σ : Fin (n + 1) → Bool} (hV : ∀ v ∈ V, v ∈ facet σ)
    (hAff : AffineIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1)))) :
    LinearIndependent ℝ (fun x : radialVertices V => x.val.val) := by
  have hlin : LinearIndependent ℝ ((↑) : V → EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hsum : ∑ j, c j = 0 := by
      have hh := congrArg (facetLinear σ) hc
      have hv (j : V) : facetLinear σ j.val = 1 := ((facet_mem_iff σ j.val).mp (hV j.val j.property)).2
      simpa only [map_sum, map_smul, map_zero, smul_eq_mul, hv, mul_one] using hh
    exact (affineIndependent_iff_of_fintype ℝ _).mp hAff c hsum
      (by rwa [Finset.weightedVSub_eq_linear_combination _ hsum]) i
  let units : V → ℝˣ := fun v => Units.mk0 (‖v.val‖⁻¹)
    (inv_ne_zero (norm_ne_zero_iff.mpr (nonzero_of_mem_facet (hV v.val v.property))))
  have hnormalized : LinearIndependent ℝ (fun v : V => (sphereNormalize v.val).val) := by
    have h := hlin.units_smul units
    have heq : (units • ((↑) : V → EuclideanSpace ℝ (Fin (n + 1)))) =
        (fun v : V => (sphereNormalize v.val).val) := by
      funext v
      rw [sphereNormalize_val (nonzero_of_mem_facet (hV v.val v.property))]
      rfl
    rw [heq] at h
    exact h
  let e : radialVertices V ↪ V :=
    { toFun := fun x => ⟨radialSection x.val, by
        obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp x.property
        rw [← hveq, radialSection_sphereNormalize (gauge_eq_one_of_mem_facet (hV v hv))]
        exact hv⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        have hh := congrArg (fun v : V => sphereNormalize v.val) h
        simpa only [sphereNormalize_radialSection] using hh }
  have h := hnormalized.comp e e.injective
  convert h using 1
  funext x
  exact congrArg GeodesicSphere.val (sphereNormalize_radialSection x.val).symm

theorem radialVertices_inter (V W : Finset (EuclideanSpace ℝ (Fin (n + 1))))
    (hV : ∀ v ∈ V, gauge v = 1) (hW : ∀ w ∈ W, gauge w = 1) :
    radialVertices (V ∩ W) = radialVertices V ∩ radialVertices W := by
  ext x
  simp only [radialVertices, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨v, ⟨hv, hw⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, ⟨v, hw, rfl⟩⟩
  · rintro ⟨⟨v, hv, hxv⟩, ⟨w, hw, hxw⟩⟩
    have hvw : v = w := sphereNormalize_injOn (hV v hv) (hW w hw) (hxv.trans hxw.symm)
    subst w
    exact ⟨v, ⟨hv, hw⟩, hxv⟩

theorem exists_radialVertices_subface {V : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    {W : Finset (GeodesicSphere n)} (hW : W ⊆ radialVertices V) :
    ∃ U : Finset (EuclideanSpace ℝ (Fin (n + 1))), U ⊆ V ∧ radialVertices U = W := by
  let U := V.filter (fun v => sphereNormalize v ∈ W)
  refine ⟨U, Finset.filter_subset _ _, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hv).2
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hW hx)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hx⟩, rfl⟩

theorem radialCells_intersection {V W : Finset (EuclideanSpace ℝ (Fin (n + 1)))}
    {σ τ : Fin (n + 1) → Bool} (hV : ∀ v ∈ V, v ∈ facet σ)
    (hW : ∀ w ∈ W, w ∈ facet τ)
    (hinter : convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      convexHull ℝ (↑(V ∩ W) : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    sphericalCell (radialVertices V) ∩ sphericalCell (radialVertices W) =
      sphericalCell (radialVertices V ∩ radialVertices W) := by
  have hVW : ∀ v ∈ (V ∩ W : Finset (EuclideanSpace ℝ (Fin (n + 1)))), v ∈ facet σ :=
    fun v hv => hV v (Finset.mem_inter.mp hv).1
  rw [← radialVertices_inter V W (fun v hv => gauge_eq_one_of_mem_facet (hV v hv))
    (fun w hw => gauge_eq_one_of_mem_facet (hW w hw))]
  rw [sphericalCell_radialVertices hV, sphericalCell_radialVertices hW,
    sphericalCell_radialVertices hVW]
  have himage : sphereNormalize '' convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩
      sphereNormalize '' convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
        sphereNormalize '' (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ convexHull ℝ (W : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    ext x
    constructor
    · rintro ⟨⟨v, hv, hxv⟩, ⟨w, hw, hxw⟩⟩
      have hvw : v = w := sphereNormalize_injOn
        (gauge_eq_one_of_mem_facet (hull_subset_facet hV hv))
        (gauge_eq_one_of_mem_facet (hull_subset_facet hW hw)) (hxv.trans hxw.symm)
      subst w
      exact ⟨v, ⟨hv, hw⟩, hxv⟩
    · rintro ⟨v, ⟨hv, hw⟩, rfl⟩
      exact ⟨⟨v, hv, rfl⟩, ⟨v, hw, rfl⟩⟩
  rw [himage, hinter]

end BrehmApprox.CrossPolytope
