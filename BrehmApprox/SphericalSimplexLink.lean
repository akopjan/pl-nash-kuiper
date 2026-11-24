module

public import BrehmApprox.SimplexRadialLink
public import BrehmApprox.SphericalGeodesics

/-!
# Tangent links of spherical simplices

The link vertices are normalized tangent projections of the other vertices.
They remain in the ambient sphere; their linear rank is one less than the
rank of the original simplex.
-/

@[expose] public section
noncomputable section

open Set Classical
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.SphericalLink

open GeodesicSphere CrossPolytope RadialLink

variable {n : ℕ}

local instance sphericalLinkDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def tangentLinear (p : GeodesicSphere n) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun v := v - inner ℝ p.val v • p.val
  map_add' v w := by
    simp only [inner_add_right, add_smul]
    abel
  map_smul' a v := by
    simp only [inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]

@[simp]
theorem tangentLinear_apply (p : GeodesicSphere n)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    tangentLinear p v = v - inner ℝ p.val v • p.val := rfl

@[simp]
theorem tangentLinear_self (p : GeodesicSphere n) : tangentLinear p p.val = 0 := by
  simp [tangentLinear, p.norm_val]

theorem inner_tangentLinear (p : GeodesicSphere n)
    (v : EuclideanSpace ℝ (Fin (n + 1))) : inner ℝ p.val (tangentLinear p v) = 0 := by
  simp [tangentLinear, inner_sub_right, inner_smul_right, p.norm_val]

def tangentVectors (V : Finset (GeodesicSphere n)) (p : GeodesicSphere n) :
    Finset (EuclideanSpace ℝ (Fin (n + 1))) :=
  (V.erase p).image (fun v => tangentLinear p v.val)

def linkVertices (V : Finset (GeodesicSphere n)) (p : GeodesicSphere n) :
    Finset (GeodesicSphere n) := radialVertices (tangentVectors V p)

theorem tangentIndexed_linearIndependent
    {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V) :
    LinearIndependent ℝ (fun v : V.erase p => tangentLinear p v.val.val) := by
  let i : V := ⟨p, hp⟩
  let c : V → ℝ := fun v => if v = i then 0 else -inner ℝ p.val v.val.val
  have hc : c i = 0 := by simp [c]
  have hg := (linearIndependent_add_smul_iff (v := fun v : V => v.val.val) hc).mpr hV
  let e : V.erase p ↪ V :=
    { toFun := fun v => ⟨v.val, Finset.mem_of_mem_erase v.property⟩
      inj' := by
        intro v w h
        apply Subtype.ext
        exact congrArg (fun z : V => z.val) h }
  have he (v : V.erase p) : e v ≠ i := by
    intro h
    exact (Finset.mem_erase.mp v.property).1 (congrArg Subtype.val h)
  have ht : LinearIndependent ℝ (fun v : V.erase p => tangentLinear p v.val.val) := by
    have hh := hg.comp e e.injective
    convert hh using 1
    funext v
    change tangentLinear p v.val.val = (e v).val.val + c (e v) • i.val.val
    simp only [tangentLinear_apply, c, he v, ite_false, neg_smul, sub_eq_add_neg]
    rfl
  exact ht

theorem tangentVectors_linearIndependent
    {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V) :
    LinearIndependent ℝ ((↑) : tangentVectors V p → EuclideanSpace ℝ (Fin (n + 1))) := by
  have ht := tangentIndexed_linearIndependent hV hp
  have hrange := ht.linearIndepOn_id
  have hset : Set.range (fun v : V.erase p => tangentLinear p v.val.val) =
      (tangentVectors V p : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    ext z
    simp only [Set.mem_range, tangentVectors, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  change LinearIndependent ℝ ((↑) : Set.range (fun v : V.erase p => tangentLinear p v.val.val) → EuclideanSpace ℝ (Fin (n + 1))) at hrange
  rw [hset] at hrange
  exact hrange

theorem linkVertices_simplex
    {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V) :
    InOpenHemisphere (linkVertices V p) ∧
      LinearIndependent ℝ (fun u : linkVertices V p => u.val.val) := by
  have ht := tangentVectors_linearIndependent hV hp
  obtain ⟨ℓ, hℓ⟩ := exists_functional_one ht
  have hℓ' : ∀ v ∈ tangentVectors V p, ℓ v = 1 := fun v hv => hℓ ⟨v, hv⟩
  exact ⟨radialVertices_hemisphere_of_functional hℓ',
    radialVertices_linearIndependent_of_functional hℓ' ht⟩

theorem inner_linkVertex {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V) {u : GeodesicSphere n}
    (hu : u ∈ linkVertices V p) : inner ℝ p.val u.val = 0 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
  have hz0 : z ≠ 0 := (tangentVectors_linearIndependent hV hp).ne_zero ⟨z, hz⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  rw [sphereNormalize_val hz0]
  simp only [NormedSpace.normalize, inner_smul_right, inner_tangentLinear, mul_zero]

theorem inner_linkCell {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V) {u : GeodesicSphere n}
    (hu : u ∈ sphericalCell (linkVertices V p)) : inner ℝ p.val u.val = 0 := by
  obtain ⟨w, hw, a, ha, hrep⟩ := hu
  have hi := congrArg (fun z => inner ℝ p.val z) hrep
  rw [inner_sum, inner_smul_right] at hi
  have hzero : ∑ v ∈ linkVertices V p, inner ℝ p.val (w v • v.val) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [inner_smul_right, inner_linkVertex hV hp hv, mul_zero]
  rw [hzero] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left ha.ne'

/-- The radial point in a unit tangent direction. -/
def radialPoint (p u : GeodesicSphere n) (hu : inner ℝ p.val u.val = 0) (r : ℝ) :
    GeodesicSphere n :=
  radialCircle p ⟨u.val, by exact hu⟩ u.norm_val r

@[simp]
theorem radialPoint_val (p u : GeodesicSphere n) (hu : inner ℝ p.val u.val = 0) (r : ℝ) :
    (radialPoint p u hu r).val = Real.cos r • p.val + Real.sin r • u.val := rfl


@[simp]
theorem tangentLinear_radialPoint (p u : GeodesicSphere n)
    (hu : inner ℝ p.val u.val = 0) (r : ℝ) :
    tangentLinear p (radialPoint p u hu r).val = Real.sin r • u.val := by
  rw [radialPoint_val, map_add, map_smul, map_smul, tangentLinear_self, smul_zero, zero_add]
  simp only [tangentLinear_apply, hu, zero_smul, sub_zero]

theorem radialPoint_dist_p (p u : GeodesicSphere n)
    (hu : inner ℝ p.val u.val = 0) {r : ℝ} (hr : 0 ≤ r) (hrπ : r ≤ Real.pi) :
    dist (radialPoint p u hu r) p = r := by
  have hup : inner ℝ u.val p.val = 0 := by rw [real_inner_comm]; exact hu
  rw [GeodesicSphere.dist_eq_arccos_inner, radialPoint_val, inner_add_left,
    real_inner_smul_left, real_inner_smul_left,
    inner_self_eq_one_of_norm_eq_one p.norm_val,
    hup, mul_zero, add_zero, mul_one]
  exact Real.arccos_cos hr hrπ

/-- The spherical cosine law on a common radial sphere. -/
theorem radialPoint_inner (p u v : GeodesicSphere n)
    (hu : inner ℝ p.val u.val = 0) (hv : inner ℝ p.val v.val = 0) (r : ℝ) :
    inner ℝ (radialPoint p u hu r).val (radialPoint p v hv r).val =
      Real.cos r ^ 2 + Real.sin r ^ 2 * inner ℝ u.val v.val := by
  have hup : inner ℝ u.val p.val = 0 := by rw [real_inner_comm]; exact hu
  simp only [radialPoint_val, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hv, hup, mul_zero, zero_add, add_zero,
    inner_self_eq_one_of_norm_eq_one p.norm_val, mul_one]
  ring

theorem angular_dist_eq_of_spherical_radial_dist_eq
    (p q u v u' v' : GeodesicSphere n)
    (hu : inner ℝ p.val u.val = 0) (hv : inner ℝ p.val v.val = 0)
    (hu' : inner ℝ q.val u'.val = 0) (hv' : inner ℝ q.val v'.val = 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r < Real.pi)
    (h : dist (radialPoint p u hu r) (radialPoint p v hv r) =
      dist (radialPoint q u' hu' r) (radialPoint q v' hv' r)) :
    dist u v = dist u' v' := by
  have hi := congrArg Real.cos h
  rw [cos_dist, cos_dist, radialPoint_inner, radialPoint_inner] at hi
  have hs := (Real.sin_pos_of_pos_of_lt_pi hr hrπ).ne'
  have he : inner ℝ u.val v.val = inner ℝ u'.val v'.val :=
    mul_left_cancel₀ (pow_ne_zero _ hs) (add_left_cancel hi)
  rw [GeodesicSphere.dist_eq_arccos_inner, GeodesicSphere.dist_eq_arccos_inner, he]

theorem exists_vertex_coordinate {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V) :
    ∃ ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ,
      ℓ p.val = 1 ∧ ∀ v ∈ V.erase p, ℓ v.val = 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_functional_values hV (fun v : V => if v.val = p then 1 else 0)
  refine ⟨ℓ, ?_, ?_⟩
  · simpa only [ite_true] using hℓ ⟨p, hp⟩
  · intro v hv
    simpa only [ite_eq_right (Finset.mem_erase.mp hv).1] using
      hℓ ⟨v, Finset.mem_of_mem_erase hv⟩

theorem tangentVectors_eq_univ_image (V : Finset (GeodesicSphere n)) (p : GeodesicSphere n) :
    tangentVectors V p = Finset.univ.image (fun v : V.erase p => tangentLinear p v.val.val) := by
  ext z
  simp only [tangentVectors, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, hz⟩
    exact ⟨⟨v, hv⟩, hz⟩
  · rintro ⟨v, hz⟩
    exact ⟨v.val, v.property, hz⟩


/-- A positive radial direction of a spherical simplex lies in its tangent link. -/
theorem link_mem_of_radialPoint_mem
    {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V)
    (u : GeodesicSphere n) (hu : inner ℝ p.val u.val = 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r < Real.pi)
    (hx : radialPoint p u hu r ∈ sphericalCell V) :
    u ∈ sphericalCell (linkVertices V p) := by
  obtain ⟨w, hw, a, ha, hrep⟩ := hx
  let f : V.erase p → EuclideanSpace ℝ (Fin (n + 1)) := fun v => tangentLinear p v.val.val
  have hinj : Function.Injective f := (tangentIndexed_linearIndependent hV hp).injective
  let wD : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    Function.extend f (fun v => w v.val) (fun _ => 0)
  have hwD (v : V.erase p) : wD (f v) = w v.val := hinj.extend_apply _ _ v
  have hpos : ∀ z ∈ tangentVectors V p, 0 ≤ wD z := by
    intro z hz
    rw [tangentVectors_eq_univ_image] at hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact (hwD v).symm ▸ hw v.val (Finset.mem_of_mem_erase v.property)
  have hcomb : ∑ z ∈ tangentVectors V p, wD z • z =
      (a * Real.sin r) • u.val := by
    rw [tangentVectors_eq_univ_image, Finset.sum_image (fun v _ w _ he => hinj he)]
    calc
      _ = ∑ v : V.erase p, w v.val • tangentLinear p v.val.val := by
        apply Finset.sum_congr rfl
        intro v _
        rw [show wD (tangentLinear p v.val.val) = w v.val from hwD v]
      _ = ∑ v ∈ V.erase p, w v • tangentLinear p v.val :=
        Finset.sum_coe_sort (V.erase p) (fun v => w v • tangentLinear p v.val)
      _ = tangentLinear p (∑ v ∈ V, w v • v.val) := by
        simp only [map_sum, map_smul]
        rw [Finset.sum_erase_eq_sub hp, tangentLinear_self, smul_zero, sub_zero]
      _ = (a * Real.sin r) • u.val := by
        rw [hrep, map_smul, tangentLinear_radialPoint, smul_smul]
  obtain ⟨ℓ, hℓ⟩ := exists_functional_one (tangentVectors_linearIndependent hV hp)
  exact mem_radialCell_of_positive_combination (fun v hv => hℓ ⟨v, hv⟩) wD hpos u
    (mul_pos ha (Real.sin_pos_of_pos_of_lt_pi hr hrπ)) hcomb

/-- Positive apex coordinate is the only additional constraint when lifting
one tangent-link direction back to the spherical simplex. -/
theorem radialPoint_mem_of_link_mem_of_coordinate_pos
    {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V)
    (ℓ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    (hℓp : ℓ p.val = 1) (hℓV : ∀ v ∈ V.erase p, ℓ v.val = 0)
    (u : GeodesicSphere n) (hu : inner ℝ p.val u.val = 0)
    {r : ℝ} (hsin : 0 ≤ Real.sin r) (huV : u ∈ sphericalCell (linkVertices V p))
    (hcoord : 0 ≤ ℓ (radialPoint p u hu r).val) :
    radialPoint p u hu r ∈ sphericalCell V := by
  have ht := tangentVectors_linearIndependent hV hp
  obtain ⟨γ, hγ⟩ := exists_functional_one ht
  have hγ' : ∀ v ∈ tangentVectors V p, γ v = 1 := fun v hv => hγ ⟨v, hv⟩
  change u ∈ sphericalCell (radialVertices (tangentVectors V p)) at huV
  rw [sphericalCell_radialVertices_of_functional hγ'] at huV
  obtain ⟨q, hq, hqu⟩ := huV
  have hq0 := nonzero_of_functional_one (functional_one_on_hull hγ' hq)
  have hqn := norm_pos_iff.mpr hq0
  have hqu' : q = ‖q‖ • u.val := by
    rw [← hqu, norm_smul_sphereNormalize hq0]
  obtain ⟨β, hβ, hβ1, hβq⟩ := Finset.mem_convexHull'.mp hq
  let α : GeodesicSphere n → ℝ := fun v => (Real.sin r / ‖q‖) * β (tangentLinear p v.val)
  have hα (v : GeodesicSphere n) (hv : v ∈ V.erase p) : 0 ≤ α v :=
    mul_nonneg (div_nonneg hsin hqn.le)
      (hβ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  have htin : Set.InjOn (fun v : GeodesicSphere n => tangentLinear p v.val)
      (V.erase p : Set (GeodesicSphere n)) := by
    intro v hv w hw h
    have hh := (tangentIndexed_linearIndependent hV hp).injective
      (a₁ := ⟨v, hv⟩) (a₂ := ⟨w, hw⟩) h
    exact congrArg Subtype.val hh
  have htan : ∑ v ∈ V.erase p, α v • tangentLinear p v.val = Real.sin r • u.val := by
    calc
      _ = (Real.sin r / ‖q‖) • ∑ v ∈ V.erase p, β (tangentLinear p v.val) • tangentLinear p v.val := by
        simp only [α, mul_smul, Finset.smul_sum]
      _ = (Real.sin r / ‖q‖) • q := by
        congr 1
        have hh := hβq
        change (∑ z ∈ (V.erase p).image (fun v => tangentLinear p v.val), β z • z) = q at hh
        rw [Finset.sum_image htin] at hh
        exact hh
      _ = (Real.sin r / ‖q‖) • (‖q‖ • u.val) :=
        congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => (Real.sin r / ‖q‖) • z) hqu'
      _ = Real.sin r • u.val := by
        rw [smul_smul, div_mul_cancel₀ _ hqn.ne']
  let c : ℝ := Real.cos r - ∑ v ∈ V.erase p, α v * inner ℝ p.val v.val
  have hrep : c • p.val + (∑ v ∈ V.erase p, α v • v.val) =
      (radialPoint p u hu r).val := by
    simp only [tangentLinear_apply, smul_sub, smul_smul, Finset.sum_sub_distrib,
      ← Finset.sum_smul] at htan
    have hB := eq_add_of_sub_eq htan
    rw [hB, radialPoint_val]
    dsimp [c]
    module
  have hℓsum : ℓ (∑ v ∈ V.erase p, α v • v.val) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro v hv
    rw [map_smul, hℓV v hv, smul_zero]
  have hc : 0 ≤ c := by
    have hh := congrArg ℓ hrep
    rw [map_add, map_smul, hℓp, smul_eq_mul, mul_one, hℓsum, add_zero] at hh
    exact hh ▸ hcoord
  let w : GeodesicSphere n → ℝ := fun v => if v = p then c else α v
  refine ⟨w, ?_, 1, zero_lt_one, ?_⟩
  · intro v hv
    by_cases hvp : v = p
    · simpa only [w, ite_eq_left hvp] using hc
    · simpa only [w, ite_eq_right hvp] using hα v (Finset.mem_erase.mpr ⟨hvp, hv⟩)
  · rw [one_smul, ← hrep]
    calc
      ∑ v ∈ V, w v • v.val = (∑ v ∈ V.erase p, w v • v.val) + w p • p.val :=
        (Finset.sum_erase_add _ _ hp).symm
      _ = (∑ v ∈ V.erase p, α v • v.val) + c • p.val := by
        simp only [w, ite_true]
        congr 1
        apply Finset.sum_congr rfl
        intro v hv
        rw [ite_eq_right (Finset.mem_erase.mp hv).1]
      _ = c • p.val + ∑ v ∈ V.erase p, α v • v.val := add_comm _ _


theorem card_linkVertices_lt {V : Finset (GeodesicSphere n)}
    {p : GeodesicSphere n} (hp : p ∈ V) : (linkVertices V p).card < V.card := by
  exact (Finset.card_image_le.trans Finset.card_image_le).trans_lt (Finset.card_erase_lt_of_mem hp)

/-- On a sufficiently small sphere about a simplex vertex, radial
coordinates identify the simplex slice with its tangent spherical link. -/
theorem exists_spherical_link_radius
    {V : Finset (GeodesicSphere n)}
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < Real.pi ∧
      ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ u : GeodesicSphere n,
        ∀ hu : inner ℝ p.val u.val = 0,
          radialPoint p u hu r ∈ sphericalCell V ↔ u ∈ sphericalCell (linkVertices V p) := by
  obtain ⟨ℓ, hℓp, hℓV⟩ := exists_vertex_coordinate hV hp
  have hopen : IsOpen {x : GeodesicSphere n | 0 < ℓ x.val} :=
    isOpen_lt continuous_const (ℓ.toContinuousLinearMap.continuous.comp continuous_val)
  have hpopen : p ∈ {x : GeodesicSphere n | 0 < ℓ x.val} := by
    change 0 < ℓ p.val
    rw [hℓp]
    exact zero_lt_one
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hpopen)
  let ρ : ℝ := min (ε / 2) (Real.pi / 2)
  have hρ : 0 < ρ := lt_min (half_pos hε) (half_pos Real.pi_pos)
  have hρπ : ρ < Real.pi := (min_le_right _ _).trans_lt (half_lt_self Real.pi_pos)
  refine ⟨ρ, hρ, hρπ, ?_⟩
  intro r hr hrρ u hu
  have hrπ : r < Real.pi := hrρ.trans_lt hρπ
  constructor
  · exact link_mem_of_radialPoint_mem hV hp u hu hr hrπ
  · intro huV
    have hclose : radialPoint p u hu r ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, radialPoint_dist_p p u hu hr.le hrπ.le]
      exact hrρ.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε))
    exact radialPoint_mem_of_link_mem_of_coordinate_pos hV hp ℓ hℓp hℓV u hu
      (Real.sin_pos_of_pos_of_lt_pi hr hrπ).le huV (hball hclose).le


/-- A tangent Gram entry in terms of the three spherical side lengths. -/
theorem normalized_tangent_gram (p x y : GeodesicSphere n)
    (hx : tangentLinear p x.val ≠ 0) (hy : tangentLinear p y.val ≠ 0) :
    inner ℝ (sphereNormalize (tangentLinear p x.val)).val
      (sphereNormalize (tangentLinear p y.val)).val =
        (Real.sin (dist p x))⁻¹ * (Real.sin (dist p y))⁻¹ *
          (Real.cos (dist x y) - Real.cos (dist p x) * Real.cos (dist p y)) := by
  have hnx : ‖tangentLinear p x.val‖ = Real.sin (dist p x) := norm_radialVector p x
  have hny : ‖tangentLinear p y.val‖ = Real.sin (dist p y) := norm_radialVector p y
  have hraw : inner ℝ (tangentLinear p x.val) (tangentLinear p y.val) =
      inner ℝ x.val y.val - inner ℝ p.val x.val * inner ℝ p.val y.val := by
    have hxp : inner ℝ x.val p.val = inner ℝ p.val x.val := real_inner_comm _ _
    simp only [tangentLinear_apply, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right,
      inner_self_eq_one_of_norm_eq_one p.norm_val, hxp]
    ring
  rw [sphereNormalize_val hx, sphereNormalize_val hy]
  simp only [NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right,
    hnx, hny, hraw, ← cos_dist]
  ring

end BrehmApprox.SphericalLink
