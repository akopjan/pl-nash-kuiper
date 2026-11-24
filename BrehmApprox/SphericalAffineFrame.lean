module

public import BrehmApprox.SphericalSimplexLink
public import BrehmApprox.SphericalBarycentricSimplex

/-! # An affine tangent chart on an entire spherical simplex

The positive affine section of the vertex cone is projected onto the tangent
space at a point of the simplex. This chart preserves every face, including
faces extending beyond the hemisphere centered at that point.
-/

@[expose] public section
noncomputable section

open Set BrehmApprox.CrossPolytope BrehmApprox.RadialLink
open scoped BigOperators InnerProductSpace

namespace BrehmApprox.SphericalLink

variable {n : ℕ}
local instance sphericalAffineFrameDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def frameFunctional (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ :=
  (RadialLink.exists_functional_one hV).choose

theorem frameFunctional_vertex (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) {v : GeodesicSphere n}
    (hv : v ∈ V) : frameFunctional V hV v.val = 1 :=
  (RadialLink.exists_functional_one hV).choose_spec ⟨v, hv⟩

private theorem normalized_hull (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {W : Finset (GeodesicSphere n)} (hWV : W ⊆ V) :
    sphericalCell W = sphereNormalize '' convexHull ℝ
      (W.image GeodesicSphere.val : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hℓ (z) (hz : z ∈ W.image GeodesicSphere.val) : frameFunctional V hV z = 1 := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact frameFunctional_vertex V hV (hWV hv)
  have he : radialVertices (W.image GeodesicSphere.val) = W := by
    ext x
    simp only [radialVertices, Finset.mem_image]
    constructor
    · rintro ⟨z, ⟨v, hv, rfl⟩, he⟩
      have hv' : sphereNormalize v.val = v := by
        apply GeodesicSphere.ext
        rw [sphereNormalize_val v.val_ne_zero, NormedSpace.normalize_eq_self_of_norm_eq_one v.norm_val]
      rw [hv'] at he
      exact he ▸ hv
    · intro hx
      refine ⟨x.val, ⟨x, hx, rfl⟩, ?_⟩
      apply GeodesicSphere.ext
      rw [sphereNormalize_val x.val_ne_zero, NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val]
  simpa only [he] using RadialLink.sphericalCell_radialVertices_of_functional hℓ

theorem frameFunctional_pos (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {x : GeodesicSphere n} (hx : x ∈ sphericalCell V) : 0 < frameFunctional V hV x.val := by
  rw [normalized_hull V hV (Finset.Subset.refl V)] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hℓ : frameFunctional V hV z = 1 :=
    RadialLink.functional_one_on_hull (fun v hv => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact frameFunctional_vertex V hV hw) hz
  rw [sphereNormalize_val (RadialLink.nonzero_of_functional_one hℓ)]
  simp only [NormedSpace.normalize, map_smul, smul_eq_mul, hℓ, mul_one]
  exact inv_pos.mpr (norm_pos_iff.mpr (RadialLink.nonzero_of_functional_one hℓ))

def frame (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    (p x : GeodesicSphere n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  tangentLinear p (RadialLink.hyperplaneSection (frameFunctional V hV) x)

def frameVertices (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    (p : GeodesicSphere n) (W : Finset (GeodesicSphere n)) :
    Finset (EuclideanSpace ℝ (Fin (n + 1))) := W.image (frame V hV p)

@[simp] theorem frame_self (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (p : GeodesicSphere n) :
    frame V hV p p = 0 := by
  simp only [frame, RadialLink.hyperplaneSection, map_smul, tangentLinear_self, smul_zero]

theorem frame_vertex (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (p : GeodesicSphere n)
    {v : GeodesicSphere n} (hv : v ∈ V) : frame V hV p v = tangentLinear p v.val := by
  simp only [frame, RadialLink.hyperplaneSection, frameFunctional_vertex V hV hv, inv_one, one_smul]

theorem normalize_frame (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (p : GeodesicSphere n)
    {x : GeodesicSphere n} (hx : x ∈ sphericalCell V) :
    NormedSpace.normalize (frame V hV p x) = NormedSpace.normalize (tangentLinear p x.val) := by
  simp only [frame, RadialLink.hyperplaneSection, map_smul]
  exact NormedSpace.normalize_smul_of_pos (inv_pos.mpr (frameFunctional_pos V hV hx)) _

theorem frame_image_face (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val)) (p : GeodesicSphere n)
    {W : Finset (GeodesicSphere n)} (hWV : W ⊆ V) :
    frame V hV p '' sphericalCell W = convexHull ℝ (frameVertices V hV p W : Set _) := by
  rw [normalized_hull V hV hWV, Set.image_image]
  have he : (fun x => frame V hV p (sphereNormalize x)) ''
      convexHull ℝ (W.image GeodesicSphere.val : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      tangentLinear p '' convexHull ℝ (W.image GeodesicSphere.val : Set _) := by
    apply Set.image_congr
    intro z hz
    have hℓ : frameFunctional V hV z = 1 :=
      RadialLink.functional_one_on_hull (fun v hv => by
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact frameFunctional_vertex V hV (hWV hw)) hz
    simp only [frame, RadialLink.section_sphereNormalize hℓ]
  rw [he, LinearMap.image_convexHull]
  congr 1
  simp only [frameVertices, Finset.coe_image, Set.image_image]
  apply Set.image_congr
  intro v hv
  exact (frame_vertex V hV p (hWV hv)).symm

theorem frame_injectiveOn (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ sphericalCell V) :
    Set.InjOn (frame V hV p) (sphericalCell V) := by
  intro x hx y hy he
  let ℓ := frameFunctional V hV
  let X := RadialLink.hyperplaneSection ℓ x
  let Y := RadialLink.hyperplaneSection ℓ y
  have hX : ℓ X = 1 := by
    simp only [X, RadialLink.hyperplaneSection, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ (frameFunctional_pos V hV hx).ne'
  have hY : ℓ Y = 1 := by
    simp only [Y, RadialLink.hyperplaneSection, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ (frameFunctional_pos V hV hy).ne'
  have ht : X - Y = (inner ℝ p.val X - inner ℝ p.val Y) • p.val := by
    change X - inner ℝ p.val X • p.val = Y - inner ℝ p.val Y • p.val at he
    rw [sub_smul]
    exact sub_eq_sub_iff_sub_eq_sub.mp he
  have ha := congrArg ℓ ht
  simp only [map_sub, hX, hY, sub_self, map_smul, smul_eq_mul] at ha
  have hc : inner ℝ p.val X - inner ℝ p.val Y = 0 :=
    (mul_eq_zero.mp ha.symm).resolve_right (frameFunctional_pos V hV hp).ne'
  rw [hc, zero_smul] at ht
  have hXY := sub_eq_zero.mp ht
  have hn := congrArg NormedSpace.normalize hXY
  simp only [X, Y, ℓ, RadialLink.hyperplaneSection,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr (frameFunctional_pos V hV hx)),
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr (frameFunctional_pos V hV hy)),
    NormedSpace.normalize_eq_self_of_norm_eq_one x.norm_val,
    NormedSpace.normalize_eq_self_of_norm_eq_one y.norm_val] at hn
  exact GeodesicSphere.ext hn

theorem frameVertices_independent (V : Finset (GeodesicSphere n))
    (hV : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ sphericalCell V) :
    AffineIndependent ℝ ((↑) : frameVertices V hV p V → EuclideanSpace ℝ (Fin (n + 1))) := by
  have hi : AffineIndependent ℝ (fun v : V => tangentLinear p v.val.val) := by
    rw [affineIndependent_iff]
    intro s a ha ht
    let b := ∑ v ∈ s, a v * inner ℝ p.val v.val.val
    have hvect : (∑ v ∈ s, a v • v.val.val) = b • p.val := by
      simpa only [tangentLinear_apply, smul_sub, smul_smul, Finset.sum_sub_distrib,
        ← Finset.sum_smul, sub_eq_zero, b] using ht
    have hh := congrArg (frameFunctional V hV) hvect
    simp only [map_sum, map_smul, frameFunctional_vertex V hV (Subtype.property _),
      smul_eq_mul, mul_one, ha] at hh
    have hb : b = 0 := (mul_eq_zero.mp hh.symm).resolve_right (frameFunctional_pos V hV hp).ne'
    rw [hb, zero_smul] at hvect
    exact linearIndependent_iff'.mp hV s a hvect
  have ha : AffineIndependent ℝ (fun v : V => frame V hV p v.val) := by
    simpa only [frame_vertex V hV p (Subtype.property _)] using hi
  have he : Set.range (fun v : V => frame V hV p v.val) =
      (frameVertices V hV p V : Set _) := by
    ext z
    simp only [Set.mem_range, frameVertices, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨v, rfl⟩; exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, hv⟩, rfl⟩
  have hr := ha.range
  change AffineIndependent ℝ ((↑) : Set.range (fun v : V => frame V hV p v.val) → EuclideanSpace ℝ (Fin (n + 1))) at hr
  rw [he] at hr
  exact hr

end BrehmApprox.SphericalLink
