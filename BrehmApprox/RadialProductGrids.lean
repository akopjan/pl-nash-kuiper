module

public import BrehmApprox.ProtectedNetPropagation
public import BrehmApprox.EuclideanFoldingGeometry
public import BrehmApprox.SphericalFoldingGeometry
public import BrehmApprox.HyperbolicFoldingGeometry

/-!
# Protected radial product grids

Using the same finite set of radii in every direction transfers protection
from an angular net to its radial product. The needed strict comparison is
proved separately from the cosine laws in all three model geometries.
-/

@[expose] public section
noncomputable section

namespace BrehmApprox

variable {P L R : Type*}

local instance radialGridDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

def radialProductGrid (o : P) (radii : Finset R) (directions : Finset L)
    (radial : R → L → P) : Finset P :=
  insert o ((radii.product directions).image fun z => radial z.1 z.2)

theorem radialProductGrid_protected
    (o : P) (radii : Finset R) (directions : Finset L) (radial : R → L → P)
    (sourceCost : P → ℝ) (angularCost : L → ℝ) (F : Set P) (G : Set L)
    (ho : o ∈ F)
    (hface : ∀ r ∈ radii, ∀ v ∈ directions, v ∈ G → radial r v ∈ F)
    (hangular : ∀ v ∈ directions,
      (∀ w ∈ directions, angularCost v ≤ angularCost w) → v ∈ G)
    (hstrict : ∀ r ∈ radii, ∀ v ∈ directions, ∀ w ∈ directions,
      angularCost w < angularCost v → sourceCost (radial r w) < sourceCost (radial r v)) :
    ∀ a ∈ radialProductGrid o radii directions radial,
      (∀ b ∈ radialProductGrid o radii directions radial, sourceCost a ≤ sourceCost b) →
      a ∈ F := by
  intro a ha hmin
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact ho
  obtain ⟨⟨r, v⟩, hrv, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hr, hv⟩ := Finset.mem_product.mp hrv
  apply hface r hr v hv
  apply hangular v hv
  intro w hw
  by_contra h
  have hlt := hstrict r hr v hv w hw (lt_of_not_ge h)
  have hmem : radial r w ∈ radialProductGrid o radii directions radial :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨(r, w), Finset.mem_product.mpr ⟨hr, hw⟩, rfl⟩)
  exact (not_lt_of_ge (hmin _ hmem)) hlt

namespace EuclideanFolding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem same_radius_strict_comparison (p x a b : E)
    (hx : 0 < dist p x) (ha : 0 < dist p a) (hab : dist p a = dist p b)
    (hangle : inner ℝ (radialDirection p x) (radialDirection p b) <
      inner ℝ (radialDirection p x) (radialDirection p a)) : dist x a < dist x b := by
  have h₁ := radial_cosine_law p x a
  have h₂ := radial_cosine_law p x b
  simp only [← hab] at h₂
  have hmul := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hx) ha)
    (sub_pos.mpr hangle)
  nlinarith [dist_nonneg (x := x) (y := a), dist_nonneg (x := x) (y := b)]

end EuclideanFolding

namespace SphericalFolding

variable {n : ℕ}

theorem same_radius_strict_comparison (p x a b : GeodesicSphere n)
    (hx0 : 0 < dist p x) (hxπ : dist p x < Real.pi)
    (ha0 : 0 < dist p a) (haπ : dist p a < Real.pi)
    (hab : dist p a = dist p b)
    (hangle : inner ℝ (GeodesicSphere.radialDirection p x hx0 hxπ)
      (GeodesicSphere.radialDirection p b (hab ▸ ha0) (hab ▸ haπ)) <
      inner ℝ (GeodesicSphere.radialDirection p x hx0 hxπ)
      (GeodesicSphere.radialDirection p a ha0 haπ)) : dist x a < dist x b := by
  have h₁ := GeodesicSphere.radial_cosine_law p x a hx0 hxπ ha0 haπ
  have h₂ := GeodesicSphere.radial_cosine_law p x b hx0 hxπ (hab ▸ ha0) (hab ▸ haπ)
  have hsin : 0 < Real.sin (dist p x) * Real.sin (dist p a) :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi hx0 hxπ) (Real.sin_pos_of_pos_of_lt_pi ha0 haπ)
  have hmul := mul_pos hsin (sub_pos.mpr hangle)
  simp only [← hab] at h₂
  have hcos : Real.cos (dist x b) < Real.cos (dist x a) := by nlinarith
  by_contra h
  have hrev := Real.cos_le_cos_of_nonneg_of_le_pi (dist_nonneg : 0 ≤ dist x b)
    (GeodesicSphere.dist_le_pi x a) (le_of_not_gt h)
  exact (not_lt_of_ge hrev) hcos

end SphericalFolding

namespace HyperbolicSpace

variable {n : ℕ}

theorem same_radius_strict_comparison (p x a b : HyperbolicSpace n)
    (hx : 0 < dist p x) (ha : 0 < dist p a) (hab : dist p a = dist p b)
    (hangle : inner ℝ (radialDirection p x) (radialDirection p b) <
      inner ℝ (radialDirection p x) (radialDirection p a)) : dist x a < dist x b := by
  have h₁ := radial_cosine_law p x a
  have h₂ := radial_cosine_law p x b
  simp only [← hab] at h₂
  have hsin : 0 < Real.sinh (dist p x) * Real.sinh (dist p a) :=
    mul_pos (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr ha)
  have hmul := mul_pos hsin (sub_pos.mpr hangle)
  have hcos : Real.cosh (dist x a) < Real.cosh (dist x b) := by nlinarith
  by_contra h
  have hrev : Real.cosh (dist x b) ≤ Real.cosh (dist x a) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg] using le_of_not_gt h
  exact (not_lt_of_ge hrev) hcos

end HyperbolicSpace

end BrehmApprox
