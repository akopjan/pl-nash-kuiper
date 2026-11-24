module

public import BrehmApprox.Core
public import BrehmApprox.SphereModel

/-!
# Finite determination on genuine spherical polyhedra

A spherical cell is the positive hull of finitely many unit vectors, intersected
with the unit sphere.  A geometric cell used in a polyhedral decomposition is
required to lie in an open hemisphere.  On each cell, a piecewise isometry agrees
with an orthogonal transformation of the ambient Euclidean vector space.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BrehmApprox

variable {n : ℕ}

/-- Positive spherical hull of a finite set.  The strictly positive scale excludes
normalizing the zero vector. -/
def sphericalCell (V : Finset (GeodesicSphere n)) : Set (GeodesicSphere n) :=
  {x | ∃ w : GeodesicSphere n → ℝ, (∀ v ∈ V, 0 ≤ w v) ∧
    ∃ a : ℝ, 0 < a ∧ ∑ v ∈ V, w v • v.val = a • x.val}

/-- The finite vertices lie in one open hemisphere. -/
def InOpenHemisphere (V : Finset (GeodesicSphere n)) : Prop :=
  ∃ p : GeodesicSphere n, ∀ v ∈ V, 0 < inner ℝ p.val v.val

lemma mem_sphericalCell_of_mem {V : Finset (GeodesicSphere n)}
    {v : GeodesicSphere n} (hv : v ∈ V) : v ∈ sphericalCell V := by
  classical
  refine ⟨fun u => if u = v then 1 else 0, ?_, 1, zero_lt_one, ?_⟩
  · intro u _
    by_cases h : u = v <;> simp [h]
  · simp [ite_smul, hv]

/-- A short self-map of the round sphere that fixes the vertices fixes their
positive spherical hull.  No hemisphere assumption is needed for this lemma. -/
lemma short_eq_on_sphericalCell_of_fixed {f : GeodesicSphere n → GeodesicSphere n}
    (hf : Short f) (V : Finset (GeodesicSphere n))
    (hV : ∀ v ∈ V, f v = v) : ∀ x ∈ sphericalCell V, f x = x := by
  classical
  intro x hx
  obtain ⟨w, hw, a, ha, hrep⟩ := hx
  have hinner (v : GeodesicSphere n) (hv : v ∈ V) :
      inner ℝ x.val v.val ≤ inner ℝ (f x).val v.val := by
    have hd : dist (f x) v ≤ dist x v := by simpa only [hV v hv] using hf x v
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (dist_nonneg : 0 ≤ dist (f x) v)
      (GeodesicSphere.dist_le_pi x v) hd
    simpa only [GeodesicSphere.cos_dist] using hc
  have hs := Finset.sum_le_sum (fun v hv =>
    mul_le_mul_of_nonneg_left (hinner v hv) (hw v hv))
  have hl : ∑ v ∈ V, w v * inner ℝ x.val v.val = a := by
    calc
      _ = inner ℝ x.val (∑ v ∈ V, w v • v.val) := by
        simp only [inner_sum, inner_smul_right]
      _ = a := by
        rw [hrep, inner_smul_right, real_inner_self_eq_norm_sq, x.norm_val]
        ring
  have hr : ∑ v ∈ V, w v * inner ℝ (f x).val v.val =
      a * inner ℝ (f x).val x.val := by
    calc
      _ = inner ℝ (f x).val (∑ v ∈ V, w v • v.val) := by
        simp only [inner_sum, inner_smul_right]
      _ = _ := by rw [hrep, inner_smul_right]
  rw [hl, hr] at hs
  have hle : inner ℝ (f x).val x.val ≤ 1 :=
    real_inner_le_one_of_norm_eq_one (f x).norm_val x.norm_val
  have heq : inner ℝ (f x).val x.val = 1 := by nlinarith
  apply GeodesicSphere.ext
  exact (inner_eq_one_iff_of_norm_eq_one (f x).norm_val x.norm_val).mp heq

/-- A finite spherical piecewise isometry on `A`, expressed using actual
hemispherical cells and orthogonal motions. -/
def SphericalPLOn (A : Set (GeodesicSphere n))
    (f : GeodesicSphere n → GeodesicSphere n) : Prop :=
  ∃ C : Finset (Finset (GeodesicSphere n)),
    A = ⋃ V ∈ C, sphericalCell V ∧
    ∀ V ∈ C, InOpenHemisphere V ∧
      ∃ r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
        ∀ x ∈ sphericalCell V, f x = GeodesicSphere.mapEquiv r x

/-- On every compact hemispherical polyhedral domain, the map has finitely many
isometric pieces. -/
def LocallySphericalPL (f : GeodesicSphere n → GeodesicSphere n) : Prop :=
  ∀ V : Finset (GeodesicSphere n), InOpenHemisphere V →
    SphericalPLOn (sphericalCell V) f

lemma determinedOn_sphericalPL {A : Set (GeodesicSphere n)}
    {g : GeodesicSphere n → GeodesicSphere n}
    (hg : SphericalPLOn A g) : DeterminedOn A g := by
  classical
  obtain ⟨C, hA, hg⟩ := hg
  let V : Finset (GeodesicSphere n) := C.biUnion id
  have hVC (D : Finset (GeodesicSphere n)) (hD : D ∈ C) :
      (D : Set (GeodesicSphere n)) ⊆ (V : Set (GeodesicSphere n)) := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨D, hD, hv⟩
  refine ⟨V, ?_, ?_⟩
  · intro v hv
    obtain ⟨D, hD, hvD⟩ := Finset.mem_biUnion.mp hv
    rw [hA]
    exact Set.mem_iUnion.mpr ⟨D, Set.mem_iUnion.mpr ⟨hD,
      mem_sphericalCell_of_mem hvD⟩⟩
  · intro h hh hV x hx
    rw [hA] at hx
    obtain ⟨D, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hD, hxD⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_, r, hr⟩ := hg D hD
    let e : GeodesicSphere n ≃ᵢ GeodesicSphere n := GeodesicSphere.mapEquiv r
    let k : GeodesicSphere n → GeodesicSphere n := fun y => e.symm (h y)
    have hk : Short k := by
      intro y z
      simpa only [k, e.symm.dist_eq] using hh y z
    have hfix : ∀ v ∈ D, k v = v := by
      intro v hv
      change e.symm (h v) = v
      rw [hV v (hVC D hD hv), hr v (mem_sphericalCell_of_mem hv)]
      exact e.symm_apply_apply v
    have hxfix := short_eq_on_sphericalCell_of_fixed hk D hfix x hxD
    calc
      h x = e (e.symm (h x)) := (e.apply_symm_apply (h x)).symm
      _ = e x := congrArg e hxfix
      _ = g x := (hr x hxD).symm

lemma determinedOn_sphericalCell {g : GeodesicSphere n → GeodesicSphere n}
    (hg : LocallySphericalPL g) (V : Finset (GeodesicSphere n))
    (hV : InOpenHemisphere V) : DeterminedOn (sphericalCell V) g :=
  determinedOn_sphericalPL (hg V hV)

end BrehmApprox
