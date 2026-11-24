module

public import BrehmApprox.SphereModel
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Obstruction to strict contraction approximation on the whole sphere

Every strict contraction of a round sphere sends some point to its antipode.
Consequently the identity cannot be uniformly approximated by strict
contractions with error below `pi`.  This refutes a proposed strictification
lemma on the whole sphere; it does not refute versions restricted to an open
hemisphere.

The final lemmas verify the balanced-equatorial-cap obstruction in the
corrected branched spherical example. They do not package the construction of
that glued source or the degree argument as assumptions with theorem names.
-/

@[expose] public section

noncomputable section

namespace GeodesicSphere

variable {n : ℕ}

open scoped BigOperators

/-- Composing a strict contraction with the antipodal isometry and applying
Banach's fixed point theorem produces a point displaced by exactly `pi`. -/
theorem exists_displacement_eq_pi {g : GeodesicSphere n → GeodesicSphere n}
    {K : NNReal} (hK : K < 1) (hg : LipschitzWith K g) :
    ∃ x : GeodesicSphere n, dist (g x) x = Real.pi := by
  let f : GeodesicSphere n → GeodesicSphere n := antipode ∘ g
  have hf : ContractingWith K f :=
    ⟨hK, (Isometry.lipschitzWith_iff K isometry_antipode).mpr hg⟩
  let x : GeodesicSphere n := hf.fixedPoint f
  have hx : antipode (g x) = x := hf.fixedPoint_isFixedPt
  refine ⟨x, ?_⟩
  calc
    dist (g x) x = dist (g x) (antipode (g x)) := congrArg (dist (g x)) hx.symm
    _ = Real.pi := dist_antipode (g x)

/-- A strict contraction cannot stay pointwise at distance less than `pi` from
the identity on the whole round sphere. -/
theorem not_uniformly_close_to_id {g : GeodesicSphere n → GeodesicSphere n}
    {K : NNReal} (hK : K < 1) (hg : LipschitzWith K g) :
    ¬ ∀ x : GeodesicSphere n, dist (g x) x < Real.pi := by
  intro hclose
  obtain ⟨x, hx⟩ := exists_displacement_eq_pi hK hg
  have hxlt := hclose x
  rw [hx] at hxlt
  exact lt_irrefl _ hxlt

/-- In particular, no fixed error bound smaller than `pi` permits a strict
contraction approximation of the identity. -/
theorem no_strict_contraction_approximation {ε : ℝ} (hε : ε < Real.pi) :
    ¬ ∃ (g : GeodesicSphere n → GeodesicSphere n) (K : NNReal),
      K < 1 ∧ LipschitzWith K g ∧ ∀ x, dist (g x) x ≤ ε := by
  rintro ⟨g, K, hK, hg, hclose⟩
  obtain ⟨x, hx⟩ := exists_displacement_eq_pi hK hg
  have hxle := hclose x
  rw [hx] at hxle
  exact (not_le_of_gt hε) hxle

/-- A quantitative necessary condition for an intersection of equal-radius
spherical caps. It detects the failure of the side-length-one example: if the
vector sum is `r p`, the lower inner-product bounds cannot sum to more than `r`.
-/
theorem cap_bound_of_vector_sum (V : Finset (GeodesicSphere n))
    (p y : GeodesicSphere n) {r R : ℝ} (hr : 0 ≤ r) (hR : R ≤ Real.pi)
    (hsum : ∑ v ∈ V, v.val = r • p.val)
    (hcaps : ∀ v ∈ V, dist y v ≤ R) :
    (V.card : ℝ) * Real.cos R ≤ r := by
  have hlower : ∀ v ∈ V, Real.cos R ≤ inner ℝ y.val v.val := by
    intro v hv
    rw [← cos_dist]
    exact Real.cos_le_cos_of_nonneg_of_le_pi dist_nonneg hR (hcaps v hv)
  have htotal := Finset.sum_le_sum hlower
  rw [Finset.sum_const, nsmul_eq_mul, ← inner_sum, hsum, inner_smul_right] at htotal
  have hp : inner ℝ y.val p.val ≤ 1 := by
    simpa only [y.norm_val, p.norm_val, one_mul] using real_inner_le_norm y.val p.val
  exact htotal.trans (by nlinarith)

/-- Strict violation of the cap bound rules out every possible image point. -/
theorem no_common_cap_of_vector_sum (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) {r R : ℝ} (hr : 0 ≤ r) (hR : R ≤ Real.pi)
    (hsum : ∑ v ∈ V, v.val = r • p.val)
    (hgap : r < (V.card : ℝ) * Real.cos R) :
    ¬ ∃ y : GeodesicSphere n, ∀ v ∈ V, dist y v ≤ R := by
  rintro ⟨y, hy⟩
  exact (not_le_of_gt hgap) (cap_bound_of_vector_sum V p y hr hR hsum hy)

/-- If finitely many unit vectors sum to zero, a point lying in all their
closed hemispheres is orthogonal to every one of them. -/
theorem inner_eq_zero_of_balanced_caps (V : Finset (GeodesicSphere n))
    (hbalance : ∑ v ∈ V, v.val = 0) (y : GeodesicSphere n)
    (hcaps : ∀ v ∈ V, dist y v ≤ Real.pi / 2) :
    ∀ v ∈ V, inner ℝ y.val v.val = 0 := by
  have hnonneg : ∀ v ∈ V, 0 ≤ inner ℝ y.val v.val := by
    intro v hv
    rw [← cos_dist]
    exact Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [dist_nonneg (x := y) (y := v), Real.pi_pos], hcaps v hv⟩
  have hsum : ∑ v ∈ V, inner ℝ y.val v.val = 0 := by
    rw [← inner_sum, hbalance, inner_zero_right]
  exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum

/-- The algebraic obstruction used by the corrected spherical counterexample.
For a balanced finite family spanning the equator, the intersection of its
closed radius-`pi/2` caps consists exactly of the two poles. -/
theorem balanced_caps_eq_poles (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hbalance : ∑ v ∈ V, v.val = 0)
    (hspan : Submodule.span ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere n))) =
      (Submodule.span ℝ ({p.val} : Set (EuclideanSpace ℝ (Fin (n + 1)))))ᗮ) :
    {y : GeodesicSphere n | ∀ v ∈ V, dist y v ≤ Real.pi / 2} = {p, antipode p} := by
  ext y
  constructor
  · intro hy
    have hz := inner_eq_zero_of_balanced_caps V hbalance y hy
    have hker : Submodule.span ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere n))) ≤
        LinearMap.ker (innerₛₗ ℝ y.val) := by
      apply Submodule.span_le.mpr
      rintro z ⟨v, hv, rfl⟩
      exact hz v hv
    have horth : y.val ∈
        (Submodule.span ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere n))))ᗮ := by
      apply (Submodule.mem_orthogonal' _ _).mpr
      exact fun z hz => hker hz
    rw [hspan, Submodule.orthogonal_orthogonal] at horth
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp horth
    have hn := congrArg norm ha
    rw [norm_smul, p.norm_val, y.norm_val, Real.norm_eq_abs, mul_one] at hn
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hn with h | h
    · have hyp : y = p := by
        apply GeodesicSphere.ext
        simpa only [h, one_smul] using ha.symm
      exact Or.inl hyp
    · have hyp : y = antipode p := by
        apply GeodesicSphere.ext
        change y.val = -p.val
        simpa only [h, neg_one_smul] using ha.symm
      exact Or.inr hyp
  · intro hy
    have hpv : ∀ v ∈ V, inner ℝ p.val v.val = 0 := by
      intro v hv
      have hvspan : v.val ∈ Submodule.span ℝ
          (GeodesicSphere.val '' (V : Set (GeodesicSphere n))) :=
        Submodule.subset_span ⟨v, hv, rfl⟩
      rw [hspan] at hvspan
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hvspan
    rcases hy with rfl | rfl
    · intro v hv
      rw [dist_eq_arccos_inner, hpv v hv, Real.arccos_zero]
    · intro v hv
      rw [dist_eq_arccos_inner]
      change Real.arccos (inner ℝ (-p.val) v.val) ≤ _
      rw [inner_neg_left, hpv v hv, neg_zero, Real.arccos_zero]

/-- A continuous map of a connected set into all the balanced equatorial caps
must be constant. This is the precise collapse forced on the shared edge of
the corrected three-octant example. -/
theorem eq_on_preconnected_of_balanced_caps (V : Finset (GeodesicSphere n))
    (p : GeodesicSphere n) (hbalance : ∑ v ∈ V, v.val = 0)
    (hspan : Submodule.span ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere n))) =
      (Submodule.span ℝ ({p.val} : Set (EuclideanSpace ℝ (Fin (n + 1)))))ᗮ)
    {A : Type*} [TopologicalSpace A] {s : Set A} (hs : IsPreconnected s)
    (g : A → GeodesicSphere n) (hg : ContinuousOn g s)
    (hcaps : ∀ x ∈ s, ∀ v ∈ V, dist (g x) v ≤ Real.pi / 2) :
    ∀ x ∈ s, ∀ y ∈ s, g x = g y := by
  have hmaps : Set.MapsTo g s ({p, antipode p} : Set (GeodesicSphere n)) := by
    intro x hx
    rw [← balanced_caps_eq_poles V p hbalance hspan]
    exact hcaps x hx
  exact fun _ hx _ hy =>
    hs.constant_of_mapsTo ((Set.finite_singleton (antipode p)).insert p).isDiscrete
      hg hmaps hx hy

end GeodesicSphere
