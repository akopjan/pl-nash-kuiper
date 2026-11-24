module

public import BrehmApprox.SphericalCellProjection
public import BrehmApprox.SphericalOrthogonalProjection

/-!
# Active spans of actual spherical convex projections

The Euclidean cone projection has a positive finite representation on an active
vertex set. Polar inequalities force orthogonality to every active vertex,
so the cone projection equals ordinary orthogonal projection onto their span.
This is the finite nearest-face selection step needed for reference agreement.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace BrehmApprox

section Cone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma coneProjection_smul (C : ProperCone ℝ E) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    coneProjection C (c • x) = c • coneProjection C x := by
  apply convexProjection_eq_of_variational (C : Set E) C.nonempty C.isClosed.isComplete C.convex
    (C.smul_mem (coneProjection_mem C x) hc)
  intro v hv
  simp only [← smul_sub, inner_sub_right, real_inner_smul_left, inner_smul_right,
    coneProjection_orthogonal, mul_zero, sub_zero]
  exact mul_nonpos_of_nonneg_of_nonpos hc (coneProjection_polar C x hv)

lemma coneProjection_after_starProjection (C : ProperCone ℝ E)
    (L : Submodule ℝ E) [L.HasOrthogonalProjection]
    (hCL : ∀ v ∈ C, v ∈ L) (x : E) :
    coneProjection C (L.starProjection x) = coneProjection C x := by
  apply convexProjection_eq_of_variational (C : Set E) C.nonempty C.isClosed.isComplete C.convex
    (coneProjection_mem C x)
  intro v hv
  have hvL : v - coneProjection C x ∈ L :=
    L.sub_mem (hCL v hv) (hCL _ (coneProjection_mem C x))
  have horth := L.starProjection_inner_eq_zero x (v - coneProjection C x) hvL
  have hvar := coneProjection_variational C x v hv
  simp only [inner_sub_left] at horth hvar ⊢
  linarith

end Cone

open GeodesicSphere

variable {n : ℕ}

/-- The actual ambient linear span of a spherical vertex set. -/
def sphericalVertexSpan (V : Finset (GeodesicSphere n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  Submodule.span ℝ (GeodesicSphere.val '' (V : Set (GeodesicSphere n)))

lemma mem_sphericalVertexSpan {V : Finset (GeodesicSphere n)} {v : GeodesicSphere n}
    (hv : v ∈ V) : v.val ∈ sphericalVertexSpan V :=
  Submodule.subset_span (Set.mem_image_of_mem _ hv)

lemma sphericalVertexSpan_mono {A V : Finset (GeodesicSphere n)} (hAV : A ⊆ V) :
    sphericalVertexSpan A ≤ sphericalVertexSpan V :=
  Submodule.span_mono (Set.image_mono hAV)

lemma vertexCone_mono {A V : Finset (GeodesicSphere n)} (hAV : A ⊆ V) :
    vertexCone A ≤ vertexCone V := by
  rintro z ⟨w, hw, hsum⟩
  rw [← hsum]
  exact (vertexCone V).sum_mem fun v hv => (vertexCone V).smul_mem (hw v hv)
    ((mem_vertexCone_unit_iff V v).mpr (mem_sphericalCell_of_mem (hAV hv)))

lemma sphericalCell_mono {A V : Finset (GeodesicSphere n)} (hAV : A ⊆ V) :
    sphericalCell A ⊆ sphericalCell V := by
  intro x hx
  exact (mem_vertexCone_unit_iff V x).mp
    (vertexCone_mono hAV ((mem_vertexCone_unit_iff A x).mpr hx))

lemma InOpenHemisphere.mono {A V : Finset (GeodesicSphere n)}
    (hV : InOpenHemisphere V) (hAV : A ⊆ V) : InOpenHemisphere A := by
  obtain ⟨p, hp⟩ := hV
  exact ⟨p, fun v hv => hp v (hAV hv)⟩

lemma vertexCone_subset_vertexSpan (V : Finset (GeodesicSphere n)) :
    (vertexCone V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ sphericalVertexSpan V := by
  rintro z ⟨w, _, hsum⟩
  rw [← hsum]
  exact (sphericalVertexSpan V).sum_mem fun v hv =>
    (sphericalVertexSpan V).smul_mem _ (mem_sphericalVertexSpan hv)

/-- A positive representation of the cone projection identifies its exact
active orthogonal subspace, with no use of differential first variation. -/
lemma coneProjection_eq_starProjection_of_positive_representation
    (V A : Finset (GeodesicSphere n)) (hV : InOpenHemisphere V) (hAV : A ⊆ V)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (w : GeodesicSphere n → ℝ)
    (hw : ∀ v ∈ A, 0 < w v)
    (hrep : ∑ v ∈ A, w v • v.val = coneProjection (sphericalCellCone V hV) x) :
    coneProjection (sphericalCellCone V hV) x = (sphericalVertexSpan A).starProjection x := by
  let C := sphericalCellCone V hV
  let p := coneProjection C x
  change ∑ v ∈ A, w v • v.val = p at hrep
  have hpA : p ∈ sphericalVertexSpan A := by
    rw [← hrep]
    exact (sphericalVertexSpan A).sum_mem fun v hv =>
      (sphericalVertexSpan A).smul_mem _ (mem_sphericalVertexSpan hv)
  have hnonpos : ∀ v ∈ A, inner ℝ (x - p) v.val ≤ 0 := by
    intro v hv
    apply coneProjection_polar C x
    change v.val ∈ vertexCone V
    exact (mem_vertexCone_unit_iff V v).mpr (mem_sphericalCell_of_mem (hAV hv))
  have hsum : (∑ v ∈ A, w v * inner ℝ (x - p) v.val) = 0 := by
    have h := congrArg (fun z => inner ℝ (x - p) z) hrep
    simp only [inner_sum, inner_smul_right] at h
    exact h.trans (coneProjection_orthogonal C x)
  have heach : ∀ v ∈ A, inner ℝ (x - p) v.val = 0 := by
    intro v hv
    have hzero := (Finset.sum_eq_zero_iff_of_nonpos
      (fun z hz => mul_nonpos_of_nonneg_of_nonpos (hw z hz).le (hnonpos z hz))).mp hsum v hv
    exact (mul_eq_zero.mp hzero).resolve_left (hw v hv).ne'
  apply Eq.symm
  apply (sphericalVertexSpan A).eq_starProjection_of_mem_of_inner_eq_zero hpA
  intro z hz
  have hspan : sphericalVertexSpan A ≤ LinearMap.ker (innerₛₗ ℝ (x - p)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact heach v hv
  exact hspan hz

/-- Every nonzero projection to a finite spherical cell has an actual finite
active vertex set, and is the orthogonal projection to its linear span. -/
theorem exists_active_spherical_projection (V : Finset (GeodesicSphere n))
    (hV : InOpenHemisphere V) (x : GeodesicSphere n)
    (hx : coneProjection (sphericalCellCone V hV) x.val ≠ 0) :
    ∃ A : Finset (GeodesicSphere n), A ⊆ V ∧ A.Nonempty ∧
      sphericalCellProjection V hV x ∈ sphericalCell A ∧
      coneProjection (sphericalCellCone V hV) x.val = (sphericalVertexSpan A).starProjection x.val := by
  classical
  obtain ⟨w, hw, hrep⟩ := coneProjection_mem (sphericalCellCone V hV) x.val
  let A := V.filter (fun v => 0 < w v)
  have hAV : A ⊆ V := Finset.filter_subset _ _
  have hwA : ∀ v ∈ A, 0 < w v := fun v hv => (Finset.mem_filter.mp hv).2
  have hrepA : ∑ v ∈ A, w v • v.val = coneProjection (sphericalCellCone V hV) x.val := by
    calc
      _ = ∑ v ∈ V, w v • v.val := Finset.sum_subset hAV (by
        intro v hvV hvA
        have hn : ¬ 0 < w v := fun h => hvA (Finset.mem_filter.mpr ⟨hvV, h⟩)
        have hz : w v = 0 := le_antisymm (le_of_not_gt hn) (hw v hvV)
        simp only [hz, zero_smul])
      _ = _ := hrep
  have hne : A.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    rw [hempty, Finset.sum_empty] at hrepA
    exact hx hrepA.symm
  have hprojA : coneProjection (sphericalCellCone V hV) x.val ∈ vertexCone A :=
    ⟨w, fun v hv => (hwA v hv).le, hrepA⟩
  have hmem := (mem_vertexCone_iff_normalize A _ hx).mp hprojA
  refine ⟨A, hAV, hne, ?_, coneProjection_eq_starProjection_of_positive_representation
    V A hV hAV x.val w hwA hrepA⟩
  have heq : sphericalCellProjection V hV x = normalizeVector
      (coneProjection (sphericalCellCone V hV) x.val) hx := by
    apply GeodesicSphere.ext
    exact sphericalConeProjection_val (sphericalCellCone V hV) x hx
  rwa [heq]

end BrehmApprox

namespace GeodesicSphere

open BrehmApprox

variable {n : ℕ}

lemma isOpen_coneProjection_ne_zero
    (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1)))) :
    IsOpen {x : GeodesicSphere n | coneProjection C x.val ≠ 0} :=
  (isClosed_singleton.preimage ((coneProjection_short C).continuous.comp continuous_val)).isOpen_compl

/-- The totalized nearest spherical projection is continuous wherever its
Euclidean cone projection is nonzero. -/
lemma sphericalConeProjection_continuousAt
    (C : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {x : GeodesicSphere n} (hx : coneProjection C x.val ≠ 0) :
    ContinuousAt (sphericalConeProjection C) x := by
  let U : Set (GeodesicSphere n) := {y | coneProjection C y.val ≠ 0}
  have hv : Continuous (fun y : GeodesicSphere n => coneProjection C y.val) :=
    (coneProjection_short C).continuous.comp continuous_val
  have hU : IsOpen U := (isClosed_singleton.preimage hv).isOpen_compl
  have hnorm : Continuous (fun y : U => normalizeVector (coneProjection C y.val.val) y.property) :=
    continuous_normalizeVector _ (hv.comp continuous_subtype_val) (fun y => y.property)
  have hres : Continuous (U.domRestrict (sphericalConeProjection C)) := by
    convert hnorm using 1
    funext y
    apply GeodesicSphere.ext
    exact sphericalConeProjection_val C y.val y.property
  exact (continuousOn_iff_continuous_domRestrict.mpr hres).continuousAt (hU.mem_nhds hx)

/-- Equality of unnormalized nested projections implies equality of the
actual spherical nearest projections after positive normalization. -/
lemma sphericalConeProjection_comp_of_projection_eq
    (C D : ProperCone ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (x : GeodesicSphere n)
    (hC : coneProjection C x.val ≠ 0) (hD : coneProjection D x.val ≠ 0)
    (hcomp : coneProjection D (coneProjection C x.val) = coneProjection D x.val) :
    sphericalConeProjection D (sphericalConeProjection C x) = sphericalConeProjection D x := by
  have hscale : coneProjection D (sphericalConeProjection C x).val =
      ‖coneProjection C x.val‖⁻¹ • coneProjection D x.val := by
    rw [sphericalConeProjection_val C x hC, NormedSpace.normalize,
      coneProjection_smul D (inv_nonneg.mpr (norm_nonneg _)), hcomp]
  have hcpos : 0 < ‖coneProjection C x.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hC)
  have hDafter : coneProjection D (sphericalConeProjection C x).val ≠ 0 := by
    rw [hscale]
    exact smul_ne_zero hcpos.ne' hD
  apply GeodesicSphere.ext
  rw [sphericalConeProjection_val D _ hDafter, sphericalConeProjection_val D x hD,
    hscale, NormedSpace.normalize_smul_of_pos hcpos]

end GeodesicSphere

namespace BrehmApprox

open GeodesicSphere

variable {n : ℕ}

lemma sphericalCellProjection_comp_of_active_span
    (W V A : Finset (GeodesicSphere n)) (hW : InOpenHemisphere W) (hV : InOpenHemisphere V)
    (x : GeodesicSphere n)
    (hWx : coneProjection (sphericalCellCone W hW) x.val ≠ 0)
    (hVx : coneProjection (sphericalCellCone V hV) x.val ≠ 0)
    (hactive : coneProjection (sphericalCellCone V hV) x.val =
      (sphericalVertexSpan A).starProjection x.val)
    (hspan : sphericalVertexSpan W ≤ sphericalVertexSpan A) :
    sphericalCellProjection W hW (sphericalCellProjection V hV x) = sphericalCellProjection W hW x := by
  apply sphericalConeProjection_comp_of_projection_eq (sphericalCellCone V hV)
    (sphericalCellCone W hW) x hVx hWx
  rw [hactive]
  exact coneProjection_after_starProjection (sphericalCellCone W hW) (sphericalVertexSpan A)
    (fun v hv => hspan (vertexCone_subset_vertexSpan W hv)) x.val

/-- A finite closed-cell avoidance argument gives exact nearest-projection
composition on a neighborhood. The explicit condition on all vertex subsets
is verified below for a point with positive simplex coordinates in `W`. -/
theorem sphericalCellProjection_eventually_comp_of_span_condition
    (W V : Finset (GeodesicSphere n)) (hW : InOpenHemisphere W) (hV : InOpenHemisphere V)
    (hWV : W ⊆ V) {p : GeodesicSphere n} (hp : p ∈ sphericalCell W)
    (hspans : ∀ A : Finset (GeodesicSphere n), A ⊆ V → p ∈ sphericalCell A →
      sphericalVertexSpan W ≤ sphericalVertexSpan A) :
    ∀ᶠ x in 𝓝 p,
      sphericalCellProjection W hW (sphericalCellProjection V hV x) = sphericalCellProjection W hW x := by
  classical
  let I := V.powerset.filter fun A => ¬ sphericalVertexSpan W ≤ sphericalVertexSpan A
  let Bad : Set (GeodesicSphere n) := ⋃ A ∈ I, sphericalCell A
  have hBad : IsClosed Bad := isClosed_biUnion_finset (by
    intro A hA
    exact isClosed_sphericalCell A (hV.mono (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)))
  have hpBad : p ∉ Bad := by
    intro h
    obtain ⟨A, hAI, hpA⟩ := Set.mem_iUnion₂.mp h
    have hA := Finset.mem_filter.mp hAI
    exact hA.2 (hspans A (Finset.mem_powerset.mp hA.1) hpA)
  have hpV : p ∈ sphericalCell V := sphericalCell_mono hWV hp
  have hpW0 : coneProjection (sphericalCellCone W hW) p.val ≠ 0 := by
    rw [coneProjection_fix (sphericalCellCone W hW) ((mem_vertexCone_unit_iff W p).mpr hp)]
    exact p.val_ne_zero
  have hpV0 : coneProjection (sphericalCellCone V hV) p.val ≠ 0 := by
    rw [coneProjection_fix (sphericalCellCone V hV) ((mem_vertexCone_unit_iff V p).mpr hpV)]
    exact p.val_ne_zero
  have hcont : ContinuousAt (sphericalCellProjection V hV) p :=
    sphericalConeProjection_continuousAt (sphericalCellCone V hV) hpV0
  have havoid : ∀ᶠ x in 𝓝 p, sphericalCellProjection V hV x ∉ Bad := by
    have he : ∀ᶠ y in 𝓝 (sphericalCellProjection V hV p), y ∉ Bad := by
      apply hBad.isOpen_compl.mem_nhds
      rwa [sphericalCellProjection_fix V hV hpV]
    exact hcont.eventually he
  have heW : ∀ᶠ x in 𝓝 p, coneProjection (sphericalCellCone W hW) x.val ≠ 0 :=
    (isOpen_coneProjection_ne_zero (sphericalCellCone W hW)).mem_nhds hpW0
  have heV : ∀ᶠ x in 𝓝 p, coneProjection (sphericalCellCone V hV) x.val ≠ 0 :=
    (isOpen_coneProjection_ne_zero (sphericalCellCone V hV)).mem_nhds hpV0
  filter_upwards [havoid, heW, heV] with x hxBad hxW hxV
  obtain ⟨A, hAV, _, hxA, hactive⟩ := exists_active_spherical_projection V hV x hxV
  have hspan : sphericalVertexSpan W ≤ sphericalVertexSpan A := by
    by_contra hnot
    apply hxBad
    exact Set.mem_iUnion₂.mpr ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAV, hnot⟩, hxA⟩
  exact sphericalCellProjection_comp_of_active_span W V A hW hV x hxW hxV hactive hspan

/-- The positive-coordinate part of a spherical cell. For an independent
vertex set, these are precisely the points in the relative interior of the
corresponding spherical simplex. The definition uses actual ambient vectors. -/
def positiveSphericalCell (W : Finset (GeodesicSphere n)) : Set (GeodesicSphere n) :=
  {p | ∃ w : GeodesicSphere n → ℝ, (∀ v ∈ W, 0 < w v) ∧
    ∃ a : ℝ, 0 < a ∧ ∑ v ∈ W, w v • v.val = a • p.val}

lemma positiveSphericalCell_subset (W : Finset (GeodesicSphere n)) :
    positiveSphericalCell W ⊆ sphericalCell W := by
  rintro p ⟨w, hw, a, ha, hrep⟩
  exact ⟨w, fun v hv => (hw v hv).le, a, ha, hrep⟩

lemma sum_spherical_coeff_extend [DecidableEq (GeodesicSphere n)]
    (W V : Finset (GeodesicSphere n)) (hWV : W ⊆ V)
    (w : GeodesicSphere n → ℝ) :
    ∑ v ∈ V, (if v ∈ W then w v else 0) • v.val = ∑ v ∈ W, w v • v.val := by
  classical
  calc
    _ = ∑ v ∈ W, (if v ∈ W then w v else 0) • v.val :=
      (Finset.sum_subset hWV (by intro v _ hv; simp [hv])).symm
    _ = _ := Finset.sum_congr rfl (fun v hv => by simp [hv])

/-- A point with positive coordinates in a face cannot lie in any other face
which omits one of its vertices. This is coefficient uniqueness, proved
directly from linear independence of the actual ambient vertex vectors. -/
theorem subset_of_positiveSphericalCell_mem
    (V W A : Finset (GeodesicSphere n))
    (hlin : LinearIndependent ℝ (fun v : V => v.val.val))
    (hWV : W ⊆ V) (hAV : A ⊆ V) {p : GeodesicSphere n}
    (hpW : p ∈ positiveSphericalCell W) (hpA : p ∈ sphericalCell A) : W ⊆ A := by
  classical
  obtain ⟨w, hw, a, ha, hW⟩ := hpW
  obtain ⟨u, _, b, hb, hA⟩ := hpA
  let f : GeodesicSphere n → ℝ := fun v => if v ∈ W then b * w v else 0
  let g : GeodesicSphere n → ℝ := fun v => if v ∈ A then a * u v else 0
  have hf : ∑ v ∈ V, f v • v.val = (b * a) • p.val := by
    rw [sum_spherical_coeff_extend W V hWV]
    simp only [mul_smul, ← Finset.smul_sum, hW]
  have hg : ∑ v ∈ V, g v • v.val = (a * b) • p.val := by
    rw [sum_spherical_coeff_extend A V hAV]
    simp only [mul_smul, ← Finset.smul_sum, hA]
  have heq : ∑ v ∈ V, f v • v.val = ∑ v ∈ V, g v • v.val := by
    rw [hf, hg, mul_comm b a]
  have hcoords := linearIndepOn_finset_iffₛ.mp hlin f g heq
  intro v hvW
  by_contra hvA
  have h := hcoords v (hWV hvW)
  simp only [f, g, ite_eq_left hvW, ite_eq_right hvA] at h
  exact (mul_pos hb (hw v hvW)).ne' h

/-- Exact local composition of nearest spherical face projections at a point
with positive coordinates in the smaller face. All projections are the
normalized Euclidean projections to the actual cones of the two simplices. -/
theorem sphericalCellProjection_eventually_comp
    (W V : Finset (GeodesicSphere n)) (hW : InOpenHemisphere W) (hV : InOpenHemisphere V)
    (hlin : LinearIndependent ℝ (fun v : V => v.val.val)) (hWV : W ⊆ V)
    {p : GeodesicSphere n} (hp : p ∈ positiveSphericalCell W) :
    ∀ᶠ x in 𝓝 p,
      sphericalCellProjection W hW (sphericalCellProjection V hV x) = sphericalCellProjection W hW x := by
  apply sphericalCellProjection_eventually_comp_of_span_condition W V hW hV hWV
    (positiveSphericalCell_subset W hp)
  intro A hAV hpA
  exact sphericalVertexSpan_mono (subset_of_positiveSphericalCell_mem V W A hlin hWV hAV hp hpA)

/-- Every point of a finite spherical cell has positive coordinates on a
nonempty subset of its vertices. No independence assumption is needed here. -/
theorem exists_positiveSphericalCell (V : Finset (GeodesicSphere n))
    {p : GeodesicSphere n} (hp : p ∈ sphericalCell V) :
    ∃ W : Finset (GeodesicSphere n), W ⊆ V ∧ W.Nonempty ∧ p ∈ positiveSphericalCell W := by
  classical
  obtain ⟨w, hw, a, ha, hrep⟩ := hp
  let W := V.filter (fun v => 0 < w v)
  have hWV : W ⊆ V := Finset.filter_subset _ _
  have hwW : ∀ v ∈ W, 0 < w v := fun v hv => (Finset.mem_filter.mp hv).2
  have hrepW : ∑ v ∈ W, w v • v.val = a • p.val := by
    calc
      _ = ∑ v ∈ V, w v • v.val := Finset.sum_subset hWV (by
        intro v hvV hvW
        have hn : ¬ 0 < w v := fun h => hvW (Finset.mem_filter.mpr ⟨hvV, h⟩)
        have hz : w v = 0 := le_antisymm (le_of_not_gt hn) (hw v hvV)
        simp only [hz, zero_smul])
      _ = _ := hrep
  have hne : W.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    rw [hempty, Finset.sum_empty] at hrepW
    exact smul_ne_zero ha.ne' p.val_ne_zero hrepW.symm
  exact ⟨W, hWV, hne, w, hwW, a, ha, hrepW⟩

/-- Independent spherical vertices stratify their cell into unique positive
faces. This supplies an actual finite face selection, rather than assuming
the existence of a suitable nearest-face label. -/
theorem existsUnique_positiveSphericalCell (V : Finset (GeodesicSphere n))
    (hlin : LinearIndependent ℝ (fun v : V => v.val.val))
    {p : GeodesicSphere n} (hp : p ∈ sphericalCell V) :
    ∃! W : Finset (GeodesicSphere n), W ⊆ V ∧ p ∈ positiveSphericalCell W := by
  obtain ⟨W, hWV, _, hpW⟩ := exists_positiveSphericalCell V hp
  refine ⟨W, ⟨hWV, hpW⟩, ?_⟩
  rintro A ⟨hAV, hpA⟩
  apply Finset.Subset.antisymm
  · exact subset_of_positiveSphericalCell_mem V A W hlin hAV hWV hpA
      (positiveSphericalCell_subset W hpW)
  · exact subset_of_positiveSphericalCell_mem V W A hlin hWV hAV hpW
      (positiveSphericalCell_subset A hpA)

/-- Faces of an actual independent spherical simplex meet in their common
vertex face. -/
theorem sphericalCell_inter_of_independent
    [DecidableEq (GeodesicSphere n)]
    (V W A : Finset (GeodesicSphere n))
    (hlin : LinearIndependent ℝ (fun v : V => v.val.val)) (hWV : W ⊆ V) (hAV : A ⊆ V) :
    sphericalCell W ∩ sphericalCell A = sphericalCell (W ∩ A) := by
  classical
  apply Set.Subset.antisymm
  · rintro p ⟨hpW, hpA⟩
    obtain ⟨F, hFW, _, hpF⟩ := exists_positiveSphericalCell W hpW
    have hFA : F ⊆ A := subset_of_positiveSphericalCell_mem V F A hlin
      (hFW.trans hWV) hAV hpF hpA
    exact sphericalCell_mono (Finset.subset_inter hFW hFA) (positiveSphericalCell_subset F hpF)
  · intro p hp
    exact ⟨sphericalCell_mono Finset.inter_subset_left hp,
      sphericalCell_mono Finset.inter_subset_right hp⟩

end BrehmApprox
