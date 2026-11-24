module

public import BrehmApprox.NearestFaceSelection
public import BrehmApprox.FoldedGeometry
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Genuine relative interiors of finite convex hulls

Positive barycentric weights put a point in the actual intrinsic interior.
Restricting arbitrary nonnegative weights to their positive support therefore
produces a genuine face-interior cover of every finite simplex. These facts
are proved from convexity and finite-dimensional topology, not included as
preparation assumptions.
-/

@[expose] public section

open scoped BigOperators

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

def PositiveConvexCombination (V : Finset E) (p : E) : Prop :=
  ∃ w : E → ℝ, (∀ v ∈ V, 0 < w v) ∧
    (∑ v ∈ V, w v) = 1 ∧ (∑ v ∈ V, w v • v) = p

omit [FiniteDimensional ℝ E] in
theorem PositiveConvexCombination.mem_convexHull
    {V : Finset E} {p : E} (hp : PositiveConvexCombination V p) :
    p ∈ convexHull ℝ (V : Set E) := by
  obtain ⟨w, hw, hw1, hwp⟩ := hp
  exact Finset.mem_convexHull'.mpr ⟨w, fun v hv => (hw v hv).le, hw1, hwp⟩

/-- Strictly positive finite barycentric weights imply true relative
interiority, including the one-vertex case. Independence is not needed. -/
theorem PositiveConvexCombination.intrinsicInterior
    {V : Finset E} {p : E} (hp : PositiveConvexCombination V p) :
    p ∈ intrinsicInterior ℝ (convexHull ℝ (V : Set E)) := by
  classical
  have hpC := hp.mem_convexHull
  obtain ⟨w, hw, hw1, hwp⟩ := hp
  have hV : V.Nonempty := by
    by_contra h
    have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hw1
  let C := convexHull ℝ (V : Set E)
  have hconv : Convex ℝ C := convex_convexHull _ _
  obtain ⟨y, hy⟩ := (show C.Nonempty from ⟨p, hpC⟩).intrinsicInterior hconv
  obtain ⟨u, hu0, hu1, huy⟩ := Finset.mem_convexHull'.mp
    (show y ∈ convexHull ℝ (V : Set E) from intrinsicInterior_subset hy)
  have hu_le (v : E) (hv : v ∈ V) : u v ≤ 1 := by
    rw [← hu1]
    exact Finset.single_le_sum hu0 hv
  have hmin : 0 < V.inf' hV w := by
    rw [Finset.lt_inf'_iff]
    exact hw
  let t : ℝ := min 1 (V.inf' hV w) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    have h := min_le_left (1 : ℝ) (V.inf' hV w)
    dsimp [t]
    linarith
  have htw (v : E) (hv : v ∈ V) : t < w v := by
    have h₁ := min_le_right (1 : ℝ) (V.inf' hV w)
    have h₂ : V.inf' hV w ≤ w v := Finset.inf'_le _ hv
    have hpos : 0 < min 1 (V.inf' hV w) := lt_min zero_lt_one hmin
    dsimp [t]
    linarith
  have hden : 0 < 1 - t := sub_pos.mpr ht1
  let z : E := ∑ v ∈ V, ((w v - t * u v) / (1 - t)) • v
  have hz : z ∈ C := by
    apply Finset.mem_convexHull'.mpr
    refine ⟨fun v => (w v - t * u v) / (1 - t), ?_, ?_, rfl⟩
    · intro v hv
      apply div_nonneg _ hden.le
      have htu : t * u v ≤ t := by nlinarith [hu_le v hv]
      linarith [htw v hv]
    · dsimp only
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, hu1]
      simp only [mul_one, div_self hden.ne']
  have hscale : (1 - t) • z = p - t • y := by
    dsimp [z]
    rw [Finset.smul_sum]
    have hcancel (v : E) : (1 - t) * ((w v - t * u v) / (1 - t)) = w v - t * u v := by
      field_simp
    simp_rw [smul_smul, hcancel, sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hwp, huy]
  apply hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hy
    (subset_intrinsicClosure hz)
  refine ⟨t, 1 - t, ht, hden, by ring, ?_⟩
  rw [hscale]
  abel

theorem PositiveConvexCombination.relativeInteriorIn
    {V : Finset E} {p : E} (hp : PositiveConvexCombination V p) :
    RelativeInteriorIn (affineSpan ℝ (convexHull ℝ (V : Set E)))
      (convexHull ℝ (V : Set E)) p :=
  (relativeInteriorIn_iff_intrinsicInterior _ _).mpr hp.intrinsicInterior

omit [FiniteDimensional ℝ E] in
/-- Every point of a finite convex hull has a positive-support subface. -/
theorem exists_positive_convex_subface {V : Finset E} {p : E}
    (hp : p ∈ convexHull ℝ (V : Set E)) :
    ∃ W : Finset E, W ⊆ V ∧ PositiveConvexCombination W p := by
  classical
  obtain ⟨w, hw0, hw1, hwp⟩ := Finset.mem_convexHull'.mp hp
  let W := V.filter fun v => 0 < w v
  have hsub : W ⊆ V := Finset.filter_subset _ _
  have hzero (v : E) (hv : v ∈ V) (hvW : v ∉ W) : w v = 0 := by
    have hn : ¬ 0 < w v := fun h => hvW (Finset.mem_filter.mpr ⟨hv, h⟩)
    exact le_antisymm (le_of_not_gt hn) (hw0 v hv)
  refine ⟨W, hsub, w, fun v hv => (Finset.mem_filter.mp hv).2, ?_, ?_⟩
  · exact (Finset.sum_subset hsub (fun v hv hvW => hzero v hv hvW)).trans hw1
  · exact (Finset.sum_subset hsub (fun v hv hvW => by rw [hzero v hv hvW, zero_smul])).trans hwp

theorem exists_relativeInterior_convex_subface {V : Finset E} {p : E}
    (hp : p ∈ convexHull ℝ (V : Set E)) :
    ∃ W : Finset E, W ⊆ V ∧
      RelativeInteriorIn (affineSpan ℝ (convexHull ℝ (W : Set E)))
        (convexHull ℝ (W : Set E)) p := by
  obtain ⟨W, hW, hpW⟩ := exists_positive_convex_subface hp
  exact ⟨W, hW, hpW.relativeInteriorIn⟩

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
private theorem sum_zero_extend
    [DecidableEq E] {A : Type*} [AddCommMonoid A] {V W : Finset E} (hWV : W ⊆ V) (w : E → A) :
    (∑ v ∈ V, if v ∈ W then w v else 0) = ∑ v ∈ W, w v := by
  classical
  calc
    (∑ v ∈ V, if v ∈ W then w v else 0) =
        ∑ v ∈ W, if v ∈ W then w v else 0 :=
      (Finset.sum_subset hWV (fun v _ hv => by simp [hv])).symm
    _ = ∑ v ∈ W, w v := Finset.sum_congr rfl (fun v hv => by simp [hv])

omit [FiniteDimensional ℝ E] in
/-- A point with positive weights on one vertex face cannot lie in another
face unless the latter contains every vertex of the former. -/
theorem PositiveConvexCombination.support_subset
    {V W U : Finset E} {p : E}
    (hV : AffineIndependent ℝ ((↑) : V → E)) (hWV : W ⊆ V) (hUV : U ⊆ V)
    (hp : PositiveConvexCombination W p)
    (hpU : p ∈ convexHull ℝ (U : Set E)) : W ⊆ U := by
  classical
  obtain ⟨w, hw, hw1, hwp⟩ := hp
  obtain ⟨u, _, hu1, hup⟩ := Finset.mem_convexHull'.mp hpU
  let w' : E → ℝ := fun v => if v ∈ W then w v else 0
  let u' : E → ℝ := fun v => if v ∈ U then u v else 0
  have hsw : (∑ v ∈ V, w' v) = 1 := (sum_zero_extend hWV w).trans hw1
  have hsu : (∑ v ∈ V, u' v) = 1 := (sum_zero_extend hUV u).trans hu1
  have hwp' : (∑ v ∈ V, w' v • v) = p := by
    simpa only [w', ite_smul, zero_smul] using (sum_zero_extend hWV (fun v => w v • v)).trans hwp
  have hup' : (∑ v ∈ V, u' v • v) = p := by
    simpa only [u', ite_smul, zero_smul] using (sum_zero_extend hUV (fun v => u v • v)).trans hup
  have heq := hV.eq_of_sum_eq_sum_subtype (hsw.trans hsu.symm) (hwp'.trans hup'.symm)
  intro v hv
  by_contra hvU
  have hvEq := heq v (hWV hv)
  have hvPos := hw v hv
  simp only [w', u', ite_eq_left hv, ite_eq_right hvU] at hvEq
  linarith

variable {Good : (E → E) → Prop} {M : PolytopeModel E Good} {N : ℕ}

/-- Actual finite simplex vertices and all their subfaces. These data are
geometric: none of the fields refers to reference maps or approximations. -/
structure SimplicialFaceData (D : PolyhedralFaceData M N) where
  vertices : Fin N → Finset E
  core_eq : ∀ i, D.core i = convexHull ℝ (vertices i : Set E)
  independent : ∀ i, AffineIndependent ℝ ((↑) : vertices i → E)
  vertices_mono : ∀ i j, D.faceLE i j → vertices i ⊆ vertices j
  all_subfaces : ∀ i W, W ⊆ vertices i →
    ∃ j, D.faceLE j i ∧ vertices j = W
  face_of_vertices : ∀ i j k, D.faceLE i k → D.faceLE j k →
    vertices i ⊆ vertices j → D.faceLE i j

namespace SimplicialFaceData

variable {D : PolyhedralFaceData M N} (T : SimplicialFaceData D)

omit [FiniteDimensional ℝ E] in
include T in
theorem convex_core (i : Fin N) : Convex ℝ (D.core i) := by
  rw [T.core_eq]
  exact convex_convexHull _ _

/-- The relative-interior coverage required by nearest-face selection follows
from the actual vertex-face data. -/
theorem core_relativeInterior_cover (i : Fin N) {p : E} (hp : p ∈ D.core i) :
    ∃ j, D.faceLE j i ∧ PositiveConvexCombination (T.vertices j) p ∧
      RelativeInteriorIn (affineSpan ℝ (D.core j)) (D.core j) p := by
  rw [T.core_eq i] at hp
  obtain ⟨W, hW, hpW⟩ := exists_positive_convex_subface hp
  obtain ⟨j, hji, hj⟩ := T.all_subfaces i W hW
  have hpj : PositiveConvexCombination (T.vertices j) p := hj ▸ hpW
  refine ⟨j, hji, hpj, ?_⟩
  rw [T.core_eq j]
  exact hpj.relativeInteriorIn

omit [FiniteDimensional ℝ E] in
/-- In a common simplex, a point in the positive part of one face lies only
in faces containing it. -/
theorem faceLE_of_positive_point {i j k : Fin N} {p : E}
    (hik : D.faceLE i k) (hjk : D.faceLE j k)
    (hp : PositiveConvexCombination (T.vertices i) p) (hpj : p ∈ D.core j) :
    D.faceLE i j := by
  apply T.face_of_vertices i j k hik hjk
  apply hp.support_subset (T.independent k) (T.vertices_mono i k hik) (T.vertices_mono j k hjk)
  rwa [T.core_eq j] at hpj

end SimplicialFaceData

namespace FoldedGeometry

variable {P : Type*} [MetricSpace P]
variable (G : FoldedGeometry (P := P) M N)
variable (T : SimplicialFaceData G.toPolyhedralFaceData)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem fold_mem_core {i : Fin N} {x : P} (hx : x ∈ G.cell i) : G.fold x ∈ G.core i := by
  rw [← G.image_cell i]
  exact Set.mem_image_of_mem G.fold hx

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Membership in a subface can be checked in the folding chart of a fixed
coface; arbitrary overlaps between unrelated folded sheets play no role. -/
theorem mem_subcell_of_fold_mem {i j : Fin N} (hji : G.faceLE j i)
    {x : P} (hx : x ∈ G.cell i) (hqx : G.fold x ∈ G.core j) : x ∈ G.cell j := by
  rw [← G.image_cell j] at hqx
  obtain ⟨y, hy, heq⟩ := hqx
  have heq' := (G.constantSource (0 : E)).fold_injective_cell i
    (G.cell_mono j i hji hy) hx heq
  exact heq' ▸ hy

omit [FiniteDimensional ℝ E] in
/-- A positive barycentric point of a source face cannot lie on a source cell
which does not contain that face. This is a statement about source cells,
not about accidental intersections of their folded images. -/
theorem faceLE_of_positive_source_point {i j : Fin N} {x : P}
    (hxi : x ∈ G.cell i) (hxj : x ∈ G.cell j)
    (hp : PositiveConvexCombination (T.vertices i) (G.fold x)) : G.faceLE i j := by
  have hxm := G.intersection i j ⟨hxi, hxj⟩
  have hqm := G.fold_mem_core hxm
  have him : G.faceLE i (G.meet i j) :=
    T.faceLE_of_positive_point (G.le_refl i) (G.meet_le_left i j) hp hqm
  exact G.le_trans _ _ _ him (G.meet_le_right i j)

/-- Every source point has an actual minimal vertex face. In particular its
relative-interior and incidence properties are derived, not assumed. -/
theorem relativeInterior_face_cover (i : Fin N) {x : P} (hx : x ∈ G.cell i) :
    ∃ j, G.faceLE j i ∧ x ∈ G.cell j ∧
      PositiveConvexCombination (T.vertices j) (G.fold x) ∧
      RelativeInteriorIn (affineSpan ℝ (G.core j)) (G.core j) (G.fold x) ∧
      ∀ k, x ∈ G.cell k → G.faceLE j k := by
  obtain ⟨j, hji, hp, hrel⟩ := T.core_relativeInterior_cover i (G.fold_mem_core hx)
  have hqx : G.fold x ∈ G.core j := relativeInteriorIn_mem hrel
  have hxj := G.mem_subcell_of_fold_mem hji hx hqx
  exact ⟨j, hji, hxj, hp, hrel,
    fun k hxk => G.faceLE_of_positive_source_point T hxj hxk hp⟩

theorem exists_minimal_face (x : P) :
    ∃ j, x ∈ G.cell j ∧
      PositiveConvexCombination (T.vertices j) (G.fold x) ∧
      RelativeInteriorIn (affineSpan ℝ (G.core j)) (G.core j) (G.fold x) ∧
      ∀ k, x ∈ G.cell k → G.faceLE j k := by
  obtain ⟨i, hxi⟩ := G.cover x
  obtain ⟨j, _, hxj, hp, hrel, hmin⟩ := G.relativeInterior_face_cover T i hxi
  exact ⟨j, hxj, hp, hrel, hmin⟩

end FoldedGeometry

end BrehmApprox
