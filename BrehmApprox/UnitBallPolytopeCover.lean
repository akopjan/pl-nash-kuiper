module

public import BrehmApprox.PolytopeArrangementCover
public import BrehmApprox.Relative
public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# A locally finite facial polyhedral cover of the open unit ball

Finite nets of the closed unit ball give circumscribed polyhedra whose bounding
hyperplanes escape to the unit sphere. The nonempty sign strata of this
countable arrangement have compact polyhedral closures. Their closures meet
along faces and form a locally finite cover relative to the open ball.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace BrehmApprox

/-- A polyhedral cover with local finiteness in its carrier. -/
structure PolytopeCoverOn (E I : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Set E) where
  cell : I → Set E
  polytope : ∀ i, IsFinitePolytope (cell i)
  cell_subset : ∀ i, cell i ⊆ A
  cover : ∀ x ∈ A, ∃ i, x ∈ cell i
  locallyFinite : LocallyFinite (fun i => (Subtype.val : A → E) ⁻¹' cell i)
  face_inter : ∀ i j, IsExtreme ℝ (cell i) (cell i ∩ cell j)

namespace UnitBallCover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Radii increasing to one, with every bounding hyperplane outside its radius. -/
def radius (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 2)

theorem radius_pos (k : ℕ) : 0 < radius k := by
  have h : 1 / ((k : ℝ) + 2) < 1 :=
    (div_lt_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  dsimp [radius]
  linarith

theorem radius_lt_one (k : ℕ) : radius k < 1 := by
  have h : 0 < 1 / ((k : ℝ) + 2) := by positivity
  dsimp [radius]
  linarith

theorem radius_mono : Monotone radius := by
  intro i j hij
  have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hinv : 1 / ((j : ℝ) + 2) ≤ 1 / ((i : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  dsimp [radius]
  linarith

theorem exists_lt_radius {r : ℝ} (hr : r < 1) : ∃ N : ℕ, r < radius N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - r))
  have hden : 0 < 1 - r := by linarith
  have hmul := (div_lt_iff₀ hden).mp hN
  have hinv : 1 / ((N : ℝ) + 2) < 1 - r :=
    (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  exact ⟨N, by dsimp [radius]; linarith⟩

/-- A finite set of normals of norm at most one bounds a polyhedron strictly
inside the unit ball while all its inequalities have positive offset `a`. -/
theorem exists_normals {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ S : Finset E, (∀ u ∈ S, ‖u‖ ≤ 1) ∧
      ∀ x : E, (∀ u ∈ S, inner ℝ u x ≤ a) → ‖x‖ ≤ (a + 1) / 2 := by
  let δ : ℝ := (1 - a) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨S, hS, hnet⟩ := compact_finite_net (isCompact_closedBall (0 : E) 1) hδ
  refine ⟨S, ?_, ?_⟩
  · intro u hu
    simpa only [Metric.mem_closedBall, dist_zero_right] using hS hu
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp only [norm_zero]
      linarith
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let y : E := ‖x‖⁻¹ • x
    have hy : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
        inv_mul_cancel₀ hnorm.ne']
    have hyball : y ∈ Metric.closedBall (0 : E) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, hy, le_refl]
    obtain ⟨u, hu, hdist⟩ := hnet y hyball
    have hinner : 1 - δ < inner ℝ u y := by
      have h := real_inner_le_norm (y - u) y
      rw [inner_sub_left, real_inner_self_eq_norm_sq, hy, one_pow, mul_one] at h
      rw [dist_eq_norm] at hdist
      linarith
    have hxy : ‖x‖ • y = x := by
      dsimp only [y]
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hux : inner ℝ u x = ‖x‖ * inner ℝ u y := by
      conv_lhs => rw [← hxy]
      rw [inner_smul_right]
    have hbound : (1 - δ) * ‖x‖ < a := by
      have hmul := mul_lt_mul_of_pos_left hinner hnorm
      rw [← hux] at hmul
      calc
        (1 - δ) * ‖x‖ = ‖x‖ * (1 - δ) := mul_comm _ _
        _ < inner ℝ u x := hmul
        _ ≤ a := hx u hu
    have hfac : 0 < 1 - δ := by dsimp [δ]; linarith
    have hr : a ≤ (1 - δ) * ((a + 1) / 2) := by
      dsimp [δ]
      nlinarith [sq_nonneg (1 - a)]
    nlinarith

/-- Fixed finite normals at every radius. -/
def normals (k : ℕ) : Finset E :=
  (exists_normals (E := E) (radius_pos k) (radius_lt_one k)).choose

theorem normal_norm (k : ℕ) (u : E) (hu : u ∈ normals (E := E) k) : ‖u‖ ≤ 1 :=
  (exists_normals (E := E) (radius_pos k) (radius_lt_one k)).choose_spec.1 u hu

def stage (k : ℕ) : Set E := {x | ∀ u ∈ normals (E := E) k, inner ℝ u x ≤ radius k}

theorem stage_norm_le (k : ℕ) {x : E} (hx : x ∈ stage k) :
    ‖x‖ ≤ (radius k + 1) / 2 :=
  (exists_normals (E := E) (radius_pos k) (radius_lt_one k)).choose_spec.2 x hx

theorem stage_subset_ball (k : ℕ) : stage (E := E) k ⊆ Metric.ball 0 1 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  exact (stage_norm_le k hx).trans_lt (by linarith [radius_lt_one k])

theorem normal_eval_le_norm (k : ℕ) (u : E) (hu : u ∈ normals (E := E) k) (x : E) :
    inner ℝ u x ≤ ‖x‖ :=
  (real_inner_le_norm u x).trans (by nlinarith [normal_norm k u hu, norm_nonneg x])

theorem stage_polytope (k : ℕ) : IsFinitePolytope (stage (E := E) k) := by
  classical
  obtain ⟨V, hV, _⟩ :=
    (convex_closedBall (0 : E) 1).exists_subset_interior_convexHull_finset_of_isCompact
      (isCompact_closedBall (0 : E) 1)
      (isOpen_univ.mem_nhdsSet.mpr (Set.subset_univ _))
  have hsub : stage (E := E) k ⊆ convexHull ℝ (V : Set E) := by
    intro x hx
    exact interior_subset (hV (Metric.ball_subset_closedBall (stage_subset_ball k hx)))
  let L : normals (E := E) k → E →ₗ[ℝ] ℝ := fun u => innerₛₗ ℝ u.val
  obtain ⟨W, hW⟩ := exists_finset_convexHull_inter_halfspaces V L (fun _ => radius k)
  refine ⟨W, ?_⟩
  rw [← hW]
  ext x
  constructor
  · intro hx
    exact ⟨hsub hx, fun u => hx u u.property⟩
  · intro hx u hu
    exact hx.2 ⟨u, hu⟩

/-- The countable family of finite sets of bounding hyperplanes. -/
abbrev PlaneIndex := Σ k : ℕ, normals (E := E) k

def plane (i : PlaneIndex (E := E)) : E →ₗ[ℝ] ℝ := innerₛₗ ℝ i.2.val

def bound (i : PlaneIndex (E := E)) : ℝ := radius i.1

theorem plane_le_norm (i : PlaneIndex (E := E)) (x : E) : plane i x ≤ ‖x‖ :=
  normal_eval_le_norm i.1 i.2.val i.2.property x

theorem plane_lt_of_norm_lt_radius {N : ℕ} {x : E} (hx : ‖x‖ < radius N)
    (i : PlaneIndex (E := E)) (hi : N ≤ i.1) : plane i x < bound i :=
  (plane_le_norm i x).trans_lt (hx.trans_le (radius_mono hi))

theorem negative_of_holds_lt {s : AffineSign} {a b : ℝ}
    (hs : s.holds a b) (hab : a < b) : s = .negative := by
  cases s with
  | negative => rfl
  | zero => simp only [AffineSign.holds] at hs; linarith
  | positive => simp only [AffineSign.holds] at hs; linarith

theorem negative_of_weak_lt {s : AffineSign} {a b : ℝ}
    (hs : s.weakMatches a b) (hab : a < b) : s = .negative := by
  cases s with
  | negative => rfl
  | zero => simp only [AffineSign.weakMatches] at hs; linarith
  | positive => simp only [AffineSign.weakMatches] at hs; linarith

/-- Only sign patterns realized at points inside the unit ball are retained. -/
def CellIndex := {s : PlaneIndex (E := E) → AffineSign //
  ∃ x ∈ Metric.ball (0 : E) 1, ∀ i, (s i).holds (plane i x) (bound i)}

/-- The closed weak sign cell of a realized sign pattern. -/
def cell (s : CellIndex (E := E)) : Set E :=
  {x | ∀ i, (s.val i).weakMatches (plane i x) (bound i)}

theorem cell_nonempty (s : CellIndex (E := E)) : (cell s).Nonempty := by
  obtain ⟨x, _, hx⟩ := s.property
  exact ⟨x, fun i => AffineSign.holds_weak (hx i)⟩

theorem exists_stage_contains_cell (s : CellIndex (E := E)) :
    ∃ N : ℕ, cell s ⊆ stage N := by
  obtain ⟨x, hx, hxs⟩ := s.property
  have hxnorm : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  obtain ⟨N, hN⟩ := exists_lt_radius hxnorm
  refine ⟨N, ?_⟩
  intro y hy u hu
  let i : PlaneIndex (E := E) := ⟨N, ⟨u, hu⟩⟩
  have hs : s.val i = .negative := negative_of_holds_lt (hxs i)
    (plane_lt_of_norm_lt_radius hN i le_rfl)
  have h := hy i
  simpa only [hs, AffineSign.weakMatches, plane, bound, i, innerₛₗ_apply_apply] using h

theorem cell_subset_ball (s : CellIndex (E := E)) : cell s ⊆ Metric.ball 0 1 := by
  obtain ⟨N, hN⟩ := exists_stage_contains_cell s
  exact hN.trans (stage_subset_ball N)

/-- A finite initial part of the hyperplane arrangement. -/
abbrev Prefix (N : ℕ) := Σ k : Fin N, normals (E := E) k.val

def prefixPlane (N : ℕ) (i : Prefix (E := E) N) : PlaneIndex (E := E) :=
  ⟨i.1.val, i.2⟩

/-- Each infinite sign cell is already cut out by finitely many inequalities
inside one bounded stage. -/
theorem cell_eq_finiteWeakCell (s : CellIndex (E := E)) :
    ∃ N M : ℕ, cell s = affineWeakCell (stage N)
      (fun i : Prefix M => plane (prefixPlane M i))
      (fun i : Prefix M => bound (prefixPlane M i))
      (fun i : Prefix M => s.val (prefixPlane M i)) := by
  obtain ⟨N, hN⟩ := exists_stage_contains_cell s
  obtain ⟨M, hM⟩ := exists_lt_radius (show (radius N + 1) / 2 < 1 by
    linarith [radius_lt_one N])
  obtain ⟨x, _, hxs⟩ := s.property
  have hxcell : x ∈ cell s := fun i => AffineSign.holds_weak (hxs i)
  have hxr : ‖x‖ < radius M := (stage_norm_le N (hN hxcell)).trans_lt hM
  have htail (i : PlaneIndex (E := E)) (hi : M ≤ i.1) : s.val i = .negative :=
    negative_of_holds_lt (hxs i) (plane_lt_of_norm_lt_radius hxr i hi)
  refine ⟨N, M, ?_⟩
  ext y
  constructor
  · intro hy
    exact ⟨hN hy, fun i => hy (prefixPlane M i)⟩
  · intro hy i
    by_cases hi : i.1 < M
    · exact hy.2 ⟨⟨i.1, hi⟩, i.2⟩
    · have hlarge := Nat.le_of_not_gt hi
      have hyr : ‖y‖ < radius M := (stage_norm_le N hy.1).trans_lt hM
      rw [htail i hlarge]
      exact (plane_lt_of_norm_lt_radius hyr i hlarge).le

theorem cell_polytope (s : CellIndex (E := E)) : IsFinitePolytope (cell s) := by
  obtain ⟨N, M, hcell⟩ := cell_eq_finiteWeakCell s
  obtain ⟨V, hV⟩ := stage_polytope (E := E) N
  rw [hcell, hV]
  exact exists_finset_affineWeakCell V
    (fun i : Prefix M => plane (prefixPlane M i))
    (fun i : Prefix M => bound (prefixPlane M i))
    (fun i : Prefix M => s.val (prefixPlane M i))

theorem cell_cover (x : E) (hx : x ∈ Metric.ball (0 : E) 1) : ∃ s, x ∈ cell s := by
  let s : PlaneIndex (E := E) → AffineSign := fun i => AffineSign.ofCompare (plane i x) (bound i)
  have hs : ∀ i, (s i).holds (plane i x) (bound i) :=
    fun i => AffineSign.holds_ofCompare _ _
  exact ⟨⟨s, x, hx, hs⟩, fun i => AffineSign.holds_weak (hs i)⟩

/-- Hyperplanes from sufficiently late stages miss each fixed neighborhood
inside the unit ball. Consequently only finitely many sign cells meet it. -/
theorem cells_locallyFinite :
    LocallyFinite (fun s : CellIndex (E := E) =>
      (Subtype.val : Metric.ball (0 : E) 1 → E) ⁻¹' cell s) := by
  classical
  intro x
  have hx : ‖x.val‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using x.property
  let R : ℝ := (‖x.val‖ + 1) / 2
  have hxR : ‖x.val‖ < R := by dsimp [R]; linarith
  have hR : R < 1 := by dsimp [R]; linarith
  obtain ⟨N, hN⟩ := exists_lt_radius hR
  let U : Set (Metric.ball (0 : E) 1) := {y | ‖y.val‖ < R}
  have hU : IsOpen U :=
    isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  refine ⟨U, hU.mem_nhds hxR, ?_⟩
  let restrict : CellIndex (E := E) → Prefix N → AffineSign :=
    fun s i => s.val (prefixPlane N i)
  apply Set.Finite.of_finite_image (f := restrict) (Set.toFinite _)
  intro s hs t ht hst
  have htail (q : CellIndex (E := E))
      (hq : (((Subtype.val : Metric.ball (0 : E) 1 → E) ⁻¹' cell q) ∩ U).Nonempty)
      (i : PlaneIndex (E := E)) (hi : N ≤ i.1) : q.val i = .negative := by
    obtain ⟨y, hy, hyU⟩ := hq
    have hyr : ‖y.val‖ < radius N := hyU.trans hN
    exact negative_of_weak_lt (hy i) (plane_lt_of_norm_lt_radius hyr i hi)
  apply Subtype.ext
  funext i
  by_cases hi : i.1 < N
  · exact congrFun hst ⟨⟨i.1, hi⟩, i.2⟩
  · rw [htail s hs i (Nat.le_of_not_gt hi), htail t ht i (Nat.le_of_not_gt hi)]

theorem cells_face_inter (s t : CellIndex (E := E)) :
    IsExtreme ℝ (cell s) (cell s ∩ cell t) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, d, ha, hd, had, rfl⟩ := hseg
  refine ⟨hx, fun i => ?_⟩
  have hzi := hz.2 i
  simp only [map_add, map_smul, smul_eq_mul] at hzi
  exact AffineSign.weak_at_left_of_combo (s.val i) (t.val i)
    (hx i) (hy i) hzi ha hd had

/-- A concrete locally finite facial polyhedral cover of the open unit ball. -/
def polytopeCover : PolytopeCoverOn E (CellIndex (E := E)) (Metric.ball (0 : E) 1) where
  cell := cell
  polytope := cell_polytope
  cell_subset := cell_subset_ball
  cover := cell_cover
  locallyFinite := cells_locallyFinite
  face_inter := cells_face_inter

end UnitBallCover
end BrehmApprox
