module

public import BrehmApprox.NormalFlattening
public import BrehmApprox.ConvexProjection

/-!
# Normal flattening along affine faces

The affine construction is the translated linear construction, with the same
Lipschitz constant. It preserves projection to every smaller affine subspace
and, more generally, nearest projection to every complete convex subset of the
face. Distances to points of the face do not increase. These are the exact
compatibility properties used when composing face collapses.
-/

@[expose] public section

noncomputable section

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Ambient-valued affine orthogonal projection. -/
def affineProjection (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (x : E) : E :=
  EuclideanGeometry.orthogonalProjection F x

lemma affineProjection_mem (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (x : E) : affineProjection F x ∈ F :=
  EuclideanGeometry.orthogonalProjection_mem x

lemma affineProjection_fix (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] {x : E} (hx : x ∈ F) :
    affineProjection F x = x := EuclideanGeometry.orthogonalProjection_eq_self_iff.mpr hx

lemma affineProjection_eq_shift (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (p : E) (hp : p ∈ F) (x : E) :
    affineProjection F x = p + F.direction.starProjection (x - p) := by
  simpa only [affineProjection, Submodule.coe_orthogonalProjectionOnto_apply,
    vsub_eq_sub, vadd_eq_add, add_comm] using
    EuclideanGeometry.orthogonalProjection_apply_mem F (p := x) hp

lemma affineProjection_short (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] : Short (affineProjection F) := by
  let p : F := Classical.choice inferInstance
  intro x y
  rw [affineProjection_eq_shift F p p.property x,
    affineProjection_eq_shift F p p.property y, dist_add_left]
  simpa only [NNReal.coe_one, one_mul, dist_sub_right] using
    F.direction.lipschitzWith_starProjection.dist_le_mul (x - p) (y - p)

lemma affineProjection_nested {F G : AffineSubspace ℝ E} [Nonempty F] [Nonempty G]
    [F.direction.HasOrthogonalProjection] [G.direction.HasOrthogonalProjection]
    (hFG : F ≤ G) (x : E) : affineProjection F (affineProjection G x) = affineProjection F x :=
  congrArg (fun y : F => (y : E)) (affine_projection_nested hFG x)

/-- Affine normal flattening, with cut-off radius evaluated at the projected
point of the face. -/
def affineNormalFlatten (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (α : ℝ) (R : E → ℝ) (x : E) : E :=
  affineProjection F x + radialFlatten α (R (affineProjection F x)) (x - affineProjection F x)

lemma affineNormalFlatten_eq_shift (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (p : E) (hp : p ∈ F)
    (α : ℝ) (R : E → ℝ) (x : E) :
    affineNormalFlatten F α R x =
      p + taperedNormalFlatten F.direction α (fun z => R (p + z)) (x - p) := by
  have hres : x - (p + F.direction.starProjection (x - p)) =
      (x - p) - F.direction.starProjection (x - p) := by abel
  rw [affineNormalFlatten, affineProjection_eq_shift F p hp x, hres]
  dsimp only [taperedNormalFlatten, normalFlatten]
  abel

lemma affineNormalFlatten_projection (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (α : ℝ) (R : E → ℝ) (x : E) :
    affineProjection F (affineNormalFlatten F α R x) = affineProjection F x := by
  apply EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mpr
  refine ⟨affineProjection_mem F x, ?_⟩
  have heq : affineNormalFlatten F α R x - affineProjection F x =
      radialFlatten α (R (affineProjection F x)) (x - affineProjection F x) := by
    dsimp only [affineNormalFlatten]
    abel
  change affineNormalFlatten F α R x - affineProjection F x ∈ F.directionᗮ
  rw [heq, radialFlatten]
  exact F.directionᗮ.smul_mem _
    (EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal F x)

lemma affineNormalFlatten_nested_projection {J F : AffineSubspace ℝ E}
    [Nonempty J] [Nonempty F]
    [J.direction.HasOrthogonalProjection] [F.direction.HasOrthogonalProjection]
    (hJF : J ≤ F) (α : ℝ) (R : E → ℝ) (x : E) :
    affineProjection J (affineNormalFlatten F α R x) = affineProjection J x := by
  calc
    _ = affineProjection J (affineProjection F (affineNormalFlatten F α R x)) :=
      (affineProjection_nested hJF _).symm
    _ = affineProjection J (affineProjection F x) := by
      rw [affineNormalFlatten_projection]
    _ = _ := affineProjection_nested hJF x

lemma affineNormalFlatten_inner (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] {α : ℝ} (hα1 : α < 1)
    (R : E → ℝ) {x : E}
    (hin : ‖x - affineProjection F x‖ ≤ α * R (affineProjection F x)) :
    affineNormalFlatten F α R x = affineProjection F x := by
  rw [affineNormalFlatten, radialFlatten_inner hα1 hin, add_zero]

lemma affineNormalFlatten_outer (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (R : E → ℝ) {x : E}
    (hout : R (affineProjection F x) ≤ ‖x - affineProjection F x‖) :
    affineNormalFlatten F α R x = x := by
  rw [affineNormalFlatten, radialFlatten_outer hα0 hα1 hout]
  abel

lemma affineNormalFlatten_displacement (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (R : E → ℝ) (hR : ∀ z ∈ F, 0 ≤ R z) (x : E) :
    dist (affineNormalFlatten F α R x) x ≤ α * R (affineProjection F x) := by
  have hx : x = affineProjection F x + (x - affineProjection F x) := by abel
  calc
    dist (affineNormalFlatten F α R x) x =
        dist (affineNormalFlatten F α R x)
          (affineProjection F x + (x - affineProjection F x)) :=
      congrArg (dist (affineNormalFlatten F α R x)) hx
    _ = dist (radialFlatten α (R (affineProjection F x)) (x - affineProjection F x))
        (x - affineProjection F x) := by simp only [affineNormalFlatten, dist_add_left]
    _ ≤ α * R (affineProjection F x) :=
      radialFlatten_displacement hα0 hα1 (hR _ (affineProjection_mem F x)) _

lemma affineNormalFlatten_mem_convex (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (α : ℝ) (R : E → ℝ)
    {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C)
    (hPx : affineProjection F x ∈ C) : affineNormalFlatten F α R x ∈ C := by
  let v := x - affineProjection F x
  let c := radialProfile α (R (affineProjection F x)) ‖v‖ / ‖v‖
  have hc0 : 0 ≤ c := radial_coefficient_nonneg α _ v
  have hc1 : c ≤ 1 := radial_coefficient_le_one α _ v
  have hmem : (1 - c) • affineProjection F x + c • x ∈ C :=
    hC hPx hx (by linarith) hc0 (by ring)
  have heq : affineNormalFlatten F α R x = (1 - c) • affineProjection F x + c • x := by
    simp only [affineNormalFlatten, radialFlatten, c, v, sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  exact hmem

/-- The collapse does not increase distance to any point of the affine face.
Thus it also preserves every fixed-radius collar around a subset of the face. -/
lemma affineNormalFlatten_dist_to_mem (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (α : ℝ) (R : E → ℝ) (x : E)
    {p : E} (hp : p ∈ F) : dist (affineNormalFlatten F α R x) p ≤ dist x p := by
  have hPx : affineProjection F x ∈ Metric.closedBall p (dist x p) := by
    have h := affineProjection_short F x p
    rw [affineProjection_fix F hp] at h
    exact h
  exact affineNormalFlatten_mem_convex F α R (convex_closedBall p (dist x p))
    (Metric.mem_closedBall.mpr le_rfl) hPx

/-- Nearest projections to complete convex subfaces are preserved exactly. -/
lemma convexProjection_affineNormalFlatten
    (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C) (hconvex : Convex ℝ C)
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    (hCF : C ⊆ F) (α : ℝ) (R : E → ℝ) (x : E) :
    convexProjection C hne hcomplete hconvex (affineNormalFlatten F α R x) =
      convexProjection C hne hcomplete hconvex x := by
  calc
    _ = convexProjection C hne hcomplete hconvex
        (affineProjection F (affineNormalFlatten F α R x)) :=
      (convexProjection_after_affine_projection C hne hcomplete hconvex F hCF _).symm
    _ = convexProjection C hne hcomplete hconvex (affineProjection F x) := by
      rw [affineNormalFlatten_projection]
    _ = _ := convexProjection_after_affine_projection C hne hcomplete hconvex F hCF x

/-- The open metric tube, expressed without an empty-set distance convention. -/
def openMetricTube (C : Set E) (r : ℝ) : Set E :=
  {x | ∃ p ∈ C, dist x p < r}

lemma affineNormalFlatten_mapsTo_tube
    (F : AffineSubspace ℝ E) [Nonempty F] [F.direction.HasOrthogonalProjection]
    {C : Set E} (hCF : C ⊆ F) (α : ℝ) (R : E → ℝ) (r : ℝ) :
    Set.MapsTo (affineNormalFlatten F α R) (openMetricTube C r) (openMetricTube C r) := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := hx
  exact ⟨p, hp, (affineNormalFlatten_dist_to_mem F α R x (hCF hp)).trans_lt hxp⟩

/-- An already flattened map remains unchanged in its whole old tube after
a normal collapse along a containing face. This is an equality of actual maps
on an actual metric neighborhood. -/
lemma flat_map_unchanged_on_tube
    {Y : Type*} (C : Set E) (hne : C.Nonempty) (hcomplete : IsComplete C)
    (hconvex : Convex ℝ C) (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] (hCF : C ⊆ F)
    (α : ℝ) (R : E → ℝ) (r : ℝ) (g : E → Y)
    (hg : ∀ x ∈ openMetricTube C r, g x = g (convexProjection C hne hcomplete hconvex x)) :
    ∀ x ∈ openMetricTube C r, g (affineNormalFlatten F α R x) = g x := by
  intro x hx
  have hQx := affineNormalFlatten_mapsTo_tube F hCF α R r hx
  calc
    g (affineNormalFlatten F α R x) =
        g (convexProjection C hne hcomplete hconvex (affineNormalFlatten F α R x)) :=
      hg _ hQx
    _ = g (convexProjection C hne hcomplete hconvex x) := by
      rw [convexProjection_affineNormalFlatten C hne hcomplete hconvex F hCF α R x]
    _ = g x := (hg x hx).symm

theorem affineNormalFlatten_lipschitz (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] {α c : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : E → ℝ) (hR : ∀ z ∈ F, 0 ≤ R z)
    (hRlip : ∀ z ∈ F, ∀ w ∈ F, |R z - R w| ≤ c * dist z w) (x y : E) :
    dist (affineNormalFlatten F α R x) (affineNormalFlatten F α R y) ≤
      ((1 + α * c) / (1 - α)) * dist x y := by
  let p : F := Classical.choice inferInstance
  have hmem (z : E) (hz : z ∈ F.direction) : (p : E) + z ∈ F := by
    simpa only [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction hz p.property
  have hshiftR : ∀ z ∈ F.direction, 0 ≤ R ((p : E) + z) :=
    fun z hz => hR _ (hmem z hz)
  have hshiftLip : ∀ z ∈ F.direction, ∀ w ∈ F.direction,
      |R ((p : E) + z) - R ((p : E) + w)| ≤ c * dist z w := by
    intro z hz w hw
    simpa only [dist_add_left] using hRlip _ (hmem z hz) _ (hmem w hw)
  rw [affineNormalFlatten_eq_shift F p p.property α R x,
    affineNormalFlatten_eq_shift F p p.property α R y, dist_add_left]
  simpa only [dist_sub_right] using
    taperedNormalFlatten_lipschitz F.direction hα0 hα1 hc
      (fun z => R ((p : E) + z)) hshiftR hshiftLip (x - p) (y - p)

theorem affineNormalFlatten_continuous (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] {α c : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : E → ℝ) (hR : ∀ z ∈ F, 0 ≤ R z)
    (hRlip : ∀ z ∈ F, ∀ w ∈ F, |R z - R w| ≤ c * dist z w) :
    Continuous (affineNormalFlatten F α R) := by
  have hconst : 0 ≤ (1 + α * c) / (1 - α) := by positivity
  exact (LipschitzWith.of_dist_le_mul (K := ⟨(1 + α * c) / (1 - α), hconst⟩)
    (affineNormalFlatten_lipschitz F hα0 hα1 hc R hR hRlip)).continuous

/-- Wherever the radius is positive on the face, the map equals orthogonal
projection on a genuine open neighborhood in the ambient space. -/
theorem affineNormalFlatten_local_collapse (F : AffineSubspace ℝ E) [Nonempty F]
    [F.direction.HasOrthogonalProjection] {α c : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hc : 0 ≤ c)
    (R : E → ℝ)
    (hRlip : ∀ z ∈ F, ∀ w ∈ F, |R z - R w| ≤ c * dist z w)
    {p : E} (hp : p ∈ F) (hpR : 0 < R p) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, affineNormalFlatten F α R x = affineProjection F x := by
  have hRcomp : LipschitzWith ⟨c, hc⟩ (fun x => R (affineProjection F x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    exact (hRlip _ (affineProjection_mem F x) _ (affineProjection_mem F y)).trans
      (mul_le_mul_of_nonneg_left (affineProjection_short F x y) hc)
  let U : Set E := {x | ‖x - affineProjection F x‖ < α * R (affineProjection F x)}
  refine ⟨U, ?_, ?_, ?_⟩
  · exact isOpen_lt (continuous_id.sub (affineProjection_short F).continuous).norm
      (continuous_const.mul hRcomp.continuous)
  · have hpos := mul_pos hα0 hpR
    simpa only [U, Set.mem_ofPred_eq, affineProjection_fix F hp, sub_self, norm_zero] using hpos
  · intro x hx
    exact affineNormalFlatten_inner F hα1 R hx.le

end BrehmApprox
