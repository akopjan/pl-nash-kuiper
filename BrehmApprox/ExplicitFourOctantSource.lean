module

public import BrehmApprox.ExplicitSphericalOctants
public import BrehmApprox.ExplicitBalancedFrame
public import BrehmApprox.CommonCenterCellMetric
public import BrehmApprox.SpherePolyhedronObstruction

/-!
# A concrete four-octant spherical source and its collapse

All points, cells and maps below are actual subsets and coordinate maps of
the round spheres. The source metric is the finite-cell chain metric;
the ambient spherical metric is used only to specify cell costs.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace ExplicitFourOctantSource

open GeodesicSphere ExplicitSphericalOctants

def northVector (v : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.sqrt (v 0 ^ 2 + v 3 ^ 2), v 1, v 2]

theorem northVector_norm_sq (v : EuclideanSpace ℝ (Fin 4)) :
    ‖northVector v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [northVector, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  ring

def northFold (x : GeodesicSphere 3) : GeodesicSphere 2 :=
  ⟨northVector x.val, by
    have h := northVector_norm_sq x.val
    rw [x.norm_val] at h
    nlinarith [norm_nonneg (northVector x.val)]⟩

lemma pair_cauchy (x y : EuclideanSpace ℝ (Fin 4)) :
    x 0 * y 0 + x 3 * y 3 ≤
      Real.sqrt (x 0 ^ 2 + x 3 ^ 2) * Real.sqrt (y 0 ^ 2 + y 3 ^ 2) := by
  let u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![x 0, x 3]
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![y 0, y 3]
  have h := real_inner_le_norm u v
  simpa only [u, v, PiLp.inner_apply, EuclideanSpace.norm_eq,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sq_abs, mul_comm] using h

theorem northVector_inner_le (x y : EuclideanSpace ℝ (Fin 4)) :
    inner ℝ x y ≤ inner ℝ (northVector x) (northVector y) := by
  have h := pair_cauchy x y
  simp only [PiLp.inner_apply, northVector, Fin.sum_univ_three, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, RCLike.inner_apply, conj_trivial]
  nlinarith

/-- Normalizing the two normal coordinates by their Euclidean norm is globally
short for the actual angular metrics. -/
theorem northFold_short : LipschitzWith 1 northFold := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (northFold x) (northFold y) ≤ (1 : ℝ) * dist x y
  rw [one_mul, dist_eq_arccos_inner, dist_eq_arccos_inner]
  exact Real.arccos_le_arccos (northVector_inner_le x.val y.val)

def signedVector (v : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![if v 0 < 0 then -Real.sqrt (v 0 ^ 2 + v 3 ^ 2)
    else Real.sqrt (v 0 ^ 2 + v 3 ^ 2), v 1, v 2]

theorem signedVector_norm_sq (v : EuclideanSpace ℝ (Fin 4)) :
    ‖signedVector v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := northVector_norm_sq v
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h ⊢
  simp only [signedVector, northVector, Fin.sum_univ_three, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h ⊢
  split_ifs <;> simpa only [neg_sq] using h

def signedFold (x : GeodesicSphere 3) : GeodesicSphere 2 :=
  ⟨signedVector x.val, by
    have h := signedVector_norm_sq x.val
    rw [x.norm_val] at h
    nlinarith [norm_nonneg (signedVector x.val)]⟩

theorem signedFold_eq_northFold {x : GeodesicSphere 3} (hx : 0 ≤ x.val 0) :
    signedFold x = northFold x := by
  apply GeodesicSphere.ext
  simp only [signedFold, signedVector, northFold, northVector, ite_eq_right (not_lt.mpr hx)]

lemma inclusion_coordinate (x : GeodesicSphere 2) (i : Fin 3) :
    (inclusion x).val i.castSucc = x.val i := by
  simp [inclusion, GeodesicSphere.map, linearInclusion,
    LinearIsometry.piLpExtendByZero, indexInclusion]
  exact (Fin.castSucc_injective 3).extend_apply x.val.ofLp 0 i

lemma inclusion_last_coordinate (x : GeodesicSphere 2) : (inclusion x).val 3 = 0 := by
  simpa only [extra, coordinatePole_val, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial] using inner_inclusion_extra x

/-- On the actual embedded equatorial sphere the signed fold is exactly its
inverse, so its restriction there is an isometry. -/
theorem signedFold_inclusion (x : GeodesicSphere 2) : signedFold (inclusion x) = x := by
  apply GeodesicSphere.ext
  ext i
  fin_cases i
  · change (if (inclusion x).val 0 < 0 then
        -Real.sqrt ((inclusion x).val 0 ^ 2 + (inclusion x).val 3 ^ 2)
      else Real.sqrt ((inclusion x).val 0 ^ 2 + (inclusion x).val 3 ^ 2)) = x.val 0
    have h0 := inclusion_coordinate x 0
    change (inclusion x).val 0 = x.val 0 at h0
    rw [h0, inclusion_last_coordinate, zero_pow (by norm_num : 2 ≠ 0), add_zero,
      Real.sqrt_sq_eq_abs]
    split_ifs with h
    · rw [abs_of_neg h, neg_neg]
    · exact abs_of_nonneg (le_of_not_gt h)
  · exact inclusion_coordinate x 1
  · exact inclusion_coordinate x 2

def octant (v : ExplicitBalancedFrame.vertices) : Set (GeodesicSphere 3) := by
  classical
  exact BrehmApprox.sphericalCell {inclusion north, inclusion v.val, extra}

def sourceSet : Set (GeodesicSphere 3) :=
  Set.range inclusion ∪ ⋃ v : ExplicitBalancedFrame.vertices, octant v

structure Source where
  val : GeodesicSphere 3
  property : val ∈ sourceSet

@[ext] theorem Source.ext {x y : Source} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem val_injective : Function.Injective Source.val := fun _ _ => Source.ext

def sphereEmbedding (x : GeodesicSphere 2) : Source :=
  ⟨inclusion x, Or.inl (Set.mem_range_self x)⟩

def centre : Source := sphereEmbedding north

def cell : Option ExplicitBalancedFrame.vertices → Set Source
  | none => {x | x.val ∈ Set.range inclusion}
  | some v => {x | x.val ∈ octant v}

theorem cell_cover (x : Source) : ∃ i, x ∈ cell i := by
  rcases x.property with h | h
  · exact ⟨none, h⟩
  · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h
    exact ⟨some v, hv⟩

theorem centre_mem (i : Option ExplicitBalancedFrame.vertices) : centre ∈ cell i := by
  classical
  cases i with
  | none => exact Set.mem_range_self north
  | some v =>
    change inclusion north ∈ BrehmApprox.sphericalCell {inclusion north, inclusion v.val, extra}
    apply BrehmApprox.mem_sphericalCell_of_mem
    simp

def collapse (x : Source) : GeodesicSphere 2 := signedFold x.val

theorem collapse_sphere (x : GeodesicSphere 2) : collapse (sphereEmbedding x) = x :=
  signedFold_inclusion x

lemma inclusion_north_val : (inclusion north).val = EuclideanSpace.single (0 : Fin 4) (1 : ℝ) := by
  simp [inclusion, GeodesicSphere.map, north, coordinatePole_val, linearInclusion, indexInclusion]

lemma inner_nonneg_of_cell {n : ℕ} (p : GeodesicSphere n)
    (V : Finset (GeodesicSphere n)) (hV : ∀ v ∈ V, 0 ≤ inner ℝ p.val v.val)
    {x : GeodesicSphere n} (hx : x ∈ BrehmApprox.sphericalCell V) :
    0 ≤ inner ℝ p.val x.val := by
  obtain ⟨w, hw, A, hA, hrep⟩ := hx
  have hs := Finset.sum_nonneg (fun v hv => mul_nonneg (hw v hv) (hV v hv))
  have heq : (∑ v ∈ V, w v * inner ℝ p.val v.val) = A * inner ℝ p.val x.val := by
    calc
      _ = inner ℝ p.val (∑ v ∈ V, w v • v.val) := by simp only [inner_sum, inner_smul_right]
      _ = _ := by rw [hrep, inner_smul_right]
  rw [heq] at hs
  nlinarith

theorem octant_north_nonneg (v : ExplicitBalancedFrame.vertices)
    {x : GeodesicSphere 3} (hx : x ∈ octant v) : 0 ≤ x.val 0 := by
  classical
  have hv : inner ℝ (inclusion north).val (inclusion v.val).val = 0 := by
    rw [inclusion_val, inclusion_val, linearInclusion.inner_map_map, real_inner_comm]
    exact ExplicitBalancedFrame.orthogonal v.property
  have hV : ∀ z ∈ ({inclusion north, inclusion v.val, extra} : Finset (GeodesicSphere 3)),
      0 ≤ inner ℝ (inclusion north).val z.val := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · rw [inner_self_eq_one_of_norm_eq_one (inclusion north).norm_val]
      norm_num
    · rw [hv]
    · rw [inner_inclusion_extra]
  have h := inner_nonneg_of_cell (inclusion north) _ hV hx
  simpa only [inclusion_north_val, EuclideanSpace.inner_single_left,
    map_one, one_mul] using h

theorem collapse_cell_short (i : Option ExplicitBalancedFrame.vertices)
    (x : Source) (hx : x ∈ cell i) (y : Source) (hy : y ∈ cell i) :
    dist (collapse x) (collapse y) ≤ dist x.val y.val := by
  change dist (signedFold x.val) (signedFold y.val) ≤ dist x.val y.val
  cases i with
  | none =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    rw [← hu, ← hv, signedFold_inclusion, signedFold_inclusion, isometry_inclusion.dist_eq]
  | some v =>
    rw [signedFold_eq_northFold (octant_north_nonneg v hx),
      signedFold_eq_northFold (octant_north_nonneg v hy)]
    simpa only [NNReal.coe_one, one_mul] using northFold_short.dist_le_mul x.val y.val

theorem connected : BrehmApprox.ConnectedCellMetric.Connected cell :=
  BrehmApprox.ConnectedCellMetric.connected_of_common_center centre cell_cover centre_mem

/-- The source has only this intrinsic metric; there is no inherited subtype
metric on the dedicated `Source` type. -/
noncomputable instance sourceMetric : MetricSpace Source :=
  BrehmApprox.ConnectedCellMetric.metricSpace connected val_injective

theorem intrinsic : BrehmApprox.ChainGenerated cell :=
  BrehmApprox.ConnectedCellMetric.intrinsic connected val_injective

theorem ambient_short : LipschitzWith 1 Source.val :=
  BrehmApprox.ConnectedCellMetric.ambient_lipschitz connected val_injective

theorem cell_dist (i : Option ExplicitBalancedFrame.vertices)
    (x : Source) (hx : x ∈ cell i) (y : Source) (hy : y ∈ cell i) :
    dist x y = dist x.val y.val :=
  BrehmApprox.ConnectedCellMetric.on_cell connected i hx hy

theorem isometry_sphereEmbedding : Isometry sphereEmbedding :=
  BrehmApprox.ConnectedCellMetric.isometry_into_cell connected val_injective none sphereEmbedding
    (fun x => Set.mem_range_self x) isometry_inclusion

/-- The explicit map is globally short for the actual intrinsic source metric. -/
theorem collapse_short : LipschitzWith 1 collapse := by
  apply BrehmApprox.ConnectedCellMetric.lipschitzWith_of_cellwise connected val_injective
  intro i x hx y hy
  simpa only [NNReal.coe_one, one_mul] using collapse_cell_short i x hx y hy

lemma nonnegative_pair_mem_cell {n : ℕ} (V : Finset (GeodesicSphere n))
    {p d x : GeodesicSphere n} (hp : p ∈ V) (hd : d ∈ V)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrep : x.val = a • p.val + b • d.val) : x ∈ BrehmApprox.sphericalCell V := by
  classical
  refine ⟨fun v => (if v = p then a else 0) + (if v = d then b else 0), ?_, 1, zero_lt_one, ?_⟩
  · intro v _
    apply add_nonneg <;> split_ifs <;> positivity
  · rw [one_smul, hrep]
    simp [add_smul, Finset.sum_add_distrib, ite_smul, hp, hd]

theorem sharedEdge_mem_octant (v : ExplicitBalancedFrame.vertices)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : sharedEdge t ∈ octant v := by
  classical
  apply nonnegative_pair_mem_cell _
    (p := inclusion north) (d := extra) (by simp) (by simp)
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩)
    (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans (by linarith [Real.pi_pos])))
  rfl

def firstVertex : ExplicitBalancedFrame.vertices :=
  ⟨ExplicitBalancedFrame.first, by classical simp [ExplicitBalancedFrame.vertices]⟩

def edge (t : Set.Icc (0 : ℝ) (Real.pi / 2)) : Source :=
  ⟨sharedEdge t, Or.inr (Set.mem_iUnion.mpr ⟨firstVertex, sharedEdge_mem_octant firstVertex t.property⟩)⟩

theorem edge_mem (v : ExplicitBalancedFrame.vertices) (t : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    edge t ∈ cell (some v) := sharedEdge_mem_octant v t.property

theorem isometry_edge : Isometry edge := by
  apply BrehmApprox.ConnectedCellMetric.isometry_into_cell connected val_injective
    (some firstVertex) edge (edge_mem firstVertex)
  apply Isometry.of_dist_eq
  intro s t
  change dist (sharedEdge s.val) (sharedEdge t.val) = dist s.val t.val
  rw [sharedEdge_dist, Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [s.property.1, t.property.2, Real.pi_pos],
    by linarith [s.property.2, t.property.1, Real.pi_pos]⟩

theorem edge_anchor_distance (v : ExplicitBalancedFrame.vertices)
    (t : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    dist (edge t) (sphereEmbedding v.val) = Real.pi / 2 := by
  classical
  rw [cell_dist (some v) (edge t) (edge_mem v t) (sphereEmbedding v.val) (by
    apply BrehmApprox.mem_sphericalCell_of_mem
    simp [sphereEmbedding])]
  change dist (sharedEdge t.val) (inclusion v.val) = _
  rw [dist_comm]
  exact sharedEdge_anchor_distance v.val (ExplicitBalancedFrame.orthogonal v.property) t.val

/-- A fully concrete short map on a fully concrete intrinsic metric space
with no short finite piecewise-isometric approximation at error `pi/2`. -/
theorem no_piecewise_isometric_approximation :
    ¬ ∃ g : Source → GeodesicSphere 2, LipschitzWith 1 g ∧
      BrehmApprox.PolyhedralPiecewiseIsometry (BrehmApprox.sphericalPolytopeModel 2) g g ∧
      ∀ x, dist (g x) (collapse x) < Real.pi / 2 := by
  rintro ⟨g, hg, hPL, hclose⟩
  apply BrehmApprox.sphere_interval_obstruction sphereEmbedding isometry_sphereEmbedding
    (show (0 : ℝ) < Real.pi / 2 by positivity) edge isometry_edge
    ExplicitBalancedFrame.vertices ExplicitBalancedFrame.pole
    ExplicitBalancedFrame.balance ExplicitBalancedFrame.span ?_ hPL hg ?_
  · intro t v hv
    exact (edge_anchor_distance ⟨v, hv⟩ t).le
  · intro x
    simpa only [collapse_sphere] using hclose (sphereEmbedding x)

end ExplicitFourOctantSource
