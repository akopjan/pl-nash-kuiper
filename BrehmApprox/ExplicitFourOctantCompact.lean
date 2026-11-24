module

public import BrehmApprox.ExplicitFourOctantSource
public import BrehmApprox.SphericalCells

/-!
# Compactness of the actual four-octant intrinsic source

Compactness is proved for the intrinsic chain metric, by expressing the source
as the finite union of compact isometrically embedded round cells. No topology
is inherited from its embedding into the ambient three-sphere.
-/

@[expose] public section
noncomputable section

namespace ExplicitFourOctantSource

open GeodesicSphere ExplicitSphericalOctants BrehmApprox

local instance explicitFourOctantCompactLocalInstance1 {n : ℕ} : DecidableEq (GeodesicSphere n) := Classical.decEq _

theorem orthogonal_triple_inOpenHemisphere {n : ℕ} (a b c : GeodesicSphere n)
    (hab : inner ℝ a.val b.val = 0) (hac : inner ℝ a.val c.val = 0)
    (hbc : inner ℝ b.val c.val = 0) : InOpenHemisphere {a, b, c} := by
  classical
  let w := a.val + b.val + c.val
  have hba : inner ℝ b.val a.val = 0 := by rw [real_inner_comm, hab]
  have hca : inner ℝ c.val a.val = 0 := by rw [real_inner_comm, hac]
  have hcb : inner ℝ c.val b.val = 0 := by rw [real_inner_comm, hbc]
  have hwa : inner ℝ w a.val = 1 := by
    simp only [w, inner_add_left, hba, hca,
      inner_self_eq_one_of_norm_eq_one a.norm_val, add_zero]
  have hwb : inner ℝ w b.val = 1 := by
    simp only [w, inner_add_left, hab, hcb,
      inner_self_eq_one_of_norm_eq_one b.norm_val, zero_add, add_zero]
  have hwc : inner ℝ w c.val = 1 := by
    simp only [w, inner_add_left, hac, hbc,
      inner_self_eq_one_of_norm_eq_one c.norm_val, zero_add]
  have hw : w ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hwa
    norm_num at hwa
  refine ⟨normalizeVector w hw, ?_⟩
  intro v hv
  have hn : 0 < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;>
    simpa only [normalizeVector_val, NormedSpace.normalize, real_inner_smul_left,
      hwa, hwb, hwc, mul_one] using hn

theorem octant_inOpenHemisphere (v : ExplicitBalancedFrame.vertices) :
    InOpenHemisphere {inclusion north, inclusion v.val, extra} := by
  apply orthogonal_triple_inOpenHemisphere
  · rw [inclusion_val, inclusion_val, linearInclusion.inner_map_map, real_inner_comm]
    exact ExplicitBalancedFrame.orthogonal v.property
  · exact inner_inclusion_extra north
  · exact inner_inclusion_extra v.val

theorem isCompact_octant (v : ExplicitBalancedFrame.vertices) : IsCompact (octant v) :=
  isCompact_sphericalCell _ (octant_inOpenHemisphere v)

def octantEmbedding (v : ExplicitBalancedFrame.vertices) (x : octant v) : Source :=
  ⟨x.val, Or.inr (Set.mem_iUnion.mpr ⟨v, x.property⟩)⟩

theorem isometry_octantEmbedding (v : ExplicitBalancedFrame.vertices) :
    Isometry (octantEmbedding v) := by
  apply Isometry.of_dist_eq
  intro x y
  exact cell_dist (some v) (octantEmbedding v x) x.property
    (octantEmbedding v y) y.property

theorem range_octantEmbedding (v : ExplicitBalancedFrame.vertices) :
    Set.range (octantEmbedding v) = cell (some v) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    refine ⟨⟨x.val, hx⟩, ?_⟩
    apply Source.ext
    rfl

theorem range_sphereEmbedding : Set.range sphereEmbedding = cell none := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Set.mem_range_self y
  · rintro ⟨y, hy⟩
    refine ⟨y, Source.ext hy⟩

theorem isCompact_cell (i : Option ExplicitBalancedFrame.vertices) : IsCompact (cell i) := by
  cases i with
  | none =>
    rw [← range_sphereEmbedding]
    exact isCompact_range isometry_sphereEmbedding.continuous
  | some v =>
    let : CompactSpace (octant v) := (isCompact_iff_compactSpace).mp (isCompact_octant v)
    rw [← range_octantEmbedding v]
    exact isCompact_range (isometry_octantEmbedding v).continuous

/-- Compactness for the genuine intrinsic source metric. -/
instance compactSpaceSource : CompactSpace Source := by
  classical
  constructor
  have hcov : (Set.univ : Set Source) = ⋃ i, cell i := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact cell_cover x
  rw [hcov]
  exact isCompact_iUnion isCompact_cell

end ExplicitFourOctantSource
