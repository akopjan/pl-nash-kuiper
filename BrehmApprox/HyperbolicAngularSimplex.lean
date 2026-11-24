module

public import BrehmApprox.HyperbolicRadialFolding

/-!
# Nondegenerate angular simplices and exact changes of radial center

A Lorentz-independent hyperbolic simplex whose linear span excludes the
radial center projects to a linearly independent family of unit directions.
For a simplex on a bisector, the angular change of center extends to a real
orthogonal motion and matches every point of the simplex, not just vertices.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ}

/-- Radial projection preserves independence when the center does not belong
to the Lorentz span of the original vertices. -/
theorem linearIndependent_radialVector {ι : Type*} [Fintype ι]
    (a : HyperbolicSpace n) (v : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => lift (v i)))
    (ha : lift a ∉ Submodule.span ℝ (Set.range (fun i => lift (v i)))) :
    LinearIndependent ℝ (fun i => radialVector a (v i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let z : ℝ × EuclideanSpace ℝ (Fin n) := ∑ j, c j • lift (v j)
  let T : ℝ := ∑ j, c j * Real.cosh (dist a (v j))
  have hboost : Hyperboloid.boostLinear a.point z = (T, 0) := by
    apply Prod.ext
    · change (Hyperboloid.boostLinear a.point z).1 = T
      dsimp only [z, T]
      rw [map_sum]
      simp only [map_smul, boosted_lift_radial_decomposition,
        Prod.fst_sum, Prod.smul_fst, smul_eq_mul]
    · change (Hyperboloid.boostLinear a.point z).2 = 0
      dsimp only [z]
      rw [map_sum]
      simpa only [map_smul, boosted_lift_radial_decomposition, Prod.snd_sum, Prod.smul_snd,
        sinh_smul_radialDirection] using hc
  have hrep : z = T • lift a := by
    apply (Hyperboloid.boostLinearEquiv a.point).injective
    change Hyperboloid.boostLinear a.point z = Hyperboloid.boostLinear a.point (T • lift a)
    rw [hboost, map_smul, boostLinear_lift_self]
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero]
  have hmem : z ∈ Submodule.span ℝ (Set.range (fun j => lift (v j))) := by
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)))
  have hT : T = 0 := by
    by_contra hT
    apply ha
    rw [hrep] at hmem
    have h := (Submodule.span ℝ (Set.range (fun j => lift (v j)))).smul_mem T⁻¹ hmem
    simpa only [smul_smul, inv_mul_cancel₀ hT, one_smul] using h
  rw [hT, zero_smul] at hrep
  exact Fintype.linearIndependent_iff.mp hv c hrep i

theorem linearIndependent_radialDirection {ι : Type*} [Fintype ι]
    (a : HyperbolicSpace n) (v : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => lift (v i)))
    (ha : lift a ∉ Submodule.span ℝ (Set.range (fun i => lift (v i)))) :
    LinearIndependent ℝ (fun i => radialDirection a (v i)) := by
  have hne (i : ι) : a ≠ v i := by
    intro hi
    apply ha
    rw [hi]
    exact Submodule.subset_span (Set.mem_range_self i)
  let u : ι → ℝˣ := fun i => Units.mk0 (Real.sinh (dist a (v i)))⁻¹
    (inv_ne_zero (Real.sinh_pos_iff.mpr (dist_pos.mpr (hne i))).ne')
  have hvec : (fun i => radialDirection a (v i)) = u • (fun i => radialVector a (v i)) := rfl
  rw [hvec, LinearIndependent.units_smul_iff]
  exact linearIndependent_radialVector a v hv ha

lemma center_ne_point_of_bisector_cell (a b : HyperbolicSpace n) (hab : a ≠ b)
    (V : Finset (HyperbolicSpace n)) (hV : ∀ v ∈ V, dist a v = dist b v)
    {x : HyperbolicSpace n} (hx : x ∈ hyperbolicCell V) : a ≠ x := by
  obtain ⟨w, _, c, hc, hrep⟩ := hx
  have heq := equal_radii_of_barycentric_bisector a b x V w c hc.ne' hrep hV
  intro hax
  rw [← hax, dist_self] at heq
  exact hab.symm (dist_eq_zero.mp heq.symm)

/-- The exact change of radial center on an entire hyperbolic bisector
simplex. Its existence, global orthogonal extension, and all-point agreement
are conclusions, not gluing assumptions. -/
theorem exists_bisector_angular_congruence (a b : HyperbolicSpace n) (hab : a ≠ b)
    (V : Finset (HyperbolicSpace n))
    (hlin : LinearIndependent ℝ (fun v : V => lift (v : HyperbolicSpace n)))
    (hV : ∀ v ∈ V, dist a v = dist b v) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x ∈ hyperbolicCell V, U (radialDirection a x) = radialDirection b x := by
  classical
  have hspan : Set.range (fun v : V => lift (v : HyperbolicSpace n)) =
      lift '' (V : Set (HyperbolicSpace n)) := by
    ext z
    simp
  have ha : lift a ∉ Submodule.span ℝ (Set.range (fun v : V => lift (v : HyperbolicSpace n))) := by
    rw [hspan]
    exact center_not_mem_span_bisector_vertices a b hab V hV
  have hdir := linearIndependent_radialDirection a ((↑) : V → HyperbolicSpace n) hlin ha
  have hgram : ∀ v w : V, ⟪radialDirection a v, radialDirection a w⟫_ℝ =
      ⟪radialDirection b v, radialDirection b w⟫_ℝ := by
    intro v w
    exact radial_gram_eq_of_equal_radii a b v w
      (dist_pos.mpr (center_ne_point_of_bisector_cell a b hab V hV
        (mem_hyperbolicCell_of_mem v.property)))
      (dist_pos.mpr (center_ne_point_of_bisector_cell a b hab V hV
        (mem_hyperbolicCell_of_mem w.property)))
      (hV v v.property) (hV w w.property)
  obtain ⟨U, hU⟩ := BrehmApprox.exists_ambient_gram_isometry
    (fun v : V => radialDirection a v) (fun v : V => radialDirection b v) hdir hgram
  refine ⟨U, ?_⟩
  intro x hx
  have hax := dist_pos.mpr (center_ne_point_of_bisector_cell a b hab V hV hx)
  obtain ⟨w, _, c, hc, hrep⟩ := hx
  exact radial_direction_compatibility a b x V w c hc hax hrep hV U.toLinearMap
    (fun v hv => hU ⟨v, hv⟩)

end BrehmApprox.HyperbolicSpace
