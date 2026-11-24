module

public import Compatibility.Original
public import BrehmApprox.FiniteDistanceIsometry
public import BrehmApprox.ModelPointRigidity
public import BrehmApprox.HyperbolicFiniteDistanceIsometry

/-! Distance correspondences on arbitrary subsets of a model space extend
to ambient motions. Finite spanning subfamilies suffice; the subsets need
not themselves be simplices or convex. -/

@[expose] public section
noncomputable section

open scoped InnerProductSpace

namespace PLGeometry.SetRigidity

open Set BrehmApprox

theorem euclidean_point {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : Set V} {x y : V} (hx : x ∈ affineSpan ℝ S)
    (hd : ∀ v ∈ S, dist x v = dist y v) : x = y := by
  apply AffineSubspace.left_mem_perpBisector.mp
  apply (affineSpan_le.mpr ?_ : affineSpan ℝ S ≤ AffineSubspace.perpBisector x y) hx
  intro v hv
  exact AffineSubspace.mem_perpBisector_iff_dist_eq'.mpr (hd v hv)

theorem euclidean_motion {A V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (v w : A → V)
    (hd : ∀ a b, dist (v a) (v b) = dist (w a) (w b)) :
    ∃ r : V ≃ᵃⁱ[ℝ] V, ∀ a, r (v a) = w a := by
  classical
  obtain ⟨S, hS, hspan, hInd⟩ := exists_affineIndependent ℝ V (Set.range v)
  letI : Finite S := (finiteDimensional_iff_finite ℝ hInd).mp inferInstance
  letI : Fintype S := Fintype.ofFinite S
  let a : S → A := fun z => (hS z.property).choose
  have ha (z : S) : v (a z) = z.val := (hS z.property).choose_spec
  obtain ⟨r, hr⟩ := exists_ambient_distance_isometry
    (fun z : S => z.val) (fun z : S => w (a z)) hInd (by
      intro z t
      rw [← ha z, ← ha t]
      exact hd (a z) (a t))
  refine ⟨r, fun x => ?_⟩
  have hx : v x ∈ affineSpan ℝ S := by
    rw [hspan]
    exact subset_affineSpan ℝ _ (Set.mem_range_self x)
  have heq : v x = r.symm (w x) := euclidean_point hx (by
    intro z hz
    have ha' := ha ⟨z, hz⟩
    calc
      dist (v x) z = dist (v x) (v (a ⟨z, hz⟩)) := by rw [ha']
      _ = dist (w x) (w (a ⟨z, hz⟩)) := hd x _
      _ = dist (w x) (r z) := by rw [hr ⟨z, hz⟩]
      _ = dist (r.symm (w x)) z := by
        rw [← r.isometry.dist_eq (r.symm (w x)) z, r.apply_symm_apply])
  rw [heq, r.apply_symm_apply]

theorem spherical_point {n : ℕ} {I : Type*} (v : I → GeodesicSphere n)
    {x y : GeodesicSphere n}
    (hx : x.val ∈ Submodule.span ℝ (Set.range (fun i => (v i).val)))
    (hd : ∀ i, dist x (v i) = dist y (v i)) : x = y := by
  have hp : ∀ z ∈ Submodule.span ℝ (Set.range (fun i => (v i).val)),
      inner ℝ x.val z = inner ℝ y.val z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      rw [← GeodesicSphere.cos_dist, ← GeodesicSphere.cos_dist, hd i]
    | zero => simp
    | add z t hz ht ihz iht => simp only [inner_add_right, ihz, iht]
    | smul a z hz ih => simp only [inner_smul_right, ih]
  have h := hp x.val hx
  rw [inner_self_eq_one_of_norm_eq_one x.norm_val] at h
  apply GeodesicSphere.ext
  exact ((inner_eq_one_iff_of_norm_eq_one y.norm_val x.norm_val).mp h.symm).symm

theorem spherical_motion {A : Type*} {n : ℕ} (v w : A → GeodesicSphere n)
    (hd : ∀ a b, dist (v a) (v b) = dist (w a) (w b)) :
    ∃ r : E (n + 1) ≃ₗᵢ[ℝ] E (n + 1),
      ∀ a, GeodesicSphere.mapEquiv r (v a) = w a := by
  classical
  obtain ⟨I, a, _, hspan, hInd⟩ :=
    exists_linearIndependent' ℝ (fun x => (v x).val)
  letI : Finite I := hInd.finite
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨r, hr⟩ := exists_spherical_vertex_motion
    (fun i => v (a i)) (fun i => w (a i)) hInd (fun i j => hd (a i) (a j))
  let R := GeodesicSphere.mapEquiv r
  refine ⟨r, fun x => ?_⟩
  have hx : (v x).val ∈ Submodule.span ℝ (Set.range (fun i => (v (a i)).val)) := by
    rw [show (fun i => (v (a i)).val) = (fun x => (v x).val) ∘ a from rfl, hspan]
    exact Submodule.subset_span (Set.mem_range_self x)
  have heq : v x = R.symm (w x) := spherical_point (fun i => v (a i)) hx (by
    intro i
    calc
      dist (v x) (v (a i)) = dist (w x) (w (a i)) := hd x (a i)
      _ = dist (w x) (R (v (a i))) := by rw [show R (v (a i)) = w (a i) from hr i]
      _ = dist (R.symm (w x)) (v (a i)) := by
        rw [← R.dist_eq (R.symm (w x)) (v (a i)), R.apply_symm_apply])
  change R (v x) = w x
  rw [heq, R.apply_symm_apply]

theorem hyperbolic_point {n : ℕ} {I : Type*} (v : I → HyperbolicSpace n)
    {x y : HyperbolicSpace n}
    (hx : HyperbolicSpace.lift x ∈
      Submodule.span ℝ (Set.range (fun i => HyperbolicSpace.lift (v i))))
    (hd : ∀ i, dist x (v i) = dist y (v i)) : x = y := by
  let F : HyperbolicSpace n → (ℝ × E n) → ℝ :=
    fun a z => Hyperboloid.height a.point * z.1 - inner ℝ a.point z.2
  have hp : ∀ z ∈ Submodule.span ℝ (Set.range (fun i => HyperbolicSpace.lift (v i))),
      F x z = F y z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      change Hyperboloid.coshDist x.point (v i).point =
        Hyperboloid.coshDist y.point (v i).point
      rw [← HyperbolicSpace.cosh_dist, ← HyperbolicSpace.cosh_dist, hd i]
    | zero => simp [F]
    | add z t hz ht ihz iht =>
      have hadd (a : HyperbolicSpace n) : F a (z + t) = F a z + F a t := by
        simp only [F, Prod.fst_add, Prod.snd_add, mul_add, inner_add_right]
        ring
      rw [hadd, hadd, ihz, iht]
    | smul a z hz ih =>
      have hsmul (b : HyperbolicSpace n) : F b (a • z) = a * F b z := by
        simp only [F, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, inner_smul_right]
        ring
      rw [hsmul, hsmul, ih]
  have h := hp (HyperbolicSpace.lift x) hx
  change Hyperboloid.coshDist x.point x.point = Hyperboloid.coshDist y.point x.point at h
  rw [Hyperboloid.coshDist_self] at h
  exact HyperbolicSpace.ext (Hyperboloid.eq_of_coshDist_eq_one h.symm).symm

theorem hyperbolic_motion {A : Type*} {n : ℕ} (v w : A → HyperbolicSpace n)
    (hd : ∀ a b, dist (v a) (v b) = dist (w a) (w b)) :
    ∃ r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n, ∀ a, r (v a) = w a := by
  classical
  obtain ⟨I, a, _, hspan, hInd⟩ :=
    exists_linearIndependent' ℝ (fun x => HyperbolicSpace.lift (v x))
  letI : Finite I := hInd.finite
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨r, hr⟩ := HyperbolicSpace.exists_vertex_motion
    (fun i => v (a i)) (fun i => w (a i)) hInd (fun i j => hd (a i) (a j))
  refine ⟨r, fun x => ?_⟩
  have hx : HyperbolicSpace.lift (v x) ∈
      Submodule.span ℝ (Set.range (fun i => HyperbolicSpace.lift (v (a i)))) := by
    rw [show (fun i => HyperbolicSpace.lift (v (a i))) =
      (fun x => HyperbolicSpace.lift (v x)) ∘ a from rfl, hspan]
    exact Submodule.subset_span (Set.mem_range_self x)
  have heq : v x = r.symm (w x) := hyperbolic_point (fun i => v (a i)) hx (by
    intro i
    calc
      dist (v x) (v (a i)) = dist (w x) (w (a i)) := hd x (a i)
      _ = dist (w x) (r (v (a i))) := by rw [hr i]
      _ = dist (r.symm (w x)) (v (a i)) := by
        rw [← r.dist_eq (r.symm (w x)) (v (a i)), r.apply_symm_apply])
  rw [heq, r.apply_symm_apply]

end PLGeometry.SetRigidity
