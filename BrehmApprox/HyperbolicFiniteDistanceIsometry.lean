module

public import BrehmApprox.HyperbolicAngularSimplex
public import BrehmApprox.HyperbolicRadialFolding

/-!
# Hyperbolic motions determined by finite distances

A distance-preserving correspondence from the vertices of a genuine
hyperbolic simplex extends to an ambient hyperbolic isometry.
-/

@[expose] public section
noncomputable section

namespace BrehmApprox.HyperbolicSpace

variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem exists_vertex_motion (v w : ι → HyperbolicSpace n)
    (hv : LinearIndependent ℝ (fun i => lift (v i)))
    (hd : ∀ i j, dist (v i) (v j) = dist (w i) (w j)) :
    ∃ r : HyperbolicSpace n ≃ᵢ HyperbolicSpace n, ∀ i, r (v i) = w i := by
  classical
  by_cases hι : Nonempty ι
  · let i₀ : ι := Classical.choice hι
    let J := {i : ι // i ≠ i₀}
    let a : J → HyperbolicSpace n := fun i => v i.val
    let b : J → HyperbolicSpace n := fun i => w i.val
    have hind : LinearIndependent ℝ (fun i : J => lift (a i)) :=
      hv.comp (fun i : J => i.val) Subtype.val_injective
    have hspan : lift (v i₀) ∉ Submodule.span ℝ (Set.range (fun i : J => lift (a i))) := by
      apply fun h => hv.notMem_span i₀ ?_
      apply Submodule.span_mono ?_ h
      rintro _ ⟨i, rfl⟩
      exact ⟨i.val, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using i.property, rfl⟩
    have hrad := linearIndependent_radialVector (v i₀) a hind hspan
    obtain ⟨r, hr₀, hr⟩ := exists_radial_congruence (v i₀) (w i₀) a b hrad
      (fun i => hd i₀ i.val) (fun i j => hd i.val j.val)
    refine ⟨r, fun i => ?_⟩
    by_cases hi : i = i₀
    · simpa only [hi] using hr₀
    · exact hr ⟨i, hi⟩
  · let : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    exact ⟨IsometryEquiv.refl _, fun i => isEmptyElim i⟩

end BrehmApprox.HyperbolicSpace
