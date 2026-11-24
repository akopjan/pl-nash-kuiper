module

public import BrehmApprox.CanonicalBadSets
public import BrehmApprox.ReferenceAgreement

/-!
# Constructing the Euclidean reference atlas from actual flat source maps

The face projections are the genuine nearest-point maps. Their local
commutation is derived from simplex barycentric coordinates and finite face
selection. Thus whole-face agreement is proved here, rather than assumed in
the final approximation theorem.
-/

@[expose] public section

noncomputable section

open scoped Topology
open Filter

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {P : Type*} [MetricSpace P]
variable {Good : (E → E) → Prop} {M : PolytopeModel E Good} {N : ℕ}

namespace FoldedGeometry

variable (G : FoldedGeometry (P := P) M N)
variable (T : SimplicialFaceData G.toPolyhedralFaceData)

def euclideanCoreProjection (i : Fin N) (hi : (G.core i).Nonempty) : E → G.core i :=
  (G.constantSource 0).convexCoreProjection i hi (T.convex_core i)

omit [FiniteDimensional ℝ E] in
lemma euclideanCoreProjection_short (i : Fin N) (hi : (G.core i).Nonempty) :
    LipschitzWith 1 (G.euclideanCoreProjection T i hi) :=
  (G.constantSource 0).convexCoreProjection_short i hi (T.convex_core i)

omit [FiniteDimensional ℝ E] in
lemma euclideanCoreProjection_fix (i : Fin N) (hi : (G.core i).Nonempty)
    {z : E} (hz : z ∈ G.core i) : (G.euclideanCoreProjection T i hi z : E) = z :=
  (G.constantSource 0).convexCoreProjection_fix i hi (T.convex_core i) hz

/-- Projection onto a simplex is locally compatible with projection onto a
positive subface, including at points on the boundary of the larger simplex. -/
theorem euclideanCoreProjection_eventually_comp
    {e i : Fin N} (hei : G.faceLE e i)
    (he : (G.core e).Nonempty) (hi : (G.core i).Nonempty)
    {p : E} (hp : PositiveConvexCombination (T.vertices e) p) :
    (fun z => (G.euclideanCoreProjection T e he
      (G.euclideanCoreProjection T i hi z) : E)) =ᶠ[𝓝 p]
      (fun z => (G.euclideanCoreProjection T e he z : E)) := by
  classical
  let I : Finset (Fin N) := Finset.univ.filter
    (fun j => G.faceLE j i ∧ (G.core j).Nonempty)
  let F : Fin N → AffineSubspace ℝ E := fun j => canonicalAffineFace (G.core j)
  have hpE : p ∈ G.core e := by rw [T.core_eq e]; exact hp.mem_convexHull
  have hpI : p ∈ G.core i := G.core_mono e i hei hpE
  have hcover : ∀ q ∈ G.core i, ∃ j ∈ I, RelativeInteriorIn (F j) (G.core j) q := by
    intro q hq
    obtain ⟨j, hji, _, hrel⟩ := T.core_relativeInterior_cover i hq
    have hj : (G.core j).Nonempty := ⟨q, relativeInteriorIn_mem hrel⟩
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, hj⟩, ?_⟩
    simpa only [F, canonicalAffineFace_eq hj] using hrel
  have havoid : ∀ j ∈ I, ¬ F e ≤ F j → p ∉ G.core j := by
    intro j hj hnot hpj
    obtain ⟨_, hji, hjne⟩ := Finset.mem_filter.mp hj
    have hej := T.faceLE_of_positive_point hei hji hp hpj
    apply hnot
    simp only [F, canonicalAffineFace_eq he, canonicalAffineFace_eq hjne]
    exact affineSpan_mono ℝ (G.core_mono e j hej)
  obtain ⟨U, hU, hpU, hcomm⟩ := convexProjection_locally_preserves_affine I G.core F
    (G.core i) hi (M.compact _ (G.polytope_core i)).isComplete (T.convex_core i)
    (fun j _ => (M.compact _ (G.polytope_core j)).isClosed)
    (fun j hj => G.core_mono j i (Finset.mem_filter.mp hj).2.1)
    hcover (F e) hpI havoid
  have hlocal : (fun z => affineProjection (F e)
      (convexProjection (G.core i) hi (M.compact _ (G.polytope_core i)).isComplete
        (T.convex_core i) z)) =ᶠ[𝓝 p] affineProjection (F e) :=
    Filter.Eventually.mono (hU.mem_nhds hpU) hcomm
  exact convexProjection_eventually_commutes (G.core e) he
    (M.compact _ (G.polytope_core e)).isComplete (T.convex_core e) (F e)
    (subset_canonicalAffineFace _) hlocal

/-- The source retraction corresponding to the actual model nearest map. -/
def euclideanRetraction (i : Fin N) (hi : (G.core i).Nonempty) : P → P :=
  (G.constantSource 0).retractFromCore i (G.euclideanCoreProjection T i hi)

def euclideanReference (i : Fin N) (f : P → E) : E → E := by
  classical
  exact if hi : (G.core i).Nonempty then
    (G.constantSource 0).referenceFromCore i (G.euclideanCoreProjection T i hi) f
  else fun _ => 0

omit [FiniteDimensional ℝ E] in
lemma euclideanReference_on_cell (i : Fin N) (f : P → E)
    {x : P} (hx : x ∈ G.cell i) : G.euclideanReference T i f (G.fold x) = f x := by
  classical
  have hi : (G.core i).Nonempty := ⟨G.fold x, G.fold_mem_core hx⟩
  simp only [euclideanReference, dite_eq_left hi]
  exact (G.constantSource 0).referenceFromCore_on_cell i (G.euclideanCoreProjection T i hi)
    (fun z hz => G.euclideanCoreProjection_fix T i hi hz) f hx

omit [FiniteDimensional ℝ E] in
theorem euclideanReference_lipschitz (i : Fin N) (f : P → E) {C : NNReal}
    (hf : LipschitzWith C f) : LipschitzWith C (G.euclideanReference T i f) := by
  classical
  by_cases hi : (G.core i).Nonempty
  · simp only [euclideanReference, dite_eq_left hi]
    simpa only [mul_one] using (G.constantSource 0).referenceFromCore_lipschitz i
      (G.euclideanCoreProjection T i hi) f hf (G.euclideanCoreProjection_short T i hi)
  · simp only [euclideanReference, dite_eq_right hi]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_self]
    positivity

/-- Local flatness at genuine minimal simplex points gives whole-face open
agreement of the explicit reference maps. -/
theorem euclideanReference_agreement (f : P → E)
    (hflat : ∀ e (he : (G.core e).Nonempty) p, p ∈ G.cell e →
      PositiveConvexCombination (T.vertices e) (G.fold p) →
      f =ᶠ[𝓝 p] (fun x => f (G.euclideanRetraction T e he x)))
    {i j : Fin N} (hij : G.faceLE i j) :
    ∃ U : Set E, IsOpen U ∧ G.core i ⊆ U ∧
      ∀ z ∈ U, G.euclideanReference T i f z = G.euclideanReference T j f z := by
  classical
  by_cases hi : (G.core i).Nonempty
  · have hj : (G.core j).Nonempty := hi.mono (G.core_mono i j hij)
    let S := G.constantSource 0
    let ri := G.euclideanCoreProjection T i hi
    let rj := G.euclideanCoreProjection T j hj
    obtain ⟨U, hU, hcoreU, hagree⟩ := S.whole_face_reference_agreement i j hij ri rj f
      (G.euclideanCoreProjection_short T i hi).continuous
      (G.euclideanCoreProjection_short T j hj).continuous
      (fun z hz => G.euclideanCoreProjection_fix T i hi hz)
      (fun z hz => G.euclideanCoreProjection_fix T j hj hz) (by
        intro p hp
        obtain ⟨k, hki, hpk, hpos, _, _⟩ := G.relativeInterior_face_cover T i hp
        have hk : (G.core k).Nonempty := ⟨G.fold p, G.fold_mem_core hpk⟩
        refine ⟨k, G.euclideanCoreProjection T k hk, hflat k hk p hpk hpos, ?_, ?_⟩
        · exact G.euclideanCoreProjection_eventually_comp T hki hk hi hpos
        · exact G.euclideanCoreProjection_eventually_comp T (G.le_trans _ _ _ hki hij) hk hj hpos)
    refine ⟨U, hU, hcoreU, ?_⟩
    intro z hz
    simpa only [euclideanReference, dite_eq_left hi, dite_eq_left hj] using hagree z hz
  · refine ⟨∅, isOpen_empty, ?_, fun _ hx => hx.elim⟩
    exact (Set.not_nonempty_iff_eq_empty.mp hi).le

/-- The actual Euclidean atlas. The only preparation hypothesis is local
flatness of the source map; its quantitative and global construction is handled
by the finite source-collapse theorem. -/
def euclideanLocalReferences (f : P → E) {C : NNReal} (hf : LipschitzWith C f)
    (hflat : ∀ e (he : (G.core e).Nonempty) p, p ∈ G.cell e →
      PositiveConvexCombination (T.vertices e) (G.fold p) →
      f =ᶠ[𝓝 p] (fun x => f (G.euclideanRetraction T e he x))) :
    G.toPolyhedralFaceData.LocalReferences (C : ℝ) where
  reference := fun i => G.euclideanReference T i f
  domain := fun _ => Set.univ
  open_domain := fun _ => isOpen_univ
  core_domain := fun _ => Set.subset_univ _
  reference_short := fun i x _ y _ => (G.euclideanReference_lipschitz T i f hf).dist_le_mul x y
  agreement := fun _ _ hij => G.euclideanReference_agreement T f hflat hij

end FoldedGeometry
end BrehmApprox
