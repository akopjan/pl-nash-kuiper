module

public import BrehmApprox.PullingComplex
public import BrehmApprox.PolytopeVertices

/-!
# Triangulation of locally finite polytope families

Every polytope is triangulated using its extreme vertices and one ambient
vertex order. Common extreme faces receive compatible triangulations. The
result preserves local finiteness, including local finiteness relative to
an open chart domain.
-/

@[expose] public section
noncomputable section

open Set Classical

namespace BrehmApprox.Pulling

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

local instance pullingPolytopeFamilyLocalInstance1 : DecidableEq E := Classical.decEq E

def familyFaces (C : I → Set E) (hC : ∀ i, IsFinitePolytope (C i)) : Set (Finset E) :=
  {S | ∃ i, S ∈ faces (polytopeVertices (C i) (hC i))}

theorem family_face_independent (C : I → Set E) (hC : ∀ i, IsFinitePolytope (C i))
    {S : Finset E} (hS : S ∈ familyFaces C hC) : AffineIndependent ℝ ((↑) : S → E) := by
  obtain ⟨i, hi⟩ := hS
  exact face_independent hi

theorem family_face_downward (C : I → Set E) (hC : ∀ i, IsFinitePolytope (C i))
    {S T : Finset E} (hS : S ∈ familyFaces C hC) (hTS : T ⊆ S) :
    T ∈ familyFaces C hC := by
  obtain ⟨i, hi⟩ := hS
  exact ⟨i, face_downward hi hTS⟩

theorem family_face_subset_cell (C : I → Set E) (hC : ∀ i, IsFinitePolytope (C i))
    {S : Finset E} {i : I} (hS : S ∈ faces (polytopeVertices (C i) (hC i))) :
    convexHull ℝ (S : Set E) ⊆ C i := by
  rw [← convexHull_polytopeVertices (C i) (hC i)]
  exact convexHull_mono (Finset.coe_subset.mpr (face_subset hS))

theorem family_faces_cover (C : I → Set E) (hC : ∀ i, IsFinitePolytope (C i)) :
    (⋃ i, C i) = ⋃ S ∈ familyFaces C hC, convexHull ℝ (S : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [← convexHull_polytopeVertices (C i) (hC i), faces_cover] at hi
    obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hi
    exact Set.mem_iUnion₂.mpr ⟨S, ⟨i, hS⟩, hxS⟩
  · intro hx
    obtain ⟨S, ⟨i, hS⟩, hxS⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion.mpr ⟨i, family_face_subset_cell C hC hS hxS⟩

omit [LinearOrder E] in
theorem vertex_mem_of_face_intersection {C D : Set E}
    (hC : IsFinitePolytope C) (hD : IsFinitePolytope D)
    (hCD : _root_.IsExtreme ℝ C (C ∩ D))
    (hDC : _root_.IsExtreme ℝ D (C ∩ D)) {x : E}
    (hx : x ∈ polytopeVertices C hC) (hxD : x ∈ D) : x ∈ polytopeVertices D hD := by
  have hxe : x ∈ C.extremePoints ℝ := by
    change x ∈ (polytopeVertices C hC : Set E) at hx
    rwa [coe_polytopeVertices] at hx
  have hxinter : x ∈ (C ∩ D).extremePoints ℝ := by
    rw [hCD.extremePoints_eq]
    exact ⟨⟨extremePoints_subset hxe, hxD⟩, hxe⟩
  have hxde := hDC.extremePoints_subset_extremePoints hxinter
  change x ∈ (polytopeVertices D hD : Set E)
  rwa [coe_polytopeVertices]

theorem family_faces_intersection (C : I → Set E) (hC : ∀ i, IsFinitePolytope (C i))
    (hface : ∀ i j, _root_.IsExtreme ℝ (C i) (C i ∩ C j))
    {S T : Finset E} (hS : S ∈ familyFaces C hC) (hT : T ∈ familyFaces C hC) :
    convexHull ℝ (S : Set E) ∩ convexHull ℝ (T : Set E) = convexHull ℝ (S ∩ T : Set E) := by
  obtain ⟨i, hi⟩ := hS
  obtain ⟨j, hj⟩ := hT
  have hji : _root_.IsExtreme ℝ (C j) (C i ∩ C j) := by
    simpa only [Set.inter_comm] using hface j i
  apply faces_intersection_of_extreme (V := polytopeVertices (C i) (hC i))
    (W := polytopeVertices (C j) (hC j))
  · simpa only [convexHull_polytopeVertices] using hface i j
  · simpa only [convexHull_polytopeVertices] using hji
  · intro x hx hxj
    rw [convexHull_polytopeVertices] at hxj
    exact vertex_mem_of_face_intersection (hC i) (hC j) (hface i j) hji hx hxj
  · intro x hx hxi
    rw [convexHull_polytopeVertices] at hxi
    apply vertex_mem_of_face_intersection (hC j) (hC i) (hface j i) ?_ hx hxi
    simpa only [Set.inter_comm] using hface i j
  · exact hi
  · exact hj

/-- Local finiteness passes to the simplices, relative to any specified
domain. In particular the domain may be the open Klein ball. -/
theorem family_faces_locallyFinite_on (C : I → Set E) (hC : ∀ i, IsFinitePolytope (C i))
    (A : Set E) (hlocal : LocallyFinite (fun i => (Subtype.val : A → E) ⁻¹' C i)) :
    LocallyFinite (fun S : familyFaces C hC =>
      (Subtype.val : A → E) ⁻¹' convexHull ℝ (S.val : Set E)) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := hlocal x
  let J : Set I := {i | (((Subtype.val : A → E) ⁻¹' C i) ∩ U).Nonempty}
  let B : Set (Finset E) := ⋃ i ∈ J, (faces (polytopeVertices (C i) (hC i)) : Set (Finset E))
  have hB : B.Finite := hfin.biUnion (fun i _ => (faces (polytopeVertices (C i) (hC i))).finite_toSet)
  have hpre : {S : familyFaces C hC | S.val ∈ B}.Finite :=
    hB.preimage (Subtype.val_injective.injOn)
  refine ⟨U, hU, hpre.subset ?_⟩
  intro S hS
  obtain ⟨i, hi⟩ := S.property
  obtain ⟨y, hyS, hyU⟩ := hS
  have hiJ : i ∈ J := ⟨y, family_face_subset_cell C hC hi hyS, hyU⟩
  exact Set.mem_iUnion₂.mpr ⟨i, hiJ, hi⟩

theorem family_faces_locallyFinite (C : I → Set E) (hC : ∀ i, IsFinitePolytope (C i))
    (hlocal : LocallyFinite C) :
    LocallyFinite (fun S : familyFaces C hC => convexHull ℝ (S.val : Set E)) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := hlocal x
  let J : Set I := {i | (C i ∩ U).Nonempty}
  let B : Set (Finset E) := ⋃ i ∈ J, (faces (polytopeVertices (C i) (hC i)) : Set (Finset E))
  have hB : B.Finite := hfin.biUnion (fun i _ => (faces (polytopeVertices (C i) (hC i))).finite_toSet)
  have hpre : {S : familyFaces C hC | S.val ∈ B}.Finite :=
    hB.preimage (Subtype.val_injective.injOn)
  refine ⟨U, hU, hpre.subset ?_⟩
  intro S hS
  obtain ⟨i, hi⟩ := S.property
  obtain ⟨y, hyS, hyU⟩ := hS
  have hiJ : i ∈ J := ⟨y, family_face_subset_cell C hC hi hyS, hyU⟩
  exact Set.mem_iUnion₂.mpr ⟨i, hiJ, hi⟩

end BrehmApprox.Pulling
