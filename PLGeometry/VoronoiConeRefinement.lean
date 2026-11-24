module

public import PLGeometry.ProtectedVoronoiCones
public import PLGeometry.ProjectiveSimplicialRefinement
public import BrehmApprox.FacialConeComplex

/-!
# Compatible cones over arbitrary subdivisions of the tie bases

The base subdivision is allowed to be refined before coning. Its vertices
are actual source points. All sites become apex vertices, and the resulting
finite family is a genuine refinement of the original geodesic complex.
-/

@[expose] public section
noncomputable section

set_option maxHeartbeats 2000000

open Set Classical BrehmApprox

namespace ArchivePLGeometry

universe u v w

local instance voronoiConeRefinementDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    {T : FiniteChartedComplex κ n P}
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem FiniteChartedComplex.eq_of_site_mem_voronoiPiece {S σ : Finset P}
    (hσ : σ ∈ T.simplices) {a b : P} (hb : b ∈ S)
    (h : b ∈ T.voronoiPiece S σ a) : b = a := by
  have hd : dist (T.chart σ b) (T.chart σ a) = 0 := by
    apply le_antisymm _ dist_nonneg
    simpa only [dist_self] using h.2.2 b ⟨hb, h.1⟩
  exact T.chart_injectiveOn σ hσ h.1 h.2.1.2 (dist_eq_zero.mp hd)

/-- A compatible finite subdivision of every Voronoi tie polytope. -/
structure VoronoiBaseFamily (A : ProjectiveVoronoiAtlas T E) (S : Finset P) (J : Type w) where
  vertices : J → Finset P
  index : J → VoronoiAtlas.TieIndex (T := T) S
  independent : ∀ j, AffineIndependent ℝ ((↑) : (vertices j).image A.coord → E)
  subset_tie : ∀ j, convexHull ℝ ((vertices j).image A.coord : Set E) ⊆
    A.toVoronoiAtlas.tiePiece S (index j)
  intersection : ∀ i j,
    convexHull ℝ ((vertices i).image A.coord : Set E) ∩
      convexHull ℝ ((vertices j).image A.coord : Set E) =
      convexHull ℝ (((vertices i ∩ vertices j).image A.coord) : Set E)
  cover : ∀ i, ∀ z ∈ A.toVoronoiAtlas.tiePiece S i,
    ∃ j, index j = i ∧ z ∈ convexHull ℝ ((vertices j).image A.coord : Set E)

namespace VoronoiBaseFamily

variable {A : ProjectiveVoronoiAtlas T E} {S : Finset P} {J : Type w}
    (B : VoronoiBaseFamily A S J)

def apex (j : J) : P := (B.index j).val.2.1.val

def oldSimplex (j : J) : Finset P := (B.index j).val.1.val

def coordinateBase (j : J) : Finset E := (B.vertices j).image A.coord

def ambientPiece (j : J) : Set E := A.coord '' T.voronoiPiece S (B.oldSimplex j) (B.apex j)

theorem oldSimplex_mem (j : J) : B.oldSimplex j ∈ T.simplices := (B.index j).val.1.property

theorem apex_mem_sites (j : J) : B.apex j ∈ S := (B.index j).val.2.1.property

theorem apex_mem_old (j : J) : B.apex j ∈ T.cell (B.oldSimplex j) := (B.index j).property.2.1

theorem apex_mem_piece (j : J) : A.coord (B.apex j) ∈ B.ambientPiece j := by
  refine ⟨B.apex j, ⟨B.apex_mem_old j, ⟨B.apex_mem_sites j, B.apex_mem_old j⟩, ?_⟩, rfl⟩
  intro b hb
  simp only [dist_self]
  exact dist_nonneg

theorem ambientPiece_polytope (j : J) : IsFinitePolytope (B.ambientPiece j) :=
  A.toVoronoiAtlas.voronoiPiece_polytope S (B.oldSimplex_mem j) (B.apex j)

theorem ambientPiece_face_inter {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (i j : J) :
    _root_.IsExtreme ℝ (B.ambientPiece i) (B.ambientPiece i ∩ B.ambientPiece j) :=
  A.toVoronoiAtlas.voronoiPiece_face_inter hnet hp (B.oldSimplex_mem i) (B.oldSimplex_mem j)
    (B.apex i) (B.apex j)

theorem tie_extreme {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (j : J) :
    _root_.IsExtreme ℝ (B.ambientPiece j) (A.toVoronoiAtlas.tiePiece S (B.index j)) :=
  A.toVoronoiAtlas.voronoiPiece_face_inter hnet hp (B.oldSimplex_mem j) (B.oldSimplex_mem j)
    (B.apex j) (B.index j).val.2.2.val

theorem base_subset_piece (j : J) : convexHull ℝ (B.coordinateBase j : Set E) ⊆ B.ambientPiece j :=
  fun _ hz => (B.subset_tie j hz).1

theorem vertex_mem_piece (j : J) {v : P} (hv : v ∈ B.vertices j) :
    v ∈ T.voronoiPiece S (B.oldSimplex j) (B.apex j) := by
  obtain ⟨x, hx, he⟩ := B.base_subset_piece j
    (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  exact (A.injective he) ▸ hx

theorem site_notMem_tie (i : VoronoiAtlas.TieIndex (T := T) S) {b : P} (hb : b ∈ S) :
    A.coord b ∉ A.toVoronoiAtlas.tiePiece S i := by
  intro hm
  obtain ⟨x, hx, hxa, hxb⟩ := A.toVoronoiAtlas.tiePiece_source S i hm
  have hxb' : x = b := A.injective hx
  subst x
  have he₁ := T.eq_of_site_mem_voronoiPiece i.val.1.property hb hxa
  have he₂ := T.eq_of_site_mem_voronoiPiece i.val.1.property hb hxb
  exact i.property.1 (he₁.symm.trans he₂)

theorem site_notMem_base (j : J) {b : P} (hb : b ∈ S) : b ∉ B.vertices j := by
  intro hm
  exact site_notMem_tie (A := A) (B.index j) hb (B.subset_tie j
    (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨b, hm, rfl⟩)))

theorem apex_notMem_tie (j : J) : A.coord (B.apex j) ∉ A.toVoronoiAtlas.tiePiece S (B.index j) :=
  site_notMem_tie (A := A) (B.index j) (B.apex_mem_sites j)

theorem other_site_notMem_piece (j : J) {b : P} (hb : b ∈ S) (hba : b ≠ B.apex j) :
    A.coord b ∉ B.ambientPiece j := by
  rintro ⟨x, hx, he⟩
  have hxb := A.injective he
  subst x
  exact hba (T.eq_of_site_mem_voronoiPiece (B.oldSimplex_mem j) hb hx)

def coneVertices (j : J) : Finset P := insert (B.apex j) (B.vertices j)

theorem coordinate_cone (j : J) :
    (B.coneVertices j).image A.coord = insert (A.coord (B.apex j)) (B.coordinateBase j) := by
  simp only [coneVertices, coordinateBase, Finset.image_insert]

theorem cone_vertices_mem_old (j : J) : (B.coneVertices j : Set P) ⊆ T.cell (B.oldSimplex j) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact B.apex_mem_old j
  · exact (B.vertex_mem_piece j hx).1

theorem cone_hull_subset_piece (j : J) :
    convexHull ℝ ((B.coneVertices j).image A.coord : Set E) ⊆ B.ambientPiece j := by
  rw [B.coordinate_cone j]
  apply convexHull_min _ (B.ambientPiece_polytope j).convex
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact B.apex_mem_piece j
  · exact B.base_subset_piece j (subset_convexHull ℝ _ hz)

theorem cone_independent (j : J) :
    AffineIndependent ℝ ((↑) : (B.coneVertices j).image A.coord → E) := by
  rw [B.coordinate_cone j]
  obtain ⟨L, c, hc⟩ := A.distanceCut (B.oldSimplex j) (B.oldSimplex_mem j)
    (B.apex j) (B.apex_mem_old j) (B.index j).val.2.2.val (B.index j).property.2.2
  apply affineIndependent_cone_of_affine_cut (B.independent j) L c
  · intro v hv
    obtain ⟨x, hx, hxa, hxb⟩ := A.toVoronoiAtlas.tiePiece_source S (B.index j)
      (B.subset_tie j (subset_convexHull ℝ _ hv))
    rw [← hx]
    exact (hc x hxa.1).2.mp (le_antisymm
      (hxa.2.2 _ hxb.2.1) (hxb.2.2 _ hxa.2.1))
  · intro he
    have hd := (hc (B.apex j) (B.apex_mem_old j)).2.mpr he
    have hh : T.chart (B.oldSimplex j) (B.apex j) =
        T.chart (B.oldSimplex j) (B.index j).val.2.2.val := by
      apply dist_eq_zero.mp
      rw [← hd, dist_self]
    exact (B.index j).property.1 (T.chart_injectiveOn _ (B.oldSimplex_mem j)
      (B.apex_mem_old j) (B.index j).property.2.2 hh)

theorem coordinate_base_intersection (i j : J) :
    convexHull ℝ (B.coordinateBase i : Set E) ∩ convexHull ℝ (B.coordinateBase j : Set E) =
      convexHull ℝ ((B.coordinateBase i ∩ B.coordinateBase j : Finset E) : Set E) := by
  have hh := B.intersection i j
  rw [Finset.image_inter _ _ A.injective] at hh
  exact hh

theorem cone_intersection {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (i j : J) :
    convexHull ℝ ((B.coneVertices i).image A.coord : Set E) ∩
      convexHull ℝ ((B.coneVertices j).image A.coord : Set E) =
      convexHull ℝ (((B.coneVertices i ∩ B.coneVertices j).image A.coord) : Set E) := by
  rw [Finset.image_inter _ _ A.injective, B.coordinate_cone i, B.coordinate_cone j]
  by_cases hij : B.apex i = B.apex j
  · have hh := same_apex_cones_intersection
      (B.ambientPiece_polytope i).convex (B.ambientPiece_polytope j).convex
      (B.ambientPiece_face_inter hnet hp i j) (B.ambientPiece_face_inter hnet hp j i)
      (B.tie_extreme hnet hp i) (B.tie_extreme hnet hp j)
      (B.apex_mem_piece i) (show A.coord (B.apex i) ∈ B.ambientPiece j by rw [hij]; exact B.apex_mem_piece j)
      (B.apex_notMem_tie i) (show A.coord (B.apex i) ∉ A.toVoronoiAtlas.tiePiece S (B.index j) by
        rw [hij]; exact B.apex_notMem_tie j)
      (B.coordinateBase i) (B.coordinateBase j) (B.subset_tie i) (B.subset_tie j)
      (B.coordinate_base_intersection i j)
    rw [← hij]
    rw [← Finset.insert_inter_distrib]
    exact hh
  · have hh := different_apex_cones_intersection
      (B.ambientPiece_polytope i).convex (B.ambientPiece_polytope j).convex
      (B.ambientPiece_face_inter hnet hp i j) (B.ambientPiece_face_inter hnet hp j i)
      (B.apex_mem_piece i) (B.apex_mem_piece j)
      (B.other_site_notMem_piece j (B.apex_mem_sites i) hij)
      (B.other_site_notMem_piece i (B.apex_mem_sites j) (Ne.symm hij))
      (B.coordinateBase i) (B.coordinateBase j)
      (fun _ hz => B.base_subset_piece i (subset_convexHull ℝ _ hz))
      (fun _ hz => B.base_subset_piece j (subset_convexHull ℝ _ hz))
      (B.coordinate_base_intersection i j)
    have hcross : insert (A.coord (B.apex i)) (B.coordinateBase i) ∩
        insert (A.coord (B.apex j)) (B.coordinateBase j) =
        B.coordinateBase i ∩ B.coordinateBase j := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hz₁ | hz₁, hz₂ | hz₂⟩
        · exact (hij (A.injective (hz₁.symm.trans hz₂))).elim
        · subst z
          exact (B.other_site_notMem_piece j (B.apex_mem_sites i) hij
            (B.base_subset_piece j (subset_convexHull ℝ _ hz₂))).elim
        · subst z
          exact (B.other_site_notMem_piece i (B.apex_mem_sites j) (Ne.symm hij)
            (B.base_subset_piece i (subset_convexHull ℝ _ hz₁))).elim
        · exact ⟨hz₁, hz₂⟩
      · exact fun h => ⟨Or.inr h.1, Or.inr h.2⟩
    rw [hcross]
    exact hh

theorem cone_site_intersection (j : J) {b : P} (hb : b ∈ S) :
    convexHull ℝ ((B.coneVertices j).image A.coord : Set E) ∩
      convexHull ℝ (({b} : Finset P).image A.coord : Set E) =
      convexHull ℝ (((B.coneVertices j ∩ {b}).image A.coord) : Set E) := by
  by_cases hm : b ∈ B.coneVertices j
  · rw [Finset.inter_singleton_of_mem hm]
    apply Set.inter_eq_right.mpr
    exact convexHull_mono (Finset.coe_subset.mpr
      (Finset.image_subset_image (Finset.singleton_subset_iff.mpr hm)))
  · rw [Finset.inter_singleton_of_notMem hm]
    simp only [Finset.image_empty, Finset.coe_empty, convexHull_empty,
      Finset.image_singleton, Finset.coe_singleton, convexHull_singleton]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hz'⟩
    have hzb : z = A.coord b := hz'
    subst z
    obtain ⟨x, hx, he⟩ := B.cone_hull_subset_piece j hz
    have hxb := A.injective he
    subst x
    have hba := T.eq_of_site_mem_voronoiPiece (B.oldSimplex_mem j) hb hx
    apply hm
    rw [hba]
    exact Finset.mem_insert_self _ _

private theorem singleton_intersection (a b : P) :
    convexHull ℝ (({a} : Finset P).image A.coord : Set E) ∩
      convexHull ℝ (({b} : Finset P).image A.coord : Set E) =
      convexHull ℝ (((({a} : Finset P) ∩ {b}).image A.coord) : Set E) := by
  by_cases hab : a = b
  · subst b
    simp only [Finset.inter_self, Set.inter_self]
  · have hi : ({a} : Finset P) ∩ {b} = ∅ := by
      exact Finset.singleton_inter_of_notMem (by simpa using hab)
    rw [hi]
    simp only [Finset.image_empty, Finset.coe_empty, convexHull_empty,
      Finset.image_singleton, Finset.coe_singleton, convexHull_singleton]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz₁, hz₂⟩
    exact hab (A.injective ((show z = A.coord a from hz₁).symm.trans hz₂))

def allVertices : J ⊕ S → Finset P
  | .inl j => B.coneVertices j
  | .inr a => {a.val}

theorem all_independent (i : J ⊕ S) :
    AffineIndependent ℝ ((↑) : (B.allVertices i).image A.coord → E) := by
  rcases i with j | a
  · exact B.cone_independent j
  · change AffineIndependent ℝ ((↑) : ({a.val} : Finset P).image A.coord → E)
    rw [Finset.image_singleton]
    exact affineIndependent_of_subsingleton ℝ _

theorem all_intersection {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S) (i j : J ⊕ S) :
    convexHull ℝ ((B.allVertices i).image A.coord : Set E) ∩
      convexHull ℝ ((B.allVertices j).image A.coord : Set E) =
      convexHull ℝ (((B.allVertices i ∩ B.allVertices j).image A.coord) : Set E) := by
  rcases i with i | a <;> rcases j with j | b
  · exact B.cone_intersection hnet hp i j
  · exact B.cone_site_intersection i b.property
  · change convexHull ℝ (({a.val} : Finset P).image A.coord : Set E) ∩
      convexHull ℝ ((B.coneVertices j).image A.coord : Set E) = _
    rw [Set.inter_comm, Finset.inter_comm]
    exact B.cone_site_intersection j a.property
  · exact singleton_intersection a.val b.val

theorem all_oldCell (i : J ⊕ S) :
    ∃ σ ∈ T.simplices, (B.allVertices i : Set P) ⊆ T.cell σ := by
  rcases i with j | a
  · exact ⟨B.oldSimplex j, B.oldSimplex_mem j, B.cone_vertices_mem_old j⟩
  · obtain ⟨σ, hσ, ha⟩ := T.cover a.val
    exact ⟨σ, hσ, fun x hx => (Finset.mem_singleton.mp hx) ▸ ha⟩

/-- Coning a compatible tie subdivision gives a source simplex family. -/
def coneSimplexFamily {η : ℝ} (hnet : T.IsCellwiseNet S η)
    (hp : T.IsCellwiseProtected S)
    (hcover : ∀ x : P, x ∈ S ∨ ∃ j,
      A.coord x ∈ convexHull ℝ ((B.coneVertices j).image A.coord : Set E)) :
    ProjectiveSimplexFamily A (J ⊕ S) where
  vertices := B.allVertices
  independent := B.all_independent
  cover x := by
    rcases hcover x with hx | ⟨j, hj⟩
    · refine ⟨.inr ⟨x, hx⟩, ?_⟩
      exact subset_convexHull ℝ _ (by simp [allVertices])
    · exact ⟨.inl j, hj⟩
  intersection := B.all_intersection hnet hp
  oldCell := B.all_oldCell

end VoronoiBaseFamily

namespace FiniteChartedComplex

variable (T : FiniteChartedComplex κ n P) {S : Finset P} {J : Type w}

local instance voronoiConeCoordinatesEq : DecidableEq (T.Vertex → ℝ) := Classical.decEq _

theorem voronoi_cone_cover
    (B : VoronoiBaseFamily T.barycentricProjectiveAtlas S J)
    {η : ℝ} (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S) (x : P) :
    x ∈ S ∨ ∃ j, T.barycentricCoords x ∈
      convexHull ℝ ((B.coneVertices j).image T.barycentricCoords : Set (T.Vertex → ℝ)) := by
  obtain ⟨σ, hσ, hxσ⟩ := T.cover x
  obtain ⟨a, ha⟩ := T.exists_nearestInCell hnet hσ hxσ
  by_cases hxa : x = a
  · exact Or.inl (hxa ▸ ha.1.1)
  · right
    obtain ⟨b, hb, hba, hbσ, y, hya, hyb, hxseg⟩ :=
      T.exists_voronoi_tie_radial_endpoint hp hσ ⟨hxσ, ha⟩ hxa
    let i : VoronoiAtlas.TieIndex (T := T) S :=
      ⟨(⟨σ, hσ⟩, ⟨a, ha.1.1⟩, ⟨b, hb⟩), hba.symm, ha.1.2, hbσ⟩
    have hyi : T.barycentricCoords y ∈ T.barycentricProjectiveAtlas.toVoronoiAtlas.tiePiece S i :=
      ⟨⟨y, hya, rfl⟩, ⟨y, hyb, rfl⟩⟩
    obtain ⟨j, hji, hyj⟩ := B.cover i _ hyi
    have hja : B.apex j = a := by simp only [VoronoiBaseFamily.apex, hji, i]
    refine ⟨j, ?_⟩
    apply (convex_convexHull ℝ ((B.coneVertices j).image T.barycentricCoords :
      Set (T.Vertex → ℝ))).segment_subset ?_ ?_ hxseg
    · apply subset_convexHull ℝ _
      exact Finset.mem_image.mpr ⟨B.apex j, Finset.mem_insert_self _ _, congrArg T.barycentricCoords hja⟩
    · exact convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image
        (Finset.subset_insert _ _))) hyj

/-- The canonical source coordinates turn every compatible tie subdivision
into an actual finite geodesic refinement. -/
def voronoiConeFamily (B : VoronoiBaseFamily T.barycentricProjectiveAtlas S J)
    {η : ℝ} (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S) :
    ProjectiveSimplexFamily T.barycentricProjectiveAtlas (J ⊕ S) :=
  B.coneSimplexFamily hnet hp (T.voronoi_cone_cover B hnet hp)

def voronoiConeRefinement [Finite J]
    (B : VoronoiBaseFamily T.barycentricProjectiveAtlas S J)
    {η : ℝ} (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S) :
    FiniteChartedComplex κ n P :=
  (T.voronoiConeFamily B hnet hp).toChartedComplex

theorem voronoiConeRefinement_refines [Finite J]
    (B : VoronoiBaseFamily T.barycentricProjectiveAtlas S J)
    {η : ℝ} (hnet : T.IsCellwiseNet S η) (hp : T.IsCellwiseProtected S) :
    (T.voronoiConeRefinement B hnet hp).Refines T :=
  (T.voronoiConeFamily B hnet hp).refines

end FiniteChartedComplex

end ArchivePLGeometry
