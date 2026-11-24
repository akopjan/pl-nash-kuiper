module

public import PLGeometry.BarycentricProjectiveAtlas
public import PLGeometry.BarycentricRadialExit
public import PLGeometry.ProtectedVoronoiTieComplex
public import BrehmApprox.FirstAffineHalfspaceHit

/-!
# Radial coverage by the protected Voronoi tie bases

A ray from a nearest site reaches an old face not containing that site.
Protection prevents its Voronoi cell from reaching that face. The first
affine distance cut met by the ray is therefore an actual tie base.
-/

@[expose] public section
noncomputable section

open Set Classical BrehmApprox

namespace ArchivePLGeometry.FiniteChartedComplex

universe u

local instance protectedVoronoiConesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {κ : Geometry} {n : ℕ} {P : Type u} [TopologicalSpace P] [T2Space P]
    (T : FiniteChartedComplex κ n P)

local instance protectedVoronoiConesVertexDecidableEq : DecidableEq T.Vertex := Classical.decEq _

theorem faceLabels_erase (σ : Finset P) (i : T.Vertex) :
    T.faceLabels (σ.erase i.val) = (T.faceLabels σ).erase i := by
  ext j
  simp only [mem_faceLabels, Finset.mem_erase]
  constructor
  · exact fun h => ⟨fun he => h.1 (congrArg Subtype.val he), h.2⟩
  · exact fun h => ⟨fun he => h.1 (Subtype.ext he), h.2⟩

theorem exists_opposite_face_radial_endpoint {σ : Finset P} (hσ : σ ∈ T.simplices)
    {a x : P} (ha : a ∈ T.cell σ) (hx : x ∈ T.cell σ) (hxa : x ≠ a) :
    ∃ τ ∈ T.simplices, τ ⊆ σ ∧ a ∉ T.cell τ ∧ ∃ y ∈ T.cell τ,
      T.barycentricCoords x ∈ segment ℝ (T.barycentricCoords a) (T.barycentricCoords y) := by
  have haw : T.barycentricCoords a ∈ Barycentric.weightsOn (T.faceLabels σ) := by
    rw [← T.barycentricCoords_image_cell hσ]
    exact ⟨a, ha, rfl⟩
  have hxw : T.barycentricCoords x ∈ Barycentric.weightsOn (T.faceLabels σ) := by
    rw [← T.barycentricCoords_image_cell hσ]
    exact ⟨x, hx, rfl⟩
  obtain ⟨i, hi, hai, w, hw, hxseg⟩ := Barycentric.exists_radial_endpoint haw hxw
    (fun he => hxa (T.barycentricCoords_injective he))
  let τ := σ.erase i.val
  have hτσ : τ ⊆ σ := Finset.erase_subset _ _
  have hτ := T.faces σ hσ τ hτσ
  have hwτ : w ∈ Barycentric.weightsOn (T.faceLabels τ) := by
    simpa only [τ, T.faceLabels_erase] using hw
  rw [← T.barycentricCoords_image_cell hτ] at hwτ
  obtain ⟨y, hy, hyw⟩ := hwτ
  refine ⟨τ, hτ, hτσ, ?_, y, hy, ?_⟩
  · intro haτ
    have hawτ : T.barycentricCoords a ∈ Barycentric.weightsOn (T.faceLabels τ) := by
      rw [← T.barycentricCoords_image_cell hτ]
      exact ⟨a, haτ, rfl⟩
    have hiτ : i ∉ T.faceLabels τ := by
      rw [T.mem_faceLabels]
      exact Finset.notMem_erase _ _
    exact hai.ne' (hawτ.2 i hiτ)
  · rwa [hyw]

theorem exists_voronoi_tie_radial_endpoint {S : Finset P}
    (hp : T.IsCellwiseProtected S) {σ : Finset P} (hσ : σ ∈ T.simplices)
    {a x : P} (hx : x ∈ T.voronoiPiece S σ a) (hxa : x ≠ a) :
    ∃ b ∈ S, b ≠ a ∧ b ∈ T.cell σ ∧ ∃ y,
      y ∈ T.voronoiPiece S σ a ∧ y ∈ T.voronoiPiece S σ b ∧
      T.barycentricCoords x ∈ segment ℝ (T.barycentricCoords a) (T.barycentricCoords y) := by
  let A := T.barycentricVoronoiAtlas
  obtain ⟨τ, hτ, hτσ, haτ, q, hqτ, hxseg⟩ :=
    T.exists_opposite_face_radial_endpoint hσ hx.2.1.2 hx.1 hxa
  have hqσ : q ∈ T.cell σ := T.cell_mono hσ hτσ hqτ
  have hqnot : q ∉ T.voronoiPiece S σ a := by
    intro hq
    exact haτ (hp σ hσ τ hτ q ⟨hqσ, hqτ⟩ a hq.2)
  let J : Finset P := (T.cellSites S σ).erase a
  have hsite (b : J) : b.val ∈ S ∧ b.val ∈ T.cell σ :=
    T.mem_cellSites.mp (Finset.mem_of_mem_erase b.property)
  choose L c hcut using fun b : J =>
    A.distanceCut σ hσ a hx.2.1.2 b.val (hsite b).2
  have hap (b : J) : L b (A.coord a) < c b := by
    have hle := (hcut b a hx.2.1.2).1.mp (by simp only [dist_self]; exact dist_nonneg)
    apply lt_of_le_of_ne hle
    intro he
    have hd := (hcut b a hx.2.1.2).2.mpr he
    have heq : T.chart σ a = T.chart σ b.val := by
      apply dist_eq_zero.mp
      rw [← hd, dist_self]
    have hab := T.chart_injectiveOn σ hσ hx.2.1.2 (hsite b).2 heq
    exact (Finset.mem_erase.mp b.property).1 hab.symm
  have hqout : ∃ b : J, c b < L b (A.coord q) := by
    by_contra hn
    push_neg at hn
    apply hqnot
    refine ⟨hqσ, hx.2.1, ?_⟩
    intro b hb
    by_cases hba : b = a
    · subst b
      exact le_rfl
    · exact (hcut ⟨b, Finset.mem_erase.mpr ⟨hba, T.mem_cellSites.mpr hb⟩⟩ q hqσ).1.mpr
        (hn ⟨b, Finset.mem_erase.mpr ⟨hba, T.mem_cellSites.mpr hb⟩⟩)
  obtain ⟨z, hzseg, hzcut, ⟨b, hzb⟩, hxinitial⟩ :=
    exists_first_affine_halfspace_hit L c (A.coord a) (A.coord q) hap hqout
  have hzold : z ∈ A.coord '' T.cell σ :=
    (A.cell_polytope σ hσ).convex.segment_subset
      (show A.coord a ∈ A.coord '' T.cell σ from ⟨a, hx.2.1.2, rfl⟩)
      (show A.coord q ∈ A.coord '' T.cell σ from ⟨q, hqσ, rfl⟩) hzseg
  obtain ⟨y, hyσ, hyz⟩ := hzold
  have hya : y ∈ T.voronoiPiece S σ a := by
    refine ⟨hyσ, hx.2.1, ?_⟩
    intro d hd
    by_cases hda : d = a
    · subst d
      exact le_rfl
    · let j : J := ⟨d, Finset.mem_erase.mpr ⟨hda, T.mem_cellSites.mpr hd⟩⟩
      apply (hcut j y hyσ).1.mpr
      rw [hyz]
      exact hzcut j
  have hyd : dist (T.chart σ y) (T.chart σ a) = dist (T.chart σ y) (T.chart σ b.val) := by
    apply (hcut b y hyσ).2.mpr
    rwa [hyz]
  have hyb : y ∈ T.voronoiPiece S σ b.val := by
    refine ⟨hyσ, hsite b, ?_⟩
    intro d hd
    change dist (T.chart σ y) (T.chart σ b.val) ≤ dist (T.chart σ y) (T.chart σ d)
    rw [← hyd]
    exact hya.2.2 d hd
  refine ⟨b.val, (hsite b).1, (Finset.mem_erase.mp b.property).1, (hsite b).2,
    y, hya, hyb, ?_⟩
  have hxcut (j : J) : L j (A.coord x) ≤ c j :=
    (hcut j x hx.1).1.mp (hx.2.2 j.val (hsite j))
  have hh := hxinitial (A.coord x) hxseg hxcut
  change T.barycentricCoords x ∈ segment ℝ (T.barycentricCoords a) z at hh
  change T.barycentricCoords x ∈ segment ℝ (T.barycentricCoords a) (A.coord y)
  rwa [hyz]

end ArchivePLGeometry.FiniteChartedComplex
