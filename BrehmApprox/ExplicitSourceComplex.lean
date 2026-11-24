module

public import BrehmApprox.ExplicitFourOctantSource
public import BrehmApprox.CoordinateSphericalCells
public import BrehmApprox.CoordinateCellCharts
public import BrehmApprox.SphericalActiveProjection
public import BrehmApprox.FiniteClosedRefinement
public import BrehmApprox.ExplicitSourceGeodesics
public import BrehmApprox.SphericalFaceTransport
public import Mathlib.Order.Extension.Linear
public import Mathlib.Data.Finset.Sort

/-!
# A genuine finite two-dimensional spherical complex for the counterexample

The finite cells are the eight coordinate octants of the old equatorial
two-sphere and the four attached octants, together with every vertex face.
All cells and all face intersections are literal spherical convex hulls.
-/

@[expose] public section
noncomputable section

namespace ExplicitSourceComplex

open GeodesicSphere ExplicitSphericalOctants ExplicitFourOctantSource BrehmApprox

local instance explicitSourceComplexLocalInstance1 : DecidableEq (GeodesicSphere 3) := Classical.decEq _

theorem inclusion_coordinatePole (i : Fin 3) :
    inclusion (coordinatePole 2 i) = coordinatePole 3 i.castSucc := by
  apply GeodesicSphere.ext
  simp [inclusion, GeodesicSphere.map, linearInclusion, indexInclusion, coordinatePole_val]

theorem inclusion_antipode (x : GeodesicSphere 2) :
    inclusion (antipode x) = antipode (inclusion x) := by
  apply GeodesicSphere.ext
  simp [inclusion, GeodesicSphere.map, antipode]

theorem range_inclusion_eq : Set.range inclusion =
    {x : GeodesicSphere 3 | x.val 3 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact inclusion_last_coordinate y
  · intro hx
    refine ⟨signedFold x, ?_⟩
    apply GeodesicSphere.ext
    ext i
    fin_cases i
    · change (inclusion (signedFold x)).val (0 : Fin 3).castSucc = x.val 0
      rw [inclusion_coordinate]
      change (if x.val 0 < 0 then -Real.sqrt (x.val 0 ^ 2 + x.val 3 ^ 2)
        else Real.sqrt (x.val 0 ^ 2 + x.val 3 ^ 2)) = x.val 0
      rw [hx, zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs]
      split_ifs with h
      · rw [abs_of_neg h, neg_neg]
      · exact abs_of_nonneg (le_of_not_gt h)
    · exact inclusion_coordinate (signedFold x) 1
    · exact inclusion_coordinate (signedFold x) 2
    · change (inclusion (signedFold x)).val 3 = x.val 3
      rw [inclusion_last_coordinate]
      exact hx.symm

def MaximalIndex := (Fin 3 → Bool) ⊕ ExplicitBalancedFrame.vertices

instance : Fintype MaximalIndex := inferInstanceAs (Fintype ((Fin 3 → Bool) ⊕ _))

def maximalVertices : MaximalIndex → Finset (GeodesicSphere 3)
  | Sum.inl σ => CoordinateSphericalCells.baseVertices σ
  | Sum.inr v => {inclusion north, inclusion v.val, extra}

theorem attached_coordinates (v : GeodesicSphere 2) (hv : v ∈ ExplicitBalancedFrame.vertices) :
    ∃ I : Finset (Fin 4), ∃ σ : Fin 4 → Bool,
      ({inclusion north, inclusion v, extra} : Finset (GeodesicSphere 3)) = CoordinateSphericalCells.vertices I σ ∧
      I.card = 3 := by
  classical
  simp only [ExplicitBalancedFrame.vertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · refine ⟨{0, 1, 3}, fun _ => true, ?_, by norm_num⟩
    simp [CoordinateSphericalCells.vertices, CoordinateSphericalCells.signedPole, ExplicitBalancedFrame.first, north, extra,
      inclusion_coordinatePole]
  · refine ⟨{0, 1, 3}, fun i => decide (i ≠ 1), ?_, by norm_num⟩
    simp [CoordinateSphericalCells.vertices, CoordinateSphericalCells.signedPole, ExplicitBalancedFrame.first, north, extra,
      inclusion_antipode, inclusion_coordinatePole]
  · refine ⟨{0, 2, 3}, fun _ => true, ?_, by norm_num⟩
    simp [CoordinateSphericalCells.vertices, CoordinateSphericalCells.signedPole, ExplicitBalancedFrame.second, north, extra,
      inclusion_coordinatePole]
  · refine ⟨{0, 2, 3}, fun i => decide (i ≠ 2), ?_, by norm_num⟩
    simp [CoordinateSphericalCells.vertices, CoordinateSphericalCells.signedPole, ExplicitBalancedFrame.second, north, extra,
      inclusion_antipode, inclusion_coordinatePole]

theorem maximal_coordinates (i : MaximalIndex) :
    ∃ I : Finset (Fin 4), ∃ σ : Fin 4 → Bool,
      maximalVertices i = CoordinateSphericalCells.vertices I σ ∧ I.card = 3 := by
  cases i with
  | inl σ => exact ⟨CoordinateSphericalCells.baseAxes, CoordinateSphericalCells.baseSign σ, rfl, by norm_num [CoordinateSphericalCells.baseAxes]⟩
  | inr v => exact attached_coordinates v.val v.property

theorem maximal_hemispherical (i : MaximalIndex) : InOpenHemisphere (maximalVertices i) := by
  obtain ⟨I, σ, hi, _⟩ := maximal_coordinates i
  rw [hi]
  exact CoordinateSphericalCells.hemispherical I σ

theorem maximal_card (i : MaximalIndex) : (maximalVertices i).card = 3 := by
  obtain ⟨I, σ, hi, hI⟩ := maximal_coordinates i
  rw [hi, CoordinateSphericalCells.vertices_card, hI]

def faces : Finset (Finset (GeodesicSphere 3)) := by
  classical
  exact Finset.univ.biUnion fun i : MaximalIndex => (maximalVertices i).powerset

theorem mem_faces (V : Finset (GeodesicSphere 3)) :
    V ∈ faces ↔ ∃ i : MaximalIndex, V ⊆ maximalVertices i := by
  classical
  simp [faces]

theorem maximal_mem_faces (i : MaximalIndex) : maximalVertices i ∈ faces :=
  (mem_faces _).mpr ⟨i, Finset.Subset.refl _⟩

theorem subface_mem {V W : Finset (GeodesicSphere 3)}
    (hV : V ∈ faces) (hWV : W ⊆ V) : W ∈ faces := by
  obtain ⟨i, hi⟩ := (mem_faces V).mp hV
  exact (mem_faces W).mpr ⟨i, hWV.trans hi⟩

theorem face_coordinates {V : Finset (GeodesicSphere 3)} (hV : V ∈ faces) :
    ∃ I : Finset (Fin 4), ∃ σ : Fin 4 → Bool, V = CoordinateSphericalCells.vertices I σ := by
  obtain ⟨i, hi⟩ := (mem_faces V).mp hV
  obtain ⟨J, σ, hj, _⟩ := maximal_coordinates i
  rw [hj] at hi
  obtain ⟨I, _, hI⟩ := CoordinateSphericalCells.subface_coordinates J σ V hi
  exact ⟨I, σ, hI⟩

theorem face_hemispherical {V : Finset (GeodesicSphere 3)} (hV : V ∈ faces) :
    InOpenHemisphere V := by
  obtain ⟨I, σ, rfl⟩ := face_coordinates hV
  exact CoordinateSphericalCells.hemispherical I σ

theorem face_independent {V : Finset (GeodesicSphere 3)} (hV : V ∈ faces) :
    LinearIndependent ℝ (fun v : V => v.val.val) := by
  obtain ⟨I, σ, rfl⟩ := face_coordinates hV
  exact CoordinateSphericalCells.vertices_independent I σ

theorem face_card_le_three {V : Finset (GeodesicSphere 3)} (hV : V ∈ faces) : V.card ≤ 3 := by
  obtain ⟨i, hi⟩ := (mem_faces V).mp hV
  exact (Finset.card_le_card hi).trans_eq (maximal_card i)

theorem face_intersection {V W : Finset (GeodesicSphere 3)}
    (hV : V ∈ faces) (hW : W ∈ faces) :
    sphericalCell V ∩ sphericalCell W = sphericalCell (V ∩ W) := by
  obtain ⟨I, σ, rfl⟩ := face_coordinates hV
  obtain ⟨J, τ, rfl⟩ := face_coordinates hW
  exact CoordinateSphericalCells.cell_intersection_vertices I J σ τ

theorem intersection_mem {V W : Finset (GeodesicSphere 3)}
    (hV : V ∈ faces) : V ∩ W ∈ faces := subface_mem hV Finset.inter_subset_left

theorem maximal_subset_source (i : MaximalIndex) :
    sphericalCell (maximalVertices i) ⊆ ExplicitFourOctantSource.sourceSet := by
  cases i with
  | inl σ =>
    intro x hx
    apply Or.inl
    rw [range_inclusion_eq, CoordinateSphericalCells.equatorial_cover]
    exact Set.mem_iUnion.mpr ⟨σ, hx⟩
  | inr v =>
    intro x hx
    exact Or.inr (Set.mem_iUnion.mpr ⟨v, hx⟩)

theorem face_subset_source {V : Finset (GeodesicSphere 3)} (hV : V ∈ faces) :
    sphericalCell V ⊆ ExplicitFourOctantSource.sourceSet := by
  obtain ⟨i, hi⟩ := (mem_faces V).mp hV
  exact (sphericalCell_mono hi).trans (maximal_subset_source i)

theorem source_eq_union_faces :
    ExplicitFourOctantSource.sourceSet = ⋃ V ∈ faces, sphericalCell V := by
  ext x
  constructor
  · intro hx
    have hex : ∃ i : MaximalIndex, x ∈ sphericalCell (maximalVertices i) := by
      rcases hx with h | h
      · rw [range_inclusion_eq, CoordinateSphericalCells.equatorial_cover] at h
        obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp h
        exact ⟨Sum.inl σ, hσ⟩
      · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h
        exact ⟨Sum.inr v, hv⟩
    obtain ⟨i, hi⟩ := hex
    exact Set.mem_iUnion.mpr ⟨maximalVertices i,
      Set.mem_iUnion.mpr ⟨maximal_mem_faces i, hi⟩⟩
  · intro hx
    obtain ⟨V, hxV⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hV, hxV⟩ := Set.mem_iUnion.mp hxV
    exact face_subset_source hV hxV

def Face := ↥faces

instance : Fintype Face := inferInstanceAs (Fintype ↥faces)

def fineCell (V : Face) : Set Source := {x | x.val ∈ sphericalCell V.val}

theorem fineCell_cover (x : Source) : ∃ V : Face, x ∈ fineCell V := by
  have hx := x.property
  rw [source_eq_union_faces] at hx
  obtain ⟨V, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hV, hx⟩ := Set.mem_iUnion.mp hx
  exact ⟨⟨V, hV⟩, hx⟩

theorem fineCell_subset_coarse (V : Face) :
    ∃ i : Option ExplicitBalancedFrame.vertices, fineCell V ⊆ cell i := by
  obtain ⟨i, hi⟩ := (mem_faces V.val).mp V.property
  cases i with
  | inl σ =>
    refine ⟨none, ?_⟩
    intro x hx
    change x.val ∈ Set.range inclusion
    rw [range_inclusion_eq, CoordinateSphericalCells.equatorial_cover]
    exact Set.mem_iUnion.mpr ⟨σ, sphericalCell_mono hi hx⟩
  | inr v =>
    exact ⟨some v, fun _ hx => sphericalCell_mono hi hx⟩

/-- The inherited distance on each fine simplex is exactly its own spherical
distance, despite the new source metric having been defined by global chains. -/
theorem fineCell_dist (V : Face) (x : Source) (hx : x ∈ fineCell V)
    (y : Source) (hy : y ∈ fineCell V) : dist x y = dist x.val y.val := by
  obtain ⟨i, hi⟩ := fineCell_subset_coarse V
  exact cell_dist i x (hi hx) y (hi hy)

theorem image_fineCell (V : Face) : Source.val '' fineCell V = sphericalCell V.val := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨y, face_subset_source V.property hy⟩, hy, rfl⟩

theorem fineCell_closed (V : Face) : IsClosed (fineCell V) :=
  (isClosed_sphericalCell V.val (face_hemispherical V.property)).preimage ambient_short.continuous

theorem fineCell_compact (V : Face) : IsCompact (fineCell V) :=
  (fineCell_closed V).isCompact

def meet (V W : Face) : Face := ⟨V.val ∩ W.val, intersection_mem V.property⟩

theorem fineCell_intersection (V W : Face) :
    fineCell V ∩ fineCell W = fineCell (meet V W) := by
  ext x
  change (x.val ∈ sphericalCell V.val ∧ x.val ∈ sphericalCell W.val) ↔
    x.val ∈ sphericalCell (V.val ∩ W.val)
  rw [← face_intersection V.property W.property]
  rfl

theorem fineCell_mono (V W : Face) (hVW : V.val ⊆ W.val) : fineCell V ⊆ fineCell W :=
  fun _ hx => sphericalCell_mono hVW hx

/-- The literal finite simplicial refinement generates the SAME source
metric. The original coarse-cell metric is not silently replaced here. -/
theorem fine_intrinsic : ChainGenerated fineCell :=
  chainGenerated_finite_closed_cover fineCell ExplicitFourOctantSource.intrinsic
    fineCell_closed fineCell_cover ExplicitFourOctantSource.exists_cell_geodesic

/-- Every actual face has its own isometric chart onto the specified genuine
spherical simplex, with at most three independent vertices. -/
def faceChart (V : Face) : fineCell V ≃ᵢ sphericalCell V.val where
  toFun x := ⟨x.val.val, x.property⟩
  invFun y := ⟨⟨y.val, face_subset_source V.property y.property⟩, y.property⟩
  left_inv := by intro x; rfl
  right_inv := by intro y; rfl
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    exact (fineCell_dist V x.val x.property y.val y.property).symm

theorem genuine_simplicial_source :
    (∀ V : Face, InOpenHemisphere V.val ∧
      LinearIndependent ℝ (fun v : V.val => v.val.val) ∧ V.val.card ≤ 3) ∧
    (∀ x : Source, ∃ V : Face, x ∈ fineCell V) ∧
    (∀ V W : Face, fineCell V ∩ fineCell W = fineCell (meet V W)) ∧
    ChainGenerated fineCell := by
  refine ⟨?_, fineCell_cover, fineCell_intersection, fine_intrinsic⟩
  intro V
  exact ⟨face_hemispherical V.property, face_independent V.property,
    face_card_le_three V.property⟩

instance : PartialOrder Face := inferInstanceAs (PartialOrder ↥faces)

instance : Fintype (LinearExtension Face) := inferInstanceAs (Fintype Face)

def numberFaces : ℕ := Fintype.card Face

def faceOrder : Fin numberFaces ≃o LinearExtension Face :=
  Fintype.orderIsoFinOfCardEq (LinearExtension Face) rfl

def enumerate : Fin numberFaces ≃ Face := faceOrder.toEquiv

theorem enumeration_strict {i j : Fin numberFaces}
    (hij : (enumerate i).val ⊆ (enumerate j).val) (hne : i ≠ j) : i.val < j.val := by
  have hle : (toLinearExtension (enumerate i)) ≤ toLinearExtension (enumerate j) :=
    toLinearExtension.monotone hij
  have hne' : toLinearExtension (enumerate i) ≠ toLinearExtension (enumerate j) := by
    intro h
    exact hne (enumerate.injective h)
  have hlt : faceOrder i < faceOrder j := lt_of_le_of_ne hle hne'
  exact faceOrder.lt_iff_lt.mp hlt

def indexedMeet (i j : Fin numberFaces) : Fin numberFaces :=
  enumerate.symm (meet (enumerate i) (enumerate j))

@[simp] theorem enumerate_indexedMeet (i j : Fin numberFaces) :
    enumerate (indexedMeet i j) = meet (enumerate i) (enumerate j) :=
  enumerate.apply_symm_apply _

/-- The concrete source, with its actual global chain metric, is a finite
spherical folded geometry in S³. Every face is a genuine simplex of dimension
at most two; this statement does not assert a folding into S². -/
def foldedGeometry : FoldedGeometry (P := Source) (sphericalPolytopeModel 3) numberFaces where
  faceLE i j := (enumerate i).val ⊆ (enumerate j).val
  le_refl i := Finset.Subset.refl _
  le_trans i j k hij hjk := hij.trans hjk
  index_strict i j hij hne := enumeration_strict hij hne
  meet := indexedMeet
  meet_comm i j := by
    apply enumerate.injective
    simp only [enumerate_indexedMeet]
    apply Subtype.ext
    exact Finset.inter_comm _ _
  meet_le_left i j := by
    simp only [enumerate_indexedMeet]
    exact Finset.inter_subset_left
  meet_le_right i j := by
    simp only [enumerate_indexedMeet]
    exact Finset.inter_subset_right
  core i := sphericalCell (enumerate i).val
  polytope_core i := ⟨(enumerate i).val, face_hemispherical (enumerate i).property, rfl⟩
  core_mono i j hij := sphericalCell_mono hij
  core_inter i j k _ _ := by
    simp only [enumerate_indexedMeet]
    exact face_intersection (enumerate j).property (enumerate k).property
  cell i := fineCell (enumerate i)
  cover x := by
    obtain ⟨V, hV⟩ := fineCell_cover x
    exact ⟨enumerate.symm V, by simpa only [enumerate.apply_symm_apply] using hV⟩
  fold := Source.val
  image_cell i := image_fineCell (enumerate i)
  isometry_cell i x hx y hy := (fineCell_dist (enumerate i) x hx y hy).symm
  cell_mono i j hij := fineCell_mono (enumerate i) (enumerate j) hij
  intersection i j := by
    simp only [enumerate_indexedMeet]
    exact (fineCell_intersection (enumerate i) (enumerate j)).subset
  intrinsic := by
    intro x y ε hε
    obtain ⟨n, z, h0, hn, hcells, hcost⟩ := fine_intrinsic x y ε hε
    refine ⟨n, z, h0, hn, ?_, hcost⟩
    intro j hj
    obtain ⟨V, hVj, hVj'⟩ := hcells j hj
    exact ⟨enumerate.symm V, by simpa only [enumerate.apply_symm_apply] using hVj,
      by simpa only [enumerate.apply_symm_apply] using hVj'⟩

/-- Full independent-vertex and all-subface data for the actual finite
spherical source complex. -/
def simplicialData : SphericalSimplicialFaceData foldedGeometry.toPolyhedralFaceData where
  vertices i := (enumerate i).val
  core_eq i := rfl
  independent i := face_independent (enumerate i).property
  vertices_mono i j hij := hij
  all_subfaces i W hW := by
    let V : Face := ⟨W, subface_mem (enumerate i).property hW⟩
    refine ⟨enumerate.symm V, ?_, ?_⟩
    · change (enumerate (enumerate.symm V)).val ⊆ (enumerate i).val
      simpa only [enumerate.apply_symm_apply] using hW
    · exact congrArg Subtype.val (enumerate.apply_symm_apply V)
  face_of_vertices i j k _ _ hij := hij

theorem simplicialData_card_le_three (i : Fin numberFaces) :
    (simplicialData.vertices i).card ≤ 3 := face_card_le_three (enumerate i).property

@[simp] theorem foldedGeometry_fold : foldedGeometry.fold = Source.val := rfl

def maximalFace (i : MaximalIndex) : Face := ⟨maximalVertices i, maximal_mem_faces i⟩

/-- Each of the concrete maximal source triangles, with the actual intrinsic
source metric, is isometric to the positive octant of the round TWO-sphere.
This certifies the model dimension directly, not merely by vertex counting. -/
theorem maximal_source_triangle_chart (i : MaximalIndex) :
    Nonempty (fineCell (maximalFace i) ≃ᵢ CoordinateCellCharts.standardSimplex 2) := by
  obtain ⟨e⟩ := CoordinateCellCharts.exists_triangle_chart_of_coordinates
    (maximalVertices i) (maximal_coordinates i)
  exact ⟨(faceChart (maximalFace i)).trans e.symm⟩

end ExplicitSourceComplex
