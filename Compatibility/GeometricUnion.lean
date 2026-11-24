module

public import Compatibility.Original

/-!
# Unions of disjoint geometric simplicial complexes

For a pairwise disjoint family of underlying spaces the union of the face
sets is again a genuine geometric simplicial complex. A finite family of
finite complexes remains finite, and its underlying space is the exact union.
-/

@[expose] public section
noncomputable section

namespace PLGeometry.GeometricUnion

universe u

variable {ι : Type u} {m : ℕ}
    (C : ι → _root_.Geometry.SimplicialComplex ℝ (E m))
    (hdisj : Pairwise (fun i j => Disjoint (C i).space (C j).space))

def complex : _root_.Geometry.SimplicialComplex ℝ (E m) where
  faces := ⋃ i, (C i).faces
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
    refine ⟨(C i).nonempty_of_mem_faces hi, ?_⟩
    intro t hts ht
    exact Set.mem_iUnion.mpr ⟨i, (C i).down_closed hi hts ht⟩
  indep := by
    intro s hs
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
    exact (C i).indep hi
  inter_subset_convexHull := by
    intro s t hs ht x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
    by_cases hij : i = j
    · subst j
      exact (C i).inter_subset_convexHull hi hj hx
    · exact False.elim ((Set.disjoint_left.mp (hdisj hij))
        ((C i).convexHull_subset_space hi hx.1)
        ((C j).convexHull_subset_space hj hx.2))

@[simp]
theorem complex_faces : (complex C hdisj).faces = ⋃ i, (C i).faces := rfl

theorem face_origin {σ : Finset (E m)} (hσ : σ ∈ (complex C hdisj).faces) :
    ∃ i, σ ∈ (C i).faces := Set.mem_iUnion.mp hσ

theorem face_mem {i : ι} {σ : Finset (E m)} (hσ : σ ∈ (C i).faces) :
    σ ∈ (complex C hdisj).faces := Set.mem_iUnion.mpr ⟨i, hσ⟩

theorem component_le (i : ι) : C i ≤ complex C hdisj :=
  fun _ hσ => face_mem C hdisj hσ

theorem complex_finite [Finite ι] (hfin : ∀ i, (C i).faces.Finite) :
    (complex C hdisj).faces.Finite := Set.finite_iUnion hfin

theorem complex_space : (complex C hdisj).space = ⋃ i, (C i).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, hσ, hxσ⟩ := _root_.Geometry.SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨i, hi⟩ := face_origin C hdisj hσ
    exact Set.mem_iUnion.mpr ⟨i,
      _root_.Geometry.SimplicialComplex.mem_space_iff.mpr ⟨σ, hi, hxσ⟩⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨σ, hσ, hxσ⟩ := _root_.Geometry.SimplicialComplex.mem_space_iff.mp hi
    exact _root_.Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨σ, face_mem C hdisj hσ, hxσ⟩

theorem space_mem {i : ι} {x : E m} (hx : x ∈ (C i).space) :
    x ∈ (complex C hdisj).space := by
  rw [complex_space]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

include hdisj in
theorem face_origin_unique {i j : ι} {σ : Finset (E m)}
    (hi : σ ∈ (C i).faces) (hj : σ ∈ (C j).faces) : i = j := by
  by_contra hij
  obtain ⟨x, hx⟩ := (C i).nonempty_of_mem_faces hi
  exact (Set.disjoint_left.mp (hdisj hij))
    ((C i).subset_space hi hx) ((C j).subset_space hj hx)

end PLGeometry.GeometricUnion
