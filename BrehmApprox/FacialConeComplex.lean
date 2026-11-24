module

public import BrehmApprox.PullingPolytopeFamily
public import Mathlib.Analysis.Convex.Join

/-!
# Compatible cones over facial bases

The bases may be arbitrary compatible subdivisions of extreme faces.
Coning preserves their common-face intersections. This is the geometric
fact needed after refining the angular complex in the initial folding.
-/

@[expose] public section
noncomputable section

open Set Classical

namespace BrehmApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance facialConeComplexDecidableEq : DecidableEq E := Classical.decEq E

/-- A genuine affine cut supplies the nondegeneracy of its cone. -/
theorem affineIndependent_cone_of_affine_cut {V : Finset E}
    (hV : AffineIndependent ℝ ((↑) : V → E)) (L : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hcut : ∀ v ∈ V, L v = c) {a : E} (ha : L a ≠ c) :
    AffineIndependent ℝ (fun x : (insert a V : Finset E) => x.val) := by
  have hnot : a ∉ affineSpan ℝ (V : Set E) := by
    intro ham
    apply ha
    refine affineSpan_induction (p := fun z : E => L z = c) ham ?_ ?_
    · exact fun z hz => hcut z hz
    · intro t x y z hx hy hz
      change L (t • (x - y) + z) = c
      simp only [map_add, map_smul, map_sub, hx, hy, hz, sub_self, smul_zero, zero_add]
  have hi : AffineIndepOn ℝ id (V : Set E) := hV
  have hh := hi.id_insert hnot
  change AffineIndepOn ℝ id ((insert a V : Finset E) : Set E)
  rw [Finset.coe_insert]
  exact hh

theorem mem_hull_insert_cases {V : Finset E} {a x : E}
    (hx : x ∈ convexHull ℝ ((insert a V : Finset E) : Set E)) :
    x = a ∨ ∃ y ∈ convexHull ℝ (V : Set E), x ∈ segment ℝ a y := by
  by_cases hV : V.Nonempty
  · right
    rw [Finset.coe_insert, convexHull_insert (show (V : Set E).Nonempty from hV),
      convexJoin_singleton_left] at hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨y, hy, hxy⟩
  · left
    have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
    simpa [he] using hx

theorem segment_positive_right_of_ne_left {a y x : E} (hx : x ≠ a)
    {r s : ℝ} (_hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1)
    (he : r • a + s • y = x) : 0 < s := by
  apply lt_of_le_of_ne hs
  intro hz
  have hs0 : s = 0 := hz.symm
  have hr1 : r = 1 := by linarith
  exact hx (by simpa only [hs0, hr1, zero_smul, one_smul, add_zero] using he.symm)

theorem extreme_right_endpoint_mem {C D : Set E} (hD : _root_.IsExtreme ℝ C D)
    {a y x : E} (ha : a ∈ C) (hy : y ∈ C) (hx : x ∈ D)
    (hxa : x ≠ a) (hseg : x ∈ segment ℝ a y) : y ∈ D := by
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  have hspos := segment_positive_right_of_ne_left hxa hr hs hrs he
  by_cases hr0 : r = 0
  · have hs1 : s = 1 := by linarith
    have hyx : y = x := by simpa only [hr0, hs1, zero_smul, one_smul, zero_add] using he
    exact hyx.symm ▸ hx
  · exact hD.right_mem_of_mem_openSegment ha hy hx
      ⟨r, s, lt_of_le_of_ne hr (Ne.symm hr0), hspos, hrs, he⟩

theorem extreme_cone_mem_base {C D : Set E} (hD : _root_.IsExtreme ℝ C D)
    (hC : Convex ℝ C) {a : E} (ha : a ∈ C) (haD : a ∉ D)
    {V : Finset E} (hV : (V : Set E) ⊆ C) {x : E}
    (hx : x ∈ convexHull ℝ ((insert a V : Finset E) : Set E)) (hxD : x ∈ D) :
    x ∈ convexHull ℝ (V : Set E) := by
  rcases mem_hull_insert_cases hx with hxa | ⟨y, hy, hseg⟩
  · exact (haD (hxa ▸ hxD)).elim
  · have hyC := convexHull_min hV hC hy
    obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
    have hr0 : r = 0 := by
      by_contra hne
      have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hne)
      by_cases hs0 : s = 0
      · have hr1 : r = 1 := by linarith
        have hax : a = x := by simpa only [hr1, hs0, one_smul, zero_smul, add_zero] using he
        exact haD (hax.symm ▸ hxD)
      · exact haD (hD.left_mem_of_mem_openSegment ha hyC hxD
          ⟨r, s, hrpos, lt_of_le_of_ne hs (Ne.symm hs0), hrs, he⟩)
    have hs1 : s = 1 := by linarith
    have hyx : y = x := by simpa only [hr0, hs1, zero_smul, one_smul, zero_add] using he
    exact hyx ▸ hy

private theorem radial_reparam {a x y z : E} {r s t u : ℝ}
    (hrs : r + s = 1) (htu : t + u = 1)
    (hxy : r • a + s • y = x) (hxz : t • a + u • z = x) (hu : u ≠ 0) :
    (1 - s / u) • a + (s / u) • y = z := by
  have hr : r = 1 - s := by linarith
  have ht : t = 1 - u := by linarith
  have hsy : s • (y - a) = x - a := by rw [← hxy, hr]; module
  have huz : u • (z - a) = x - a := by rw [← hxz, ht]; module
  have he : (s / u) • (y - a) = z - a := by
    calc
      _ = u⁻¹ • (s • (y - a)) := by rw [smul_smul]; congr 1; ring
      _ = u⁻¹ • (u • (z - a)) := by rw [hsy, huz]
      _ = z - a := by rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
  calc
    (1 - s / u) • a + (s / u) • y = a + (s / u) • (y - a) := by module
    _ = z := by rw [he]; abel

/-- An extreme face missing the apex meets each outgoing ray at most once. -/
theorem radial_faces_unique {C D F G : Set E}
    (hF : _root_.IsExtreme ℝ C F) (hG : _root_.IsExtreme ℝ D G)
    {a x y z : E} (haC : a ∈ C) (haD : a ∈ D) (haF : a ∉ F) (haG : a ∉ G)
    (hyF : y ∈ F) (hyD : y ∈ D) (hzG : z ∈ G) (hzC : z ∈ C)
    (hxa : x ≠ a) (hxy : x ∈ segment ℝ a y) (hxz : x ∈ segment ℝ a z) : y = z := by
  obtain ⟨r, s, hr, hs, hrs, hexy⟩ := hxy
  obtain ⟨t, u, ht, hu, htu, hexz⟩ := hxz
  have hspos := segment_positive_right_of_ne_left hxa hr hs hrs hexy
  have hupos := segment_positive_right_of_ne_left hxa ht hu htu hexz
  have hsu : s = u := by
    apply le_antisymm
    · by_contra h
      have hus : u < s := lt_of_not_ge h
      have hseg : y ∈ openSegment ℝ a z := by
        refine ⟨1 - u / s, u / s, ?_, div_pos hupos hspos, by ring, ?_⟩
        · exact sub_pos.mpr ((div_lt_one hspos).mpr hus)
        · exact radial_reparam htu hrs hexz hexy hspos.ne'
      exact haF (hF.left_mem_of_mem_openSegment haC hzC hyF hseg)
    · by_contra h
      have hsu' : s < u := lt_of_not_ge h
      have hseg : z ∈ openSegment ℝ a y := by
        refine ⟨1 - s / u, s / u, ?_, div_pos hspos hupos, by ring, ?_⟩
        · exact sub_pos.mpr ((div_lt_one hupos).mpr hsu')
        · exact radial_reparam hrs htu hexy hexz hupos.ne'
      exact haG (hG.left_mem_of_mem_openSegment haD hyD hzG hseg)
  have hh := radial_reparam hrs htu hexy hexz hupos.ne'
  simpa only [hsu, div_self hupos.ne', sub_self, zero_smul, one_smul, zero_add] using hh

/-- Cones with one apex inherit intersections from their facial bases, even
when those bases belong to different polytopes of a face-to-face family. -/
theorem same_apex_cones_intersection {C D F G : Set E}
    (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCD : _root_.IsExtreme ℝ C (C ∩ D))
    (hDC : _root_.IsExtreme ℝ D (D ∩ C))
    (hF : _root_.IsExtreme ℝ C F) (hG : _root_.IsExtreme ℝ D G)
    {a : E} (haC : a ∈ C) (haD : a ∈ D) (haF : a ∉ F) (haG : a ∉ G)
    (V W : Finset E) (hVF : convexHull ℝ (V : Set E) ⊆ F)
    (hWG : convexHull ℝ (W : Set E) ⊆ G)
    (hVW : convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E) =
      convexHull ℝ ((V ∩ W : Finset E) : Set E)) :
    convexHull ℝ ((insert a V : Finset E) : Set E) ∩ convexHull ℝ ((insert a W : Finset E) : Set E) =
      convexHull ℝ ((insert a (V ∩ W) : Finset E) : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxa : x = a
    · rw [hxa]
      exact subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
    obtain ⟨y, hy, hxy⟩ := (mem_hull_insert_cases hx.1).resolve_left hxa
    obtain ⟨z, hz, hxz⟩ := (mem_hull_insert_cases hx.2).resolve_left hxa
    have hyC := hF.subset (hVF hy)
    have hzD := hG.subset (hWG hz)
    have hxC := hC.segment_subset haC hyC hxy
    have hxD := hD.segment_subset haD hzD hxz
    have hyD := (extreme_right_endpoint_mem hCD haC hyC ⟨hxC, hxD⟩ hxa hxy).2
    have hzC := (extreme_right_endpoint_mem hDC haD hzD ⟨hxD, hxC⟩ hxa hxz).2
    have hyz := radial_faces_unique hF hG haC haD haF haG (hVF hy) hyD
      (hWG hz) hzC hxa hxy hxz
    have hyVW : y ∈ convexHull ℝ ((V ∩ W : Finset E) : Set E) := by
      rw [← hVW]
      exact ⟨hy, hyz.symm ▸ hz⟩
    exact (convex_convexHull ℝ ((insert a (V ∩ W) : Finset E) : Set E)).segment_subset
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))
      (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hyVW) hxy
  · intro x hx
    exact ⟨convexHull_mono (Finset.coe_subset.mpr (Finset.insert_subset_insert a Finset.inter_subset_left)) hx,
      convexHull_mono (Finset.coe_subset.mpr (Finset.insert_subset_insert a Finset.inter_subset_right)) hx⟩

/-- Cones from distinct Voronoi sites meet only along their bases. -/
theorem different_apex_cones_intersection {C D : Set E}
    (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCD : _root_.IsExtreme ℝ C (C ∩ D))
    (hDC : _root_.IsExtreme ℝ D (D ∩ C))
    {a b : E} (haC : a ∈ C) (hbD : b ∈ D) (haD : a ∉ D) (hbC : b ∉ C)
    (V W : Finset E) (hVC : (V : Set E) ⊆ C) (hWD : (W : Set E) ⊆ D)
    (hVW : convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E) =
      convexHull ℝ ((V ∩ W : Finset E) : Set E)) :
    convexHull ℝ ((insert a V : Finset E) : Set E) ∩ convexHull ℝ ((insert b W : Finset E) : Set E) =
      convexHull ℝ ((V ∩ W : Finset E) : Set E) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxC := convexHull_min (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact haC
      · exact hVC hz) hC hx.1
    have hxD := convexHull_min (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hbD
      · exact hWD hz) hD hx.2
    rw [← hVW]
    exact ⟨extreme_cone_mem_base hCD hC haC (fun h => haD h.2) hVC hx.1 ⟨hxC, hxD⟩,
      extreme_cone_mem_base hDC hD hbD (fun h => hbC h.2) hWD hx.2 ⟨hxD, hxC⟩⟩
  · intro x hx
    have hx' : x ∈ convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E) := by rwa [hVW]
    exact ⟨convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hx'.1,
      convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hx'.2⟩

end BrehmApprox
