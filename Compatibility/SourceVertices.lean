module

public import Compatibility.SourceIndependence
public import Compatibility.ModelHemisphere
public import BrehmApprox.SphericalFaceTransport
public import BrehmApprox.HyperbolicSimplicialCharts

/-! The original chart axioms imply the concrete nondegeneracy conditions. -/

@[expose] public section
noncomputable section

namespace PLGeometry

open Set GeodesicSphere BrehmApprox

local instance sourceVerticesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem affineIndependent_finset_image {V W : Type*}
    [AddCommGroup W] [Module ℝ W] (σ : Finset V) (f : V → W)
    (hf : AffineIndependent ℝ (fun x : σ => f x.val)) :
    AffineIndependent ℝ (fun x : σ.image f => x.val) := by
  have he : Set.range (fun x : σ => f x.val) = (σ.image f : Set W) := by
    ext y
    simp
  change AffineIndepOn ℝ id (σ.image f : Set W)
  rw [← he]
  exact hf.range

namespace Simplex

variable {d m : ℕ} {σ : Finset (E m)}

theorem klein_image_hull (S : Simplex .hyperbolic d m σ)
    (V : Finset (E m)) (hV : (V : Set (E m)) ⊆ cell σ) :
    (fun x => (S.toModel x).val) '' convexHull ℝ (V : Set (E m)) =
      convexHull ℝ ((fun x => (S.toModel x).val) '' (V : Set (E m))) := by
  have hball : convexHull ℝ (Subtype.val '' (S.toModel '' (V : Set (E m)))) ⊆
      Metric.ball (0 : E d) 1 := by
    apply convexHull_min _ (convex_ball _ _)
    rintro x ⟨v, _, rfl⟩
    exact v.property
  calc
    _ = Subtype.val '' (S.toModel '' convexHull ℝ (V : Set (E m))) := by
      rw [Set.image_image]
    _ = Subtype.val '' hull .hyperbolic d (S.toModel '' (V : Set (E m))) :=
      congrArg (Set.image Subtype.val) (S.convex V hV)
    _ = convexHull ℝ (Subtype.val '' (S.toModel '' (V : Set (E m)))) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hball hx⟩, hx, rfl⟩
    _ = _ := by rw [Set.image_image]

theorem hyperbolic_vertex_independent (S : Simplex .hyperbolic d m σ)
    (hσ : AffineIndependent ℝ (fun x : σ => (x : E m))) :
    LinearIndependent ℝ
      (fun x : σ => HyperbolicSpace.lift (modelEquiv .hyperbolic d (S.toModel x.val))) := by
  have hi : AffineIndependent ℝ (fun x : σ => (S.toModel x.val).val) := by
    apply affineIndependent_of_hull_preserving σ hσ (fun x => (S.toModel x).val)
    · intro x hx y hy h
      exact S.injective hx hy (Subtype.ext h)
    · intro V hV
      exact S.klein_image_hull V ((Finset.coe_subset.mpr hV).trans (subset_convexHull ℝ _))
  apply (HyperbolicSpace.linearIndependent_lift_iff_affineIndependent_klein
    (fun x : σ => modelEquiv .hyperbolic d (S.toModel x.val))).mpr
  have he : (fun x : σ => HyperbolicSpace.klein (modelEquiv .hyperbolic d (S.toModel x.val))) =
      (fun x : σ => (S.toModel x.val).val) := by
    funext x
    exact klein_modelEquiv _
  rw [he]
  exact hi

def sphericalGnomonicChart (S : Simplex .spherical d m σ)
    (p : GeodesicSphere d)
    (hp : ∀ x ∈ cell σ, 0 < inner ℝ p.val (modelEquiv .spherical d (S.toModel x)).val)
    (x : E m) : tangentPlane p := by
  classical
  exact if hx : x ∈ cell σ then
    gnomonic p ⟨modelEquiv .spherical d (S.toModel x), hp x hx⟩ else 0

theorem sphericalGnomonicChart_of_mem (S : Simplex .spherical d m σ)
    (p : GeodesicSphere d)
    (hp : ∀ x ∈ cell σ, 0 < inner ℝ p.val (modelEquiv .spherical d (S.toModel x)).val)
    {x : E m} (hx : x ∈ cell σ) :
    S.sphericalGnomonicChart p hp x =
      gnomonic p ⟨modelEquiv .spherical d (S.toModel x), hp x hx⟩ := by
  simp only [sphericalGnomonicChart, dif_pos hx]

theorem sphericalGnomonicChart_injective (S : Simplex .spherical d m σ)
    (p : GeodesicSphere d)
    (hp : ∀ x ∈ cell σ, 0 < inner ℝ p.val (modelEquiv .spherical d (S.toModel x)).val) :
    Set.InjOn (S.sphericalGnomonicChart p hp) (cell σ) := by
  intro x hx y hy h
  rw [S.sphericalGnomonicChart_of_mem p hp hx,
    S.sphericalGnomonicChart_of_mem p hp hy] at h
  have he := congrArg Subtype.val ((gnomonicHomeomorph p).injective h)
  exact S.injective hx hy ((modelEquiv .spherical d).injective he)

theorem sphericalGnomonicChart_image_hull (S : Simplex .spherical d m σ)
    (p : GeodesicSphere d)
    (hp : ∀ x ∈ cell σ, 0 < inner ℝ p.val (modelEquiv .spherical d (S.toModel x)).val)
    (V : Finset (E m)) (hV : V ⊆ σ) :
    S.sphericalGnomonicChart p hp '' convexHull ℝ (V : Set (E m)) =
      convexHull ℝ (S.sphericalGnomonicChart p hp '' (V : Set (E m))) := by
  let F : E m → GeodesicSphere d := fun x => modelEquiv .spherical d (S.toModel x)
  let W : Finset (GeodesicSphere d) := V.image F
  have hVcell : (V : Set (E m)) ⊆ cell σ :=
    (Finset.coe_subset.mpr hV).trans (subset_convexHull ℝ _)
  have hcell : convexHull ℝ (V : Set (E m)) ⊆ cell σ :=
    convexHull_mono (Finset.coe_subset.mpr hV)
  have hW : ∀ v ∈ W, 0 < inner ℝ p.val v.val := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hp x (hVcell hx)
  have hproj : projectVertices p W hW = V.image (S.sphericalGnomonicChart p hp) := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨v, hv⟩, _, he⟩ := Finset.mem_image.mp hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
      simpa only [S.sphericalGnomonicChart_of_mem p hp (hVcell hx)] using he
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      refine Finset.mem_image.mpr ⟨⟨F x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩,
        Finset.mem_attach _ _, ?_⟩
      exact (S.sphericalGnomonicChart_of_mem p hp (hVcell hx)).symm
  have hhull : F '' convexHull ℝ (V : Set (E m)) = sphericalCell W :=
    S.archive_image_hull V hVcell
  rw [← Finset.coe_image, ← hproj]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (gnomonicInverse_mem_cell_iff p W hW _).mp
    rw [S.sphericalGnomonicChart_of_mem p hp (hcell hx), gnomonicInverse_gnomonic]
    rw [← hhull]
    exact ⟨x, hx, rfl⟩
  · intro hz
    have hzW := (gnomonicInverse_mem_cell_iff p W hW z).mpr hz
    rw [← hhull] at hzW
    obtain ⟨x, hx, hFx⟩ := hzW
    refine ⟨x, hx, ?_⟩
    rw [S.sphericalGnomonicChart_of_mem p hp (hcell hx)]
    have he : (⟨F x, hp x (hcell hx)⟩ : openHemisphere p) = gnomonicInverse p z :=
      Subtype.ext hFx
    change gnomonic p ⟨F x, hp x (hcell hx)⟩ = z
    rw [he, gnomonic_gnomonicInverse]

theorem spherical_vertex_independent (S : Simplex .spherical d m σ)
    (hσ : AffineIndependent ℝ (fun x : σ => (x : E m))) :
    LinearIndependent ℝ (fun x : σ => (modelEquiv .spherical d (S.toModel x.val)).val) := by
  obtain ⟨p, hp⟩ := S.spherical_cell_hemisphere
  let v : σ → openHemisphere p := fun x =>
    ⟨modelEquiv .spherical d (S.toModel x.val), hp x.val (subset_convexHull ℝ _ x.property)⟩
  have hG : AffineIndependent ℝ (fun x : σ => S.sphericalGnomonicChart p hp x.val) :=
    affineIndependent_of_hull_preserving σ hσ _ (S.sphericalGnomonicChart_injective p hp)
      (S.sphericalGnomonicChart_image_hull p hp)
  have he : (fun x : σ => S.sphericalGnomonicChart p hp x.val) =
      (fun x : σ => gnomonic p (v x)) := by
    funext x
    exact S.sphericalGnomonicChart_of_mem p hp (subset_convexHull ℝ _ x.property)
  rw [he] at hG
  exact (gnomonic_affineIndependent_iff p v).mp hG

theorem archive_simplexVertices {κ : Geometry} (S : Simplex κ d m σ)
    (hσ : AffineIndependent ℝ (fun x : σ => (x : E m))) :
    ArchivePLGeometry.simplexVertices κ.toArchive d
      (σ.image (fun x => modelEquiv κ d (S.toModel x))) := by
  cases κ with
  | euclidean =>
    exact affineIndependent_finset_image σ _ (S.euclidean_vertex_independent hσ)
  | hyperbolic =>
    have h := LinearIndepOn.image_of_comp
      (fun x => modelEquiv .hyperbolic d (S.toModel x)) HyperbolicSpace.lift
      (S.hyperbolic_vertex_independent hσ)
    change LinearIndepOn ℝ HyperbolicSpace.lift
      (σ.image (fun x => modelEquiv .hyperbolic d (S.toModel x)) : Set (HyperbolicSpace d))
    rw [Finset.coe_image]
    exact h
  | spherical =>
    refine ⟨S.spherical_hemisphere, ?_⟩
    have h := LinearIndepOn.image_of_comp
      (fun x => modelEquiv .spherical d (S.toModel x)) GeodesicSphere.val
      (S.spherical_vertex_independent hσ)
    change LinearIndepOn ℝ GeodesicSphere.val
      (σ.image (fun x => modelEquiv .spherical d (S.toModel x)) : Set (GeodesicSphere d))
    rw [Finset.coe_image]
    exact h

end Simplex
end PLGeometry
