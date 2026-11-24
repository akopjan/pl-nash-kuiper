# Mathematical audit of the transfer

The review covers `Solution.lean`, `Compatibility/Transfer.lean`,
`EmbeddedRefinement.lean`, `ComponentRefinement.lean`,
`GeometricRealization.lean`, `GeometricUnion.lean`, `ModelDimension.lean`,
and the model, source-atlas, intrinsic-metric, and component bridges on which
they depend. No mathematical gap or additional hypothesis was found in
these transfer steps. Kernel checking and transitive axiom checking are
separate checks; their build and audit logs provide the corresponding
mechanical evidence.

## Exact public statement

A normalized-text comparison gives identical theorem signatures for
`PLGeometry.akopyan_pl_nash_kuiper` in `Challenge.lean` and `Solution.lean`.
The definition blocks in `Challenge.lean` and
`Compatibility/Original.lean` also agree after removing comments and
normalizing whitespace. The target remains the original predicate requiring
an actual finite `Geometry.SimplicialComplex` in the original Euclidean
ambient space. It is not replaced by the archive's charted PL predicate.

## Empty and zero-dimensional cases

`approximation_equal_dimension` handles the empty underlying space before
choosing a source point or face. It takes `g = f` and the original geometric
complex as its subdivision. A purported nonempty face would provide a point
of the empty underlying space, so the cellwise conditions are vacuous.

All dimensions range over `ℕ`; neither the transfer nor the public theorem
assumes positive source or target dimension. The coordinate embedding in
`ModelDimension.lean` uses `d ≤ n`; the sphere uses the corresponding
embedding of the `(d + 1)`-dimensional vector space. The archive folding
induction has an explicit dimension-zero branch. In dimension zero,
spherical source cells cannot contain both antipodes: the original
finite-hull-preservation and injectivity axioms already rule this out.
No additional hemisphere premise is imposed on source charts.

## Intrinsic distance and disconnected sources

The original ball and sphere inherit their ambient topologies, but the
theorem uses the explicit `modelDist`, not the ambient chordal or Euclidean
distance on those subtypes. `Models.lean` proves both the homeomorphisms
and exact preservation of `modelDist`. The spherical angular metric and
the Klein hyperbolic metric are consequently retained in the final theorem.
There is no substitution of an ambient Euclidean metric for either one.

The transfer uses the original extended distance only through the proved
bound `intrinsicEDist ≤` the distance inside an original simplex. This
turns the original global Lipschitz hypothesis into the required cellwise
bound. It does not assume that an arbitrary original chart is an isometric
embedding for the global intrinsic distance. Conversion from `ENNReal` to
real numbers is made under a finite chart-distance bound; no cancellation
or finiteness assumption is used across different components.

After the initial finite folding, components are equivalence classes of
finite cell chains. There are finitely many classes because there are
finitely many covering cells. Each component is compact and receives the
proved chain metric with exactly its original subtype topology. This metric
agrees with chart distances on each folded cell, is a genuine metric, and
is intrinsic. Approximation is performed on each component with the same
positive error. Quotient representatives are used only to choose component
types; the covering and equality lemmas justify the final gluing. There is
no connectedness assumption in the public theorem.

## Spherical condition and change of dimension

The two original spherical alternatives are preserved: one uniform
constant `L < 1`, or a center at distance strictly below `π / 2` from every
image point. Model transport preserves the distance exactly. Component
restriction preserves the same constant and center. The archive's closed
hemisphere alternative is used by passing from `< π / 2` to `≤ π / 2`;
the public hypothesis remains the original open-hemisphere condition.

Raising the chart dimension leaves the embedded geometric complex
unchanged. `modelEmbedding_image_hull` verifies the full finite-hull chart
axiom. Segment distances and intrinsic extended distances are equal before
and after dimension enlargement; the original Lipschitz and PL-isometry
predicates are therefore equivalent. This is how the equal-dimension
transfer yields the public case `d ≤ n`.

## Actual finite geometric subdivision

For every refined charted cell, `embedded_refinement_hull` proves that its
image in the original ambient Euclidean space is precisely the convex hull
of its image vertices. The proof uses original chart injectivity and the
original finite-hull axiom together with model-cell rigidity. It does not
assume the original chart is affine.

`GeometricRealization` derives affine independence by Radon's theorem
applied to disjoint vertex subsets, proves the geometric intersection
condition, and constructs
an actual simplicial complex, removing only the empty face required by the
Mathlib convention. `geometric_piece` retains containment in an original
face and equality with that face's original model metric. Complexes from
different components have disjoint underlying spaces. `GeometricUnion`
therefore preserves the simplicial intersection axiom; its faces are finite,
its space is the entire original space, and each face has an originating
component. These are exactly the witnesses required by the original
`PLIsometry` definition.

The original predicate has no separate continuity field.
`Compatibility/PLContinuity.lean` proves `PLGeometry.PLIsometry.continuous`
from that predicate: distance equality gives continuity on every subdivision
cell through `modelEquiv`, and the finite closed cover gives continuity in
the original model topology. Thus continuity follows from the existing
geometric requirements; it is not an omitted additional assumption.

No `sorry`, `admit`, new `axiom`, or `unsafe` declaration occurs in
`Compatibility/` or `Solution.lean` in the reviewed sources.
