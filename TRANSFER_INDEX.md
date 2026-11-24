# Transfer index for reviewers

**Target:** `PLGeometry.akopyan_pl_nash_kuiper` — statement in
[`Challenge.lean`](Challenge.lean), proof in [`Solution.lean`](Solution.lean).
The proof-side original definitions are in
[`Compatibility/Original.lean`](Compatibility/Original.lean).

This index tracks the original Challenge. In particular,
`PLGeometry.Simplex.convex` preserves geodesic hulls of **every finite
subset of a cell**, not just its original vertices. The source may be
empty or disconnected; `PLGeometry.intrinsicEDist` takes values in
`ENNReal`, including `⊤`. Neither connectedness nor finiteness of every
pairwise intrinsic distance is an additional public hypothesis.

All declaration names below are fully qualified. File links name the
implementations; constructors include their required proof fields.

## Models, source charts, and shortness

| Original object or obligation | Exact Lean declarations | File |
| --- | --- | --- |
| Concrete model equivalence and inherited topology | `PLGeometry.modelEquiv`; `PLGeometry.modelHomeomorph`; `PLGeometry.modelHomeomorph_toEquiv` | [Models.lean](Compatibility/Models.lean) |
| Exact distance and finite geodesic-hull transport | `PLGeometry.modelEquiv_dist`; `PLGeometry.modelDist_modelEquiv_symm`; `PLGeometry.modelEquiv_image_hull` | [Models.lean](Compatibility/Models.lean) |
| Transport the original all-finite-subsets chart axiom; derive a spherical hemisphere | `PLGeometry.Simplex.archive_image_hull`; `PLGeometry.Simplex.spherical_hemisphere`; `PLGeometry.Simplex.spherical_cell_hemisphere` | [ModelHemisphere.lean](Compatibility/ModelHemisphere.lean) |
| Derive admissible model vertices from an original geometric simplex | `PLGeometry.affineIndependent_of_hull_preserving`; `PLGeometry.Simplex.archive_simplexVertices` | [SourceIndependence.lean](Compatibility/SourceIndependence.lean); [SourceVertices.lean](Compatibility/SourceVertices.lean) |
| Assemble the original finite source atlas, including chart topology and distances | `PLGeometry.Polyhedron.sourceCellHomeomorph`; `PLGeometry.Polyhedron.toArchiveChartedComplex`; `PLGeometry.Polyhedron.sourceChart_dist` | [SourceAtlas.lean](Compatibility/SourceAtlas.lean) |
| Relate the original extended distance to one cell | `PLGeometry.Polyhedron.intrinsicEDist_le_chart` | [SourceDistance.lean](Compatibility/SourceDistance.lean) |
| Original global Lipschitz bound implies cellwise bounds, also after refinement | `PLGeometry.Lipschitz.modelEquiv_cellwise`; `PLGeometry.Lipschitz.archive_refinement_cellwise` | [SourceShortness.lean](Compatibility/SourceShortness.lean); [SourceRefinementShortness.lean](Compatibility/SourceRefinementShortness.lean) |

## Components and compatible approximation

| Obligation | Exact Lean declarations | File |
| --- | --- | --- |
| Construct the initial finite small folding | `ArchivePLGeometry.FiniteChartedComplex.hasSmallFiniteFolding` | [FiniteFoldingExistence.lean](PLGeometry/FiniteFoldingExistence.lean) |
| A connected folded complex has a genuine intrinsic metric with its original topology and exact cell metrics | `PLGeometry.Compatibility.FoldedMetric.topology_eq`; `ArchivePLGeometry.FiniteChartedComplex.foldedIntrinsicMetric`; `ArchivePLGeometry.FiniteChartedComplex.foldedIntrinsicMetric_on_cell`; `ArchivePLGeometry.FiniteChartedComplex.isFinitePolyhedron_foldedIntrinsicMetric` | [IntrinsicMetric.lean](Compatibility/IntrinsicMetric.lean) |
| Restrict to the finitely many connected cell components | `ArchivePLGeometry.FiniteChartedComplex.componentIndex_finite`; `ArchivePLGeometry.FiniteChartedComplex.componentChartedComplex`; `ArchivePLGeometry.FiniteChartedComplex.componentChartedComplex_connected` | [SourceComponents.lean](Compatibility/SourceComponents.lean) |
| Components cover the source, are disjoint, and permit function gluing | `ArchivePLGeometry.FiniteChartedComplex.indexedComponent_cover`; `ArchivePLGeometry.FiniteChartedComplex.indexedComponent_disjoint`; `ArchivePLGeometry.FiniteChartedComplex.glueComponents_apply` | [SourceComponents.lean](Compatibility/SourceComponents.lean) |
| An archive PL-isometry has a finite refinement compatible with a finite intrinsic triangulation carrying a small folding | `PLGeometry.Refined.refinement_of_plIsometry` | [PLRefinement.lean](Compatibility/PLRefinement.lean) |
| Approximate on a connected component while retaining refinement, cellwise isometry, and the error bound | `PLGeometry.Compatibility.approximate_connected`; `PLGeometry.Compatibility.approximate_component` | [ConnectedApproximation.lean](Compatibility/ConnectedApproximation.lean); [ComponentApproximation.lean](Compatibility/ComponentApproximation.lean) |

The shortness transfer needs only `intrinsicEDist_le_chart`; it does not
identify an arbitrary original chart distance with the global intrinsic
distance. Genuine metric spaces are constructed on the folded components.
The original spherical alternative remains uniform strict shortness or an
**open** hemisphere; the latter implies the archive's closed-hemisphere
condition by the elementary implication `< π / 2 → ≤ π / 2`.

## Return to the exact original conclusion

| Obligation | Exact Lean declarations | File |
| --- | --- | --- |
| Each component refinement retains an original containing face and its metric | `PLGeometry.Polyhedron.component_refinement` | [ComponentRefinement.lean](Compatibility/ComponentRefinement.lean) |
| Refined cells become actual convex hulls in the original ambient space | `PLGeometry.Polyhedron.embedded_refinement_hull`; `PLGeometry.Polyhedron.geometric_piece` | [EmbeddedRefinement.lean](Compatibility/EmbeddedRefinement.lean) |
| Construct a finite geometric complex whose space is the range of the component embedding | `PLGeometry.ChartedRealization.complex`; `PLGeometry.ChartedRealization.complex_finite`; `PLGeometry.ChartedRealization.complex_space` | [GeometricRealization.lean](Compatibility/GeometricRealization.lean) |
| Unite the disjoint component complexes, retaining finiteness, space equality, and face origin | `PLGeometry.GeometricUnion.complex`; `PLGeometry.GeometricUnion.complex_finite`; `PLGeometry.GeometricUnion.complex_space`; `PLGeometry.GeometricUnion.face_origin` | [GeometricUnion.lean](Compatibility/GeometricUnion.lean) |
| Equal-dimension conclusion, including the explicit empty-source branch and component assembly | `PLGeometry.Compatibility.approximation_equal_dimension` | [Transfer.lean](Compatibility/Transfer.lean) |
| Enlarge chart dimension without changing finite hulls or model distances | `PLGeometry.modelEmbedding_dist`; `PLGeometry.modelEmbedding_image_hull`; `PLGeometry.Polyhedron.raiseDimension` | [ModelDimension.lean](Compatibility/ModelDimension.lean) |
| Preserve the original extended distance and predicates when `d ≤ n` | `PLGeometry.Polyhedron.intrinsicEDist_raiseDimension`; `PLGeometry.Polyhedron.lipschitz_raiseDimension_iff`; `PLGeometry.Polyhedron.plIsometry_raiseDimension_iff` | [ModelDimension.lean](Compatibility/ModelDimension.lean) |
| Conclude the original unified theorem | `PLGeometry.akopyan_pl_nash_kuiper` | [Solution.lean](Solution.lean) |
| Continuity follows from the original PL predicate, without adding a field or hypothesis | `PLGeometry.PLIsometry.continuous` | [PLContinuity.lean](Compatibility/PLContinuity.lean) |

For the proof narrative, see [PROOF_GUIDE.md](PROOF_GUIDE.md). Mathematical
edge cases and literature alignment are reviewed in
[transfer-mathematical-audit.md](verification/transfer-mathematical-audit.md)
and [source-alignment-audit.md](verification/source-alignment-audit.md).
Actual command outcomes are recorded in
[verification/SUMMARY.md](verification/SUMMARY.md).
