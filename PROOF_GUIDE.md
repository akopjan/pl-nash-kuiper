# Proof guide

The public theorem is `PLGeometry.akopyan_pl_nash_kuiper`.
`Challenge.lean` contains its embedded-polyhedron formulation;
`Solution.lean` proves that same statement. The core geometric library lives in
`BrehmApprox/` and `PLGeometry/` (internal namespace `ArchivePLGeometry`), and
the `Compatibility/` modules connect the definitions in `Challenge.lean` to
this library.

## The original unified theorem

Let $d,m,n$ be natural numbers with $d\leq n$, and let
$\kappa$ be a real number in $\{0,1,-1\}$ specifying the curvature. Let $K$ be a finite geometric
simplicial complex in $\mathbb R^m$, and let $P=|K|$ be its underlying
topological space. Each simplex has a
continuous injective chart into the model space $M_\kappa^d$, preserving
geodesic hulls of all finite subsets. The chart metrics agree on common
faces. These are precisely the data in `PLGeometry.Polyhedron`.

The original models are Euclidean space, the unit Klein ball with its
hyperbolic distance, and the unit sphere with its angular distance. The
intrinsic extended distance on $P$ is the infimum of lengths of finite
cell chains. It may be infinite between different components. Let
$f:P\to M_\kappa^n$ be short for this distance. In the spherical case,
assume either one nonnegative real global Lipschitz constant $L<1$ or a
point $o\in S^n$ satisfying $\operatorname{dist}(f(x),o)<\pi/2$ for every
$x\in P$.

For every real $\varepsilon>0$, the theorem produces a map
$g:P\to M_\kappa^n$ with $\operatorname{dist}(g(x),f(x))<\varepsilon$ for
every $x\in P$.
Its PL-isometry witness is an actual finite geometric simplicial complex
$T$ in the same $\mathbb R^m$, with $|T|=|K|$. Every simplex of $T$ lies in
a simplex of $K$, and $g$ preserves the original chart metric there.
The source may be empty or disconnected, and zero dimensions are allowed.
Continuity follows from this original PL predicate:
`Compatibility/PLContinuity.lean` proves `PLGeometry.PLIsometry.continuous`
by gluing over the finitely many closed subdivision cells.

## Bridges to the completed library

`Compatibility/Models.lean` gives explicit equivalences of the concrete
model spaces. The Euclidean map is the identity; the spherical map passes
from the unit-sphere subtype to the angular-metric wrapper; the hyperbolic
map is the inverse Klein map to
hyperboloid spatial coordinates. These maps are homeomorphisms and preserve
model distances and finite geodesic hulls exactly. Thus passing between
models preserves the numerical approximation error.

The original charts are not assumed affine. `SourceIndependence.lean`,
`ModelHemisphere.lean`, and `SourceVertices.lean` derive the vertex
independence required by the geometric library. A dependence among image vertices
would give intersecting hulls of disjoint source faces, contradicting chart
injectivity. For a
spherical chart, an antipodal image pair is impossible: its positive
spherical hull has only two points, while the source segment has a distinct
midpoint. A positive dependence producing zero would force such an
antipodal pair. Separation from zero then gives an open hemisphere, and
gnomonic coordinates reduce independence to the affine argument.
`SourceAtlas.lean` consequently constructs a finite charted complex from
exactly the original chart axioms.

The original global shortness hypothesis implies shortness on every source
cell, since the intrinsic extended distance is at most its single-cell
length. `SourceDistance.lean`, `SourceShortness.lean`, and
`SourceRefinementShortness.lean` prove this implication and its preservation
under charted refinement. No equality between an arbitrary original chart
metric and the global intrinsic metric is assumed.

The small-folding theorem gives a finite charted refinement and a
continuous map that is isometric on each refined cell. `IntrinsicMetric.lean`
uses it to construct a genuine chain metric on each connected cell
component. A compact-star argument separates distinct points; finite
closed gluing identifies the metric topology with the original topology.
The metric agrees with chart distance on each refined cell and is generated
by finite cell chains. `SourceComponents.lean` proves that there are only
finitely many components, including their covering and disjointness
properties.

`ConnectedApproximation.lean` and `ComponentApproximation.lean` apply the
completed approximation theorems to these metric components. The original
strict spherical constant restricts unchanged to every component; an
original open hemisphere satisfies the closed-hemisphere
alternative. A finite refinement compatible with the initial folded cells
is obtained from ambient model motions on cell intersections and their
finite polyhedral arrangement; `SetRigidity.lean`, `RefinedPL.lean`, and
`PLRefinement.lean` prove this additional containment requirement.

`EmbeddedRefinement.lean` proves that every resulting cell is the ordinary
convex hull of its vertices in the original Euclidean ambient space. It
uses the original all-finite-subsets hull axiom and injectivity to pull
model-cell hull equality back to that space. `GeometricRealization.lean`
then proves affine independence and the geometric intersection condition,
constructing a finite `Geometry.SimplicialComplex`.
`ComponentRefinement.lean` retains the original containing face and its
metric. `GeometricUnion.lean` unites the disjoint component complexes.
`Transfer.lean` supplies the final geometric subdivision and pointwise
error bound in equal model dimension, handling the empty source directly.

Finally, `ModelDimension.lean` transports coordinate embeddings through
the model equivalences. Raising the chart dimension from $d$ to $n$ keeps
the original embedded complex, all segment distances, and the intrinsic
extended distance unchanged. It preserves the original Lipschitz and
PL-isometry predicates. `Solution.lean` uses these equalities to deduce the
unified theorem for every $d\leq n$.

### Why the component chain distance separates points

Let $P$ be a Hausdorff topological space, let $I$ be a finite index set,
and let $C_i\subset P$, for $i\in I$, be compact sets covering $P$.
Let $E$ be a metric space and let $q:P\to E$ be a continuous map
injective on each cell. Assume that any two points of $P$
are joined by a finite cell chain; in the application, $P$ is one cell-chain
component. Fix a point $p\in P$. Let $A_p\subset P$
be the union of cells containing $p$, and let $B_p\subset P$ be the union
of the other cells. Both sets are compact. Cellwise injectivity implies
$q(p)\notin q(A_p\cap B_p)$, so there is a real number $R>0$ such that
$\operatorname{dist}(q(p),q(x))\geq R$ on $A_p\cap B_p$.
Define a function $\varphi_p:P\to\mathbb R$ by

$$
\varphi_p(x)=
\begin{cases}
\min\{R,\operatorname{dist}(q(p),q(x))\},&x\in A_p,\\
R,&x\notin A_p.
\end{cases}
$$

On each cell containing $p$, this is a truncated distance function. On
every other cell it is constant. Hence
$|\varphi_p(x)-\varphi_p(y)|\leq\operatorname{dist}(q(x),q(y))$
whenever $x,y$ lie in one cell. Moreover, $\varphi_p(p)=0$ and
$\varphi_p(y)>0$ for every $y\ne p$. Summing along any cell chain from
$p$ to $y$ gives a positive lower bound for its cost. The infimum of those
costs therefore separates points. Cell-chain connectedness ensures that
the set of chain costs is nonempty and bounds its infimum above by the
cost of one finite chain.

The chain metric equals $\operatorname{dist}(q(x),q(y))$ on each cell:
the triangle inequality gives one bound, and the single-cell chain gives
the other. Thus the identity map from the original topology to the metric
topology is continuous on every cell, and finite closed gluing makes it
continuous globally. Compactness of $P$ then makes this bijection a
homeomorphism. These are the separation and topology arguments formalized
in `Compatibility/IntrinsicMetric.lean`.

## The core geometric library

The remainder of this guide describes the geometric library in `BrehmApprox/`
and `PLGeometry/` (internal namespace `ArchivePLGeometry`). Its metric models
use Euclidean distance, spherical angular distance, and the hyperboloid
distance.

## Geodesic simplices and PL-isometries

Let $M_\kappa^n$ be the model space of dimension $n$
and curvature $\kappa\in\{0,1,-1\}$. A geodesic simplex is specified by
finitely many independent vertices. In the spherical case the vertices lie
in an open hemisphere. Its underlying set is their Euclidean convex hull,
positive spherical hull, or positive Lorentz hull, as appropriate.

Let $P$ be a metric space. A triangulation of $P$ consists of geodesic
simplex charts which are isometric on their cells, cover $P$, contain all
faces, and agree on the incidence of faces. Distinct cells meet along their
common face. The family of cells is locally finite.

A map $g:P\to M_\kappa^n$ is a PL-isometry if it is continuous and isometric
on every simplex of some such triangulation. It may fold different simplices
onto the same region. For the approximation theorems, the source metric is
intrinsic: finite chains lying successively in cells approximate the distance
between their endpoints. Thus a continuous map that is short on every cell
is globally short.

## Finite piecewise isometric extension

Let $A\subset M_\kappa^n$ be finite, and let $f:A\to M_\kappa^n$ be short.
The extension theorem constructs a global short PL-isometry which agrees
with $f$ on $A$.

The Euclidean argument interpolates the prescribed points successively.
A bounded folding supplies the initial map. At each step a radial correction
preserves the previous interpolation conditions and enforces the next one.
The correction is realized by model motions on polyhedral regions. Affine
arrangements and compatible triangulation of those regions turn this motion
selection into the locally finite geodesic triangulation required by the
public definition.

For the sphere, a Euclidean extension in one more dimension fixes the
origin. Its sufficiently small radial germ is realized by orthogonal maps.
Restriction to unit vectors gives a spherical piecewise isometry. The
finite interpolation conditions, shortness, and compatibility of the
spherical cells are proved explicitly.

For hyperbolic space, the Pogorelov pair transformation converts the finite
short-data problem into its Euclidean counterpart. The inverse construction
produces Lorentz motions on hyperbolic polyhedral regions. Their refinement
gives the required hyperbolic geodesic triangulation.

The extension theorem declaration is
`ArchivePLGeometry.brehm_akopyan_tarasov`. The three
model-level extension theorems are `BrehmApprox.euclideanBrehm`,
`BrehmApprox.sphericalBrehm`, and `BrehmApprox.hyperbolicBrehm`.

## Protected nets

Let $T$ be a finite charted complex on $P$, and let $\eta>0$ be a real number.
A finite set $S\subset P$ is a cellwise $\eta$-net if every point of each
cell lies at chart distance less than $\eta$ from a site in the same cell.
The net is protected if every nearest site, computed within any incident
cell, to a point of a face belongs to that face. All nearest sites are
covered by this condition, including ties.

The construction first treats small neighborhoods of a point $p\in P$.
The stellar link at $p$ has genuine spherical charts, with face incidence
inherited from $T$. Protected angular nets in the link and a common finite
radial grid yield a protected net in the neighborhood. The cosine laws make
a strict improvement in angular distance a strict improvement in model
distance at positive radii. A finite open-star cover then assembles these
local grids into one protected net.

This is an induction on the maximum number of vertices of a face. Every
face of a stellar link has fewer vertices. This measure decreases even when
the chosen spherical ambient space does not change.

For spherical source cells, an affine chart is needed on the whole simplex.
Let $V\subset S^n$ be its vertex set, let $p$ belong to its spherical
hull, and choose a linear functional $\ell:\mathbb R^{n+1}\to\mathbb R$
with $\ell(v)=1$ for all
$v\in V$. Positivity gives $\ell(x)>0$ throughout the cell. The map

$$
 x\longmapsto \frac{x-\langle p,x\rangle p}{\ell(x)}
$$

is injective on the cell, sends $p$ to zero, and carries every spherical
face onto an affine face. For $x\ne p$, its normalized value is the tangent
direction at $p$. This supplies the visible-boundary argument used in the spherical
polar-coordinate construction.

The final net theorem is
`ArchivePLGeometry.FiniteChartedComplex.exists_protected_net`.

## Finite foldings into arbitrarily small balls

Let $T$ be a finite charted complex with model dimension $n$. The
construction of a small folding is an induction on $n$; the case $n=0$
is immediate. Choose a sufficiently fine protected net and its Voronoi
cells. Protection makes the Voronoi data compatible with all old faces.

The sets where nearest sites tie form finite polyhedral pieces. Their
angular realizations carry charts in $S^{n-1}$, and their transition metrics agree.
By the induction hypothesis this angular complex has a finite PL folding.
A compatible refinement of the tie pieces is then coned to their nearest
sites.

All sites are mapped to one chosen pole. A point on a conical base is mapped
at its original nearest-site radius in the direction prescribed by the
angular folding. Preserving angular distances and each radial coordinate
preserves model distances. The Euclidean, spherical, and hyperbolic cosine laws prove
this assertion uniformly.

Consequently the proposed images of the vertices of each conical simplex
have exactly the original pairwise distances. A model isometry realizes
these images on the simplex. Rigidity on common faces makes the resulting
maps agree; finite closed gluing proves continuity. The nearest-site radius
bounds the entire image, so the folding lies in the prescribed small ball.
The construction supplies a genuine finite refinement of $T$.

The two final declarations are
`ArchivePLGeometry.FiniteChartedComplex.hasSmallFiniteFolding` and
`ArchivePLGeometry.IsFinitePolyhedron.exists_small_plIsometry`.

## Uniform approximation

Let $P$ be a finite intrinsic polyhedral space, and let
$f:P\to M_\kappa^n$ be short. The small-folding theorem supplies the initial
model-isometric charts needed by the relative approximation construction.
Finite Brehm interpolation, local approximation on charted pieces, and
compatible gluing give a PL-isometry $g$ within any prescribed positive
uniform error. The intrinsic metric turns cellwise shortness into global
shortness. Model embeddings allow the target dimension to exceed the source
dimension.

In the spherical case the argument applies when $f$ has one global
Lipschitz constant below one, or when its image is contained in a closed
hemisphere. These alternatives are stated explicitly in the internal
spherical theorem.

The final declarations are `ArchivePLGeometry.pl_nash_kuiper_euclidean`,
`ArchivePLGeometry.pl_nash_kuiper_spherical`, and
`ArchivePLGeometry.pl_nash_kuiper_hyperbolic`. Their statements assume no initial
folding, protected net, angular triangulation, or geometric extension axiom.

## Verification

The intended proof dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. `AxiomAudit.lean` prints the actual transitive dependencies of
the public declarations and the principal constructions. `verify.py` runs the
local build and axiom checks, and Palomar Comparator checks that the Solution
proves the Challenge statement and replays the exported proof.
