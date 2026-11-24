# Piecewise isometries in constant curvature

This Lean 4 development concerns finite piecewise isometric extension and
uniform PL approximation in Euclidean, spherical, and hyperbolic geometry.
The public statements and the complete definition of a PL-isometry are in
[`Challenge.lean`](Challenge.lean).

**Proof status:** all four public declarations are proved in Lean. The
finite-extension theorems, protected-net construction, finite-folding
induction, and approximation arguments are included in the source.
[`PROOF_GUIDE.md`](PROOF_GUIDE.md) explains the construction and its two
inductions. See [`PUBLICATION.md`](PUBLICATION.md) and `verification/` for
the recorded checks and the publication metadata still requiring an owner.

## Mathematical statements

Let $M_\kappa^n$ denote Euclidean space, the round unit sphere with its angular
distance, or hyperbolic space of curvature $-1$, according as
$\kappa=0,1,-1$. A map is **short** if it is $1$-Lipschitz.

A **PL-isometry** is a continuous map that preserves distances on each simplex
of some locally finite geodesic triangulation of its source. The simplices
are genuine nondegenerate model simplices; their intersections are common
faces. Global injectivity is not required. A finite polyhedral source carries
the intrinsic metric obtained by taking infima of lengths of finite chains
whose consecutive points lie in a common simplex.

**Brehm–Akopyan–Tarasov extension theorem.** Let $A\subset M_\kappa^n$ be a
finite set and let $f:A\to M_\kappa^n$ be short. There is a short PL-isometry
$F:M_\kappa^n\to M_\kappa^n$ whose restriction to $A$ is $f$.

**Euclidean PL Nash–Kuiper theorem.** Let $P$ be a finite intrinsic Euclidean
polyhedral space of dimension at most $d$, let $d\le n$, and let
$f:P\to\mathbb R^n$ be short. For every real number $\varepsilon>0$, there
is a short PL-isometry $g:P\to\mathbb R^n$ with
$d(g(x),f(x))<\varepsilon$ for every point $x\in P$.

**Spherical PL Nash–Kuiper theorem.** Let $P$ be a finite intrinsic spherical
polyhedral space of dimension at most $d$, let $d\le n$, and let
$f:P\to S^n$ be short. Suppose that either $f$ has a Lipschitz constant
strictly smaller than one or $f(P)$ is contained in a closed hemisphere.
Then, for every $\varepsilon>0$, there is a short PL-isometry
$g:P\to S^n$ with $d(g(x),f(x))<\varepsilon$ for every $x\in P$.

**Hyperbolic PL Nash–Kuiper theorem.** Let $P$ be a finite intrinsic
hyperbolic polyhedral space of dimension at most $d$, let $d\le n$, and
let $f:P\to H^n$ be short. For every $\varepsilon>0$, there is a short
PL-isometry $g:P\to H^n$ with $d(g(x),f(x))<\varepsilon$ for every
$x\in P$.

The four Lean names are:

| Mathematical statement | Challenge declaration |
| --- | --- |
| Finite extension in all three geometries | `PLGeometry.brehm_akopyan_tarasov` |
| Euclidean approximation | `PLGeometry.pl_nash_kuiper_euclidean` |
| Spherical approximation | `PLGeometry.pl_nash_kuiper_spherical` |
| Hyperbolic approximation | `PLGeometry.pl_nash_kuiper_hyperbolic` |

## Formal organization

`Challenge.lean` imports only Mathlib. It gives concrete metric models,
geodesic hulls, compatible triangulations, the intrinsic source metric,
`PLGeometry.PLIsometry`, and the four theorem statements. Its deliberate
proof holes belong to the statement side of the Comparator protocol.

`PLGeometry/Definitions.lean` contains the same public geometric definitions
using the library's proved model metrics. `PLGeometry/Basic.lean` proves
that model cells and finite sources are compact, constructs the actual cell
isometry equivalences, and identifies the intrinsic metric with the cell-chain
condition used by the approximation machinery.

The `BrehmApprox` library develops finite extension through bounded Euclidean
folding, finite motion selection, affine arrangements, spherical central
charts, and the hyperbolic Pogorelov transformation. Its approximation
theorems construct and glue model-isometric polyhedral pieces.
`PLGeometry/ProtectedNetExistence.lean` constructs protected nets on arbitrary
finite charted complexes. `PLGeometry/FiniteFoldingExistence.lean` proves
the universal small-folding theorem by dimension induction.
`PLGeometry/PLNashKuiper.lean` then proves all three approximation statements
for arbitrary finite intrinsic polyhedral sources.

`Solution.lean` is the proof-side entry point. `PLGeometry.lean` also exports
the complete public API. The four target proofs have no geometric axioms or
initial-folding assumptions. `comparator.json` permits exactly `propext`,
`Classical.choice`, and `Quot.sound`. Comparator also checks the six model
metric laws whose proof positions are left open in the standalone Challenge;
no definition is registered as a hole.

## Recorded verification

The full Lean build and all ten registered theorem audits passed. The local
Comparator run also passed statement matching and replay in con-ron, NanoDa,
and Lean's default kernel. It used `--inadvisably-no-sandbox` because the
workspace could not start Comparator's nested `bubblewrap` sandbox. The
standard sandboxed check remains in CI. The exact records are in
[`verification/SUMMARY.md`](verification/SUMMARY.md).

## Reproduce the checks

Install Lean through the [official installation guide](https://lean-lang.org/install/)
if `lean` and `lake` are not yet available. The version manager `elan` selects
the toolchain specified by this project. Python 3 is used for the audit
scripts; the proof build itself is performed by Lean and Lake.

The toolchain is pinned in `lean-toolchain`. The exact dependency revisions
are committed in `lake-manifest.json`; retain that file.

```sh
elan toolchain install leanprover/lean4:v4.36.0
lake exe cache get
python3 verify.py
```

`verify.py` runs the build, the source checks, and the public theorem axiom
audits. It writes the actual command statuses, logs, and source hashes to
`verification/`. With a separately installed toolchain, use
`python3 verify.py --lake ./lakew` and set `LEAN_BIN` to its `bin` directory.

The source check verifies module headers and size limits. The contract check
verifies the standalone Challenge imports and rejects proof-side `sorry`,
`admit`, and additional axiom declarations. The solution check asks Lean to
resolve each requested theorem and print its transitive axiom dependencies.
It rejects missing declarations and every dependency outside the three
permitted logical axioms.

For metadata and the independent-kernel check:

```sh
python3 -m pip install -r scripts/requirements.txt
python3 scripts/check-publication.py
./scripts/verify-comparator.sh
```

The Comparator script requires `bubblewrap` and the `lake comparator`,
`leanexport`, `leanchecker`, `nanoda_bin`, and `con-ron` executables from the
pinned Lean toolchain. It uses the same bundled independent kernels as the
Palomar submission workflow. It must not be replaced by a source-text scan.

## Sources

1. Ulrich Brehm, *Extensions of distance reducing mappings to piecewise
   congruent mappings on* $\mathbb R^m$, Journal of Geometry **16** (1981),
   187–193. [DOI: 10.1007/BF01917587](https://doi.org/10.1007/BF01917587).
2. Arseniy V. Akopyan and Aleksey S. Tarasov, *A Constructive Proof of
   Kirszbraun's Theorem*, Mathematical Notes **84** (2008), 725–728.
   [DOI: 10.1134/S000143460811014X](https://doi.org/10.1134/S000143460811014X).
3. Arseniy V. Akopyan, *A PL-analogue of the Nash–Kuiper theorem*, preprint
   (2007). [Author's publication list](https://users.mccme.ru/akopyan/papers.html)
   and [preprint](https://www.moebiuscontest.ru/files/2007/akopyan.pdf).

4. Anton Petrunin and Allan Yashinski, *Lectures on piecewise distance
   preserving maps* (2014). [arXiv:1405.6606](https://arxiv.org/abs/1405.6606).
   Background on finite extension, folding, and PL approximation.

The preparation follows the current
[Palomar submission instructions](https://palomar-registry.org/how-to-submit),
[repository policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
and [formalization.yaml v0.4 specification](https://github.com/mathlib-initiative/formalization.yaml).
Once all release conditions hold, submissions go to
<https://submit.palomar-registry.org/>.
