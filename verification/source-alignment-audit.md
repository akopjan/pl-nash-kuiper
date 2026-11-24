# Source alignment audit

Reviewed on 24 November 2026: `README.md`, `formalization.yaml`, and
`PROOF_GUIDE.md`, against the exact `Challenge.lean` and the public sources
listed below. No Lean file or target statement was changed.

## Alignment with the actual Challenge

The descriptions correctly specify all four central features:

- **Shortness:** `Lipschitz K f 1`, measured using the original intrinsic
  extended distance. Uniform strict shortness is a separate spherical
  alternative with one nonnegative real constant `L < 1`.
- **Dimensions:** natural numbers `d ≤ n`. The README and guide describe
  charts into the `d`-dimensional model; they do not require every source
  simplex to have dimension exactly `d`.
- **Finite PL subdivision:** an actual finite geometric simplicial complex
  in the original ambient Euclidean space, with the same underlying space,
  each new simplex contained in an original simplex, and equality of its
  original chart distances. Global injectivity is not required. Continuity
  follows from this predicate, as separately proved in `PLContinuity.lean`.
- **Spherical hypothesis:** uniform strict shortness **or** containment in
  an **open** hemisphere, expressed by distance `< π / 2`. The guide
  explicitly distinguishes the archive theorem's closed-hemisphere
  alternative from the original target's stronger hypothesis.

These are checks against the formal statement. They are not claims that
the inaccessible dissertation text has been independently compared word
for word with that statement.

## What the accessible primary texts confirm

**Akopyan–Tarasov (2008), p. 725.** The paper identifies short, weakly
contractive, and nonexpansive maps with distance-nonincreasing maps. It
defines a PL-isometry by continuity and a locally finite triangulation
whose simplex restrictions are motions. Its main theorem extends finite
short data in Euclidean, spherical, and hyperbolic model spaces. This is
the finite-extension result used by the archive, not a statement of the
target approximation theorem. On a compact source, local finiteness gives
finitely many cells; the present transfer additionally proves compatibility
with the original geometric subdivision.

Primary URLs:

- <https://users.mccme.ru/akopyan/papers/Kirszbraun%20Akopyan%20Tarasov.pdf>
- <https://doi.org/10.1134/S000143460811014X>

**Petrunin–Yashinski (2014), version 3.** Definition 0.2 gives the
distance-nonincreasing inequality. The preliminaries use finite simplicial
complexes; Lecture 1 defines piecewise distance preservation and records
the dimension obstruction. Theorem 3.2 proves planar approximation for PL
short maps. The final remarks state the higher-dimensional extension and
explain that the PL assumption on the input map can be removed. This
supports the Euclidean background cited in the project. It does not supply
the target's spherical alternative. The original unversioned arXiv URL now
selects version 4 from August 2026; `REFERENCES.md` and `formalization.yaml`
have therefore been corrected to pin the 2014 version.

Primary URLs:

- <https://arxiv.org/abs/1405.6606v3>
- <https://arxiv.org/html/1405.6606v3>
- <https://arxiv.org/pdf/1405.6606v3>

**Akopyan (2007) and the 2010 dissertation.** The author's publication
list confirms the 2007 preprint and links to the Möbius Contest PDF. That
PDF returned gateway/service errors during this review, so its theorem
wording was not directly checked. The RSL catalogue confirms the 2010
dissertation's title, Moscow publication, 75 pages, and Yaroslavl defence;
the author's homepage independently confirms the defence year and
institution. These bibliographic sources do not establish the wording of
Theorems 3.7, 3.17, and 3.18.

Primary URLs:

- <https://users.mccme.ru/akopyan/papers.html>
- <https://www.moebiuscontest.ru/files/2007/akopyan.pdf>
- <https://search.rsl.ru/ru/record/01004895074>
- <https://users.mccme.ru/akopyan/index.html>
- <https://search.rsl.ru/ru/record/01004615038> (public abstract catalogue)

## Remaining literature check

The exact spherical disjunction in the complete 2010 dissertation has
**not** been independently verified from an accessible primary full text.
The protected dissertation was not retrieved and its access restrictions
were not bypassed. A public OCR reproduction of the author's abstract
mentions Theorem 3.7 and its curved analogues 3.17 and 3.18, but does not
give the full spherical hypotheses; it was not used to certify the exact
inequalities or alternatives:
<https://fizmathim.com/diskretnye-transversali-vypuklyh-mnozhestv>.

The existing attribution “as cited by the original challenge” is therefore
appropriate and must be retained. No correction to the mathematical
description or to the original target is indicated by the sources actually
read. Comparator checks correspondence with that original formal
Challenge; it does not by itself certify equivalence with an unread
literary source.
