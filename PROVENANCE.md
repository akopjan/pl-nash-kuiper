# Source provenance and exact changes

## Supplied proof archive

Input: `palomar_pl_geometry (2).zip`.

SHA-256:
`e3b20bbab101552699c0e95df03f4d0c6772bd2767f216eb6c53f4ae266e4486`.

The 311 library modules under `BrehmApprox/`, `PLGeometry/`, and their root
entry points were copied from that archive. In non-import lines, the namespace
identifier `PLGeometry` was renamed to `ArchivePLGeometry`. Module paths and
import lines were retained. Every copied library file was compared against
that precise transformation; the per-file hashes and results are in
`verification/donor-source-comparison.json`.

The archive's old solution is available as `ArchiveSolution.lean`. Its old
statement template is preserved as `reference/ArchiveChallenge.lean.txt`;
its README and publication metadata are preserved as donor reference text.
Their four-target comparison surface is not the target of this transfer.
`verification-archive/` contains the donor's historical checks, with no claim
that they verify the new final theorem.

## Original statement

`reference/Challenge.original.lean.txt` preserves the complete original
Challenge source available in the conversation. Its SHA-256 is
`a273a7a2032317b02316776d38d7739a5cb5aac0600d0b81ba788fc31cedced3`.
The reference is not inferred from the donor's definitions.

The compiled `Challenge.lean` differs from that reference only by the
following enumerated elaboration and visibility repairs:

* opening the `NNReal` notation scope;
* declaring the inherited topology of each concrete model by cases;
* making `cell` and `segmentEDist` public so the two independent modules
  expose the same comparison dependencies;
* writing the already intended `Finset (E m)` types explicitly on the
  `Polyhedron.simplex` and `PLIsometry` existential binders.

The model distances, hulls, simplex axioms, finite polyhedron data, chain
distance, Lipschitz predicate, PL-isometry predicate, and final theorem
signature are unchanged. The final theorem's docstring is also retained.
`Compatibility/Original.lean` contains these same definitions on the proof
side, with no target placeholder and no import of `Challenge`.

`scripts/check-contract.py` verifies the reference hash, applies exactly the
listed repairs, compares the resulting full Challenge text, checks the
proof-side definitions and final theorem signature, and rejects proof-side
holes, axiom declarations, prohibited proof shortcuts, and Challenge imports.
The mathematical bridge is proved in the new `Compatibility/` modules.

## Current preparation

The transfer session began on 24 November 2026 at 15:26:51 UTC.
The current compiler and dependency revisions are recorded in
`lean-toolchain` and `lake-manifest.json`. Current build and proof-check
records are under `verification/`. Authorship, ownership, and license facts
not established by the supplied files have not been filled in.
