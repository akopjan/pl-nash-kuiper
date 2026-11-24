# Palomar publication record

The proof-side entry point is [`Solution.lean`](Solution.lean). It proves
the single original theorem `PLGeometry.akopyan_pl_nash_kuiper`, using
the original definitions and a proved bridge to the completed geometric
library. This source package has not been submitted to Palomar.
The current build and audit results are recorded in
[`verification/SUMMARY.md`](verification/SUMMARY.md).

## Exact challenge contract

`Challenge.lean` is a standalone statement file importing only Mathlib.
It defines the Euclidean, Klein hyperbolic, and spherical models, finite
embedded polyhedra, the intrinsic extended distance, and the original
finite-subdivision predicate `PLIsometry`.

The target assumes $d\leq n$ and global shortness. In the spherical case it
retains the original alternative: a uniform Lipschitz constant strictly
smaller than one, or containment in an **open hemisphere**, expressed as
`modelDist κ n (f x) o < Real.pi / 2`. Its conclusion provides a finite
geometric subdivision in the same ambient Euclidean space, with the exact
original chart metric preserved on every refined simplex. Empty and
disconnected sources are supported.

There is exactly one intentional statement-side placeholder in
`Challenge.lean`. No definition is registered as a hole. The proof side
imports no Challenge module, contains no proof placeholders or newly
declared axioms, and adds no assumptions to the original theorem.
`comparator.json` selects only `PLGeometry.akopyan_pl_nash_kuiper` and
permits exactly `propext`, `Classical.choice`, and `Quot.sound`.

`Compatibility/Original.lean` repeats the original definitions for the proof
side. The `Compatibility/` proofs establish model equivalence, the source
atlas, intrinsic metrics on finite components, approximation, and the
required geometric subdivision. In particular, an initial folding and
simplex independence are derived rather than assumed.
[`PROOF_GUIDE.md`](PROOF_GUIDE.md) explains this construction.

The supplied challenge is preserved in
`reference/Challenge.original.lean.txt`. `scripts/check-contract.py` accepts
only the enumerated visibility and elaboration repairs and checks the target
signature and proof-side definitions against that reference.
[`PROVENANCE.md`](PROVENANCE.md) records those repairs and the donor source
provenance. All 311 retained donor modules are unchanged except for the
namespace renaming to `ArchivePLGeometry`, as recorded in
`verification/donor-source-comparison.json`.

## Verification evidence and its limits

The authoritative status for this transfer is
[`verification/SUMMARY.md`](verification/SUMMARY.md), together with the
command logs and result files it references. Reproduce the ordinary build,
source contract, and transitive axiom audit with `python3 verify.py`.

`python3 scripts/verify-kernels.py --lake lake` performs a fresh build and
proof export, a read-only comparison of the exported Challenge and Solution
types, and independent proof replay using the pinned toolchain's con-ron,
NanoDa, and Lean kernels. It records each command's actual exit status in
`verification/kernel-results.json`. These checks are recorded separately
from the standard sandboxed Comparator; they are not a Palomar acceptance
certificate.

The standard sandboxed Comparator was attempted in this workspace. It
stopped with `bwrap: Failed to mount tmpfs: No such file or directory` before
judging the solution. The attempt is recorded in
`verification/comparator-sandbox-final.log` and its adjacent result
JSON. A successful standard sandboxed run remains required on a supported
host. `scripts/verify-comparator.sh` and the GitHub Actions workflow retain
that invocation.

The donor archive's verification claims are preserved only as historical
reference material. Its older target list, statement checks, and kernel
logs do not certify the new transfer. Consult the current summary for
completed, failed, or pending checks; no success is inferred from the
presence of a verification script.

## Publication information requiring an owner

The supplied files do not establish the formalization authors' names, the
responsible maintainer's name, or an authorized project licence.
Consequently `project.authors`, `project.responsible_maintainers`, and
`project.license` in `formalization.yaml` remain empty. The metadata check
also reports the missing root `LICENSE` file.

The owner must provide the actual credited people and select an authorized
SPDX licence identifier with the corresponding `LICENSE` text. Third-party
notices and licences are recorded separately in `THIRD_PARTY_NOTICES.md`
and `licenses/`; they do not determine the licence of this project.
The submission also needs the intended public GitHub repository and its
full immutable 40-character commit hash. No repository ownership or human
referee review is claimed by this package.

## Submission sequence

1. Supply the authorship, responsible maintainer, and licence information,
   add `LICENSE`, and run `python3 scripts/check-publication.py`.
2. Run `python3 verify.py`, then
   `python3 scripts/verify-kernels.py --lake lake`, and obtain a successful
   standard sandboxed check with `./scripts/verify-comparator.sh`.
3. Publish the checked source in the intended public GitHub repository,
   including the toolchain and dependency lockfile. Record the full commit
   hash and ensure that the checks refer to that exact source revision.
4. Submit the repository and immutable commit at
   <https://submit.palomar-registry.org/>.

The package includes the proof source, original challenge, pinned dependency
revisions, Comparator configuration, audit scripts, CI workflow, proof guide,
metadata, and recorded verification evidence. Compiler binaries and the
Mathlib cache are obtained during reproduction and are not part of the
source release.
