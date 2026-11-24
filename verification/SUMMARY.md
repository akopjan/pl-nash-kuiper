# Verification of the original Akopyan challenge

## Checked theorem

The sole publication target is `PLGeometry.akopyan_pl_nash_kuiper`, with the
original source `Polyhedron`, intrinsic extended distance, `Lipschitz`, and
`PLIsometry` definitions. It includes all three geometries, arbitrary
`d ≤ n`, and the original strict-shortness or **open**-hemisphere condition
in the spherical case.

`scripts/check-contract.py` checks the final theorem signature against the
preserved original challenge and checks every original definition. The
reference SHA256 is:

```text
a273a7a2032317b02316776d38d7739a5cb5aac0600d0b81ba788fc31cedced3
```

The only permitted edits to the statement template are the explicit
elaboration and visibility repairs: open the `NNReal` scope; provide the
canonical topology on `Model κ n`; annotate two finite-set binders; and
expose `cell` and `segmentEDist` for use from separate proof modules. The
checker enumerates these replacements and rejects any other change.

The proof side contains no `sorry`, `admit`, additional axiom declaration,
`sorryAx`, `unsafe`, `implemented_by`, or `native_decide`. It imports no
challenge template. The sole deliberate `sorry` in `Challenge.lean` is the
statement-side target that Comparator is meant to compare with the proved
declaration in `Solution.lean`. The archived templates are stored as
`.lean.txt`, outside the proof modules.

## Build and dependency audit

The complete default build succeeded. Its coverage was then extended to
include `ArchiveSolution`, `Compatibility.GeometricRefinement`, and
`Compatibility.PLContinuity` explicitly; that final default configuration
also passed, with **18,933 Lake jobs**. The coverage correction changed no
Lean sources or proof exports. There are **339 compiled project modules**;
`AxiomAudit.lean` and `scripts/CompareExports.lean` were checked directly,
giving coverage of **all 341 Lean files**. Source-policy and source-contract
checks passed.

The actual build/audit commands, timestamps, and exit codes are in
`results.json`; the full build output is in `build.log`. The subsequent
coverage check is recorded in `default-coverage-build-result.json` and
`default-coverage-build.log`. Warnings about
style, unused variables, or deprecated tactic names remain visible in the
logs. There are no compilation errors.

Lean reports exactly these transitive axioms for the original target:

```text
[propext, Classical.choice, Quot.sound]
```

The main approximation theorems from the archive, finite-folding theorem,
and constructed intrinsic metric have the same standard axiom list. The
reports are in `axioms.log`, `solution-check.log`, and `kernel-axioms.log`.

## Fresh export comparison and kernel replay

Fresh exports were produced from the built `Challenge` and `Solution`
modules. The solution export SHA256 is:

```text
93d951ebc3cbdbe3c0817d4606a6961339399210c4c2ba43198c90030f2355a0
```

The challenge export SHA256 is:

```text
d0117925d2f08a080baf6e745a649bd78bd0c7ecedaaff11725dc1d329c32bfe
```

`kernel-export-manifest.json` records these hashes, the source-file hashes,
the statement hash, and the pinned toolchain and dependency manifest. The
exported data are reproducible and are omitted from the source archive
because of their size.

| Check | Observed result |
|---|---|
| Toolchain `Lake.Check.compareAt` | Original theorem and all referenced definitions match; exit 0. |
| Toolchain `Lake.Check.checkAxioms` | Only `propext`, `Quot.sound`, and `Classical.choice`; exit 0. |
| con-ron | **50,246 declarations accepted**, `--verified`, `--jobs=4`; exit 0. |
| NanoDa | **52,270 declarations checked, zero typechecker errors**; exit 0. |
| Lean default kernel | Fresh NDJSON replay accepted, including quotient post-check; exit 0. |

The original NanoDa run printed `Unable to print axioms`: axiom printing
was enabled by default, but no output destination was configured. The exact
source branch and its separation from typechecking and axiom admission are
documented in `nanoda-warning.md`. The reproducer now sets `pp_to_stdout=true`.
A supplemental run on the identical export printed `propext`, `Quot.sound`,
and `Classical.choice`, and accepted all **52,270 declarations with no
errors**: zero typechecker and zero pretty-printer errors, exit 0. Its
separate records are `kernel-nanoda-with-axioms.log` and
`kernel-nanoda-with-axioms.json`. The strict axiom gate remained enabled;
the original warning log and original three-kernel receipts are preserved.

The final kernel replay completed at **2026-11-24 15:59:05 UTC**.
`kernel-results.json` combines the real successful receipts from the staged
export, comparison, and replay commands. The individual comparison and
kernel receipts are retained as `export-statement-comparison-result.json`
and `kernel-replay-results.json`. The logs are
`export-statement-comparison.log`, `kernel-con-ron.log`,
`kernel-nanoda.log`, and `kernel-lean.log`.

The successful statement and dependency comparison uses the pinned
toolchain's own Comparator engine, `Lake.Check.compareAt` and
`Lake.Check.checkAxioms`. The comparison operator imports only those
toolchain libraries,
loads the toolchain's own `libLake_shared.so`, and reads the two exports as
data. It does not import project modules, run a project build, or alter a
sandbox. An initial operator invocation lacked this native library; its
loader failure and original receipts are preserved in `tooling-attempt-1`.
The corrected comparison passed. The reproduction script includes the
native-library loading argument.

## Standard sandboxed Comparator

The standard `scripts/verify-comparator.sh` invocation was attempted after
the completed Solution/Challenge build. It failed **before inspecting the
proof**, when bubblewrap could not initialize the sandbox:

```text
bwrap: Failed to mount tmpfs: No such file or directory
error: Child exited with 1
```

The exact final invocation and output are in `comparator-sandbox-final.json`
and `comparator-sandbox-final.log`. `sandbox-diagnostic.md` records the
additional host restriction on initializing the sandbox's network
namespace. No sandbox setting, namespace restriction, host security
setting, or toolchain source was disabled or modified.

The read-only export comparison and the three kernel replays above are
successful independent proof checks. **They are not a sandboxed Palomar
acceptance certificate.** The normal Comparator command still needs to be
run on a host supporting its sandbox, or by the registry.

## Clean source-ZIP reproduction

The source ZIP was extracted into a new directory, separate from the main
project. Before the first build there were **zero project compiled
artifacts**, and `.lake/build` did not exist. Only the nine pinned external
dependencies were shared; their checkout revisions were checked against
the manifest. Project build outputs were not copied, and Lake artifact
restoration was disabled.

The first clean `./lakew build` ran on **24 November 2026,
15:55:21–16:04:42 UTC**, exited successfully, and created **336 new project
`.olean` files**. It completed 18,926 Lake jobs under the initial default
target list. The original-theorem axiom audit then passed at 16:04:55 UTC.
`reproduction-results.json` records the input ZIP hash, source-manifest
hashes, dependency revisions, commands, timestamps, and exit codes;
`reproduction-build.log` and `reproduction-solution-audit.log` contain the
outputs.

The supplemental stage ran at **16:07:35–16:07:53 UTC** after copying only
the updated `lakefile.toml` into that same reproduction directory. Its sole
change was to add the three previously omitted default targets. The
expanded default build passed with **18,933 jobs** and produced **three
additional `.olean` files**. All 336 earlier objects retained their hashes
and modification times; they were not rebuilt. Direct checks of
`AxiomAudit.lean` and `scripts/CompareExports.lean` also passed, without
running the latter's `main`. This gives **339 compiled modules plus two
directly checked files, covering all 341 Lean files**.

`reproduction-supplemental-results.json`, its three command logs, and
`reproduction-supplemental-lakefile.diff` record this stage. Hash checks
confirmed that all Lean source files from the ZIP remained unchanged and
matched the main project. Both sets of historical receipts remain intact.
The subsequent root-package-name correction in `lake-manifest.json` is
recorded separately below; it changed no Lean proof text.

## Pinned environment and reproduction

```text
Lean 4.36.0
Lean commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9
Mathlib commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842
```

All nine dependency checkouts have the exact revisions in
`lake-manifest.json` and no changed tracked sources; see
`dependency-pins.json`. Compiler binaries and dependency caches are not
included in the source archive.

After the proof checks, the manifest's root package name was synchronized
with `lakefile.toml`: `brehm_approx` became `akopyan_palomar_transfer`.
That was the sole JSON change. All dependency records, all 341 Lean source
files, and the checked proof-export bytes remained unchanged. Ordinary
default builds of both the main project and the clean-reproduction copy
then passed with 18,933 jobs each. `final-package-config-result.json`
records the old and new raw manifest hashes, the unchanged dependency and
source hashes, and both build receipts. Historical kernel and reproduction
receipts retain the exact manifest hashes present during those earlier
runs; they have not been rewritten.

After installing the pinned toolchain:

```sh
./lakew exe cache get
python3 verify.py
python3 scripts/verify-kernels.py
./scripts/verify-comparator.sh
```

The last command requires a supported Linux sandbox environment. The
publication metadata checks and actual submission are separate from this
mathematical verification record; see `PUBLICATION.md`.

## Release source binding

`release-source-binding.json` compares the complete current source set with
the checked kernel export and with the final clean-reproduction copy. All
341 Lean files are byte-identical to the sources recorded at export time;
all 341 Lean files and the four build/comparison configuration files match
the final reproduction copy. The current 345-file proof/configuration
manifest is `release-proof-sources.sha256`. The broader `sources.sha256`
manifest also covers the released documentation and scripts, while excluding
the changing verification records themselves.

`final-prepackage-checks.json` records the final source-policy and exact
source-contract checks, both successful. The publication metadata check
reports only the unset authors, responsible maintainers, licence identifier,
and root licence text. `document-links-result.json` records the local-link
check of the current project documentation. The declaration-level reviewer
index is `TRANSFER_INDEX.md`.

Historical verification logs for the supplied archive are retained only
under `verification-archive`. The results in this document come from the
fresh original-target transfer and its current exports.
