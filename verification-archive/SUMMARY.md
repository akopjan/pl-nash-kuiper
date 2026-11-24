# Verification record

## Outcome

The complete Lean development builds successfully. All four public theorem
statements and the six auxiliary metric-law obligations pass the transitive
axiom audit. The local Palomar Comparator run exited with code **0** at
**2026-11-23T21:55:43.907447+00:00**.

- Statement comparison: accepted.
- con-ron independent kernel: accepted; 50,099 exported declarations checked.
- NanoDa independent kernel: accepted.
- Lean default kernel: accepted.
- Definition holes registered with Comparator: none.
- Permitted and actually used axioms: `propext`, `Classical.choice`, `Quot.sound`.

The standard sandboxed run could not start because `bubblewrap` reported
`Failed to mount tmpfs: No such file or directory`. The successful local run
used the documented `--inadvisably-no-sandbox` option. It is a local checking
result, not a sandboxed registry acceptance certificate. The standard
sandboxed check is retained in the CI workflow and submission script.

## Toolchain

```text
Lean (version 4.36.0, x86_64-unknown-linux-gnu, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, Release)
```

Mathlib is pinned to revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (`v4.36.0`). All nine Lean
package dependencies are pinned by `lake-manifest.json`.
The metadata checker used PyYAML 6.0.3 and jsonschema 4.26.0.

## Public theorems

1. `PLGeometry.brehm_akopyan_tarasov`
2. `PLGeometry.pl_nash_kuiper_euclidean`
3. `PLGeometry.pl_nash_kuiper_spherical`
4. `PLGeometry.pl_nash_kuiper_hyperbolic`

The extension theorem covers Euclidean, spherical, and hyperbolic model
spaces. The three approximation theorems concern arbitrary finite intrinsic
polyhedral sources. In the spherical case the map is uniformly strictly
short or its image lies in a closed hemisphere. No initial folding,
protected-net hypothesis, or geometric extension axiom is assumed.

The additional six Comparator targets prove the spherical and hyperbolic
metric laws stated in the standalone Challenge. `comparator.json` records
their exact names. Every deliberate Challenge hole is registered as a
proof obligation. The proof side has no `sorry` or `admit`, and no additional
axiom declaration, `unsafe` declaration, or `native_decide` proof.

## Evidence in the archive

- `build.log`: the complete successful project build.
- `axioms.log`: public types and principal construction dependency reports.
- `solution-check.log` and `solution-audit.log`: all ten registered obligations.
- `source-policy.log` and `source-contract.log`: source requirements.
- `results.json`: actual command timestamps and exit statuses.
- `comparator-local.log` and `comparator-local-result.json`: successful local replay.
- `comparator-sandbox.log` and `comparator-sandbox-result.json`: sandbox startup failure.
- `sources.sha256`: hashes of the distributed project sources and service files.

## Publication metadata

The metadata schema check reports only the unset authorship, maintainer,
and licence fields and the missing root `LICENSE` file. Those values are
not specified in the supplied material. The remaining metadata, sources,
automation provenance, classification, pinned service files, and CI are
included. `PUBLICATION.md` gives the submission sequence.

## Reproduction

From the project directory, after installing Lean through its official
installation instructions:

```sh
elan toolchain install leanprover/lean4:v4.36.0
lake exe cache get
python3 verify.py
```

On a Linux host supporting bubblewrap, run `./scripts/verify-comparator.sh`
for the standard sandboxed Comparator check.
