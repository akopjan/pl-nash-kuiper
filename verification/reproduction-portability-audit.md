# CI and reproduction portability audit

Checked on **2026-11-24 UTC**. This is a static audit plus read-only GitHub and PyPI
requests and shell syntax checks. It did not rerun the proof builds or
kernels, execute the GitHub workflow, or change security settings.

## The pinned actions exist

Both commit endpoints and both pinned `action.yml` files returned HTTP 200
from GitHub. The API returned the exact requested 40-character SHA.
`reproduction-portability-sources.json` records the URLs, response codes,
timestamps, and downloaded-content hashes.

| Action | Verified immutable commit | Primary source |
|---|---|---|
| `actions/checkout` | `3d3c42e5aac5ba805825da76410c181273ba90b1` | [Commit: v7.0.1 release preparation](https://github.com/actions/checkout/commit/3d3c42e5aac5ba805825da76410c181273ba90b1) |
| `leanprover/lean-action` | `38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9` | [Commit used by v1.5.0](https://github.com/leanprover/lean-action/commit/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9) |

The pinned [checkout action definition](https://raw.githubusercontent.com/actions/checkout/3d3c42e5aac5ba805825da76410c181273ba90b1/action.yml)
uses Node 24. Its [README](https://raw.githubusercontent.com/actions/checkout/3d3c42e5aac5ba805825da76410c181273ba90b1/README.md)
requires Actions Runner 2.327.1 or newer for this runtime. A sufficiently
recent runner is therefore necessary for any future self-hosted deployment.

The pinned [Lean action definition](https://raw.githubusercontent.com/leanprover/lean-action/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9/action.yml)
accepts the workflow's `build: true` and `build: false` inputs. Its
[configuration script](https://raw.githubusercontent.com/leanprover/lean-action/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9/scripts/config.sh)
honours those values. Its [Mathlib detection script](https://raw.githubusercontent.com/leanprover/lean-action/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9/scripts/detect_mathlib.sh)
matches the Mathlib URL in this project's lockfile; the action then runs
`lake exe cache get`. Thus the Comparator job can install the toolchain and
obtain the cache with `build: false`, leaving the actual challenge/solution
build to the standard Comparator.

## Local command consistency

The metadata validator was run with exactly the versions in
`scripts/requirements.txt`: PyYAML 6.0.3 and jsonschema 4.26.0. Both pinned
releases are available from their primary PyPI pages:
[PyYAML 6.0.3](https://pypi.org/project/PyYAML/6.0.3/) and
[jsonschema 4.26.0](https://pypi.org/project/jsonschema/4.26.0/).
The latter requires Python 3.10 or newer. The README states this minimum
and the Linux scope of the complete verification commands.

`lakew` selects an explicit `LEAN_BIN` directory first, otherwise an
existing `lake` on `PATH`, otherwise the adjacent workspace runtime. It
does not require that adjacent runtime when elan or `LEAN_BIN` is available.
Both `lakew` and `scripts/verify-comparator.sh` have executable permissions
and passed `bash -n`.

The default build now explicitly includes `ArchiveSolution`,
`Compatibility.GeometricRefinement`, and `Compatibility.PLContinuity`,
which were not reachable from the former default import graph. The pinned
Lake SDK resolves TOML default targets as either declared targets or module
names. The requested coverage check passed with **18,933 jobs**; see
`default-coverage-build-result.json`. No Lean source or proof-export data
changed in this correction.

The manifest's inherited root name was also synchronized with the package
name, `akopyan_palomar_transfer`. `final-package-config-result.json` proves
that only that root field changed, all dependency entries and Lean files
remained identical, and ordinary builds of both copies passed. The earlier
verification receipts were preserved.

The project pins Lean 4.36.0 and all dependency revisions. From the project
directory, the complete cold-start sequence with an explicitly installed
Linux toolchain is:

```sh
export LEAN_BIN=/absolute/path/to/lean-4.36.0-linux/bin
./lakew exe cache get
python3 verify.py --lake ./lakew
python3 scripts/verify-kernels.py --lake ./lakew
./scripts/verify-comparator.sh
```

The cache command matters when using only the manual-bin route; omitting
it may cause a much longer build from Mathlib sources. With elan installed,
the README's `lake exe cache get` and `--lake lake` variants select the
toolchain through `lean-toolchain`.

`verify.py` and `verify-kernels.py` run their subprocesses from the project
root. The Comparator wrapper also changes to that directory and derives
all verifier paths from the selected Lean prefix. It retains the standard
sandboxed invocation and registers the bundled kernels in a temporary
configuration, leaving submission `comparator.json` unchanged.

## Remaining constraints

- **Owner metadata:** the current metadata check exits 1 for empty author,
  responsible-maintainer, and licence fields, plus missing `LICENSE`.
  Consequently the CI metadata job is expected to fail until the owner
  supplies those facts. No other metadata error was reported in this audit.
- **Linux sandbox:** Comparator needs a host that supports bubblewrap's
  namespace and mount operations. The current workspace does not; see
  `sandbox-diagnostic.md`. The existing CI setup also assumes an Ubuntu
  runner with its declared administrative setup commands available. Those
  commands were neither run nor changed by this audit.
- **Host portability:** the independent export-comparison runner currently
  loads `libLake_shared.so`, so the supplied verification command is a
  Linux command. A macOS or Windows port would need platform-specific
  shared-library paths and a separate plan for the Linux Comparator.
- **Infrastructure is not fully immutable:** although the two outer
  actions use full SHAs, this Lean action calls `actions/cache/*@v5` and its
  [installer](https://raw.githubusercontent.com/leanprover/lean-action/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9/scripts/install_elan.sh)
  downloads elan's installer from `master`. `ubuntu-latest` also follows
  the hosted runner image. Organizations requiring every transitive action
  to use a commit SHA may reject that inherited cache reference.
- **Toolchain selection:** `lakew` forwards to the supplied or existing
  executable; it does not itself reject an incorrectly selected version.
  A direct system installation or `LEAN_BIN` must therefore contain the
  pinned 4.36.0 toolchain. Elan's project selection and the recorded
  `lean-version.txt` provide the normal version check.

No remote GitHub Actions success or registry acceptance is inferred from
this audit. The mathematical checks and clean-rebuild results have their
own receipts.
