# Contributing

## Public statements

The mathematical interface is `Challenge.lean`. It imports only Mathlib and
contains the original model metrics, geometric definitions, and the single
target theorem `PLGeometry.akopyan_pl_nash_kuiper`.

Keep the concrete definitions synchronized with `Compatibility/Original.lean`.
The archive's definitions live in the separate `ArchivePLGeometry` namespace;
their connection to the original definitions must be proved in the
compatibility modules. Comparator checks the elaborated original target and
all definitions on which it depends. Keep the sole target in `comparator.json`
unchanged and keep `definition_names` empty.

The public approximation theorem quantifies over the original finite
geometric polyhedra, including empty and disconnected spaces, and permits
`d ≤ n`. The protected-net and finite-folding constructions belong inside
its proof. The spherical hypothesis is the original alternative between
uniform strict shortness and containment in an open hemisphere. Preserve
the original theorem docstring as well as its signature.

## Proof checks

Use the toolchain and dependency revisions already pinned by the project.
Run:

```sh
lake exe cache get
python3 verify.py
```

Every proof-side Lean file must use a `module` header. The standalone Challenge
is limited to 1,000 lines and 100 KiB; each Lean source file is limited to
10,000 lines. Proof-side `sorry`, `admit`, and geometric axiom declarations
are rejected by the source contract check. The theorem audit permits only
`propext`, `Classical.choice`, and `Quot.sound`.

Run the standard sandboxed statement and independent-kernel check before
submitting a revision:

```sh
./scripts/verify-comparator.sh
```

The CI workflow runs these checks and validates the publication metadata.
The metadata job requires the owner-supplied authorship and licence fields
listed in `PUBLICATION.md`; these have not been fabricated for this archive.
Logs are evidence of the recorded source revision; regenerate the source-hash
manifest whenever the distributed files change.

## Documentation and metadata

Keep public documentation and comments in English. Update the proof guide
when a construction changes. Maintain the actual scope, sources, automation
provenance, axiom list, and review status in `formalization.yaml`.
Authorship, maintainer details, and the project licence must be supplied by
the responsible people. Dependency and vendored-file notices are kept in
`THIRD_PARTY_NOTICES.md`.
