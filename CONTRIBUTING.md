# Contributing

## Public statements

The mathematical interface is `Challenge.lean`. It contains the model metrics,
geometric definitions, and the single target theorem
`PLGeometry.akopyan_pl_nash_kuiper`.

Keep the concrete definitions synchronized with `Compatibility/Original.lean`.
The internal geometric library modules live in `BrehmApprox/` and `PLGeometry/`
(under the `ArchivePLGeometry` namespace), and `Compatibility/` connects them
to the definitions in `Challenge.lean`. Comparator checks the elaborated target
and all definitions on which it depends. Keep the sole target in
`comparator.json` unchanged and keep `definition_names` empty.

The public approximation theorem quantifies over finite geometric polyhedra,
including empty and disconnected spaces, and permits `d ≤ n`. The protected-net
and finite-folding constructions belong inside its proof. The spherical
hypothesis is the alternative between uniform strict shortness and containment
in an open hemisphere. Preserve the original theorem docstring as well as its
signature.

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

The CI workflow runs these checks and validates `formalization.yaml` via
`scripts/check-publication.py`.

## Documentation, authorship, and licensing

Keep public documentation and comments in English. Maintain the actual scope,
sources, automation provenance, axiom list, and review status in
`formalization.yaml`. The repository is authored and maintained by Arseniy
Akopyan and distributed under the Apache License 2.0 (`LICENSE`); third-party
notices are recorded in `THIRD_PARTY_NOTICES.md`.
