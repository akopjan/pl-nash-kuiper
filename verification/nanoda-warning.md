# NanoDa's axiom-printing warning

## Exact source and cause

Lean 4.36.0, source commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, pins NanoDa to
`ammkrn/nanoda_lib` commit
`4c544ed4099c8227f07d5de77ad1e69fb0740a27` in
[src/CMakeLists.txt, lines 1071–1083](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/CMakeLists.txt#L1071-L1083).
The code below was read at that exact NanoDa revision. The installed binary
has SHA256
`8241c5e6baa29490aa118d382f97961b208ae730fdb96545c2abed74c9ece5a8`.

The original configuration omitted `pp_output_path`, `pp_to_stdout`, and
`print_axioms`. At this revision, `pp_to_stdout` defaults to false,
`print_axioms` defaults to true, and the absent output path is `None`.
Consequently `get_pp_destination()` returns `Ok(None)`.
See [src/util.rs, lines 915–927 and 978–987](https://github.com/ammkrn/nanoda_lib/blob/4c544ed4099c8227f07d5de77ad1e69fb0740a27/src/util.rs#L915-L987).

The precise branch that produces the observed message is
[src/pretty_printer.rs, lines 382–385](https://github.com/ammkrn/nanoda_lib/blob/4c544ed4099c8227f07d5de77ad1e69fb0740a27/src/pretty_printer.rs#L382-L385):

```rust
} else {
    if self.config.print_axioms {
        errs.push(Box::<dyn Error>::from("Unable to print axioms"));
    }
}
```

Thus the warning means that printing the admitted axioms was enabled but
no pretty-printer destination was supplied. It does not identify an
unpermitted axiom.

## Relation to proof checking

In [src/main.rs, lines 24–45](https://github.com/ammkrn/nanoda_lib/blob/4c544ed4099c8227f07d5de77ad1e69fb0740a27/src/main.rs#L24-L45),
parsing and declaration checking precede pretty printing:

```rust
export_file.check_all_declars();
let pp_errs = export_file.pp_selected_declars(pp_destination.as_mut());
```

The message about pretty-printer errors is returned as a successful result
after those checks. The separate axiom admission gate is in
[src/parser.rs, lines 469–472 and 765–781](https://github.com/ammkrn/nanoda_lib/blob/4c544ed4099c8227f07d5de77ad1e69fb0740a27/src/parser.rs#L765-L781):
an axiom outside the allowlist returns an error when
`unpermitted_axiom_hard_error` is true. Our original and supplemental
configurations both set that flag to true and permit exactly `propext`,
`Quot.sound`, and `Classical.choice`. The printing branch does not alter
this gate or the typechecking pass.

## Corrected reproduction and observed result

The reproduction script now supplies only the missing destination option,
`pp_to_stdout: true`. `print_axioms` remains enabled. One supplemental
NanoDa run used a separate configuration and the unchanged existing export;
no other kernel or proof build was rerun for this correction.

The supplemental run finished at **2026-11-24 16:15:07 UTC**, exit **0**. It
printed the declarations of all three permitted axioms and then:

```text
Checked 52270 declarations with no errors
```

There were zero typechecker errors and zero pretty-printer errors. Both the
before and after export hashes were
`93d951ebc3cbdbe3c0817d4606a6961339399210c4c2ba43198c90030f2355a0`.
All Lean source hashes also remained unchanged.

The actual output is in `kernel-nanoda-with-axioms.log`. Its separate
receipt, `kernel-nanoda-with-axioms.json`, records the command, complete
configuration, binary hash, timestamps, printed axioms, and export hashes.
The original warning log and original kernel receipts are preserved.
