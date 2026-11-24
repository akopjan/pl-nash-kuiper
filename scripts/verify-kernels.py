#!/usr/bin/env python3
"""Replay a freshly built original-target proof in the bundled independent kernels.

This is an independent proof audit, not a replacement for the sandboxed
Comparator. It never changes or disables Comparator's sandbox. The separate
verify-comparator.sh script retains the standard sandboxed invocation.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from source_lex import source_files

ROOT = Path(__file__).resolve().parents[1]
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
    "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk", "Char",
    "optParam", "autoParam", "semiOutParam", "outParam",
]


def now():
    return datetime.now(timezone.utc).isoformat()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="./lakew")
    args = parser.parse_args()
    config = json.loads((ROOT / "comparator.json").read_text())
    if config["theorem_names"] != ["PLGeometry.akopyan_pl_nash_kuiper"]:
        raise SystemExit("Refusing to audit an altered target list")
    if set(config["permitted_axioms"]) != set(AXIOMS) or config.get("definition_names", []) != []:
        raise SystemExit("Refusing altered axiom permissions or definition holes")
    logs = ROOT / "verification"
    generated = logs / "generated"
    generated.mkdir(parents=True, exist_ok=True)
    records = []

    def run(name, command, stdout_path=None):
        log = logs / name
        record = {"command": command, "log": str(log.relative_to(ROOT)), "started_utc": now()}
        if stdout_path is not None:
            record["stdout"] = str(stdout_path.relative_to(ROOT))
            with stdout_path.open("wb") as output, log.open("wb") as error:
                process = subprocess.run(command, cwd=ROOT, stdout=output, stderr=error)
        else:
            with log.open("wb") as output:
                process = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        record.update(exit_code=process.returncode, finished_utc=now())
        records.append(record)
        (logs / "kernel-results.json").write_text(json.dumps(records, indent=2) + "\n")
        print(f"{name}: exit {process.returncode}", flush=True)
        if process.returncode:
            print(log.read_text(errors="replace"))
            raise SystemExit(process.returncode)

    run("kernel-source-contract.log", [sys.executable, "scripts/check-contract.py"])
    run("kernel-build.log", [args.lake, "build", "Solution", "Challenge"])
    run("kernel-axioms.log", [sys.executable, "scripts/check-solution.py", "--lake", args.lake])
    prefix = Path(subprocess.check_output([args.lake, "env", "lean", "--print-prefix"],
                                         cwd=ROOT, text=True).strip())
    targets = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", *config["theorem_names"], *AXIOMS, *PRIMITIVES]
    challenge_export = generated / "challenge.ndjson"
    run("challenge-export.log", [args.lake, "env", "leanexport", config["challenge_module"], "--", *targets], challenge_export)
    export = generated / "solution.ndjson"
    run("kernel-export.log", [args.lake, "env", "leanexport", config["solution_module"], "--", *targets], export)
    manifest = {
        "target": config["theorem_names"][0], "export_file": str(export.relative_to(ROOT)),
        "export_sha256": hashlib.sha256(export.read_bytes()).hexdigest(),
        "challenge_export_sha256": hashlib.sha256(challenge_export.read_bytes()).hexdigest(),
        "challenge_sha256": hashlib.sha256((ROOT / "Challenge.lean").read_bytes()).hexdigest(),
        "solution_source_sha256": hashlib.sha256((ROOT / "Solution.lean").read_bytes()).hexdigest(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lake_manifest_sha256": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
        "lean_sources_sha256": {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(source_files(ROOT))
        },
        "permitted_axioms": AXIOMS, "created_utc": now(),
        "scope": "Independent kernel replay; not a sandboxed Comparator acceptance certificate",
    }
    (logs / "kernel-export-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    # These native reader/comparator symbols ship in Lake's own shared library.
    # Load that pinned toolchain library, never a project-built dynamic module.
    run("export-statement-comparison.log", [args.lake, "env", "lean",
        "--load-dynlib=" + str(prefix / "lib/lean/libLake_shared.so"), "--run",
        "scripts/CompareExports.lean", str(challenge_export), str(export)])
    nanoda_config = generated / "nanoda.json"
    nanoda_config.write_text(json.dumps({
        "export_file_path": str(export), "use_stdin": False, "permitted_axioms": AXIOMS,
        "unpermitted_axiom_hard_error": True, "num_threads": 4,
        "nat_extension": True, "string_extension": True, "print_success_message": True,
        "pp_to_stdout": True,
    }, indent=2) + "\n")
    run("kernel-con-ron.log", [str(prefix / "bin/con-ron"), "--verified", "--jobs=4", str(export)])
    run("kernel-nanoda.log", [str(prefix / "bin/nanoda_bin"), str(nanoda_config)])
    # leanchecker invokes the pinned `lean` subprocess; Lake supplies the same
    # toolchain PATH used for the build/export, including when invoked by lakew.
    run("kernel-lean.log", [args.lake, "env", "leanchecker", "--from-export", str(export)])
    print("Fresh original-target export accepted by con-ron (verified mode), NanoDa and Lean.")
    print("The standard sandboxed Comparator remains a separate check.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
