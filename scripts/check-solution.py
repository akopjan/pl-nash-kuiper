#!/usr/bin/env python3
"""Ask Lean to resolve every requested solution theorem and audit its axioms."""
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="./lakew", help="Lake executable or wrapper")
    args = parser.parse_args()
    config = json.loads((ROOT / "comparator.json").read_text())
    names = config["theorem_names"]
    if set(config.get("permitted_axioms", [])) != STANDARD_AXIOMS:
        print("Refusing an audit with a modified standard-axiom allowlist.")
        return 1
    for name in [config["solution_module"], *names]:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*", name):
            print(f"Unsupported module/declaration identifier in comparator.json: {name}")
            return 1
    lines = ["module", f"public import {config['solution_module']}", ""]
    for name in names:
        lines.extend([f"#check {name}", f"#print axioms {name}"])
    with tempfile.TemporaryDirectory(prefix="pl-geometry-audit-") as temporary:
        path = Path(temporary) / "SolutionAudit.lean"
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        process = subprocess.run(
            [args.lake, "env", "lean", str(path)], cwd=ROOT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
    output = process.stdout
    destination = ROOT / "verification" / "solution-audit.log"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(output, encoding="utf-8")
    print(output, end="" if output.endswith("\n") else "\n")
    if process.returncode:
        print("Solution audit failed: at least one requested theorem is missing or does not elaborate.")
        return process.returncode
    failed = False
    for name in names:
        match = re.search(rf"'{re.escape(name)}' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
        if match:
            axioms = {part.strip() for part in match.group(1).split(",") if part.strip()}
        elif re.search(rf"'{re.escape(name)}' does not depend on any axioms", output):
            axioms = set()
        else:
            print(f"No transitive axiom report was produced for {name}.")
            failed = True
            continue
        extra = axioms - STANDARD_AXIOMS
        if extra:
            print(f"{name}: forbidden dependencies: {', '.join(sorted(extra))}")
            failed = True
    if not failed:
        print(f"Solution audit passed for all {len(names)} obligation(s), including the exact original Akopyan target.")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
