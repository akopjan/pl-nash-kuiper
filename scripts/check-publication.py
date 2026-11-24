#!/usr/bin/env python3
"""Validate release metadata without inventing missing publication facts."""
import json
import re
from pathlib import Path
import yaml
from jsonschema import Draft7Validator

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    document = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    schema = json.loads((ROOT / "scripts/schema/formalization.v0.4.schema.json").read_text())
    errors = []
    for error in sorted(Draft7Validator(schema).iter_errors(document), key=lambda e: str(e.path)):
        where = ".".join(str(part) for part in error.path) or "root"
        errors.append(f"formalization.yaml:{where}: {error.message}")
    if document.get("version") != "v0.4":
        errors.append("formalization.yaml: version must be v0.4")
    project = document.get("project", {})
    for field in ("authors", "responsible_maintainers"):
        names = project.get(field, [])
        if not names or not all(isinstance(name, str) and name.strip() for name in names):
            errors.append(f"formalization.yaml: project.{field} needs true, nonempty names")
    if not project.get("license", "").strip():
        errors.append("formalization.yaml: project.license requires an authorized SPDX identifier")
    if not (ROOT / "LICENSE").is_file():
        errors.append("LICENSE: no project licence has been selected")
    for field, minimum, maximum, pattern in (
        ("arxiv", 1, 2, r"(?:math|cs)\.[A-Z]{2}"),
        ("msc2020", 1, 8, r"[0-9]{2}[A-Z][0-9]{2}"),
    ):
        codes = document.get("classification", {}).get(field, [])
        if not minimum <= len(codes) <= maximum or not all(re.fullmatch(pattern, code) for code in codes):
            errors.append(f"formalization.yaml: classification.{field} has invalid count or format")
    source_relationships = {"formalizes", "adapts", "independently-proves", "background", "other"}
    for index, source in enumerate(document.get("sources", [])):
        if source.get("relationship") not in source_relationships:
            errors.append(f"formalization.yaml: sources[{index}].relationship is required")
    for field in ("sorry_count", "sorry_in_definitions"):
        if document.get("status", {}).get(field) != 0:
            errors.append(f"formalization.yaml: status.{field} must be zero for release")
    axioms = set(document.get("status", {}).get("axioms", []))
    if axioms - {"propext", "Classical.choice", "Quot.sound"}:
        errors.append("formalization.yaml: status.axioms includes a nonstandard dependency")
    if "TEMPLATE:" in (ROOT / "formalization.yaml").read_text():
        errors.append("formalization.yaml: retained template placeholder")
    if "https://submit.palomar-registry.org/" not in (ROOT / "README.md").read_text():
        errors.append("README.md: current Palomar submission address is missing")
    if errors:
        print("Publication metadata is not ready:")
        for error in errors:
            print(f"- {error}")
        return 1
    print("Publication metadata passed. Mathematical acceptance still requires the solution audit and Comparator.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
