#!/usr/bin/env python3
"""Check the unchanged original target and the source-level proof contract.

This check complements compilation, the transitive Lean axiom audit and kernel
replay. It does not claim to replace the sandboxed Palomar Comparator.
"""
import hashlib
import json
import re
from pathlib import Path
from source_lex import code_only, source_files

ROOT = Path(__file__).resolve().parents[1]
TARGET = "PLGeometry.akopyan_pl_nash_kuiper"
REFERENCE_SHA256 = "a273a7a2032317b02316776d38d7739a5cb5aac0600d0b81ba788fc31cedced3"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORT = re.compile(r"^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\n]+)", re.M)
FORBIDDEN = re.compile(r"(?<![\w'])\b(?:sorry|admit|axiom|sorryAx|unsafe|implemented_by|native_decide)\b(?![\w'])")


def normalized(text):
    return " ".join(code_only(text).split())


def repaired_challenge(text):
    """The explicitly enumerated elaboration/visibility repairs, and nothing else."""
    repairs = [
        ("public import Mathlib\n",
         "public import Mathlib.Analysis.Convex.SimplicialComplex.Basic\n"
         "public import Mathlib.Analysis.InnerProductSpace.PiL2\n"
         "public import Mathlib.Analysis.SpecialFunctions.Arcosh\n"
         "public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic\n"),
        ("open scoped InnerProductSpace\n", "open scoped InnerProductSpace NNReal\n"),
        ("/-- Euclidean, Klein hyperbolic, and spherical geodesic distances. -/",
         "instance modelTopology (κ : Geometry) (n : ℕ) : TopologicalSpace (Model κ n) := by\n"
         "  cases κ <;> infer_instance\n\n"
         "/-- Euclidean, Klein hyperbolic, and spherical geodesic distances. -/"),
        ("private def cell ", "def cell "),
        ("  simplex : ∀ σ, σ ∈ K.faces → Simplex κ d m σ",
         "  simplex : ∀ (σ : Finset (E m)), σ ∈ K.faces → Simplex κ d m σ"),
        ("private def segmentEDist ", "def segmentEDist "),
        ("    ∀ σ ∈ T.faces, ∃ τ (hτ : τ ∈ K.K.faces),",
         "    ∀ σ ∈ T.faces, ∃ (τ : Finset (E m)) (hτ : τ ∈ K.K.faces),"),
    ]
    for before, after in repairs:
        if text.count(before) != 1:
            raise ValueError(f"Original reference no longer has the unique expected text: {before!r}")
        text = text.replace(before, after)
    return text


def target_signature(text):
    start = text.index("theorem akopyan_pl_nash_kuiper")
    end = text.index(":=", start)
    return normalized(text[start:end])


def target_documentation(text):
    prefix = text[:text.index("theorem akopyan_pl_nash_kuiper")].rstrip()
    if not prefix.endswith("-/") or "/--" not in prefix:
        return None
    return prefix[prefix.rindex("/--"):]


def definitions(text):
    start = text.index("abbrev E ")
    end = text.find("theorem akopyan_pl_nash_kuiper", start)
    if end < 0:
        end = text.rindex("end PLGeometry")
    return normalized(text[start:end])


def main():
    errors = []
    config = json.loads((ROOT / "comparator.json").read_text())
    for key, wanted in (("challenge_module", "Challenge"), ("solution_module", "Solution")):
        if config.get(key) != wanted:
            errors.append(f"comparator.json: {key} must be {wanted}")
    if config.get("theorem_names") != [TARGET]:
        errors.append("comparator.json: the exact original theorem must be the sole target")
    if config.get("definition_names") != []:
        errors.append("comparator.json: no definition holes are permitted")
    if set(config.get("permitted_axioms", [])) != STANDARD_AXIOMS:
        errors.append("comparator.json: permit exactly the three standard logical axioms")
    if "external_kernels" in config:
        errors.append("comparator.json: registry kernel registration is generated separately")

    reference = (ROOT / "reference/Challenge.original.lean.txt").read_text()
    if hashlib.sha256(reference.encode()).hexdigest() != REFERENCE_SHA256:
        errors.append("The preserved original Challenge reference was changed")
    challenge_path = ROOT / "Challenge.lean"
    challenge = challenge_path.read_text()
    if challenge != repaired_challenge(reference):
        errors.append("Challenge.lean differs from the original beyond the enumerated elaboration repairs")
    original_definitions = (ROOT / "Compatibility/Original.lean").read_text()
    if definitions(original_definitions) != definitions(challenge):
        errors.append("Compatibility/Original.lean changes the Challenge definitions")
    if len(challenge.encode()) > 100 * 1024 or len(challenge.splitlines()) > 1000:
        errors.append("Challenge.lean exceeds the statement-file size limit")
    if not all(token == "Mathlib" or token.startswith("Mathlib.") for line in IMPORT.findall(code_only(challenge)) for token in line.split()):
        errors.append("Challenge.lean must remain standalone and import only Mathlib")
    if len(re.findall(r"\bsorry\b", code_only(challenge))) != 1:
        errors.append("Challenge.lean must have exactly its one deliberate target proof hole")

    count = 0
    targets = []
    for path in source_files(ROOT):
        if path == challenge_path:
            continue
        raw = path.read_text(encoding="utf-8")
        code = code_only(raw)
        for match in FORBIDDEN.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: proof-side {match.group()} is forbidden")
        for line in IMPORT.findall(code):
            if any(name in {"Challenge", "ArchiveChallenge"} for name in line.split()):
                errors.append(f"{path.relative_to(ROOT)}: proof files must not import a statement template")
        if re.search(r"\btheorem\s+akopyan_pl_nash_kuiper\b", code):
            targets.append(path)
            if target_signature(raw) != target_signature(reference):
                errors.append(f"{path.relative_to(ROOT)}: the final theorem signature changed")
            if target_documentation(raw) != target_documentation(reference):
                errors.append(f"{path.relative_to(ROOT)}: the target documentation differs from the original Challenge")
        count += 1
    if len(targets) != 1:
        errors.append(f"Expected exactly one proof-side original target, found {len(targets)}")
    if errors:
        print("\n".join(errors))
        return 1
    print(f"Source contract passed: {count} proof-side Lean files; exact original target {TARGET}.")
    print("Original definitions and final target signature are preserved; no proof holes or new axioms found.")
    print("The target theorem documentation matches the original Challenge exactly.")
    print("Original reference SHA256:", hashlib.sha256(reference.encode()).hexdigest())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
