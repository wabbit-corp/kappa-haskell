#!/usr/bin/env python3
"""Validate the active Nat/Fin/refinement conformance contract."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
CONTRACT_ROOT = ROOT / "tests/conformance/spec-coverage/nat-fin-refinement"
MANIFEST = CONTRACT_ROOT / "manifest.json"
OWNER_STAGE = re.compile(r"NFR-[1-7]\Z")
EXPECTED_OUTCOMES = {"accept", "reject", "mixed-artifact"}
CATEGORIES = {"positive", "negative", "analysis", "backend", "artifact"}
REQUIRED_APPENDIX_SECTIONS = {f"T.12.{index}" for index in range(1, 10)}
SUITE_ENTRY_NAMES = {"main.kp", "suite.ktest"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    errors: list[str] = []

    try:
        data = json.loads(MANIFEST.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(exc, file=sys.stderr)
        return 1

    suites = data.get("suites")
    suite_count = data.get("suiteCount")
    if not isinstance(suites, list):
        errors.append("manifest suites must be a list")
        suites = []
    if suite_count != len(suites):
        errors.append(f"suiteCount {suite_count!r} does not match {len(suites)} entries")

    source_pairs = (
        ("sourceSpecPatch", "sourceSpecPatchSha256"),
        ("sourceAppendix", "sourceAppendixSha256"),
        ("sourcePseudotests", "sourcePseudotestsSha256"),
    )
    for path_key, hash_key in source_pairs:
        relative = data.get(path_key)
        expected_hash = data.get(hash_key)
        if not isinstance(relative, str) or not isinstance(expected_hash, str):
            errors.append(f"manifest must contain string {path_key} and {hash_key}")
            continue
        source = ROOT / relative
        if not source.is_file():
            errors.append(f"missing provenance file {relative}")
        elif digest(source) != expected_hash:
            errors.append(f"provenance hash mismatch for {relative}")

    declared_paths: set[str] = set()
    covered_sections: set[str] = set()
    for suite in suites:
        if not isinstance(suite, dict):
            errors.append("suite entry must be an object")
            continue

        path = suite.get("path")
        if not isinstance(path, str) or not path:
            errors.append("suite entry has no path")
            continue
        if path in declared_paths:
            errors.append(f"duplicate suite path {path}")
            continue
        declared_paths.add(path)

        suite_dir = CONTRACT_ROOT / path
        if not suite_dir.is_dir():
            errors.append(f"{path}: directory is missing")

        category = suite.get("category")
        if category not in CATEGORIES or path.split("/", 1)[0] != category:
            errors.append(f"{path}: invalid or mismatched category {category!r}")
        if suite.get("expectedOutcome") not in EXPECTED_OUTCOMES:
            errors.append(f"{path}: invalid expectedOutcome {suite.get('expectedOutcome')!r}")
        if suite.get("currentStatus") != "active":
            errors.append(f"{path}: currentStatus must be active after promotion")
        if not isinstance(suite.get("ownerStage"), str) or not OWNER_STAGE.fullmatch(
            suite["ownerStage"]
        ):
            errors.append(f"{path}: invalid ownerStage {suite.get('ownerStage')!r}")

        sections = suite.get("appendixSections")
        if not isinstance(sections, list) or not sections:
            errors.append(f"{path}: appendixSections must be a nonempty list")
        elif any(section not in REQUIRED_APPENDIX_SECTIONS for section in sections):
            errors.append(f"{path}: invalid Appendix T section")
        else:
            covered_sections.update(sections)

        capabilities = suite.get("capabilities")
        if (
            not isinstance(capabilities, list)
            or any(not isinstance(capability, str) or not capability for capability in capabilities)
            or capabilities != sorted(set(capabilities))
        ):
            errors.append(f"{path}: capabilities must be sorted unique strings")

        files = suite.get("files")
        if not isinstance(files, list) or not files:
            errors.append(f"{path}: files must be a nonempty list")
            continue
        if files != list(dict.fromkeys(files)):
            errors.append(f"{path}: files contains duplicates")
        for relative_file in files:
            if not isinstance(relative_file, str) or not (suite_dir / relative_file).is_file():
                errors.append(f"{path}: missing declared file {relative_file!r}")
        if suite_dir.is_dir():
            actual_files = {
                str(child.relative_to(suite_dir))
                for child in suite_dir.rglob("*")
                if child.is_file()
            }
            declared_files = {
                relative_file for relative_file in files if isinstance(relative_file, str)
            }
            if actual_files != declared_files:
                errors.append(
                    f"{path}: manifest files differ from suite files: "
                    f"unowned={sorted(actual_files - declared_files)}, "
                    f"missing={sorted(declared_files - actual_files)}"
                )

        if suite_dir.is_dir() and not any(
            child.name in SUITE_ENTRY_NAMES for child in suite_dir.iterdir() if child.is_file()
        ):
            errors.append(f"{path}: suite has neither main.kp nor suite.ktest")

    actual_paths = {
        str(path.parent.relative_to(CONTRACT_ROOT))
        for path in CONTRACT_ROOT.rglob("*")
        if path.is_file() and path.name in SUITE_ENTRY_NAMES
    }
    if actual_paths != declared_paths:
        errors.append(
            "manifest paths differ from suite directories: "
            f"missing={sorted(actual_paths - declared_paths)}, "
            f"extra={sorted(declared_paths - actual_paths)}"
        )

    missing_sections = REQUIRED_APPENDIX_SECTIONS - covered_sections
    if missing_sections:
        errors.append(f"Appendix T sections lack owners: {sorted(missing_sections)}")

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    counts: dict[str, int] = {}
    for suite in suites:
        category = suite["category"]
        counts[category] = counts.get(category, 0) + 1
    rendered = ", ".join(f"{category}={counts[category]}" for category in sorted(counts))
    print(f"Nat/Fin contract validation passed: {len(suites)} active suites ({rendered})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
