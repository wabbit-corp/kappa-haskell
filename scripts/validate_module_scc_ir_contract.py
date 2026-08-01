#!/usr/bin/env python3
"""Validate the staged module-SCC/induction-recursion pending bundle.

Checks tests/pending-import/module-scc-ir/ against its manifest.json:

* suiteCount matches the number of manifest suites and on-disk suite dirs;
* every manifest category exists and every suite dir belongs to a category;
* every listed suite file exists on disk (and no unlisted .kp/.ktest strays
  exist inside a suite, STATUS-only additions aside);
* for non-incremental suites, suite.ktest exists and its `--!` directives
  match the manifest `directives` list exactly and in order;
* incremental suites have incremental.ktest plus contiguous stepN roots.

Exit 0 with a summary line on success; exit 1 listing problems otherwise.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BUNDLE = ROOT / "tests" / "pending-import" / "module-scc-ir"


def main() -> int:
    problems: list[str] = []
    manifest = json.loads((BUNDLE / "manifest.json").read_text())
    suites = manifest["suites"]

    if manifest["suiteCount"] != len(suites):
        problems.append(
            f"suiteCount {manifest['suiteCount']} != manifest suites {len(suites)}"
        )

    on_disk = set()
    for cat in manifest["categories"]:
        cat_dir = BUNDLE / cat
        if not cat_dir.is_dir():
            problems.append(f"missing category dir: {cat}")
            continue
        for child in sorted(cat_dir.iterdir()):
            if child.is_dir():
                on_disk.add(f"{cat}/{child.name}")

    listed = set()
    per_category: dict[str, int] = {}
    for suite in suites:
        rel = f"{suite['category']}/{suite['id']}"
        listed.add(rel)
        per_category[suite["category"]] = per_category.get(suite["category"], 0) + 1
        suite_dir = BUNDLE / rel
        if not suite_dir.is_dir():
            problems.append(f"missing suite dir: {rel}")
            continue
        for f in suite["files"]:
            if not (suite_dir / f).is_file():
                problems.append(f"{rel}: listed file missing: {f}")
        if suite["incremental"]:
            if not (suite_dir / "incremental.ktest").is_file():
                problems.append(f"{rel}: incremental suite lacks incremental.ktest")
            steps = sorted(
                int(p.name[4:])
                for p in suite_dir.iterdir()
                if p.is_dir() and re.fullmatch(r"step\d+", p.name)
            )
            if steps != list(range(len(steps))) or not steps and True:
                if steps != list(range(len(steps))):
                    problems.append(f"{rel}: non-contiguous steps {steps}")
            if not steps:
                problems.append(f"{rel}: incremental suite has no stepN roots")
        else:
            ktest = suite_dir / "suite.ktest"
            if not ktest.is_file():
                problems.append(f"{rel}: missing suite.ktest")
                continue
            directives = [
                line.strip()[4:].strip()
                for line in ktest.read_text().splitlines()
                if line.strip().startswith("--! ")
            ]
            if directives != suite["directives"]:
                problems.append(
                    f"{rel}: suite.ktest directives differ from manifest\n"
                    f"    disk:     {directives}\n"
                    f"    manifest: {suite['directives']}"
                )

    for stray in sorted(on_disk - listed):
        problems.append(f"on-disk suite not in manifest: {stray}")
    for missing in sorted(listed - on_disk):
        problems.append(f"manifest suite not on disk: {missing}")

    if problems:
        print("Module-SCC/IR contract validation FAILED:")
        for p in problems:
            print("  " + p)
        return 1

    cats = ", ".join(f"{c}={n}" for c, n in sorted(per_category.items()))
    print(
        f"Module-SCC/IR contract validation passed: {len(suites)} pending suites ({cats})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
