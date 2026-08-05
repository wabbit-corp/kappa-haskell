#!/usr/bin/env python3
"""Validate the staged derive-automation pending bundle.

Checks tests/pending-import/derive-automation/ against its manifest.json:
109 suites; every root and listed file exists; no stray suite dirs; every
non-incremental suite carries inline `--!` directives in its first .kp;
incremental suites have incremental.ktest plus contiguous stepN roots.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BUNDLE = ROOT / "tests" / "pending-import" / "derive-automation"


def main() -> int:
    problems: list[str] = []
    manifest = json.loads((BUNDLE / "manifest.json").read_text())
    if len(manifest) != 109:
        problems.append(f"manifest has {len(manifest)} suites, expected 109")

    listed = set()
    for suite in manifest:
        rel = suite["root"].removeprefix("tests/")
        listed.add(rel)
        sdir = BUNDLE / rel
        if not sdir.is_dir():
            problems.append(f"missing suite root: {rel}")
            continue
        for f in suite["files"]:
            if not (sdir / f).is_file():
                problems.append(f"{rel}: listed file missing: {f}")
        incremental = any(f == "incremental.ktest" for f in suite["files"])
        if incremental:
            steps = sorted(
                int(p.name[4:])
                for p in sdir.iterdir()
                if p.is_dir() and re.fullmatch(r"step\d+", p.name)
            )
            if not steps or steps != list(range(len(steps))):
                problems.append(f"{rel}: bad incremental steps {steps}")
        else:
            kps = [f for f in suite["files"] if f.endswith(".kp")]
            if not kps:
                problems.append(f"{rel}: no .kp files listed")
            else:
                joined = "".join((sdir / f).read_text() for f in kps)
                if "--! " not in joined:
                    problems.append(f"{rel}: no inline directives found")

    on_disk = {
        p.name for p in BUNDLE.iterdir() if p.is_dir() and p.name != "retargeted"
    }
    for stray in sorted(on_disk - listed):
        problems.append(f"on-disk suite not in manifest: {stray}")
    for missing in sorted(listed - on_disk):
        problems.append(f"manifest suite not on disk: {missing}")

    if problems:
        print("Derive-automation contract validation FAILED:")
        for p in problems:
            print("  " + p)
        return 1
    print(f"Derive-automation contract validation passed: {len(manifest)} pending suites")
    return 0


if __name__ == "__main__":
    sys.exit(main())
