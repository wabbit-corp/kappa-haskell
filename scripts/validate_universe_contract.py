#!/usr/bin/env python3
"""Validate the U-E/U-F/U-G universe-suite ledgers and source files."""

from __future__ import annotations

import json
import hashlib
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
STAGES = (
    {f"U-E{i}" for i in range(1, 10)}
    | {f"U-F{i}" for i in range(1, 9)}
    | {f"U-G{i}" for i in range(1, 9)}
)
EXPECTATIONS = {"accept", "reject"}
HARNESS_OUTCOMES = {"pass", "unsupported"}
CAPABILITY_DIRECTIVE = re.compile(r"^\s*--!\s*requires\s+capability\s+([A-Za-z0-9_.-]+)\s*$")

VARIANCE_OWNER_STAGES = {
    **{path: "U-F8" for path in (
        "future/hiit_path_naturality_negative",
        "future/hiit_path_naturality_positive",
        "future/hirt_recursive_equation_negative",
        "future/hirt_recursive_equation_positive",
        "future/qiit_joint_variance_negative",
        "future/qiit_joint_variance_positive",
        "future/qit_quotient_equation_negative",
        "future/qit_quotient_equation_positive",
    )},
    "interface/roles_affect_semantic_identity": "U-F6",
    **{path: "U-F5" for path in (
        "kcore/reject_family_argument_mismatch",
        "kcore/reject_family_head_mismatch",
        "kcore/reject_forged_schema_certificate",
        "kcore/reject_runtime_transform_certificate",
        "kcore/reject_unsaturated_schema_lift",
        "kcore/reject_wrong_direction_schema_lift",
        "kcore/roundtrip_mutual_role_fixed_point",
        "kcore/roundtrip_schema_lift",
        "kcore/roundtrip_variance_certificate",
    )},
    "negative/annotation_covariant_too_permissive": "U-F1",
    "negative/annotation_irrelevant_too_permissive": "U-F1",
    "negative/variance_not_applicable_term": "U-F1",
    "negative/parametric_field_not_irrelevant": "U-F2",
    "negative/covariant_downcast": "U-F3",
    "negative/invariant_mismatch": "U-F3",
    "negative/mismatched_family_arguments": "U-F3",
    "negative/schema_constraint_target_invalid": "U-F3",
    "positive/infer_covariant_ordinary_code": "U-F2",
    "positive/infer_covariant_parametric_witness": "U-F2",
    "positive/infer_invariant_function_domain": "U-F2",
    "positive/infer_irrelevant_box": "U-F2",
    "positive/infer_irrelevant_phantom": "U-F2",
    "positive/explicit_stricter_covariant": "U-F2",
    "positive/explicit_stricter_invariant": "U-F2",
    "positive/covariant_up_lift": "U-F3",
    "positive/gadt_family_arguments_align": "U-F3",
    "positive/irrelevant_bidirectional_lift": "U-F3",
    "positive/schema_lift_case_coherence": "U-F3",
    "positive/schema_lift_composition": "U-F3",
    "positive/opaque_import_certificate": "U-F6",
    "positive/trait_evidence_irrelevant": "U-F6",
    "positive/equality_irrelevant": "U-F7",
    "positive/typebelow_covariant": "U-F7",
}

FIRST_CLASS_LEVEL_OWNER_STAGES = {
    **{path: "U-G4" for path in (
        "kcore/arithmetic_certificate_bad_assumption",
        "kcore/arithmetic_certificate_valid",
        "kcore/canonical_ac_level_hash",
        "kcore/direct_and_composed_lift_same_hash",
        "kcore/lift_proof_identity_hash",
        "kcore/monotone_witness_alpha_roundtrip",
        "kcore/monotone_witness_proof_irrelevant_hash",
        "kcore/reject_declared_sealing_eliminator",
        "kcore/structural_and_arithmetic_same_hash",
        "kcore/typelevel_algebra_version_mismatch",
    )},
    **{path: "U-G2" for path in (
        "negative/principal_self_containment",
        "solver/constructor_nf_add_ac",
        "solver/constructor_nf_max_aci",
        "solver/monotone_not_order_embedding",
        "solver/neutral_atom_not_entailed",
        "solver/no_pointwise_least",
        "solver/outside_portable_fragment",
        "solver/principal_additive_cancellation",
        "solver/principal_closed_residuation",
        "solver/principal_direct_lower_bounds",
        "solver/principal_single_meta_max_context",
        "solver/principal_successor_cancellation",
        "solver/semantic_distribution_beyond_nf",
        "solver/semantic_equality_beyond_nf",
    )},
    **{path: "U-G5" for path in (
        "negative/recursive_schema_increase",
        "negative/recursive_schema_leq_not_termination",
        "negative/recursive_schema_nonidentity_implicit",
        "positive/first_class_level_recursion_can_increase",
        "positive/recursive_schema_identity",
        "positive/recursive_schema_lower",
        "positive/recursive_schema_strict_level_termination",
    )},
    **{path: "U-G7" for path in (
        "negative/monotone_theorem_not_scanned",
        "kcore/reject_unwitnessed_neutral_covariance",
        "positive/imported_monotone_certificate",
        "positive/monotone_global_instance",
        "positive/monotone_local_evidence",
        "positive/standard_add_partial_monotone",
    )},
    **{path: "U-G6" for path in (
        "negative/forall_does_not_commute_implicitly",
        "negative/inverse_schema_lift_not_implicit",
        "negative/schema_reification_does_not_fill_explicit_level",
        "positive/branch_expected_widening",
        "positive/forall_commutes_with_selected_evidence",
        "positive/preserve_existing_forall",
        "positive/schema_lift_expected_type_direct",
        "positive/schema_lift_not_used_for_meta_solving",
        "positive/schema_reify_bounded_expected_type",
        "positive/schema_store_bounded_first_class",
        "positive/schema_store_monomorphic_context",
    )},
    **{path: "U-G1" for path in (
        "negative/distinct_neutral_atoms_need_evidence",
        "negative/mutable_current_level_index",
        "negative/wrong_type_level_index",
        "positive/exact_level_result_not_widened",
        "positive/level_snapshot_from_var",
        "positive/neutral_level_bound_evidence",
        "positive/neutral_term_schema_instantiation",
        "positive/opaque_level_application_exact_result",
        "positive/record_projection_level_index",
        "positive/same_neutral_term_atom_identity",
    )},
    **{path: "U-G3" for path in (
        "negative/generalization_meta_free_in_environment",
        "negative/generalization_parametric_escape",
        "negative/monadic_bound_value_not_generalized",
        "negative/pattern_match_does_not_drop_dependency",
        "negative/schema_constraint_unsatisfied",
        "negative/unbounded_parametric_package_no_code_escape",
        "positive/action_value_generalizes_outer_parameter",
        "positive/explicit_schema_constraint_proof_binder",
        "positive/inferred_schema_constraint_becomes_binder",
        "positive/local_closure_body_constraint",
        "positive/local_declaration_universe_generalization",
        "positive/unbounded_parametric_package_projection",
        "positive/unbounded_parametric_package_repack",
        "positive/user_constraint_reuses_generated_obligation",
    )},
}

FIRST_CLASS_LEVEL_STRENGTHENING = {
    "kcore/monotone_witness_alpha_roundtrip",
    "kcore/monotone_witness_proof_irrelevant_hash",
    "kcore/reject_unwitnessed_neutral_covariance",
    "positive/imported_monotone_certificate",
    "positive/local_closure_body_constraint",
}

CONTRACTS = [
    (
        ROOT / "tests/conformance/spec-coverage/ordinary-parametric-kcoretext",
        ["manifest.json"],
        48,
        None,
        None,
    ),
    (
        ROOT / "tests/conformance/spec-coverage/parametric-packages-universe-schemas",
        ["manifest.json", "extension-manifest.json"],
        89,
        None,
        None,
    ),
    (
        ROOT / "tests/conformance/spec-coverage/universe-variance",
        ["manifest.json"],
        42,
        VARIANCE_OWNER_STAGES,
        None,
    ),
    (
        ROOT / "tests/conformance/spec-coverage/first-class-levels-solver-generalization",
        ["manifest.json"],
        72,
        FIRST_CLASS_LEVEL_OWNER_STAGES,
        (67, FIRST_CLASS_LEVEL_STRENGTHENING),
    ),
]


def load_manifest(path: Path) -> tuple[dict[str, object], list[dict[str, object]]]:
    data = json.loads(path.read_text())
    suites = data.get("suites")
    count = data.get("suiteCount")
    if not isinstance(suites, list) or count != len(suites):
        raise ValueError(f"{path}: suiteCount {count!r} does not match suites")
    return data, suites


def validate_root(
    root: Path,
    manifests: list[str],
    expected: int,
    external_stages: dict[str, str] | None = None,
    provenance_contract: tuple[int, set[str]] | None = None,
) -> list[str]:
    errors: list[str] = []
    entries: dict[str, tuple[Path, dict[str, object]]] = {}
    manifest_data: dict[str, dict[str, object]] = {}
    for manifest_name in manifests:
        manifest_path = root / manifest_name
        try:
            data, suites = load_manifest(manifest_path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(str(exc))
            continue
        manifest_data[manifest_name] = data
        for suite in suites:
            path = suite.get("path")
            stage = suite.get("ownerStage")
            files = suite.get("files")
            if not isinstance(path, str):
                errors.append(f"{manifest_path}: suite has no string path")
                continue
            if path in entries:
                errors.append(f"{root}: duplicate suite path {path}")
                continue
            entries[path] = (manifest_path, suite)
            if stage not in STAGES:
                errors.append(f"{manifest_path}: {path} has invalid ownerStage {stage!r}")
            if external_stages is not None and external_stages.get(path) != stage:
                errors.append(
                    f"{manifest_path}: {path} ownerStage {stage!r} disagrees with the stage ledger "
                    f"{external_stages.get(path)!r}"
                )
            category = suite.get("category")
            description = suite.get("description")
            expectation = suite.get("sourceExpectation")
            harness_outcome = suite.get("harnessOutcome")
            capabilities = suite.get("capabilities")
            if not isinstance(category, str) or not category:
                errors.append(f"{manifest_path}: {path} has no category")
            if not isinstance(description, str) or not description:
                errors.append(f"{manifest_path}: {path} has no description")
            if expectation not in EXPECTATIONS:
                errors.append(f"{manifest_path}: {path} has invalid sourceExpectation {expectation!r}")
            if harness_outcome not in HARNESS_OUTCOMES:
                errors.append(f"{manifest_path}: {path} has invalid harnessOutcome {harness_outcome!r}")
            if (
                not isinstance(capabilities, list)
                or any(not isinstance(capability, str) or not capability for capability in capabilities)
                or capabilities != sorted(set(capabilities))
            ):
                errors.append(f"{manifest_path}: {path} capabilities must be a sorted unique string list")
            if not isinstance(files, list) or not files:
                errors.append(f"{manifest_path}: {path} has no files")
                continue
            entry_points = {"main.kp", "suite.ktest"} & set(files)
            if not entry_points:
                errors.append(f"{manifest_path}: {path} files omit its active entry point")
            directive_capabilities: set[str] = set()
            for source in files:
                source_path = root / path / source if isinstance(source, str) else None
                if source_path is None or not source_path.is_file():
                    errors.append(f"{manifest_path}: missing {path}/{source}")
                    continue
                for line in source_path.read_text().splitlines():
                    match = CAPABILITY_DIRECTIVE.match(line)
                    if match:
                        directive_capabilities.add(match.group(1))
            if isinstance(capabilities, list) and sorted(directive_capabilities) != capabilities:
                errors.append(
                    f"{manifest_path}: {path} capabilities {capabilities!r} disagree with directives "
                    f"{sorted(directive_capabilities)!r}"
                )
            expected_outcome = "unsupported" if category == "future" else "pass"
            if harness_outcome in HARNESS_OUTCOMES and harness_outcome != expected_outcome:
                errors.append(
                    f"{manifest_path}: {path} harnessOutcome {harness_outcome!r} disagrees with "
                    f"its capability contract {expected_outcome!r}"
                )

    active = {
        str(path.parent.relative_to(root))
        for pattern in ("main.kp", "suite.ktest")
        for path in root.rglob(pattern)
    }
    registered = set(entries)
    for path in sorted(active - registered):
        errors.append(f"{root}: active suite is not registered: {path}")
    for path in sorted(registered - active):
        errors.append(f"{root}: registered suite has no active entry point: {path}")
    if len(entries) != expected:
        errors.append(f"{root}: expected {expected} registered suites, found {len(entries)}")
    if provenance_contract is not None:
        base_count, strengthening_paths = provenance_contract
        data = manifest_data.get("manifest.json")
        if data is not None:
            declared_strengthening = data.get("strengtheningSuites")
            declared_strengthening_set = (
                set(declared_strengthening)
                if isinstance(declared_strengthening, list)
                and all(isinstance(path, str) for path in declared_strengthening)
                else None
            )
            if data.get("baseSpec") != "docs/Spec.md" or not (ROOT / "docs/Spec.md").is_file():
                errors.append(f"{root}: active baseSpec must resolve to docs/Spec.md")
            if data.get("baseSuiteCount") != base_count:
                errors.append(f"{root}: baseSuiteCount must be {base_count}")
            if data.get("strengtheningSuiteCount") != len(strengthening_paths):
                errors.append(
                    f"{root}: strengtheningSuiteCount must be {len(strengthening_paths)}"
                )
            if declared_strengthening_set != strengthening_paths:
                errors.append(
                    f"{root}: strengtheningSuites do not match the exact implementation-strengthening ledger"
                )
            if isinstance(declared_strengthening, list) and declared_strengthening != sorted(declared_strengthening):
                errors.append(f"{root}: strengtheningSuites must be sorted")
            if not strengthening_paths <= set(entries):
                errors.append(f"{root}: strengtheningSuites contain unregistered paths")
            if len(entries) - len(strengthening_paths) != base_count:
                errors.append(
                    f"{root}: registered suites do not partition into {base_count} base + "
                    f"{len(strengthening_paths)} strengthening suites"
                )
            source_manifest_name = data.get("sourceManifest")
            source_patch_name = data.get("sourceSpecPatch")
            provenance_files = (
                ("sourceManifest", source_manifest_name, data.get("sourceManifestSha256")),
                ("sourceSpecPatch", source_patch_name, data.get("sourceSpecPatchSha256")),
            )
            for label, relative_name, expected_digest in provenance_files:
                if not isinstance(relative_name, str) or not isinstance(expected_digest, str):
                    errors.append(f"{root}: {label} provenance path and SHA-256 are mandatory")
                    continue
                source_path = ROOT / relative_name
                if not source_path.is_file():
                    errors.append(f"{root}: {label} does not exist: {relative_name}")
                    continue
                actual_digest = hashlib.sha256(source_path.read_bytes()).hexdigest()
                if actual_digest != expected_digest:
                    errors.append(
                        f"{root}: {label} SHA-256 mismatch; expected {expected_digest}, "
                        f"found {actual_digest}"
                    )
            if isinstance(source_manifest_name, str):
                source_manifest_path = ROOT / source_manifest_name
                try:
                    source_data, source_suites = load_manifest(source_manifest_path)
                    source_paths = {
                        suite.get("path")
                        for suite in source_suites
                        if isinstance(suite.get("path"), str)
                    }
                    active_base_paths = set(entries) - strengthening_paths
                    if source_data.get("suiteCount") != base_count:
                        errors.append(
                            f"{root}: source manifest suiteCount must be {base_count}"
                        )
                    if source_paths != active_base_paths:
                        errors.append(
                            f"{root}: active base suites do not exactly match the source manifest"
                        )
                except (OSError, ValueError, json.JSONDecodeError) as exc:
                    errors.append(str(exc))
    if external_stages is not None:
        if set(external_stages) != registered:
            errors.append(f"{root}: stage ledger paths do not exactly match the manifest")
        future = {path for path, (_, suite) in entries.items() if suite.get("category") == "future"}
        if future:
            if len(future) != 8 or len(entries) - len(future) != 34:
                errors.append(f"{root}: expected 34 current and 8 future suites, found {len(entries) - len(future)} and {len(future)}")
            for path in sorted(future):
                suite_file = root / path / "suite.ktest"
                text = suite_file.read_text() if suite_file.is_file() else ""
                if "requires capability" not in text or "UniverseVariance" not in text:
                    errors.append(f"{root}: future suite is not capability-gated: {path}")
    return errors


def main() -> int:
    errors = [
        error
        for root, manifests, expected, external_stages, provenance_contract in CONTRACTS
        for error in validate_root(
            root, manifests, expected, external_stages, provenance_contract
        )
    ]
    if errors:
        print("universe contract validation failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    print(
        "universe contract validation passed: 48 ordinary-parametric, "
        "89 parametric-package, 34 current variance + 8 gated future variance, "
        "67 first-class-level base + 5 strengthening suites"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
