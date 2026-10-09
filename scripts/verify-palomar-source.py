#!/usr/bin/env python3
"""Audit the local Palomar surface before running Comparator.

This is a staging-repository guard, not a replacement for Palomar's official
verifier.  It deliberately imports the validators from the pinned
PalomarSubmission checkout for Comparator JSON and formalization.yaml.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


DECLARATION_RE = re.compile(
    r"(?m)^[ \t]*(?:noncomputable[ \t]+)?(theorem|lemma|def)[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b"
)
TOKEN_RE = re.compile(
    r"\b(?:admit|sorry|sorryAx)\b|"
    r"(?m:^[ \\t]*(?:axiom|axioms|constant|constants|opaque|unsafe)\b)"
)
IMPORT_RE = re.compile(r"(?m)^[ \t]*import[ \t]+([A-Za-z_][A-Za-z0-9_'.]*)")
GITHUB_URL_RE = re.compile(
    r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?"
)
SHA_RE = re.compile(r"[0-9a-f]{40}")
LICENSE_RE = re.compile(
    r"(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?",
    re.IGNORECASE,
)


class AuditError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise AuditError(message)


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            fail(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        fail(f"cannot read valid JSON from {path}: {error}")
    if not isinstance(value, dict):
        fail(f"{path} must contain one JSON object")
    return value


def regular_path(root: Path, relative: str) -> Path:
    pure = Path(relative)
    if pure.is_absolute() or ".." in pure.parts or pure.as_posix() != relative:
        fail(f"unsafe repository-relative path in policy: {relative!r}")
    path = root / pure
    if path.is_symlink() or not path.is_file():
        fail(f"required regular file is missing: {relative}")
    try:
        path.resolve().relative_to(root)
    except ValueError:
        fail(f"path escapes repository root: {relative}")
    return path


def strip_lean_comments_and_strings(source: str) -> str:
    """Blank comments and strings while retaining newlines and source offsets."""
    output = list(source)
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        if block_depth:
            if source.startswith("/-", index):
                output[index : index + 2] = "  "
                block_depth += 1
                index += 2
            elif source.startswith("-/", index):
                output[index : index + 2] = "  "
                block_depth -= 1
                index += 2
            else:
                if source[index] != "\n":
                    output[index] = " "
                index += 1
            continue
        if in_string:
            if source[index] != "\n":
                output[index] = " "
            if escaped:
                escaped = False
            elif source[index] == "\\":
                escaped = True
            elif source[index] == '"':
                in_string = False
            index += 1
            continue
        if source.startswith("--", index):
            while index < len(source) and source[index] != "\n":
                output[index] = " "
                index += 1
            continue
        if source.startswith("/-", index):
            output[index : index + 2] = "  "
            block_depth = 1
            index += 2
            continue
        if source[index] == '"':
            output[index] = " "
            in_string = True
        index += 1
    if block_depth:
        fail("unterminated Lean block comment")
    if in_string:
        fail("unterminated Lean string")
    return "".join(output)


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def expected_holes(entry: dict[str, Any]) -> dict[str, str]:
    holes = entry.get("holes")
    if not isinstance(holes, list) or not holes:
        fail(f"entry {entry.get('id')!r} has no hole allowlist")
    result: dict[str, str] = {}
    for item in holes:
        if not isinstance(item, dict):
            fail(f"entry {entry.get('id')!r} has a malformed hole record")
        name, kind = item.get("name"), item.get("kind")
        if not isinstance(name, str) or not name or kind not in {"definition", "theorem"}:
            fail(f"entry {entry.get('id')!r} has a malformed hole record")
        if name in result:
            fail(f"duplicate allowlisted declaration: {name}")
        result[name] = kind
    return result


def audit_challenge_holes(path: Path, holes: dict[str, str]) -> None:
    source = path.read_text(encoding="utf-8")
    stripped = strip_lean_comments_and_strings(source)
    example = re.search(r"(?m)^[ \t]*example\b", stripped)
    if example:
        line = line_number(stripped, example.start())
        fail(f"{path}:{line}: Challenge examples are not allowed in the hole surface")
    declarations = list(DECLARATION_RE.finditer(stripped))
    allowed_by_short_name: dict[str, tuple[str, str]] = {}
    for name, kind in holes.items():
        short_name = name.rsplit(".", 1)[-1]
        if short_name in allowed_by_short_name:
            fail(f"{path}: ambiguous short declaration name {short_name}")
        allowed_by_short_name[short_name] = (name, kind)

    seen: dict[str, int] = {name: 0 for name in holes}
    for match in TOKEN_RE.finditer(stripped):
        token = match.group(0).strip()
        line = line_number(stripped, match.start())
        if token != "sorry":
            fail(f"{path}:{line}: forbidden Lean token {token!r}")
        preceding = [declaration for declaration in declarations if declaration.start() < match.start()]
        if not preceding:
            fail(f"{path}:{line}: sorry is outside a declaration")
        declaration = preceding[-1]
        actual_kind = "definition" if declaration.group(1) == "def" else "theorem"
        short_name = declaration.group(2)
        allowed = allowed_by_short_name.get(short_name)
        if allowed is None:
            fail(f"{path}:{line}: sorry in non-allowlisted declaration {short_name}")
        name, expected_kind = allowed
        if actual_kind != expected_kind:
            fail(f"{path}:{line}: {name} is {actual_kind}, expected {expected_kind}")
        seen[name] += 1

    wrong = {name: count for name, count in seen.items() if count != 1}
    if wrong:
        fail(f"{path}: every allowlisted declaration must contain exactly one sorry: {wrong}")


def tracked_lean_files(root: Path) -> list[Path]:
    process = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"],
        check=True,
        capture_output=True,
    )
    return [root / item.decode("utf-8") for item in process.stdout.split(b"\0") if item]


def audit_lean_sources(root: Path, entries: list[dict[str, Any]]) -> int:
    challenge_holes = {
        entry["challenge"]: expected_holes(entry)
        for entry in entries
    }
    discovered = {
        path.relative_to(root).as_posix()
        for path in (root / "Palomar").glob("*/Challenge.lean")
    }
    if discovered != set(challenge_holes):
        fail(
            "Challenge file set differs from the allowlist: "
            f"expected {sorted(challenge_holes)}, found {sorted(discovered)}"
        )

    for relative, holes in challenge_holes.items():
        audit_challenge_holes(root / relative, holes)

    for path in tracked_lean_files(root):
        relative = path.relative_to(root).as_posix()
        if relative in challenge_holes:
            continue
        source = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        match = TOKEN_RE.search(source)
        if match:
            line = line_number(source, match.start())
            fail(f"{relative}:{line}: forbidden substantive Lean token {match.group(0).strip()!r}")
    return sum(len(holes) for holes in challenge_holes.values())


def audit_imports(path: Path) -> None:
    source = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
    imports = IMPORT_RE.findall(source)
    if not imports:
        fail(f"{path}: Challenge must import an explicit Mathlib surface")
    rejected = [module for module in imports if module != "Mathlib" and not module.startswith("Mathlib.")]
    if rejected:
        fail(f"{path}: Challenge imports outside Mathlib: {rejected}")
    if path.stat().st_size > 100 * 1024 or len(source.splitlines()) > 1000:
        fail(f"{path}: Challenge exceeds Palomar's hard size limit")


def path_is_within(path: Path, roots: list[Path]) -> bool:
    for root in roots:
        try:
            path.relative_to(root)
            return True
        except ValueError:
            continue
    return False


def audit_challenge_closure(root: Path, entries: list[dict[str, Any]]) -> None:
    lean_prefix_process = subprocess.run(
        ["lean", "--print-prefix"], check=True, capture_output=True, text=True
    )
    trusted_roots = [Path(lean_prefix_process.stdout.strip()).resolve()]
    manifest = load_json(root / "lake-manifest.json")
    for package in manifest.get("packages", []):
        name = package.get("name")
        if isinstance(name, str) and name:
            trusted_roots.append((root / ".lake" / "packages" / name).resolve())
    for entry in entries:
        challenge = root / entry["challenge"]
        process = subprocess.run(
            ["lake", "env", "lean", "--src-deps", str(challenge)],
            cwd=root,
            capture_output=True,
            text=True,
        )
        if process.returncode:
            sys.stdout.write(process.stdout)
            sys.stderr.write(process.stderr)
            fail(f"{challenge}: Lean source-closure query failed")
        for raw_path in process.stdout.splitlines():
            if not raw_path.strip():
                continue
            dependency = Path(raw_path.strip())
            if not dependency.is_absolute() or dependency.suffix != ".lean":
                fail(f"{challenge}: Lean reported an invalid source dependency {raw_path!r}")
            resolved = dependency.resolve(strict=True)
            if not path_is_within(resolved, trusted_roots):
                fail(f"{challenge}: untrusted source dependency {resolved}")


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def import_official_validators(pipeline: Path) -> tuple[Any, Any, Any]:
    if pipeline.is_symlink() or not pipeline.is_dir():
        fail(f"official pipeline checkout is missing: {pipeline}")
    sys.path.insert(0, str(pipeline))
    try:
        from scripts.submission_contract import load_formalization_metadata
        from scripts.verify_submission import load_comparator_config, manifest_packages
    except (ImportError, ModuleNotFoundError) as error:
        fail(f"cannot import pinned official validators: {error}")
    return load_formalization_metadata, load_comparator_config, manifest_packages


def audit_official_profile(policy: dict[str, Any], pipeline: Path) -> None:
    expected = policy["official_profile"]
    head = subprocess.run(
        ["git", "-C", str(pipeline), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if head != expected["palomar_submission_commit"]:
        fail(f"official pipeline is at {head}, expected {expected['palomar_submission_commit']}")
    profile = load_json(pipeline / "verification-profile.json")
    comparisons = {
        "id": profile.get("id"),
        "runner": profile.get("runner", {}).get("label"),
        "job_timeout_minutes": profile.get("limits", {}).get("job_timeout_minutes"),
        "execution_budget_seconds": profile.get("limits", {}).get("execution_budget_seconds"),
        "comparator_commit": profile.get("trusted_tools", {}).get("comparator_commit"),
        "landrun_commit": profile.get("trusted_tools", {}).get("landrun_commit"),
        "nanoda_commit": profile.get("trusted_tools", {}).get("nanoda_commit"),
    }
    for key, actual in comparisons.items():
        if expected.get(key) != actual:
            fail(f"official profile drift for {key}: policy={expected.get(key)!r}, official={actual!r}")


def audit_license(root: Path, policy: dict[str, Any], metadata: list[dict[str, Any]]) -> None:
    record = policy["license"]
    path = regular_path(root, record["path"])
    candidates = [item for item in root.iterdir() if item.is_file() and LICENSE_RE.fullmatch(item.name)]
    if candidates != [path]:
        fail(f"expected exactly one root license file, found {[item.name for item in candidates]}")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != record["sha256"]:
        fail(f"{path}: digest differs from the reviewed {record['spdx']} license")
    if "Apache License" not in path.read_text(encoding="utf-8"):
        fail(f"{path}: reviewed Apache-2.0 marker is missing")
    for item in metadata:
        declared = item.get("project", {}).get("license")
        if declared != record["spdx"]:
            fail(f"formalization.yaml declares {declared!r}, expected {record['spdx']!r}")


def audit_dependencies(root: Path, manifest_packages: Any) -> int:
    packages = manifest_packages(root)
    if not packages:
        fail("lake-manifest.json has no dependencies")
    for package in packages:
        url, revision = package["url"], package["revision"]
        if not isinstance(url, str) or not GITHUB_URL_RE.fullmatch(url):
            fail(f"dependency {package['name']!r} is not a canonical public GitHub URL: {url!r}")
        if not SHA_RE.fullmatch(revision):
            fail(f"dependency {package['name']!r} is not pinned to a full commit")
    mathlib = [package for package in packages if package["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["repository"] != "leanprover-community/mathlib4":
        fail("the manifest must contain exactly the canonical Mathlib dependency")
    root_manifest = load_json(root / "lake-manifest.json")
    mathlib_manifest = load_json(
        root / ".lake" / "packages" / "mathlib" / "lake-manifest.json"
    )
    official_closure = {
        item.get("name"): item for item in mathlib_manifest.get("packages", [])
    }
    for item in root_manifest.get("packages", []):
        name = item.get("name")
        if name == "mathlib":
            continue
        official = official_closure.get(name)
        compared = ("type", "url", "rev", "subDir")
        if official is None or any(item.get(key) != official.get(key) for key in compared):
            fail(f"dependency {name!r} does not match the pinned Mathlib closure")
    return len(packages)


def audit_entries(
    root: Path,
    policy: dict[str, Any],
    load_metadata: Any,
    load_comparator: Any,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    entries = policy.get("entries")
    if not isinstance(entries, list) or len(entries) != 1:
        fail("policy must contain exactly one Palomar entry")
    metadata_documents: list[dict[str, Any]] = []
    selected: list[dict[str, Any]] = []
    seen_names: set[str] = set()
    for entry in entries:
        for key in ("challenge", "solution", "comparator", "metadata"):
            regular_path(root, entry[key])
        config = load_comparator(root / entry["comparator"])
        metadata = load_metadata(root / entry["metadata"])
        metadata_documents.append(metadata)
        if module_path(config["challenge_module"]) != entry["challenge"]:
            fail(f"{entry['id']}: Challenge module does not match its file")
        if module_path(config["solution_module"]) != entry["solution"]:
            fail(f"{entry['id']}: Solution module does not match its file")
        if config.get("enable_nanoda") is not True:
            fail(f"{entry['id']}: enable_nanoda must be exactly true for the repository preflight")
        if set(config["permitted_axioms"]) != set(policy["standard_axioms"]):
            fail(f"{entry['id']}: permitted_axioms must equal the standard axiom set")
        holes = expected_holes(entry)
        configured = {
            **{name: "theorem" for name in config["theorem_names"]},
            **{name: "definition" for name in config.get("definition_names", [])},
        }
        if configured != holes:
            fail(f"{entry['id']}: Comparator declarations differ from the hole allowlist")
        overlap = seen_names.intersection(configured)
        if overlap:
            fail(f"declarations selected by multiple entries: {sorted(overlap)}")
        seen_names.update(configured)
        audit_imports(root / entry["challenge"])
        selected.append({"solution_module": config["solution_module"], "names": list(configured)})
    if len(seen_names) != 24:
        fail(f"expected exactly 24 selected declarations, found {len(seen_names)}")
    return metadata_documents, selected


def audit_axioms(root: Path, selected: list[dict[str, Any]], allowed: set[str]) -> None:
    lines: list[str] = []
    names: list[str] = []
    for entry in selected:
        lines.append(f"import {entry['solution_module']}")
        names.extend(entry["names"])
    lines.extend(f"#print axioms {name}" for name in names)
    with tempfile.TemporaryDirectory(prefix="palomar-axiom-audit-") as directory:
        source = Path(directory) / "Audit.lean"
        source.write_text("\n".join(lines) + "\n", encoding="utf-8")
        environment = os.environ.copy()
        environment["LEAN_ABORT_ON_PANIC"] = "1"
        process = subprocess.run(
            ["lake", "env", "lean", str(source)],
            cwd=root,
            env=environment,
            capture_output=True,
            text=True,
        )
    if process.returncode:
        sys.stdout.write(process.stdout)
        sys.stderr.write(process.stderr)
        fail("Lean axiom audit did not compile")
    results: dict[str, set[str]] = {}
    depends_pattern = r"'([^']+)' depends on axioms:\s*\[([^]]*)\]"
    for match in re.finditer(depends_pattern, process.stdout):
        axioms = {item.strip() for item in match.group(2).split(",") if item.strip()}
        results[match.group(1)] = axioms
    none_pattern = r"'([^']+)' does not depend on any axioms"
    for match in re.finditer(none_pattern, process.stdout):
        results[match.group(1)] = set()
    missing = set(names) - results.keys()
    if missing:
        fail(f"axiom audit produced no result for: {sorted(missing)}")
    excess = {name: sorted(axioms - allowed) for name, axioms in results.items() if axioms - allowed}
    if excess:
        fail(f"selected declarations use nonstandard axioms: {excess}")
    print(f"Axiom audit passed for {len(names)} selected declarations.")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--policy", type=Path, required=True)
    parser.add_argument("--official-pipeline", type=Path, required=True)
    parser.add_argument("--skip-axioms", action="store_true")
    args = parser.parse_args()

    root = args.root.resolve(strict=True)
    policy = load_json(args.policy.resolve(strict=True))
    if policy.get("schema_version") != 1:
        fail("unsupported Palomar preflight policy schema")
    toolchain = regular_path(root, "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != policy["lean_toolchain"]:
        fail(f"lean-toolchain is {toolchain!r}, expected {policy['lean_toolchain']!r}")

    pipeline = args.official_pipeline.resolve(strict=True)
    audit_official_profile(policy, pipeline)
    load_metadata, load_comparator, manifest_packages = import_official_validators(pipeline)
    metadata, selected = audit_entries(root, policy, load_metadata, load_comparator)
    audit_license(root, policy, metadata)
    dependency_count = audit_dependencies(root, manifest_packages)
    hole_count = audit_lean_sources(root, policy["entries"])
    if hole_count != 24:
        fail(f"expected exactly 24 deliberate Challenge holes, found {hole_count}")
    audit_challenge_closure(root, policy["entries"])
    if not args.skip_axioms:
        audit_axioms(root, selected, set(policy["standard_axioms"]))
    print(
        "Palomar source preflight passed: "
        f"1 entry, {hole_count} deliberate Challenge holes, "
        f"{dependency_count} pinned GitHub dependencies."
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AuditError, KeyError, TypeError, ValueError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
