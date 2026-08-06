#!/usr/bin/env python3
"""
Editorial review registry validator — cf docs/notebook-metadata/editorial-review-registry.md.

Coherence check between the editorial review whitelist (YAML registry) and the
generated catalogue (COURSE_CATALOG.generated.json). Validates:

1. Registry YAML parses cleanly (multi-line literal entries).
2. Each entry's notebook_path exists in the catalogue.
3. review_scope is in the valid enum {typo, pedagogie, factual, substance, full}.
4. reviewer != owner_logique of the notebook (auto-review rejection, cf regle §3.1 #4).
5. evidence_pr (#NNNN) is in MERGED state via `gh pr view` (best-effort: skip if gh unavailable).
6. Cross-check: catalogue entries that the registry should promote (BETA -> FINAL).

Exit codes:
  0 = no errors (warnings allowed)
  1 = errors found (DRIFT/INVALID/MISSING/etc.) — only with --check flag

Anti-FP strategy (cf editorial-review-registry.md §9):
- DRIFT_REVIEWER_ALIAS: reviewer is a substring of owner_logique (heuristic best-effort).
- DRIFT_PR_NOT_TOUCHING: PR diff does not touch the notebook path (TODO c.765+).
- WARN_PR_STATE_UNKNOWN: gh CLI unavailable (CI without auth).
- WARN_REVIEWER_ALIAS: substring heuristic warning, not blocking.

Run:
    python scripts/audit/check_editorial_review.py --check
    python scripts/audit/check_editorial_review.py --registry <path> --catalogue <path>

See also:
    docs/notebook-metadata/editorial-review-registry.md (canonical schema)
    docs/notebook-metadata/EDITORIAL_REVIEW_CARD.md (review template)
    scripts/audit/check_dataset_registry.py (c.795, analogous pattern)
"""
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REVIEW_SCOPES = {"typo", "pedagogie", "factual", "substance", "full"}
PROMOTING_SCOPES = {"factual", "substance", "full"}


def parse_registry(registry_path: Path) -> list[dict]:
    """Extract YAML entries from registry markdown.

    The registry format (cf editorial-review-registry.md §4) uses fenced
    ```yaml blocks containing multi-line literal entries. We parse by
    finding each line starting with "- notebook_path:" and accumulating
    subsequent indented "key: value" lines until the next "- " line.

    This is a simplified YAML parser sufficient for the c.764 whitelist
    (flat dicts, no nesting, no anchors). For complex YAML, use PyYAML.
    """
    text = registry_path.read_text(encoding="utf-8")
    entries = []

    # Find all ```yaml ... ``` blocks (DOTALL: multi-line)
    yaml_blocks = re.findall(r"```yaml\s*\n(.*?)```", text, re.DOTALL)
    for block in yaml_blocks:
        # Skip blocks that are exclusively comments
        non_comment_lines = [
            line for line in block.splitlines()
            if line.strip() and not line.strip().startswith("#")
        ]
        if not non_comment_lines:
            continue

        # Walk through lines, build entries
        current = None
        for line in block.splitlines():
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue
            if stripped.startswith("- "):
                # Save previous entry (only if it has a real evidence_pr,
                # i.e. NOT a template placeholder and NOT empty).
                if current and _is_real_entry(current):
                    entries.append(current)
                # Start new entry: "- key: value"
                kv = stripped[2:]
                key, _, value = kv.partition(":")
                current = {key.strip(): value.strip().strip('"').strip("'")}
            elif current is not None and ":" in stripped:
                # Continuation line: "  key: value"
                key, _, value = stripped.partition(":")
                current[key.strip()] = value.strip().strip('"').strip("'")
        if current and _is_real_entry(current):
            entries.append(current)

    return entries


def _is_real_entry(entry: dict) -> bool:
    """Filter out template/example entries (placeholder values in angle brackets).

    A real registry entry has evidence_pr matching the pattern `#NNNN` (digits only).
    Template entries (cf §2 of the registry) have placeholders like `<#NNNN>` which
    must be excluded from validation.
    """
    evidence = entry.get("evidence_pr", "").strip()
    if not evidence:
        return False
    # Real evidence_pr format: "#NNNN" (digits only, optional leading #)
    digits = evidence.lstrip("#")
    return digits.isdigit()


def load_catalogue(catalogue_path: Path) -> list[dict]:
    """Load JSON catalogue (array of notebook entries)."""
    raw = catalogue_path.read_text(encoding="utf-8")
    data = json.loads(raw)
    if isinstance(data, dict) and "results" in data:
        return data["results"]
    return data


def gh_pr_state(pr_number: str, repo: str = "jsboige/CoursIA") -> str | None:
    """Return 'MERGED' / 'OPEN' / 'CLOSED' via gh CLI.

    Returns None if gh is unavailable, the PR does not exist, or auth fails.
    Best-effort: the validator continues with WARN_PR_STATE_UNKNOWN.
    """
    try:
        out = subprocess.run(
            ["gh", "pr", "view", pr_number, "--repo", repo, "--json", "state"],
            capture_output=True, text=True, check=True, timeout=30,
        )
        return json.loads(out.stdout).get("state")
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, json.JSONDecodeError):
        return None


def check_entry(entry: dict, catalogue: list[dict], repo: str = "jsboige/CoursIA") -> list[str]:
    """Return list of issue codes for one registry entry.

    Issue code prefixes:
      WARN_* : informational, does not block --check
      (other) : error, blocks --check
    """
    issues = []
    nb_path = entry.get("notebook_path")

    # 1. notebook_path exists in catalogue
    paths = {nb["path"] for nb in catalogue}
    if not nb_path:
        issues.append("MISSING_NOTEBOOK_PATH")
        return issues
    if nb_path not in paths:
        issues.append(f"NOTEBOOK_NOT_FOUND: {nb_path}")
        return issues  # No point checking further

    # 2. review_scope is valid
    scope = entry.get("review_scope")
    if scope not in REVIEW_SCOPES:
        issues.append(f"INVALID_SCOPE: {scope!r} (valid: {sorted(REVIEW_SCOPES)})")

    # 3. reviewer is present and non-empty
    reviewer = entry.get("reviewer")
    if not reviewer:
        issues.append("MISSING_REVIEWER")

    # 4. evidence_pr format and state
    evidence_pr = entry.get("evidence_pr", "")
    pr_digits = evidence_pr.lstrip("#").strip()
    if pr_digits.isdigit():
        state = gh_pr_state(pr_digits, repo)
        if state is None:
            issues.append(f"WARN_PR_STATE_UNKNOWN: #{pr_digits} (gh unavailable or PR not found)")
        elif state != "MERGED":
            issues.append(f"PR_NOT_MERGED: #{pr_digits} state={state}")
    elif evidence_pr:
        issues.append(f"INVALID_PR_FORMAT: {evidence_pr!r}")

    # 5. reviewer != owner_logique (cross-check catalogue)
    nb = next(n for n in catalogue if n["path"] == nb_path)
    owner = nb.get("owner_logique")
    if reviewer and owner:
        if reviewer == owner:
            issues.append(f"AUTO_REVIEW: reviewer={reviewer} == owner_logique={owner}")
        elif reviewer in owner or owner in reviewer:
            # Substring heuristic for alias detection (best-effort)
            issues.append(f"WARN_REVIEWER_ALIAS: reviewer={reviewer} substring of owner_logique={owner}")

    return issues


def check_promotions(entries: list[dict], catalogue: list[dict]) -> list[str]:
    """Cross-check: catalogue entries that the registry should promote.

    This checks that each whitelisted notebook (with scope in PROMOTING_SCOPES
    and a non-empty reviewer) has editorial=BETA or FINAL in the catalogue.

    If the catalogue is from BEFORE the classifier extension (c.764), it won't
    have the editorial field — in that case, we emit an INFO note rather than
    an error.
    """
    notes = []
    paths_to_promote = set()
    for entry in entries:
        if (entry.get("review_scope") in PROMOTING_SCOPES
                and entry.get("notebook_path")
                and entry.get("reviewer")):
            paths_to_promote.add(entry["notebook_path"])

    has_editorial_field = any("editorial" in nb for nb in catalogue)

    for nb in catalogue:
        if nb["path"] in paths_to_promote:
            if not has_editorial_field:
                notes.append(
                    f"INFO: {nb['path']} whitelisted but catalogue has no 'editorial' field "
                    f"(pre-c.764 catalogue? regenerate with new classifier)"
                )
            elif nb.get("editorial") not in ("FINAL", "BETA"):
                notes.append(
                    f"NOTE: {nb['path']} expected editorial in (FINAL, BETA), got {nb.get('editorial')!r}"
                )
    return notes


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate editorial-review-registry.md coherence with catalogue"
    )
    parser.add_argument(
        "--registry",
        default="docs/notebook-metadata/editorial-review-registry.md",
        help="Path to editorial-review-registry.md",
    )
    parser.add_argument(
        "--catalogue",
        default="COURSE_CATALOG.generated.json",
        help="Path to COURSE_CATALOG.generated.json",
    )
    parser.add_argument(
        "--repo",
        default="jsboige/CoursIA",
        help="GitHub repo for gh pr view (default: jsboige/CoursIA)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit 1 if any error (non-WARN) is found",
    )
    args = parser.parse_args()

    registry_path = Path(args.registry)
    catalogue_path = Path(args.catalogue)

    if not registry_path.exists():
        print(f"ERROR: registry not found: {registry_path}", file=sys.stderr)
        return 1
    if not catalogue_path.exists():
        print(f"ERROR: catalogue not found: {catalogue_path}", file=sys.stderr)
        return 1

    entries = parse_registry(registry_path)
    catalogue = load_catalogue(catalogue_path)

    print(f"=== Editorial review registry validator (c.764) ===")
    print(f"Registry: {registry_path} ({len(entries)} entries)")
    print(f"Catalogue: {catalogue_path} ({len(catalogue)} notebooks)")
    print(f"Repo: {args.repo}")
    print()

    all_issues = []
    for entry in entries:
        issues = check_entry(entry, catalogue, repo=args.repo)
        nb_path = entry.get("notebook_path", "?")
        if issues:
            print(f"[{nb_path}]")
            for issue in issues:
                print(f"  - {issue}")
            all_issues.extend(issues)
        else:
            print(
                f"[OK] {nb_path} "
                f"(reviewer={entry.get('reviewer')}, scope={entry.get('review_scope')}, "
                f"evidence={entry.get('evidence_pr')})"
            )

    promotions = check_promotions(entries, catalogue)
    if promotions:
        print()
        print("=== Promotion cross-check ===")
        for p in promotions:
            print(f"  - {p}")

    print()
    error_count = sum(1 for i in all_issues if not i.startswith("WARN_"))
    warn_count = sum(1 for i in all_issues if i.startswith("WARN_"))
    print(f"Summary: {error_count} errors, {warn_count} warnings, {len(promotions)} notes")

    if args.check and error_count > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
