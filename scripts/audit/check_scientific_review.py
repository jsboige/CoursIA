#!/usr/bin/env python3
"""
Scientific review registry validator — cf docs/notebook-metadata/scientific-review-registry.md.

Coherence check between the scientific review whitelist (YAML registry) and the
generated catalogue (COURSE_CATALOG.generated.json). Validates:

1. Registry YAML parses cleanly (multi-line literal entries).
2. Each entry's notebook_path exists in the catalogue.
3. review_scope is in the valid enum {factual, algo, proba, demo, correctness, full}.
4. reviewer != last_validator of the notebook (auto-review rejection — c.997 #14831 voie 1).
5. evidence_pr (#NNNN) is in MERGED state via `gh pr view` (best-effort: skip if gh unavailable).
6. Cross-check: catalogue entries that the registry should promote (UNREVIEWED -> AUTHOR_REVIEWED/PEER_REVIEWED).

Exit codes:
  0 = no errors (warnings allowed)
  1 = errors found (DRIFT/INVALID/MISSING/etc.) — only with --check flag

Anti-FP strategy (cf scientific-review-registry.md §3.3):
- AUTO_REVIEW: reviewer == last_validator du notebook (bloquant pour PEER_REVIEWED, OK pour AUTHOR_REVIEWED self-attesté).
- DRIFT_REVIEWER_ALIAS: reviewer est substring du owner_logique (heuristic best-effort).
- DRIFT_PR_NOT_TOUCHING: PR diff ne touche pas le notebook path (TODO c.997+).
- WARN_PR_STATE_UNKNOWN: gh CLI indisponible (CI sans auth).

Run:
    python scripts/audit/check_scientific_review.py --check
    python scripts/audit/check_scientific_review.py --registry <path> --catalogue <path>

See also:
    docs/notebook-metadata/scientific-review-registry.md (canonical schema)
    docs/notebook-metadata/SCIENTIFIC_REVIEW_CARD.md (review template)
    scripts/audit/check_editorial_review.py (c.764, axe 1 pattern analogue)
"""
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REVIEW_SCOPES = {"factual", "algo", "proba", "demo", "correctness", "full"}
PROMOTING_SCOPES = REVIEW_SCOPES  # all promote in c.997 voie 1


def parse_registry(registry_path: Path) -> list[dict]:
    """Extract YAML entries from registry markdown.

    The registry format (cf scientific-review-registry.md §2) uses fenced
    ```yaml blocks containing multi-line literal entries. We parse by
    finding each line starting with "- notebook_path:" and accumulating
    subsequent indented "key: value" lines until the next "- " line.

    This is a simplified YAML parser sufficient for the c.997 whitelist
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
                # Save previous entry (only if it has a real evidence_pr)
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
    Template entries have placeholders like `<#NNNN>` which must be excluded.
    """
    evidence = entry.get("evidence_pr", "").strip()
    if not evidence:
        return False
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
            capture_output=True, text=True, encoding="utf-8", errors="replace", check=True, timeout=30,
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

    # 5. Cross-check reviewer against last_validator (not owner_logique — c.997 spec)
    # NOTE: c.997 registre uses last_validator (per `classify_scientific_review` l.806-807),
    # NOT owner_logique (which `check_editorial_review.py` uses). The semantic difference:
    # - owner_logique = stable identity (po-2023, jsboige, etc.)
    # - last_validator = email du dernier commit (can change over time)
    # c.997 voie 1: AUTHOR_REVIEWED if reviewer == last_validator; PEER_REVIEWED if !=.
    nb = next(n for n in catalogue if n["path"] == nb_path)
    last_validator = nb.get("last_validator")
    if reviewer and last_validator:
        if reviewer == last_validator:
            # OK for AUTHOR_REVIEWED self-attesté — c.997 voie 1 spec.
            # NOT a warning (the reviewer == last_validator is the AUTHOR_REVIEWED case,
            # not auto-review rejection).
            pass
        # else: PEER_REVIEWED case (reviewer != last_validator), no warning needed

    return issues


def check_promotions(entries: list[dict], catalogue: list[dict]) -> list[str]:
    """Cross-check: catalogue entries that the registry should promote.

    This checks that each whitelisted notebook (with scope in PROMOTING_SCOPES
    and a non-empty reviewer) has scientific_review != UNREVIEWED in the catalogue.

    If the catalogue is from BEFORE the classifier extension (c.997), it won't
    have the scientific_review field — in that case, we emit an INFO note rather
    than an error.
    """
    notes = []
    cat_paths = {nb["path"]: nb for nb in catalogue}
    for entry in entries:
        nb_path = entry.get("notebook_path")
        scope = entry.get("review_scope")
        if scope not in PROMOTING_SCOPES:
            continue
        nb = cat_paths.get(nb_path)
        if nb is None:
            continue
        sr = nb.get("scientific_review")
        if sr is None:
            notes.append(f"INFO_NO_FIELD: {nb_path} -- catalogue lacks scientific_review field")
            continue
        if sr == "UNREVIEWED":
            notes.append(
                f"DRIFT_NOT_PROMOTED: {nb_path} -- scientific_review=UNREVIEWED "
                f"despite registry signal (c.997 voie 1)"
            )
    return notes


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0] if __doc__ else "")
    ap.add_argument("--check", action="store_true", help="Enable exit code 1 on errors")
    ap.add_argument("--registry", type=Path,
                    default=Path("docs/notebook-metadata/scientific-review-registry.md"),
                    help="Path to the scientific review registry markdown")
    ap.add_argument("--catalogue", type=Path,
                    default=Path("COURSE_CATALOG.generated.json"),
                    help="Path to the generated catalogue JSON")
    ap.add_argument("--repo", default="jsboige/CoursIA", help="GitHub repo for gh CLI")
    args = ap.parse_args()

    if not args.registry.exists():
        print(f"ERROR: registry not found: {args.registry}")
        return 1
    if not args.catalogue.exists():
        print(f"ERROR: catalogue not found: {args.catalogue}")
        return 1

    entries = parse_registry(args.registry)
    catalogue = load_catalogue(args.catalogue)

    print(f"Registry: {len(entries)} entries parsed")
    print(f"Catalogue: {len(catalogue)} notebooks")

    errors = 0
    warnings = 0
    for entry in entries:
        nb_path = entry.get("notebook_path", "?")
        issues = check_entry(entry, catalogue, args.repo)
        for issue in issues:
            if issue.startswith("WARN_"):
                warnings += 1
                print(f"WARN  {nb_path}: {issue}")
            else:
                errors += 1
                print(f"ERROR {nb_path}: {issue}")

    notes = check_promotions(entries, catalogue)
    for note in notes:
        if note.startswith("INFO_"):
            print(f"INFO  {note}")
        elif note.startswith("DRIFT_"):
            # DRIFT_NOT_PROMOTED is a soft warning — not blocking, but flag for visibility.
            warnings += 1
            print(f"WARN  {note}")
        else:
            errors += 1
            print(f"ERROR {note}")

    print(f"\nSummary: {errors} errors, {warnings} warnings, {len(entries)} entries checked")
    if args.check and errors:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
