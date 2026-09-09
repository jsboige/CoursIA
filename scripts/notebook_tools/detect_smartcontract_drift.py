#!/usr/bin/env python3
"""Detect bounded Smart Contracts notebook drift and compare scan snapshots.

The detector intentionally covers only evidence-backed rules from issue #15246:
legacy ERC-4337 ``UserOperation``, retired Goerli/Mumbai networks, and Foundry
suites presented through printed commands without a real Forge invocation.
Papermill failures are owned by the existing papermill state detectors.

Exit codes: 0 clean/inherited debt, 1 finding or delta regression, 2 unreadable
input/setup. Corpus scans are informative unless ``--check`` is supplied.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional

from audit_engine_named_not_invoked import (
    ENGINE_REGISTRY,
    _cell_source,
    _scan_engine,
)


@dataclass(frozen=True)
class DriftRule:
    rule_id: str
    pattern: re.Pattern[str]
    message: str
    remediation: str


DRIFT_RULES = (
    DriftRule(
        rule_id="ERC4337_LEGACY_USER_OPERATION",
        pattern=re.compile(r"\bstruct\s+UserOperation\s*\{", re.IGNORECASE),
        message="Unpacked ERC-4337 UserOperation is taught as current.",
        remediation=(
            "Use PackedUserOperation and explain accountGasLimits, gasFees, "
            "and packed paymasterAndData."
        ),
    ),
    DriftRule(
        rule_id="RETIRED_GOERLI_NETWORK",
        pattern=re.compile(r"\bgoerli\b", re.IGNORECASE),
        message="Retired Goerli network is presented as an active target.",
        remediation="Use a maintained testnet/local chain or label this as history.",
    ),
    DriftRule(
        rule_id="RETIRED_POLYGON_MUMBAI_NETWORK",
        pattern=re.compile(r"\b(?:polygon\s+)?mumbai\b", re.IGNORECASE),
        message="Retired Polygon Mumbai network is presented as an active target.",
        remediation="Use Polygon Amoy/local chain or label this as history.",
    ),
)

_HISTORICAL_MARKERS = re.compile(
    r"\b(?:historique|history|historical|ancien(?:ne)?|legacy|obsolete|"
    r"deprecated|retire(?:e)?|v0\.6|avant\s+v0\.[78])\b",
    re.IGNORECASE,
)
_EXERCISE_MARKERS = re.compile(
    r"TODO\s*:?(?:\s+etudiant|\s+ecrivez|\s+implementez)|"
    r"Exercice\s+a\s+completer|\bpass\s*(?:#.*)?$",
    re.IGNORECASE | re.MULTILINE,
)
_FORGE_COMMAND = re.compile(r"\bforge\s+(?:build|test)\b", re.IGNORECASE)
_PRINT_CALL = re.compile(r"\bprint\s*\(", re.IGNORECASE)


def _context_for_cell(cells: list[dict], index: int) -> str:
    """Return the cell and adjacent markdown used to classify historical prose."""
    pieces = [_cell_source(cells[index])]
    for neighbor in (index - 1, index + 1):
        if 0 <= neighbor < len(cells) and cells[neighbor].get("cell_type") == "markdown":
            pieces.append(_cell_source(cells[neighbor]))
    return "\n".join(pieces)


def _evidence(text: str, match: re.Match[str]) -> str:
    start = max(0, match.start() - 60)
    end = min(len(text), match.end() + 80)
    return re.sub(r"\s+", " ", text[start:end]).strip()[:180]


def scan_notebook(path: Path, notebook: dict) -> list[dict]:
    """Return actionable findings for one parsed notebook."""
    findings: list[dict] = []
    cells = notebook.get("cells", [])
    for index, cell in enumerate(cells):
        source = _cell_source(cell)
        if not source or _EXERCISE_MARKERS.search(source):
            continue
        context = _context_for_cell(cells, index)
        for rule in DRIFT_RULES:
            match = rule.pattern.search(source)
            if not match or _HISTORICAL_MARKERS.search(context):
                continue
            findings.append({
                "rule_id": rule.rule_id,
                "notebook": path.as_posix(),
                "cell": index,
                "evidence": _evidence(source, match),
                "message": rule.message,
                "remediation": rule.remediation,
            })

    foundry_hits = _scan_engine(notebook, ENGINE_REGISTRY["foundry"])
    printed_cells = []
    for index, cell in enumerate(cells):
        if cell.get("cell_type") != "code":
            continue
        source = _cell_source(cell)
        if _EXERCISE_MARKERS.search(source):
            continue
        if _FORGE_COMMAND.search(source) and _PRINT_CALL.search(source):
            printed_cells.append((index, source))
    if printed_cells and not foundry_hits.invocation_hits:
        index, source = printed_cells[0]
        match = _FORGE_COMMAND.search(source)
        findings.append({
            "rule_id": "FOUNDRY_SUITE_PRINTED_ONLY",
            "notebook": path.as_posix(),
            "cell": index,
            "evidence": _evidence(source, match),
            "message": "Foundry command is printed but Forge is never invoked.",
            "remediation": "Run forge build/test via subprocess or an invoked helper and commit its output.",
        })
    return findings


def _iter_notebooks(root: Path) -> Iterable[Path]:
    if root.is_file():
        if not root.name.endswith(("_output.ipynb", "_executed.ipynb")):
            yield root
        return
    yield from (
        path for path in sorted(root.rglob("*.ipynb"))
        if not path.name.endswith(("_output.ipynb", "_executed.ipynb"))
    )


def scan_paths(paths: Iterable[Path]) -> dict:
    findings: list[dict] = []
    errors: list[dict] = []
    for root in paths:
        for path in _iter_notebooks(root):
            try:
                notebook = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                errors.append({"notebook": path.as_posix(), "error": str(exc)})
                continue
            findings.extend(scan_notebook(path, notebook))
    return {"findings": findings, "errors": errors, "count": len(findings)}


def _finding_key(finding: dict) -> tuple[str, str]:
    return finding.get("notebook", ""), finding.get("rule_id", "")


def compare_snapshots(base: dict, head: dict) -> list[dict]:
    """Return findings whose notebook/rule pair is absent from the base."""
    base_keys = {_finding_key(item) for item in base.get("findings", [])}
    return [
        item for item in head.get("findings", [])
        if _finding_key(item) not in base_keys
    ]


def _load_snapshot(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict) or not isinstance(payload.get("findings", []), list):
        raise ValueError("snapshot must be a JSON object with a findings list")
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", type=Path, nargs="*")
    parser.add_argument("--scan-all", type=Path)
    parser.add_argument("--compare-base", type=Path)
    parser.add_argument("--compare-head", type=Path)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)

    if bool(args.compare_base) != bool(args.compare_head):
        parser.error("--compare-base and --compare-head must be used together")

    try:
        if args.compare_base:
            if args.paths or args.scan_all:
                parser.error("comparison mode cannot be combined with scan paths")
            base = _load_snapshot(args.compare_base)
            head = _load_snapshot(args.compare_head)
            if base.get("errors") or head.get("errors"):
                print(
                    "[ERROR] unreadable notebooks in scan snapshots",
                    file=sys.stderr,
                )
                return 2
            regressions = compare_snapshots(base, head)
            result = {"regressions": regressions, "count": len(regressions)}
            exit_code = 1 if regressions else 0
        else:
            paths = list(args.paths)
            if args.scan_all:
                paths.append(args.scan_all)
            if not paths:
                parser.error("provide PATH or --scan-all PATH")
            result = scan_paths(paths)
            exit_code = 2 if result["errors"] else (
                1 if args.check and result["findings"] else 0
            )
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"[ERROR] {exc}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=False))
    else:
        items = result.get("regressions", result.get("findings", []))
        for item in items:
            print(
                f"[{item['rule_id']}] {item['notebook']}:cell {item['cell']} "
                f"{item['evidence']}"
            )
        print(f"Smart-contract drift findings: {result['count']}")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
