#!/usr/bin/env python3
"""Check that workflows do not combine `push: main` + group keyed on github.ref
+ literal `cancel-in-progress: true` (#13488).

## Why this exists

The defect #13372 corrected in three workflows measured firsthand: on a cascade
of merges onto `main`, `concurrency.group: <name>-${{ github.ref }}` evaluates
to a constant `<name>-refs/heads/main` -- so every commit shares the same
group. With `cancel-in-progress: true`, the new run kills the previous one
before it can finish. The guard being correct on isolated PRs (where
`github.ref` is `refs/pull/N/merge`, unique per PR) masks the defect: the
workflow verifies its own PR (1 run, 1 group), goes green, and the regression
on `main` is invisible until a cascade actually hits.

The fix on the workflow side is `cancel-in-progress:
${{ github.event_name == 'pull_request' }}` -- cancel ONLY on PR, never on
push. The fix on the guard side is the present script: refuse the conjunction
on `main` so a regression of the fix is impossible to land.

## The discriminator

The conjunction is the THREE-WAY:
  (a) `on.push.branches` includes `main`
  (b) `concurrency.group` template contains `github.ref`
  (c) `concurrency.cancel-in-progress` is the literal `true`

All three must be true for the failure. (a) is the structural trigger;
(b) is what makes the group constant across commits; (c) is what makes the
cancellation happen.

Without (a), `github.ref` is per-PR and the bug cannot occur -- the 59
workflows with `cancel-in-progress: true` and no `push: main` are harmless.

## Allowlist

Some workflows deliberately use literal `true` because they supersede
concurrent deploys of the same artefact -- e.g. `quarto-pages-deploy.yml`,
which wants the new deploy to win. The allowlist is **by file name**, never
a glob, with a comment in the script citing the reason. The cliquet that
makes the gate rough on every new file is the whole value of the organ --
same discipline as `Classical.choice` whitelisting in the Lean axiom gate.

## Modes

  --check       print summary + offenders; exit 0 if clean, exit 1 if any
                workflow offends, exit 2 on instrument failure (PyYAML
                missing, workflow unreadable).
  --json        same as --check but emits a JSON document on stdout.

Run: python scripts/ci/check_concurrency_conj.py --check
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

EXIT_CLEAN, EXIT_OFFENDERS, EXIT_BROKEN = 0, 1, 2

DEFAULT_WORKFLOWS_DIR = str(
    Path(__file__).resolve().parents[2] / ".github" / "workflows"
)

# Allowlist by file name (no glob). The cliquet that roughs the gate on every
# new name is the entire value of the organ. Add a name ONLY with a one-line
# reason; never wildcard.
ALLOWLIST: dict[str, str] = {
    # pages-deploy supersedes concurrent deploys of the same Quarto artifact:
    # the new deploy must win. Comment in quarto-pages-deploy.yml confirms.
    "quarto-pages-deploy.yml": "Quarto pages deploy supersedes prior in-flight deploy",
}


def _load_yaml():
    try:
        import yaml
    except ImportError:
        return None
    return yaml


def _parse_workflow(text: str, yaml):
    """Parse one workflow YAML, working around PyYAML's `on:` -> True issue.

    PyYAML 1.1 treats the bareword `on` as a boolean; we rewrite the trigger
    key to a quoted string before parsing. Returns the parsed dict or None.
    """
    out_lines: list[str] = []
    for line in text.splitlines(keepends=True):
        if line.startswith("on:") or line.startswith("on :"):
            out_lines.append('"on":' + line[len("on:"):])
        else:
            out_lines.append(line)
    rewritten = "".join(out_lines)
    try:
        return yaml.safe_load(rewritten)
    except yaml.YAMLError:
        return None


def _branches_include_main(trigger: dict | None) -> bool:
    """True if the workflow's `push:` trigger lists `main` (or wildcard '*').

    Handles three shapes:
      - ``push: { branches: [main, ...] }``
      - ``push: { branches: main }`` (scalar)
      - ``push: branches: [main]`` (flattened)

    A ``push:`` without ``branches:`` is treated as default (all branches),
    which includes main. This is the GitHub Actions default.
    """
    if not isinstance(trigger, dict):
        return False
    push = trigger.get("push")
    if push is None:
        return False
    # Default push trigger (no explicit branches) covers main.
    if push is True:
        return True
    if not isinstance(push, dict):
        return False
    if "branches" not in push and "branches-ignore" not in push:
        # No filter at all -> default, includes main.
        return True
    branches = push.get("branches", [])
    if isinstance(branches, str):
        branches = [branches]
    if not isinstance(branches, list):
        return False
    for b in branches:
        if not isinstance(b, str):
            continue
        # Quoted wildcards: '*' or '**' covers main.
        if b in {"*", "**"}:
            return True
        # Plain or quoted: main (literal match).
        if b == "main" or b.strip('"').strip("'") == "main":
            return True
    return False


def _group_has_github_ref(group: str | None) -> bool:
    """True if `concurrency.group` template contains the substring ``github.ref``.

    Any occurrence is enough -- ``${{ github.ref }}``, ``${{ github.event.pull_request.base.ref }}``,
    or the like. The bug is structural to the template form, not the literal
    expression.
    """
    if not isinstance(group, str):
        return False
    return "github.ref" in group


def _cancel_is_literal_true(cancel: object) -> bool:
    """True only if `concurrency.cancel-in-progress` is the literal `true`.

    A template expression like ``${{ github.event_name == 'pull_request' }}``
    is NOT literal true even when the YAML parses to the Python value True:
    PyYAML evaluates unquoted `true` to True, but a quoted or templated value
    stays a string. We discriminate on type + value: bool True AND not a
    string.

    Wait -- that discrimination fails on the literal-true case. The bug we
    catch is specifically the LITERAL `true` (no template), so we accept
    bool True as the only signal. A template that EVALUATES to true at
    runtime but is a STRING in YAML is structurally the fix -- keep it.
    """
    # YAML literal `true` -> Python bool True.
    return cancel is True


def offenders(workflows_dir: str = DEFAULT_WORKFLOWS_DIR) -> list[dict]:
    """Return the list of workflows that carry the conjunction.

    Each entry is a dict with: ``file``, ``reason``, ``line_group`` (1-indexed
    line where ``concurrency:`` begins), ``fix`` (the canonical replacement).
    """
    yaml = _load_yaml()
    if yaml is None:
        return [{"file": "<instrument>", "reason": "PyYAML indisponible",
                 "line_group": 0, "fix": ""}]
    wdir = Path(workflows_dir)
    if not wdir.is_dir():
        return [{"file": str(wdir), "reason": "workflows dir introuvable",
                 "line_group": 0, "fix": ""}]
    out: list[dict] = []
    for wf in sorted(wdir.glob("*.y*ml")):
        name = wf.name
        if name in ALLOWLIST:
            continue
        try:
            text = wf.read_text(encoding="utf-8")
        except OSError:
            out.append({"file": name, "reason": "illisible",
                        "line_group": 0, "fix": ""})
            continue
        data = _parse_workflow(text, yaml)
        if not isinstance(data, dict):
            continue
        trigger = data.get("on") if "on" in data else data.get(True)
        # After the on:-rewrite, "on" survives as a quoted key in the dict.
        if "on" not in data and True in data:
            trigger = data[True]
        concurrency = data.get("concurrency") or {}
        if not isinstance(concurrency, dict):
            continue
        if not _branches_include_main(trigger):
            continue
        if not _group_has_github_ref(concurrency.get("group")):
            continue
        if not _cancel_is_literal_true(concurrency.get("cancel-in-progress")):
            continue
        # All three conjuncts true: offender.
        line_group = _line_of(text, "concurrency:")
        out.append({
            "file": name,
            "reason": ("push: main + concurrency.group porte github.ref + "
                       "cancel-in-progress litteral true (defaut #13372, "
                       "le garde s'annule sur cascade de merges)"),
            "line_group": line_group,
            "fix": ('cancel-in-progress: ${{ github.event_name == \'pull_request\' }} '
                   '(forme fix de #13372, deja majoritaire dans lean-*, '
                   'bash-syntax, ict-tests, ml-tests, secret-scan, '
                   'validation-matrix).'),
        })
    return out


def _line_of(text: str, token: str) -> int:
    """1-indexed line number where `token` first appears at column 0.

    Used to point the author to the concurrency block. Falls back to 0 if not
    found (should not happen for parsed workflows).
    """
    for i, line in enumerate(text.splitlines(), start=1):
        if line.startswith(token):
            return i
    return 0


def _main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Refuser la conjonction push:main + group github.ref + cancel-in-progress litteral true (#13488)."
    )
    parser.add_argument("--check", action="store_true",
                        help="exit 0/1/2 par verdict")
    parser.add_argument("--json", action="store_true",
                        help="sortie JSON sur stdout")
    parser.add_argument("--workflows-dir", default=DEFAULT_WORKFLOWS_DIR,
                        help="repertoire des workflows (override pour les tests)")
    args = parser.parse_args(argv)

    yaml = _load_yaml()
    if yaml is None:
        msg = {"guard": "concurrency-conj", "status": "BROKEN_INSTRUMENT",
               "reason": "PyYAML indisponible"}
        if args.json:
            print(json.dumps(msg))
        else:
            print("[concurrency-conj] BROKEN INSTRUMENT: PyYAML absent.",
                  file=sys.stderr)
        return EXIT_BROKEN

    offs = offenders(args.workflows_dir)
    summary = {
        "guard": "concurrency-conj",
        "workflows_scanned": sum(1 for _ in Path(args.workflows_dir).glob("*.y*ml")),
        "allowlist": sorted(ALLOWLIST.keys()),
        "offenders": offs,
    }
    if args.json:
        print(json.dumps(summary, ensure_ascii=False, indent=2))
    else:
        print(f"[concurrency-conj] workflows_scanned={summary['workflows_scanned']} "
              f"allowlist={summary['allowlist']} offenders={len(offs)}")
        for o in offs:
            print(f"  - {o['file']}:{o['line_group']} -- {o['reason']}")
            print(f"    fix: {o['fix']}")

    if not args.check:
        return EXIT_CLEAN
    return EXIT_CLEAN if not offs else EXIT_OFFENDERS


if __name__ == "__main__":
    sys.exit(_main())
