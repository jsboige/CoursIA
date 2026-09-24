#!/usr/bin/env python3
"""check_hr_substitution.py - garde substitution silencieuse hr markdown.

Source : PR #17428 (NanoClaw VERDICT: CONCERNS, tete 8193664f) + issue #14683.
Issue 1 : le regex ^[-+](---|***)$ du rule ne couvre que 2 des 4 notations
CommonMark (---, ***, * * *, ___). * * * et ___ passent en silence.
Issue 2 : claim "le workflow reecriture-non-annoncee.yml existe" est faux
(156 workflows au head, aucun match) -- fausse assurance dans la regle.

Garde : sur tout diff qui touche un .ipynb de MyIA.AI.Notebooks/**, sort en
rouge si une substitution hr est detectee SANS mention explicite dans le body
de la PR (l'agent doit declarer le sweep). Couvre les 4 notations.

Verdict :
  exit 0 = aucune substitution silencieuse (ou PR le declare dans le body)
  exit 1 = substitution silencieuse detectee (l'agent doit l'expliquer)

Usage :
  python scripts/ci/check_hr_substitution.py <PR_NUMBER>
  python scripts/ci/check_hr_substitution.py --self
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Optional

# 4 notations CommonMark (cf CommonMark spec §4.1 thematic breaks)
HR_NOTATIONS = ["---", "***", "* * *", "___"]
HR_RE = re.compile(r"^([ \t]*)(?:---|\*\*\*|\* \* \*|___)[ \t]*$")

# Pattern strict : ligne dans un diff git qui ajoute/supprime une notation hr
# - la notation doit etre SEULE sur la ligne (espaces/tabs tolérés)
# - le caractere - au début du diff est ajoute (nouveau) ou retire (supprime)
# - supporte `+++---` (diff prefix `+++` puis `+---` ligne ajoutee) et
#   `+++` (ligne ajoutee vide), et ` ---` ligne retiree avec prefixe espace
DIFF_HR_LINE_RE = re.compile(
    r"^[+-]{1,2}\s*(?:---|\*\*\*|\* \* \*|___)\s*$"
)


def get_pr_diff(pr_number: int) -> str:
    """Return the unified diff of a PR via gh CLI."""
    cmd = [
        "gh", "pr", "diff", str(pr_number),
        "--repo", "jsboige/CoursIA",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    if out.returncode != 0:
        sys.stderr.write(f"gh pr diff failed: {out.stderr}\n")
        sys.exit(2)
    return out.stdout


def get_pr_body(pr_number: int) -> str:
    """Return the PR body (markdown text)."""
    cmd = [
        "gh", "pr", "view", str(pr_number),
        "--repo", "jsboige/CoursIA",
        "--json", "body",
        "--jq", ".body",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    if out.returncode != 0:
        sys.stderr.write(f"gh pr view failed: {out.stderr}\n")
        sys.exit(2)
    return out.stdout or ""


def get_self_diff() -> str:
    """Return the staged/working-tree diff against HEAD."""
    cmd = ["git", "diff", "--no-color", "HEAD"]
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    if out.returncode != 0:
        sys.stderr.write(f"git diff failed: {out.stderr}\n")
        sys.exit(2)
    return out.stdout


def get_self_body() -> str:
    """No PR body in --self mode; empty string disables 'declared in body' check."""
    return ""


def detect_hr_substitutions(diff_text: str) -> list[dict]:
    """Parse diff_text and return list of HR substitutions."""
    findings: list[dict] = []
    current_file: Optional[str] = None

    for raw_line in diff_text.splitlines():
        # Track current file
        if raw_line.startswith("+++ b/"):
            current_file = raw_line[6:]
            continue
        if raw_line.startswith("--- a/"):
            # Skip the 'before' header
            continue

        m = DIFF_HR_LINE_RE.match(raw_line)
        if not m:
            continue
        if current_file is None:
            continue
        if not current_file.endswith(".ipynb"):
            continue
        if "MyIA.AI.Notebooks/" not in current_file:
            continue

        notation = m.group(1).replace("\\*", "*")
        verdict = "added" if raw_line.startswith("+") else "removed"
        findings.append(
            {
                "file": current_file,
                "line": raw_line,
                "notation": notation,
                "verdict": verdict,
            }
        )
    return findings


def body_declares(body: str, file: str, n_added: int, n_removed: int) -> bool:
    """Heuristique : le body de la PR declare-t-il un sweep hr sur ce fichier ?

    Conditions positives (TOUTES requises) :
      - le chemin du fichier apparait dans le body (relatif ou basename)
      - le compteur (X added / Y removed ou similaire) apparait
      - le motif (substitution / hr / thematic / sweep) apparait
    """
    if not body:
        return False
    body_low = body.lower()
    file_low = file.lower()
    base = Path(file).name.lower()
    file_ref = file_low in body_low or base in body_low
    n_ref = (
        f"{n_added} ajout" in body_low
        or f"{n_added} add" in body_low
        or f"+{n_added}" in body
        or f"{n_removed} removed" in body_low
        or f"-{n_removed}" in body
    )
    motif_ref = any(
        kw in body_low
        for kw in (
            "substitut", "sweep", "thematic break", "hr",
            "notat", "---", "***",
        )
    )
    return file_ref and n_ref and motif_ref


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("pr_number", type=int, nargs="?", help="PR number (omit for --self)")
    ap.add_argument("--self", action="store_true", help="Check staged/working diff vs HEAD")
    ap.add_argument("--json", action="store_true", help="JSON output")
    args = ap.parse_args()

    if not args.self and args.pr_number is None:
        ap.error("either PR number or --self required")

    if args.self:
        diff_text = get_self_diff()
        body = ""
    else:
        diff_text = get_pr_diff(args.pr_number)
        body = get_pr_body(args.pr_number)

    findings = detect_hr_substitutions(diff_text)

    # Group by file
    by_file: dict[str, dict[str, int]] = {}
    for f in findings:
        by_file.setdefault(f["file"], {"added": 0, "removed": 0})
        if f["verdict"] == "added":
            by_file[f["file"]]["added"] += 1
        else:
            by_file[f["file"]]["removed"] += 1

    silent: list[dict] = []
    declared: list[dict] = []
    for fp, c in by_file.items():
        n_added = c["added"]
        n_removed = c["removed"]
        # Only flag substitutions (added AND removed)
        if n_added > 0 and n_removed > 0:
            if body_declares(body, fp, n_added, n_removed):
                declared.append({"file": fp, "added": n_added, "removed": n_removed})
            else:
                silent.append({"file": fp, "added": n_added, "removed": n_removed})

    payload = {
        "n_findings": len(findings),
        "files_touched": len(by_file),
        "silent_substitutions": silent,
        "declared_substitutions": declared,
        "verdict": "OK" if not silent else "SILENT_SUBSTITUTION_DETECTED",
    }

    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(f"[hr] {len(findings)} hr lines, {len(by_file)} files touched")
        for fp, c in by_file.items():
            tag = ""
            if c["added"] > 0 and c["removed"] > 0:
                tag = " [SUBSTITUTION]"
            print(f"  {fp}  +{c['added']}/-{c['removed']}{tag}")
        if silent:
            print()
            print(f"[FAIL] {len(silent)} silent substitution(s) -- declare in PR body:")
            for s in silent:
                print(f"  {s['file']}  +{s['added']}/-{s['removed']}")
            return 1
        if declared:
            print()
            print(f"[OK] {len(declared)} declared substitution(s) (body matches).")
        return 0


if __name__ == "__main__":
    sys.exit(main())
