#!/usr/bin/env python3
"""Distribution du verdict nocturne du garde markdown-table (#13660).

Le scanner `scan_md_table_syntax.py` (justice, NON modifie ici) produit sur
`--json` un `{total_findings, files:[{path, findings:[{pathology, cell_index|line,
detail, snippet}]}]}`. Ce script est le DESTINATAIRE de ce verdict : il construit
un commentaire marker-garde (`MD-TABLE-SWEEP`) et l'**upserte** -- un seul
commentaire, mis a jour sur place, jamais un flot quotidien -- sur une issue de
rendez-vous OUVERTE, calque sur le patron GRAIN-ORPHANS-SWEEP (#13086 /
`grain-orphans-sweep.yml`).

ADVISORY, jamais bloquant (exit 0 toujours) : le job ne tagge rien, ne ferme rien,
il route, ai-01 tranche. Le manque n'etait pas la severite, c'etait l'adresse --
un scanner parfait dont le verdict tombe dans un log planifie que personne
n'ouvre est un organe muet.

Usage:
  python md_table_sweep_comment.py --payload payload.json \
      --window "last-24h window of main" --issue 13660 [--apply]

Sans `--apply` : dry-run (imprime le corps, ne poste rien). Avec `--apply` :
upsert du commentaire marker-garde sur l'issue. Toute erreur gh est avalee
(`try/except`) pour garantir l'exit 0 advisory.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import subprocess
import sys

MARKER_START = "<!-- MD-TABLE-SWEEP:START -->"
MARKER_END = "<!-- MD-TABLE-SWEEP:END -->"

# Resolu depuis l'env (workflow) ou la cible canonique (dev local).
def _repo() -> str:
    return os.environ.get("GH_REPO", "jsboige/CoursIA")


def _coverage_note() -> str:
    return (
        "_Portée : mesure la syntaxe SOURCE, pas le rendu ; ne voit pas les tables "
        "des `.md` hors notebooks ; une ligne « irrégulière » peut être un choix "
        "d'auteur, pas un défaut. Recalcul à la demande : `python scripts/"
        "notebook_tools/scan_md_table_syntax.py --check`. Cf #10097, #3966, #12817, "
        "#13660._"
    )


def _code_wrap(text: str) -> str:
    """Entoure en code inline GFM en tolérant les backticks internes.

    Un `CODE_SPAN_PIPE` a un backtick littéral dans son snippet ; un délimiteur
    `` ` `` le casserait dans le rendu. On choisit un délimiteur d'une longueur
    supérieure à la plus longue course de backticks du contenu.
    """
    run = max_run = 0
    for ch in text:
        run = run + 1 if ch == "`" else 0
        max_run = max(max_run, run)
    fence = "`" * (max_run + 1)
    return f"{fence}{text}{fence}"


def build_comment(files: list[dict], total: int, window: str, stamp: str) -> str:
    lines = [MARKER_START]
    if total == 0:
        lines += [
            f"**Défauts de syntaxe de table markdown : 0** dans la fenêtre "
            f"`{window}` (mesure du {stamp}). Rien à signaler à l'instant du "
            f"balayage.",
            "",
            _coverage_note(),
            MARKER_END,
        ]
        return "\n".join(lines)
    lines.append(
        f"**{total} défaut(s) de syntaxe de table markdown** dans la fenêtre "
        f"`{window}` (mesure du {stamp}). Par notebook :"
    )
    lines.append("")
    for r in files:
        findings = r.get("findings") or []
        if not findings:
            continue
        lines.append(f"- **{r['path']}** :")
        for f in findings:
            cell = f.get("cell_index")
            loc = f"cellule {cell}" if cell is not None else f"ligne {f.get('line')}"
            snippet = (f.get("snippet") or "").strip()
            if len(snippet) > 60:
                snippet = snippet[:57] + "..."
            lines.append(
                f"  - {loc} — `{f.get('pathology')}` : {_code_wrap(snippet)}"
            )
    lines += ["", _coverage_note(), MARKER_END]
    return "\n".join(lines)


def upsert_comment(issue: int, body: str) -> None:
    """Un seul commentaire marker-garde par issue, mis a jour sur place."""
    repo = _repo()
    comments = json.loads(subprocess.run(
        ["gh", "issue", "view", str(issue), "--repo", repo, "--json", "comments"],
        capture_output=True, text=True, encoding="utf-8", check=True, timeout=60,
    ).stdout)
    cid = next((c["id"] for c in (comments.get("comments") or [])
                if MARKER_START in (c.get("body") or "")), None)
    if cid is not None:
        subprocess.run(
            ["gh", "api", f"repos/{repo}/issues/comments/{cid}",
             "-X", "PATCH", "-f", f"body={body}"],
            capture_output=True, text=True, encoding="utf-8", check=True, timeout=60)
    else:
        subprocess.run(
            ["gh", "issue", "comment", str(issue), "--repo", repo,
             "--body-file", "-"],
            input=body, capture_output=True, text=True, encoding="utf-8",
            check=True, timeout=60)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--payload", required=True,
                    help="JSON produit par scan_md_table_syntax.py --json")
    ap.add_argument("--window", default="last-24h window of main",
                    help="description de la fenetre scannee (millesime du rapport)")
    ap.add_argument("--issue", type=int, required=True,
                    help="issue de rendez-vous OUVERTE a upserter")
    ap.add_argument("--apply", action="store_true",
                    help="upsert du commentaire (defaut : dry-run, impression seule)")
    args = ap.parse_args(argv)

    with open(args.payload, encoding="utf-8") as fh:
        payload = json.load(fh)
    total = int(payload.get("total_findings", 0))
    files = payload.get("files", [])
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%MZ")

    body = build_comment(files, total, args.window, stamp)
    print(body)
    if not args.apply:
        print(f"[dry-run] commentaire construit (issue #{args.issue}) — "
              f"relancer avec --apply pour upserter.")
        return 0

    try:
        upsert_comment(args.issue, body)
        print(f"[apply] commentaire marker-garde mis a jour sur #{args.issue}")
    except Exception as exc:  # advisory : avaler, ne jamais casser le job
        print(f"[apply] ECHEC avale (advisory, exit 0) : {exc}", file=sys.stderr)
        return 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
