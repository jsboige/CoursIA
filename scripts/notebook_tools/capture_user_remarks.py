#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Capture des remarques user en vrac -> issues GitHub scopées.

Epic #11259 — tâche T3 (« boucle de capture »). Le user ne doit JAMAIS ouvrir
d'issue lui-même : il dit ce qui ne va pas, en vrac, comme ça vient ; cet outil
convertit chaque remarque en une issue GitHub prête à instruire.

Division du travail, non négociable :
- l'OUTIL garantit la **fidélité verbatim** (la remarque est citée à l'identique,
  jamais reformulée) et le **rattachement mécanique** (notebook(s) détecté(s)
  par matching de chemin, ambiguïtés signalées, jamais devinées) ;
- l'AGENT opérateur garantit le **sens** (acceptance rédigée, diagnostic,
  correctif). Le squelette d'acceptance émis est générique et le dit.

Entrée : fichier de remarques ou stdin. Découpage : blocs séparés par une ligne
`---` seule ; sans séparateur, chaque ligne non vide = une remarque unitaire
(une remarque multi-lignes doit donc être soit séparée par `---`, soit écrite
sur une ligne).

Sortie : dry-run sur stdout par défaut. `--create` crée une issue GitHub par
remarque (`gh issue create`, label `user-remark`). Advisory : exit 0 même si
des remarques restent ambiguës — elles sont listées pour arbitrage.
"""

from __future__ import annotations

import argparse
import datetime
import os
import subprocess
import sys
import unicodedata
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(_TOOLS_DIR))

from generate_review_dossier import REPO_ROOT, SCOPE_FILE, _scope_of  # noqa: E402

NOTEBOOKS_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_DIR_PARTS = {
    "_archive", "_research", "temp", "assets", "_probes", "_output",
    "RDF.Net-Legacy", "planning_lean", ".lake", "node_modules", "__pycache__",
}

LABEL = "user-remark"


def _normalize(s: str) -> str:
    """Lowercase, accents pliés, séparateurs unifiés en tiret, espaces pliés."""
    folded = unicodedata.normalize("NFKD", s)
    stripped = "".join(c for c in folded if not unicodedata.combining(c))
    lowered = stripped.lower()
    for sep in ("_", " ", ".", ","):
        lowered = lowered.replace(sep, "-")
    while "--" in lowered:
        lowered = lowered.replace("--", "-")
    return lowered.strip("-")


def split_remarks(text: str) -> list[str]:
    """Découpe le vrac en remarques unitaires (blocs `---` ou lignes)."""
    if not text.strip():
        return []
    if any(line.strip() == "---" for line in text.splitlines()):
        blocks = []
        current: list[str] = []
        for line in text.splitlines():
            if line.strip() == "---":
                blocks.append("\n".join(current))
                current = []
            else:
                current.append(line)
        blocks.append("\n".join(current))
        return [b.strip() for b in blocks if b.strip()]
    return [line.strip() for line in text.splitlines() if line.strip()]


def build_index() -> list[str]:
    """Index des notebooks relatifs à NOTEBOOKS_ROOT (chemins posix)."""
    out = []
    for dirpath, dirnames, filenames in os.walk(NOTEBOOKS_ROOT):
        dirnames[:] = [d for d in dirnames if d not in EXCLUDE_DIR_PARTS]
        for fn in filenames:
            if fn.endswith(".ipynb"):
                rel = Path(dirpath, fn).relative_to(NOTEBOOKS_ROOT).as_posix()
                out.append(rel)
    return sorted(out)


def _tokens(s: str) -> list[str]:
    return [t for t in _normalize(s).split("-") if t]


def _longest_segment_cited(stem_tokens: list[str], remark_tokens: list[str]) -> int:
    """Longueur (en tokens) du plus long segment CONSÉCUTIF du stem cité
    consécutivement dans la remarque — préfixe inclus, segment médian inclus
    (« Toulmin_Model » cite le segment médian de
    « Argument_Analysis_Toulmin_Model »). 0 si aucun."""
    best = 0
    n = len(stem_tokens)
    for start in range(n):
        for k in range(n - start, 0, -1):
            seg = stem_tokens[start:start + k]
            for i in range(len(remark_tokens) - k + 1):
                if remark_tokens[i:i + k] == seg:
                    best = max(best, k)
                    break  # k décroissant : premier match = meilleur pour ce start
    return best


def resolve_notebooks(remark: str, index: list[str]) -> tuple[str, list[str]]:
    """Rattache la remarque aux notebooks cités.

    Retourne (statut, chemins) : UNIQUE / AMBIGUOUS / NONE. Le stem du notebook
    (basename sans extension, normalisé) doit être cité dans la remarque : soit
    en entier, soit par un préfixe d'au moins 2 tokens (« QC-Py-02 » rattache
    « QC-Py-02-Platform-Fundamentals.ipynb »). Seuls les rattachements les plus
    longs sont retenus — un préfixe plus court qui matche d'autres notebooks
    est dominé, pas accumulé. Jamais deviné : plusieurs candidats ex-aequo =
    AMBIGUOUS, l'agent tranche.
    """
    remark_tokens = _tokens(remark)
    if not remark_tokens:
        return ("NONE", [])
    scored: list[tuple[int, str]] = []
    for rel in index:
        stem_tokens = _tokens(Path(rel).stem)
        if len(stem_tokens) < 2:
            continue
        k = _longest_segment_cited(stem_tokens, remark_tokens)
        # préfixe significatif : >= 2 tokens ET >= 6 caractères joints
        if k >= 2 and len("-".join(stem_tokens[:k])) >= 6:
            scored.append((k, rel))
    if not scored:
        return ("NONE", [])
    kmax = max(k for k, _ in scored)
    hits = [rel for k, rel in scored if k == kmax]
    return ("UNIQUE" if len(hits) == 1 else "AMBIGUOUS", hits)


def build_issue(remark: str, status: str, matches: list[str],
                captured_on: str | None = None) -> dict:
    """Émet le brouillon d'issue : citation verbatim + contexte mécanique.

    Aucune interprétation n'est ajoutée au-delà du squelette générique,
    explicitement marqué « à instruire par l'agent ».
    """
    first_line = remark.splitlines()[0]
    title = first_line if len(first_line) <= 60 else first_line[:57] + "..."
    quoted = "\n".join("> " + line for line in remark.splitlines())
    when = captured_on or datetime.date.today().isoformat()

    if status == "UNIQUE":
        rel = matches[0]
        strate = _scope_of(rel)
        attach = f"- `{rel}` — strate {strate} du périmètre PRODUCTION"
    elif status == "AMBIGUOUS":
        attach = ("- **AMBIGU** — plusieurs notebooks correspondent, "
                  "l'agent tranche (jamais deviné par l'outil) :\n"
                  + "\n".join(f"  - `{m}`" for m in matches))
    else:
        attach = ("- **aucun notebook rattaché mécaniquement** — périmètre ou "
                  "sujet à qualifier par l'agent")

    body = (
        f"{quoted}\n\n"
        f"---\n\n"
        f"**Source** : remarque user en vrac, capturée le {when} "
        f"(Epic #11259, boucle de capture T3 — `capture_user_remarks.py`).\n\n"
        f"**Rattachement mécanique** :\n{attach}\n\n"
        f"**À instruire par l'agent** (l'outil ne devine pas le sens) :\n"
        f"- [ ] Reproduire/qualifier le constat sur un worktree frais (`origin/main`)\n"
        f"- [ ] Rédiger le diagnostic et le correctif\n"
        f"- [ ] Livrer la PR (`See #11259`)\n"
    )
    return {"title": f"[User remark] {title}", "body": body}


def create_issue(issue: dict, label: str) -> tuple[bool, str]:
    """Crée l'issue via gh. Retourne (succès, sortie/erreur)."""
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False,
                                     encoding="utf-8") as fh:
        fh.write(issue["body"])
        path = fh.name
    try:
        proc = subprocess.run(
            ["gh", "issue", "create", "--title", issue["title"],
             "--body-file", path, "--label", label],
            capture_output=True, text=True, timeout=60,
        )
        ok = proc.returncode == 0
        return (ok, (proc.stdout + proc.stderr).strip())
    finally:
        os.unlink(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Remarques user en vrac -> issues GitHub scopées (Epic #11259 T3)")
    parser.add_argument("file", nargs="?",
                        help="fichier de remarques (défaut : stdin)")
    parser.add_argument("--create", action="store_true",
                        help="crée réellement les issues (défaut : dry-run stdout)")
    parser.add_argument("--label", default=LABEL,
                        help=f"label GitHub (défaut : {LABEL})")
    args = parser.parse_args(argv)

    if args.file:
        text = Path(args.file).read_text(encoding="utf-8")
    else:
        text = sys.stdin.read()

    remarks = split_remarks(text)
    if not remarks:
        print("Aucune remarque capturée (entrée vide).")
        return 0

    index = build_index()
    issues = []
    statuses = {"UNIQUE": 0, "AMBIGUOUS": 0, "NONE": 0}
    for i, remark in enumerate(remarks, 1):
        status, matches = resolve_notebooks(remark, index)
        statuses[status] += 1
        issues.append(build_issue(remark, status, matches))

    print(f"Remarques capturées : {len(remarks)} "
          f"(rattachées : {statuses['UNIQUE']}, ambiguës : {statuses['AMBIGUOUS']}, "
          f"sans rattachement : {statuses['NONE']})")

    created = 0
    for i, issue in enumerate(issues, 1):
        print(f"\n{'=' * 60}\nISSUE {i}/{len(issues)}\n{'=' * 60}")
        print(f"Title: {issue['title']}\n")
        print(issue["body"])
        if args.create:
            ok, out = create_issue(issue, args.label)
            print(f"-> gh issue create : {'OK ' + out if ok else 'FAIL ' + out}")
            created += int(ok)

    if args.create:
        print(f"\nIssues créées : {created}/{len(issues)}")
    else:
        print(f"\nDry-run (aucune issue créée). Relancer avec --create pour créer.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
