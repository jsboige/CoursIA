#!/usr/bin/env python3
"""Detecte la chronologie de livraison Git dans la prose des carnets (audit de stock).

Issue #14442 (défaut 3) : certaines introductions et conclusions de carnets
justifient leur contenu par la **chronologie de livraison** — renvois à un EPIC,
à une PR/issue, ou au fait qu'un morceau a été « livré » — au lieu de le
justifier **pédagogiquement**. Ce récit de livraison vit dans git, les PR et les
issues, pas dans le carnet que lit l'apprenant.

Ce script est un **audit de stock** (pas un ratchet de diff) : il parcourt les
cellules markdown d'un carnet ou d'une série et signale chaque **marqueur de
chronologie de livraison** présent, avec l'index de la cellule et le texte qui
a matché. Il ne **classe** pas : l'issue impose que chaque occurrence soit
**relue dans son contexte** (un « GT-3b » nu est un pointeur pédagogique vers
un carnet voisin et reste ; un « GT-3b (#12213) » est une référence de
livraison). La classification (PEDAGOGIQUE / PROVENANCE_UTILE /
CHRONOLOGIE_GIT_A_RETIRER) est donc produite par la lecture humaine, consignée
dans le ledger d'accompagnement ; l'organe rend seulement le candidat précis.

Différenciation avec ``check_activity_leak.py`` : celui-ci est un **ratchet sur
les passages AJOUTÉS** d'une PR (densité de récit de cycle) ; ici c'est un
**inventaire des marqueurs PRÉSENTS** dans le stock, pour un balayage ponctuel.
Les deux sont complémentaires.

Marqueurs (taxonomie #14442, focale sur la livraison) :

- ``EPIC #N`` / ``Epic #N``   — renvoi à un EPIC.
- ``PR #N``                   — renvoi à une pull request.
- ``Issue #N``                — renvoi à une issue.
- ``(#NNNN)`` (4-5 chiffres)  — numéro de PR/issue en parenthèse, la forme
  canonique du renvoi de livraison (« GT-3b (#12213) »). La parenthèse fermante
  est facultative : un renvoi suivi d'un commentaire (« (#15399, clos
  COMPLETED) », « (#10382, axe 5) ») ou non fermé (« (#15399 ») relève de la
  même classe.
- ``livré / livrée / livrée(s)`` accolé à un numéro ou à ``sur main`` —
  past-participe de livraison.

Faux positifs évités : un pointeur de carnet **sans** numéro (« voir GT-3b »,
« les murs de GT-3b ») ne matche pas ; « promesse livrée à Colonne » (prose
française courante) ne matche pas (pas de numéro accolé). Un carnet qui
**enseigne** git peut citer une issue en exemple : un tel passage se classe
PEDAGOGIQUE à la lecture, il n'est pas supprimé.

Usage :
    python scripts/notebook_tools/audit_workflow_chronology.py <chemin> [--json]

``<chemin>`` est un carnet ``.ipynb`` ou un répertoire (parcours récursif).
Sortie : un rapport par carnet portant ≥ 1 marqueur. Code de sortie : 0 = aucun
marqueur, 1 = marqueur(s) trouvé(s), 2 = erreur (chemin absent, JSON invalide).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

# Marqueurs de chronologie de livraison. Le premier groupe (renvois EPIC/PR/
# issue + numéro en parenthèse) est la signature : un carnet pédagogique ne
# cite pas de numéros de PR/issue. Le second groupe (past-participe « livré »)
# n'est retenu que s'il est accolé à un numéro ou à « sur main ».
MARKERS = [
    ("epic", re.compile(r"\bEPIC\s+#\d+", re.IGNORECASE)),
    ("pr", re.compile(r"\bPR\s+#\d+")),
    ("issue", re.compile(r"\bIssue\s+#\d+", re.IGNORECASE)),
    # Renvoi de livraison en parenthese. La forme « (#NNNN) » exacte etait la
    # seule reconnue : un renvoi suivi d'un commentaire (« (#15399, clos
    # COMPLETED) », « (#10382, axe 5) ») ou non ferme (« (#15399 ») passait sous
    # le radar -- cecite de regex mesuree par la review Hermes sur #22658
    # (4 occurrences muettes au head, 5 a la base, sur 44 renvois). La forme
    # retenue capture les trois ecritures ; la frontiere de nombre (4-5
    # chiffres) reste inchangee, et le patron ne demande plus la parenthese
    # fermante.
    ("pr_paren", re.compile(r"\(#\d{4,5}\b")),
    ("livre", re.compile(r"\blivr\w*\s+(?:#?\d|\bsur\s+main\b)", re.IGNORECASE)),
]

SKIP_DIRS = {"_archive", "archive", ".ipynb_checkpoints", "node_modules"}


def iter_notebooks(path: str):
    """Yield les chemins de carnets .ipynb sous ``path`` (fichier ou répertoire)."""
    if os.path.isfile(path):
        if path.endswith(".ipynb"):
            yield path
        return
    for dirpath, dirnames, filenames in os.walk(path):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for f in filenames:
            if f.endswith(".ipynb") and not f.endswith("_output.ipynb"):
                yield os.path.join(dirpath, f)


def scan_notebook(path: str):
    """Retourne la liste des (index_cellule, marqueur, texte_matche) d'un carnet."""
    with open(path, encoding="utf-8") as fh:
        nb = json.load(fh)
    hits = []
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        text = "".join(cell.get("source", []))
        for name, rx in MARKERS:
            for m in rx.finditer(text):
                start = max(0, m.start() - 24)
                end = min(len(text), m.end() + 24)
                snippet = text[start:end].replace("\n", " ").strip()
                hits.append((idx, name, snippet))
    return hits


def _emit_utf8(text, indent=None):
    """Ecrit sur stdout en UTF-8, quel que soit l'encodage du flux redirige.

    Sous Windows, un stdout redirige encode en cp1252 : un accent du corpus
    (« la ou » avec un accent grave) sort en octet 0xe0 et tout consommateur
    UTF-8 leve ``UnicodeDecodeError`` au premier accent. Le rapport devient
    alors illisible pour une chaine d'outils, alors que l'audit lui-meme est
    correct.

    On reconfigure le flux quand il l'expose ; si l'encodage reste contraint,
    on retombe sur une serialisation ASCII echappee -- du JSON valide quand
    le texte en est, du texte lisible sinon.
    """
    stream = sys.stdout
    reconfigure = getattr(stream, "reconfigure", None)
    if reconfigure is not None:
        try:
            reconfigure(encoding="utf-8")
        except (ValueError, OSError):
            pass
    try:
        stream.write(text)
    except UnicodeEncodeError:
        try:
            payload = json.loads(text)
        except ValueError:
            stream.write(text.encode("ascii", "backslashreplace").decode("ascii"))
        else:
            reserialized = json.dumps(payload, ensure_ascii=True, indent=indent)
            # Symetrie avec la voie primaire : conserver le saut de ligne final
            # du texte d'origine, pour que le fichier produit ne depende pas de
            # l'encodage du flux (repli : pas de "\\n" final sinon).
            if text.endswith("\n"):
                reserialized += "\n"
            stream.write(reserialized)
    stream.flush()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("path", help="carnet .ipynb ou répertoire")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    args = ap.parse_args(argv)

    if not os.path.exists(args.path):
        print("chemin absent : %s" % args.path, file=sys.stderr)
        return 2

    results = []
    for nbpath in iter_notebooks(args.path):
        rel = nbpath.replace("\\", "/")
        try:
            hits = scan_notebook(nbpath)
        except (json.JSONDecodeError, OSError) as exc:
            print("lecture impossible %s : %s" % (rel, exc), file=sys.stderr)
            return 2
        if hits:
            results.append({"path": rel, "n_hits": len(hits), "hits": hits})

    results.sort(key=lambda r: (r["path"]))

    if args.json:
        indent = 1
        rendered = json.dumps({"n_notebooks_flagged": len(results), "notebooks": results},
                              ensure_ascii=False, indent=indent)
        _emit_utf8(rendered + "\n", indent)
    else:
        lines = []
        if not results:
            lines.append("aucun marqueur de chronologie de livraison")
        for r in results:
            lines.append("%s  (%d marqueur%s)" % (r["path"], r["n_hits"],
                                                  "s" if r["n_hits"] > 1 else ""))
            for idx, name, snippet in r["hits"]:
                lines.append("   cellule %2d  [%s]  …%s…" % (idx, name, snippet))
        _emit_utf8("\n".join(lines) + "\n")
    return 1 if results else 0


if __name__ == "__main__":
    sys.exit(main())
