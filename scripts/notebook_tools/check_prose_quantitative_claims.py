"""Refuse les compteurs quantitatifs ecrits a la main dans la prose.

Mandat user 2026-08-04 : « les donnees quantitatives doivent etre tenues par le
CI, pas dans la prose manuelle ». Registre : issue #9377.

Le catalogue genere (`COURSE_CATALOG.generated.*` + marqueurs `CATALOG-STATUS`)
a ete mis en place parce que les agents ouvraient des PR sans fin pour
resynchroniser des decomptes de notebooks. Le genre n'a pas disparu : il a
migre vers la prose, ou aucun generateur ne l'atteint. 11 PR de resynchro
mergees en 3 semaines au 2026-08-04, dont une (#9153) dont le titre avoue
« re-drift post #6914 ».

Le tri est celui de l'issue : **calcule = legitime, prose = interdit**.

  - Une cellule *code* qui compte et affiche est la bonne facon de porter un
    chiffre : il se recalcule a chaque execution. On ne la regarde pas.
  - Une cellule *markdown* qui affirme « (140 lignes) » fige une mesure que
    rien ne remesure. Elle derive des qu'un tiers touche au fichier cite --
    y compris pour une raison sans rapport (sur game_theory_lean, 4 des 6
    commits de juillet sont des flips de docstrings FR/EN, qui changent le
    nombre de lignes sans toucher une ligne de mathematiques).

Ce qui reste autorise : les predicats (`0 sorry` dit que la preuve est
complete), et tout nombre qui n'est pas une mesure d'artefact du depot.

Angle mort connu -- mesure VIVANTE vs mesure FIGEE
--------------------------------------------------
Le scanner voit la forme (« N lignes »), pas le temps du recit. Il flague donc
aussi les chiffres qui datent d'un incident **clos**, ou le nombre decrit un
fait passe et ne peut plus deriver : personne n'ouvrira de PR pour
resynchroniser une mesure d'evenement. Exemple rencontre a la mise en service
(`variation-protocol-detail.md`) : « ~98 lignes redigees trois fois » chiffre
le doublon #8961/#8983/#8996 du 2026-07-31 -- c'est la PIECE qui fonde le
verdict, pas un compteur a tenir.

La ligne de partage : un decompte d'**artefact vivant** derive et revient au
CI ; un decompte **fige dans un recit au passe** est une preuve, et se garde.
D'ou le mode advisory par defaut -- l'arbitrage est humain. Ne PAS « corriger »
un chiffre d'incident au motif que le guard l'a signale : ce serait supprimer
la preuve pour faire taire l'organe.

Usage
-----
    # CI sur une PR : ne juge que les lignes AJOUTEES
    python check_prose_quantitative_claims.py --diff origin/main...HEAD

    # Inventaire du stock restant (suivi #9377)
    python check_prose_quantitative_claims.py --all

    # Bloquant (une fois le stock vide)
    python check_prose_quantitative_claims.py --diff origin/main...HEAD --strict
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Noms d'artefacts du depot. Un nombre colle a l'un d'eux est une mesure d'etat
# du depot, donc perissable. Volontairement restreint : « 4 proprietes de Nash »
# ou « 3 joueurs » sont du contenu pedagogique, pas de l'etat de depot, et ne
# doivent jamais declencher.
ARTIFACT_NOUNS = r"(?:lignes?|lines?|cellules?|cells?|notebooks?|modules?|fichiers?|files?)"

# Formes attrapees : « (140 lignes) », « ~525 lignes », « **224** notebooks »,
# « 87 cellules ». Le nombre doit preceder immediatement le nom d'artefact.
COUNT_RE = re.compile(
    r"(?<![\w.])~?\*{0,2}\d{1,6}\*{0,2}\s+" + ARTIFACT_NOUNS + r"(?![\w-])",
    re.IGNORECASE,
)

# Une ligne de diff .ipynb qui ouvre un champ JSON autre que "source" est une
# metadonnee machine-ecrite, pas de la prose.
JSON_KEY_RE = re.compile(r'"(?!source")[A-Za-z_][A-Za-z0-9_]*"\s*:')

# Blocs generes : le catalogue a le droit de porter des chiffres, c'est son role.
GENERATED_MARKERS = ("CATALOG-STATUS", "COURSE_CATALOG.generated")

# Hors perimetre. `.claude` est le harnais (regles, memoires d'agents, plans,
# worktrees d'autres sessions) : ce n'est pas de la prose livree a un etudiant,
# et il y cite legitimement des seuils chiffres (« > 3000 lignes »).
SKIP_PARTS = (
    ".claude",
    ".lake",
    "node_modules",
    ".git",
    "_peters",
    "foundry-lib/lib",
    ".pytest_cache",
    "bin",
    "obj",
    "tmp",  # gitignore:582 -- scratch d'execution, pas du contenu livre
)

# Le catalogue genere porte des chiffres : c'est exactement son role.
SKIP_NAME_PREFIXES = ("COURSE_CATALOG.generated",)

# Un fichier qui se declare genere a le droit de porter des chiffres : c'est
# precisement le motif vise (« les donnees quantitatives sont tenues par le
# CI »). L'exemption n'est donc pas une liste de noms a maintenir, mais la
# presence d'un generateur proprietaire, declaree en tete de fichier.
GENERATED_HEADER_RE = re.compile(
    r"fichier\s+g[eé]n[eé]r[eé]"
    r"|ne\s+pas\s+[eé]diter\s+[aà]\s+la\s+main"
    r"|n'est\s+pas\s+maintenu\s+[aà]\s+la\s+main"
    r"|do\s+not\s+edit\s+(?:this\s+file\s+)?(?:by\s+hand|manually)"
    r"|auto(?:matically)?[-\s]generated",
    re.IGNORECASE,
)


def _declares_generated(text: str) -> bool:
    """Vrai si l'en-tete revendique un generateur proprietaire."""
    head = "\n".join(text.splitlines()[:20])
    return bool(GENERATED_HEADER_RE.search(head))


def _skipped(path: Path) -> bool:
    if any(part in SKIP_PARTS for part in path.parts):
        return True
    return path.name.startswith(SKIP_NAME_PREFIXES)


def _iter_markdown_sources(nb_path: Path):
    """Rend (index_cellule, source) pour les seules cellules markdown."""
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        yield idx, src


def _findings_in_text(text: str, location: str) -> list[tuple[str, str]]:
    out = []
    for line in text.splitlines():
        if any(m in line for m in GENERATED_MARKERS):
            continue
        for match in COUNT_RE.finditer(line):
            out.append((location, match.group(0).strip()))
    return out


def scan_all(root: Path) -> list[tuple[str, str]]:
    findings: list[tuple[str, str]] = []

    for nb in root.rglob("*.ipynb"):
        if _skipped(nb):
            continue
        rel = nb.relative_to(root).as_posix()
        for idx, src in _iter_markdown_sources(nb):
            findings += _findings_in_text(src, f"{rel} MD[{idx}]")

    for md in root.rglob("*.md"):
        if _skipped(md):
            continue
        rel = md.relative_to(root).as_posix()
        try:
            text = md.read_text(encoding="utf-8")
        except OSError:
            continue
        if _declares_generated(text):
            continue
        # Neutralise les blocs generes delimites par des marqueurs.
        if "CATALOG-STATUS:START" in text:
            text = re.sub(
                r"<!--\s*CATALOG-STATUS:START.*?CATALOG-STATUS:END\s*-->",
                "",
                text,
                flags=re.DOTALL,
            )
        findings += _findings_in_text(text, rel)

    return findings


def scan_diff(diff_range: str) -> list[tuple[str, str]]:
    """Ne juge que les lignes AJOUTEES : le stock existant ne fait pas echouer."""
    try:
        diff = subprocess.run(
            ["git", "diff", "--unified=0", diff_range],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=180, check=False,
        ).stdout
    except (OSError, subprocess.SubprocessError) as exc:
        print(f"[ERREUR] git diff a echoue : {exc}", file=sys.stderr)
        return []

    findings: list[tuple[str, str]] = []
    generated_cache: dict[str, bool] = {}

    def _is_generated_file(rel: str) -> bool:
        if rel not in generated_cache:
            try:
                head = Path(rel).read_text(encoding="utf-8", errors="replace")
                generated_cache[rel] = _declares_generated(head)
            except OSError:
                generated_cache[rel] = False
        return generated_cache[rel]

    current = "?"
    for line in diff.splitlines():
        if line.startswith("+++ b/"):
            current = line[6:]
            continue
        if not line.startswith("+") or line.startswith("+++"):
            continue
        if not (current.endswith(".ipynb") or current.endswith(".md")):
            continue
        if _skipped(Path(current)):
            continue
        if current.endswith(".md") and _is_generated_file(current):
            continue
        # Dans un .ipynb, seule une valeur de "source" est de la prose. Les
        # champs de metadonnees (`"notes": "... 14/14 cells executed."`, ecrit
        # par le populateur metadata.cost) sont machine-ecrits : ils portent
        # legitimement des chiffres et ne derivent pas en prose.
        if current.endswith(".ipynb"):
            body = line[1:].lstrip()
            if any(k in line for k in ('"output_type"', '"execution_count"', '"outputs"')):
                continue
            if JSON_KEY_RE.match(body):  # "<cle>": ... avec <cle> != source
                continue
            if '"source"' not in line and not body.startswith('"'):
                continue
        findings += _findings_in_text(line[1:], current)

    return findings


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--all", action="store_true", help="inventaire complet du stock (suivi #9377)")
    g.add_argument("--diff", metavar="RANGE", help="ne juge que les lignes ajoutees (ex: origin/main...HEAD)")
    ap.add_argument("--strict", action="store_true", help="rc=1 sur finding (defaut : advisory, rc=0)")
    ap.add_argument("--root", default=".", help="racine du depot")
    args = ap.parse_args()

    findings = scan_all(Path(args.root).resolve()) if args.all else scan_diff(args.diff)

    if not findings:
        print("[OK] aucun compteur quantitatif en prose.")
        return 0

    by_file: dict[str, list[str]] = {}
    for loc, snippet in findings:
        by_file.setdefault(loc.split(" MD[")[0], []).append(snippet)

    label = "REFUS" if args.strict else "ADVISORY"
    print(f"[{label}] {len(findings)} compteur(s) quantitatif(s) en prose, {len(by_file)} fichier(s) :\n")
    for path in sorted(by_file):
        snippets = by_file[path]
        preview = ", ".join(sorted(set(snippets))[:6])
        print(f"  {path}  ({len(snippets)})  {preview}")

    print(
        "\nLes donnees quantitatives sont tenues par le CI, pas par la prose (issue #9377)."
        "\nSupprimer la mesure, garder le predicat : `(140 lignes, 0 sorry)` -> `(0 sorry)`."
    )
    return 1 if args.strict else 0


if __name__ == "__main__":
    sys.exit(main())
