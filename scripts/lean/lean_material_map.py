#!/usr/bin/env python3
"""Carte du materiel Lean du depot — page regeneree, jamais recopiee.

Issue #23097, tranche T1. Le depot porte plusieurs dizaines de lacs Lean, dont
une partie seulement est declaree au CI et une partie plus petite encore est
couverte par le gate d'axiomes. Une table ecrite a la main derive au premier
merge : ce script est le generateur proprietaire de la page
``docs/reference/lean-material-map.md``, et ``--check`` echoue quand la page et
l'arbre divergent.

La colonne « naissance » (date d'ajout du ``lakefile``) est celle qui rend
l'accretion visible sans recherche git : c'est elle qui a permis de mesurer que
``assignment_lean`` et ``asymmetric_information_lean`` sont nes apres la
cloture de #4365.

Usage :
    python scripts/lean/lean_material_map.py                 # page sur stdout
    python scripts/lean/lean_material_map.py --write         # ecrit la page
    python scripts/lean/lean_material_map.py --check         # 0 = page a jour
    python scripts/lean/lean_material_map.py --json          # sortie machine
    python scripts/lean/lean_material_map.py --with-sorry    # ajoute la dette

``--with-sorry`` est opt-in : ``count_code_sorry.py --json`` parcourt tout le
depot et depasse les deux minutes, ce qui est incompatible avec un ``--check``
de CI. La page par defaut ne porte donc pas de colonne de dette.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
PAGE = REPO_ROOT / "docs" / "reference" / "lean-material-map.md"
CI_LAKES = REPO_ROOT / "scripts" / "lean" / "ci_lakes.json"
COVERAGE = REPO_ROOT / "scripts" / "lean" / "check_axiom_gate_coverage.py"
WORKFLOWS = REPO_ROOT / ".github" / "workflows"

GENERATED_HEADER = (
    "<!-- fichier genere par scripts/lean/lean_material_map.py -- "
    "ne pas editer a la main ; relancer le generateur -->"
)

# T2 #23097 : la regle d'accretion d'un lac, tranchee par la mesure.
# Les verdicts sont datees : la mesure qui les fonde est citee dans la cellule.
ACCRETION_RULE = (
    "Un lac nouveau dans une serie existante est legitime si (1) sa toolchain"
    " diverge de celle du lac de la serie, (2) sa theorie est distincte au sens"
    " de la clause anti-god-lake (#4365), ou (3) a toolchain egale il est le"
    " compagnon de construction d'un arc numerote de carnets -- importe par au"
    " moins un carnet Lean de cet arc, sans import croise avec le lac de la"
    " serie, et sans lui imposer une dependance (un path dep d'un lac tiers"
    " deviendrait sinon facteur commun). A defaut, c'est un module de plus du"
    " lac de la serie."
)

ACCRETION_VERDICTS = [
    (
        "assignment_lean",
        "(3) compagnon d'arc",
        "legitime-documente",
        "Arc 16f : `GameTheory-16f-Lean-Assignment-Lean.ipynb` importe"
        " `Assignment.KuhnMunkres`. Toolchain et pin Mathlib identiques a"
        " `game_theory_lean` (v4.33.0, db584cd6), zero import croise, theorie"
        " (affectation hongroise, Kuhn-Munkres) absente des 8 branches du lac"
        " de la serie.",
    ),
    (
        "asymmetric_information_lean",
        "(3) compagnon d'arc",
        "legitime-documente",
        "Arc 17b-17e : `GameTheory-17c-Lean-Lemons-Certificat-Lean.ipynb`"
        " importe `AsymmetricInformation.Lemons`, `GameTheory-17d-Lean-"
        "Screening-Signaling-Lean.ipynb` en importe 4 modules. Path dep non"
        " negociable vers `lean_game_defs_ext` (#12848) : la fusion imposerait"
        " ce pont aux 38 modules de `game_theory_lean`. Zero import croise.",
    ),
]

# Un lakefile dont le dossier porte l'un de ces fragments est vendu, pas a nous.
VENDORED_MARKERS = (".lake/packages", "_peters/", "reference_docs/")

# `git ls-files '*.lean'` attrape aussi les fichiers qui portent l'extension sans
# etre du Lean : le Dockerfile du runner Lean s'appelle `Dockerfile.lean`. Le
# compter comme module gonflerait la carte d'un fichier qui ne se compile pas.
NOT_LEAN_NAMES = ("Dockerfile",)


def _git(*args: str) -> str:
    """Rend la sortie de git, ou une chaine vide si la commande echoue."""
    try:
        r = subprocess.run(
            ["git", "-C", str(REPO_ROOT), *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except OSError:
        return ""
    if r.returncode != 0:
        return ""
    return r.stdout


def _git_paths(*patterns: str) -> list[str]:
    out = _git("ls-files", "-z", *patterns)
    return [p for p in out.split("\0") if p]


def _declared_lakes() -> dict[str, dict]:
    """Les entrees de ci_lakes.json, indexees par project-path normalise."""
    try:
        raw = json.loads(CI_LAKES.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    entries = raw.get("lakes", []) if isinstance(raw, dict) else raw
    out: dict[str, dict] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        path = entry.get("project-path")
        if not path:
            continue
        out[path.replace("\\", "/").rstrip("/")] = entry
    return out


def _coverage() -> dict:
    """Le verdict du gate d'axiomes, s'il est joignable ; sinon un verdict neutre."""
    try:
        r = subprocess.run(
            [sys.executable, "-I", str(COVERAGE), "--ref", "HEAD", "--json"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            cwd=str(REPO_ROOT),
            timeout=300,
        )
        if r.returncode == 0 and r.stdout.strip():
            return json.loads(r.stdout)
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError):
        pass
    return {}


def _sorry_by_lake() -> dict[str, int]:
    """Dette ``distinct_code_sorry`` par lac. Opt-in, couteux (cf docstring)."""
    try:
        r = subprocess.run(
            [sys.executable, "-I", str(REPO_ROOT / "scripts" / "lean" / "count_code_sorry.py"), "--json"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            cwd=str(REPO_ROOT),
            timeout=1800,
        )
        if r.returncode != 0 or not r.stdout.strip():
            return {}
        data = json.loads(r.stdout)
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError):
        return {}
    # Forme mesuree de count_code_sorry.py --json :
    #   {"lakes": [{"lake": <chemin>, "files": n, "naive_sorry": n,
    #               "code_sorry": n, "distinct_code_sorry": n, "vacuous": [...]}]}
    # On accepte aussi une liste nue d'entrees, pour ne pas casser au premier
    # changement de forme de l'organe amont.
    entries = data.get("lakes") if isinstance(data, dict) else data
    out: dict[str, int] = {}
    if not isinstance(entries, list):
        return out
    for value in entries:
        if not isinstance(value, dict):
            continue
        path = value.get("lake") or value.get("project-path")
        count = value.get("distinct_code_sorry")
        if path and isinstance(count, int):
            out[str(path).replace("\\", "/").rstrip("/")] = count
    return out


def _workflow_texts() -> list[tuple[str, str]]:
    """(nom, contenu) de chaque workflow : l'autre surface de declaration du CI.

    `scripts/lean/ci_lakes.json` ne porte PAS tous les lacs : une serie de lacs a
    son propre workflow dedie (`lean-asymmetric-information.yml`,
    `lean-grothendieck.yml`, ...). Ne lire que le JSON classe « hors CI » des
    lacs que le CI construit a chaque push -- c'est un faux negatif mesure, pas
    une hypothese.
    """
    out: list[tuple[str, str]] = []
    for path in sorted(WORKFLOWS.glob("*.yml")) + sorted(WORKFLOWS.glob("*.yaml")):
        try:
            out.append((path.name, path.read_text(encoding="utf-8", errors="replace")))
        except OSError:
            continue
    return out


def _ci_surfaces(lakes: list[str]) -> dict[str, list[str]]:
    """Pour chaque lac, la liste des surfaces de CI qui le nomment."""
    out: dict[str, list[str]] = {lake: [] for lake in lakes}
    declared = _declared_lakes()
    for lake in lakes:
        if lake in declared:
            out[lake].append("ci_lakes.json")
    for name, text in _workflow_texts():
        for lake in lakes:
            if lake in text and name not in out[lake]:
                out[lake].append(name)
    return out


def _birth(lakefile: str) -> str:
    """Date (AAAA-MM-JJ) du commit qui a ajoute ce lakefile ; vide si inconnue."""
    out = _git("log", "-1", "--diff-filter=A", "--format=%cs", "--", lakefile).strip()
    return out.splitlines()[-1] if out else ""


def collect(with_sorry: bool = False) -> dict:
    """Un enregistrement par lac, plus les fichiers hors lac : le fait mesure."""
    lakefiles = _git_paths("*lakefile.lean", "*lakefile.toml")
    coverage = _coverage()
    gated = set(coverage.get("gated_lakes") or [])
    matrix = set(coverage.get("matrix_lakes") or [])
    ungated = set(coverage.get("matrix_lakes_without_gate") or [])
    sorry = _sorry_by_lake() if with_sorry else {}

    by_lake: dict[str, dict] = {}
    for lakefile in lakefiles:
        lake = lakefile.rsplit("/", 1)[0] if "/" in lakefile else "."
        vendored = any(marker in lakefile for marker in VENDORED_MARKERS)
        entry = by_lake.setdefault(
            lake,
            {
                "lake": lake,
                "lakefile": lakefile,
                "vendored": vendored,
                "modules": 0,
                "mirrors": 0,
                "birth": "",
            },
        )
        # Un lac peut porter deux lakefiles (lean + toml) : la naissance est la
        # plus ancienne des deux, c'est celle du lac.
        born = _birth(lakefile)
        if born and (not entry["birth"] or born < entry["birth"]):
            entry["birth"] = born

    # Un module appartient au lac le plus proche qui le CONTIENT, pas au dossier
    # qui le porte : `game_theory_lean/SocialChoice/Arrow.lean` est un module de
    # `game_theory_lean`. Attribuer par dossier immediat efface silencieusement
    # tous les modules des lacs arborescents -- la mesure serait fausse sans
    # qu'aucun temoin ne le dise.
    lake_dirs = sorted(by_lake, key=len, reverse=True)

    def owner(path: str) -> str | None:
        for lake in lake_dirs:
            if path.startswith(lake + "/"):
                return lake
        return None

    orphans: list[str] = []
    excluded = 0
    not_lean = 0
    for path in _git_paths("*.lean"):
        if any(marker in path for marker in VENDORED_MARKERS):
            excluded += 1
            continue
        if path.rsplit("/", 1)[-1].startswith(NOT_LEAN_NAMES):
            not_lean += 1
            continue
        lake = owner(path)
        if lake is None:
            orphans.append(path)
            continue
        entry = by_lake[lake]
        if path.endswith("_en.lean"):
            entry["mirrors"] += 1
        else:
            entry["modules"] += 1

    rows: list[dict] = []
    surfaces = _ci_surfaces([lake.replace("\\", "/").rstrip("/") for lake in by_lake])
    for lake, entry in by_lake.items():
        key = lake.replace("\\", "/").rstrip("/")
        where = surfaces.get(key, [])
        if entry["vendored"]:
            gate = "vendu"
        elif key in ungated:
            gate = "sans gate"
        elif key in gated:
            gate = "couverte"
        elif key in matrix:
            gate = "matrice"
        else:
            gate = "hors matrice"
        entry["ci"] = "declare" if where else "hors CI"
        entry["ci_surfaces"] = where
        entry["gate"] = gate
        entry["sorry"] = sorry.get(key)
        rows.append(entry)

    rows.sort(key=lambda r: (-r["modules"], r["lake"]))
    return {
        "lakes": rows,
        "orphans": sorted(orphans),
        "excluded": excluded,
        "not_lean": not_lean,
    }


def render(
    rows: list[dict],
    orphans: list[str],
    excluded: int,
    not_lean: int,
    with_sorry: bool,
) -> str:
    lines: list[str] = [GENERATED_HEADER, ""]
    lines.append("# Carte du materiel Lean du depot")
    lines.append("")
    lines.append(
        "Une ligne par lac. Les colonnes sont des mesures rejouables, pas des"
        " appreciations : `Modules` compte les fichiers `.lean` propres du lac,"
        " `Miroirs` les freres `_en`, `Naissance` la date d'ajout du `lakefile`."
        " La colonne `Gate axiomes` reprend le verdict de"
        " `scripts/lean/check_axiom_gate_coverage.py`."
    )
    lines.append("")
    lines.append(
        "Cette page est regeneree par `scripts/lean/lean_material_map.py`. Une"
        " table recopiee a la main derive au premier merge : c'est la maladie"
        " que #23097 soigne, et `--check` est le garde-fou."
    )
    lines.append("")
    lines.append(
        "`sans gate` n'est pas un defaut : la couverture est une mesure, pas un"
        " verdict de surete (#17097 critere 3). Un lac sans gate doit seulement"
        " etre **connu** comme tel."
    )
    lines.append("")

    head = ["Lac", "Modules", "Miroirs", "CI", "Gate axiomes", "Naissance"]
    if with_sorry:
        head.append("Dette")
    lines.append("| " + " | ".join(head) + " |")
    lines.append("|" + "|".join(["---"] * len(head)) + "|")
    for row in rows:
        cells = [
            "`%s`" % row["lake"],
            str(row["modules"]),
            str(row["mirrors"]),
            row["ci"],
            row["gate"],
            row["birth"] or "-",
        ]
        if with_sorry:
            cells.append("-" if row["sorry"] is None else str(row["sorry"]))
        lines.append("| " + " | ".join(cells) + " |")
    lines.append("")

    own = [r for r in rows if not r["vendored"]]
    lines.append("## Ce que la carte etablit")
    lines.append("")
    lines.append(
        "%d lacs propres, plus %d dossier vendu. Les lacs hors CI sont listes"
        " ci-dessous : ce sont eux qui rendent une consolidation invisible"
        " depuis la matrice de build."
        % (len(own), len(rows) - len(own))
    )
    lines.append("")
    modules = sum(r["modules"] for r in own)
    mirrors = sum(r["mirrors"] for r in own)
    lines.append("### Reconciliation")
    lines.append("")
    lines.append(
        "%d modules + %d miroirs attribues a un lac + %d fichiers hors lac"
        " + %d fichiers ecartes (dossier vendu, ou extension `.lean` portee par"
        " un fichier qui n'est pas du Lean) = %d fichiers `.lean` traces, soit"
        " la population entiere de `git ls-files '*.lean'`. Un fichier qui"
        " n'apparait dans aucune de ces quatre colonnes a ete perdu en route :"
        " c'est le defaut que cette reconciliation rend visible."
        % (
            modules,
            mirrors,
            len(orphans),
            excluded + not_lean,
            modules + mirrors + len(orphans) + excluded + not_lean,
        )
    )
    lines.append("")

    uncabled = [r for r in own if r["ci"] == "hors CI"]
    if uncabled:
        lines.append("### Lacs hors CI")
        lines.append("")
        lines.append(
            "Ces lacs existent dans l'arbre et aucun workflow ne les nomme : ni"
            " `scripts/lean/ci_lakes.json`, ni un fichier de"
            " `.github/workflows/`. Aucun build de matrice ne les couvre."
        )
        lines.append("")
        for row in uncabled:
            lines.append("- `%s` — %d modules, ne le %s" % (row["lake"], row["modules"], row["birth"] or "?"))
        lines.append("")

    ungated_rows = [r for r in own if r["gate"] == "sans gate"]
    if ungated_rows:
        lines.append("### Lacs de la matrice sans gate d'axiomes")
        lines.append("")
        lines.append(
            "Declares au CI, donc construits, mais le job `lean-axiom` ne les"
            " atteint pas : rien ne rougit si un axiome interdit y entre."
        )
        lines.append("")
        for row in ungated_rows:
            lines.append("- `%s` — %d modules" % (row["lake"], row["modules"]))
        lines.append("")

    if orphans:
        lines.append("### Fichiers `.lean` hors lac")
        lines.append("")
        lines.append(
            "Traces par git, mais dans aucun dossier portant un `lakefile` : ils"
            " ne sont construits par aucun lac, et aucune matrice ne les voit."
        )
        lines.append("")
        for path in orphans:
            lines.append("- `%s`" % path)
        lines.append("")

    lines.append("## Regle d'accretion d'un lac")
    lines.append("")
    lines.append(ACCRETION_RULE)
    lines.append("")
    lines.append("Verdicts tranches par la mesure (T2 #23097) :")
    lines.append("")
    lines.append("| Lac | Cas | Verdict | Mesure fondatrice |")
    lines.append("|---|---|---|---|")
    for name, case, verdict, why in ACCRETION_VERDICTS:
        lines.append("| `%s` | %s | %s | %s |" % (name, case, verdict, why))
    lines.append("")
    lines.append(
        "Les cas (1) toolchain divergente et (2) theorie distincte sont deja"
        " tranches : `social_choice_lean_peters` pour (1) (INTRINSIC #7081),"
        " `minimax_lean` et `conway_cgt_lean` pour (2)."
    )
    lines.append("")

    if with_sorry:
        lines.append("## Dette formelle")
        lines.append("")
        lines.append(
            "`distinct_code_sorry` par lac, mesure par"
            " `scripts/lean/count_code_sorry.py --json`. La colonne est opt-in :"
            " le comptage parcourt tout le depot et coute plusieurs minutes."
        )
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument("--write", action="store_true", help="ecrit la page")
    parser.add_argument("--check", action="store_true", help="0 si la page est a jour")
    parser.add_argument("--with-sorry", action="store_true", help="ajoute la dette formelle")
    args = parser.parse_args(argv)

    data = collect(with_sorry=args.with_sorry)
    rows = data["lakes"]
    orphans = data["orphans"]
    if args.json:
        print(json.dumps(data, indent=1, ensure_ascii=False))
        return 0

    page = render(rows, orphans, data["excluded"], data["not_lean"], args.with_sorry)
    if args.write:
        PAGE.parent.mkdir(parents=True, exist_ok=True)
        PAGE.write_text(page, encoding="utf-8", newline="\n")
        print("ecrit : %s (%d lacs)" % (PAGE, len(rows)))
        return 0

    if args.check:
        if not PAGE.exists():
            print("ABSENTE : %s n'existe pas -- lancer --write" % PAGE)
            return 1
        current = PAGE.read_text(encoding="utf-8")
        if current != page:
            print(
                "PERIMEE : %s diverge de l'arbre -- relancer --write"
                " (le generateur est proprietaire de la page)" % PAGE
            )
            return 1
        print("A JOUR : %s (%d lacs)" % (PAGE, len(rows)))
        return 0

    sys.stdout.write(page)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
