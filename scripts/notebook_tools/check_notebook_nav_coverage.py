#!/usr/bin/env python3
"""Couverture de la barre de navigation, PAR DOSSIER (#24224, Part of #5081).

Ce que cet organe mesure, et ce que les autres ne voient pas
------------------------------------------------------------
`check_notebook_navlinks.py` regarde les liens casses, `check_notebook_nav_chain.py`
regarde le graphe des series (extremites non atteignables). Les deux partent
des aretes QUI EXISTENT.

Un carnet sans barre n'a aucune arete : il n'apparait dans aucun des deux.
C'est ce trou que cet organe rend visible.

Mesure du 2026-11-02 sur `main` (1733 carnets, 246 dossiers) : 1287 carnets
portent une barre, 446 n'en portent pas ; 129 dossiers exhibent la convention,
dont **45 en deficit**, et ces 45 dossiers portent **249 carnets** sans barre.

Ces chiffres different de l'estimation de #24224 §3 (353 avec barre, 746 en
deficit), et l'ecart est **mesure sur le controle positif de l'issue
lui-meme**. Le detecteur de §4 teste la presence litterale des mots
« Precedent » / « Suivant » dans une cellule markdown ; il manque les barres
ecrites autrement. Sur `GenAI/Audio/04-Applications`, #24224 §4 annonce 5
carnets sans barre et nomme `04-5`, `04-8`, `04-14`, `04-15`, `04-20` ; deux
d'entre eux portent une barre parfaitement lisible, avec des chevrons :

    04-5   **Navigation :** [<< 04-4](04-4-Audio-Video-Sync.ipynb) | [Index](../README.md) | [Image >>](../../Image/README.md)
    04-14  **Navigation** : [<< App-21 VoiceLeading (Search)](...) | [Index](...) | [04-3 Workflow >>](...)

Le deficit reel de ce dossier est de **3** carnets (`04-8`, `04-15`, `04-20`).
La note §6 de l'issue annonce que sa detection « sous-estime le deficit » :
c'est l'inverse qui se produit, une barre non reconnue se lit comme un carnet
sans barre et **gonfle** le deficit. Le nombre de dossiers mixtes, lui, est
identique dans les deux mesures (45), et c'est la grandeur la plus robuste.

Deux principes bornent le rapport
---------------------------------
1. **Par dossier, jamais a l'echelle du depot.** Un dossier entierement sans
   barre n'a pas de convention a respecter : ce n'est pas un finding, c'est un
   dossier qui n'utilise pas la navigation. Seuls les dossiers qui EXHIBENT la
   convention (au moins un carnet avec barre) sont mesures, et leur deficit est
   le nombre de carnets sans barre qu'ils portent.
2. **Advisory, adosse a une baseline.** On ne rougit pas 45 dossiers d'un coup.
   Le baseline fige l'ensemble des carnets en deficit, et seuls ceux qui
   S'AJOUTENT rougissent (`--check`). Le cliquet se resserre par serie servie.

Ce qu'est une barre
-------------------
Un **lien** de navigation dans une cellule markdown, classe par
`_looks_nav()` — la fonction qui decide deja, dans
`check_notebook_nav_chain.py`, si un lien est une arete du graphe. Elle est
**importee**, pas recopiee : deux vocabulaires ecrits separement divergeraient,
et l'un des organes dirait « avec barre » la ou l'autre dit « sans ».

La presence d'un simple mot NE SUFFIT PAS, et c'est une mesure, pas une
intuition : une premiere version comptait un marqueur de navigation n'importe
ou dans la cellule markdown, et rendait **1655 carnets avec barre sur 1733**.
« next » et « suivant » sont des mots de prose ordinaire dans un cours ; le
rapport devenait un faux negatif geant. Le lien est ce qui distingue une barre
d'une phrase.

La detection reste laxiste sur la CIBLE : une barre dont les liens sont casses
reste une barre, son 404 est le metier de `check_notebook_nav_chain.py`. Le
sens de l'erreur est de sous-estimer le deficit, jamais de l'inventer.

Un carnet illisible (JSON corrompu) n'est **ni** avec **ni** sans barre : il
part dans `errors`. Le compter comme deficit fabriquerait un finding que
personne ne peut traiter.

Usage
-----
    python scripts/notebook_tools/check_notebook_nav_coverage.py            # rapport
    python scripts/notebook_tools/check_notebook_nav_coverage.py --check     # cliquet CI
    python scripts/notebook_tools/check_notebook_nav_coverage.py --baseline  # (re)figer
    python scripts/notebook_tools/check_notebook_nav_coverage.py --json

Codes de sortie : 0 = rien de nouveau, 1 = carnet(s) entrant(s) dans le deficit,
3 = ecriture du baseline refusee (arbre qui n'est pas `main` propre).
"""

from __future__ import annotations

import argparse
import datetime
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_notebook_navlinks import (  # noqa: E402
    LINK_PATTERN, NOTEBOOKS_ROOT, REPO_ROOT, _iter_notebooks,
)
from check_notebook_nav_chain import _git_output, _looks_nav  # noqa: E402

BASELINE_PATH = REPO_ROOT / "scripts" / "tests" / "baseline_nb_nav_coverage.json"
INSTRUMENT_VERSION = "2026-11-02.1"

# Dossiers jamais parcourus quand on scanne une racine arbitraire (`--root`,
# utilise par les tests). En mode depot, le filtrage est celui de
# `_iter_notebooks` (git-tracked + SKIP_DIRS), qui fait deja foi.
LOCAL_SKIP_PARTS = {".ipynb_checkpoints", "node_modules", ".git", "__pycache__"}


def has_nav_bar(nb_path: Path):
    """True / False, ou None si le carnet est illisible.

    None n'est pas False : un JSON corrompu ne prouve pas l'absence de barre.
    """
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return None
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", [])
        text = src if isinstance(src, str) else "".join(src)
        cell_is_nav = "navigation" in text.lower()
        for line in text.splitlines():
            for match in LINK_PATTERN.finditer(line):
                if _looks_nav(match.group(1), match.group(2), line, cell_is_nav):
                    return True
    return False


def _walk(root: Path | None):
    """Carnets a examiner. Sans racine : les carnets pedagogiques git-tracked."""
    if root is None:
        yield from _iter_notebooks()
        return
    for nb in sorted(root.rglob("*.ipynb")):
        if nb.name.endswith("_output.ipynb"):
            continue
        if any(part in LOCAL_SKIP_PARTS for part in nb.relative_to(root).parts):
            continue
        yield nb


def collect(root: Path | None = None):
    """Regroupe les carnets par dossier et note la presence de barre.

    La cle de dossier est relative a `MyIA.AI.Notebooks` (mode depot) ou a la
    racine passee : une cle relative a `REPO_ROOT` changerait si l'arborescence
    pedagogique bougeait, et casserait le baseline sans qu'aucun carnet n'ait
    change de dossier.
    """
    base = NOTEBOOKS_ROOT if root is None else root
    folders: dict[str, dict[str, list[str]]] = {}
    errors: list[str] = []
    for nb in _walk(root):
        try:
            rel = nb.relative_to(base).as_posix()
        except ValueError:
            errors.append(nb.as_posix())
            continue
        slot = folders.setdefault(
            Path(rel).parent.as_posix() or ".",
            {"with_bar": [], "without_bar": []},
        )
        verdict = has_nav_bar(nb)
        if verdict is None:
            errors.append(rel)
            continue
        slot["with_bar" if verdict else "without_bar"].append(rel)
    return folders, sorted(errors)


def analyse(folders):
    """Verdict par dossier. Un dossier sans aucune barre n'est pas un finding."""
    findings, complete, no_convention = [], [], []
    for folder in sorted(folders):
        slot = folders[folder]
        with_bar = sorted(slot["with_bar"])
        without = sorted(slot["without_bar"])
        if not with_bar:
            no_convention.append(folder)
            continue
        if not without:
            complete.append({"folder": folder, "with_bar": len(with_bar)})
            continue
        total = len(with_bar) + len(without)
        findings.append({
            "folder": folder,
            "with_bar": len(with_bar),
            "without_bar": len(without),
            "total": total,
            "coverage": round(len(with_bar) / total, 4),
            "missing": without,
        })
    return {
        "folders_total": len(folders),
        "folders_with_convention": len(findings) + len(complete),
        "folders_deficit": len(findings),
        "folders_no_convention": len(no_convention),
        "notebooks_with_bar": sum(len(v["with_bar"]) for v in folders.values()),
        "notebooks_without_bar": sum(len(v["without_bar"]) for v in folders.values()),
        "findings": findings,
        "complete": complete,
        "no_convention": no_convention,
    }


def _baseline_doc(report, provenance):
    """Baseline = l'ENSEMBLE des carnets en deficit, pas un compte.

    Un compte par dossier laisserait un echange (un carnet sorti, un autre
    entre) passer pour une absence de changement. L'ensemble nomme : le
    cliquet ne peut que se resserrer.
    """
    return {
        "instrument": INSTRUMENT_VERSION,
        "provenance": provenance,
        "deficit": {f["folder"]: f["missing"] for f in report["findings"]},
    }


def _new_deficit(report, baseline):
    """(dossiers, carnets) entrant dans le deficit par rapport au baseline."""
    known = baseline.get("deficit", {}) if baseline else {}
    new_folders, new_notebooks = [], []
    for finding in report["findings"]:
        folder = finding["folder"]
        before = set(known.get(folder, []))
        fresh = [nb for nb in finding["missing"] if nb not in before]
        if fresh:
            new_folders.append({"folder": folder, "new": fresh,
                                "with_bar": finding["with_bar"],
                                "without_bar": finding["without_bar"]})
            # `missing` porte deja le chemin relatif a la base de scan : le
            # prefixer du dossier le doublerait (« Serie/Serie/02-b.ipynb »).
            new_notebooks.extend(fresh)
    return new_folders, new_notebooks


def _git_provenance(baseline_path=None):
    """Provenance de l'arbre qui ecrit le baseline (#22121).

    Meme contrat que `check_notebook_nav_chain.py` : un baseline ecrit depuis
    une branche de sujet absorbe en silence les findings apparus entre-temps.
    """
    head = _git_output("rev-parse", "HEAD") or ""
    branch = _git_output("rev-parse", "--abbrev-ref", "HEAD") or ""
    origin_main = _git_output("rev-parse", "origin/main") or ""

    own = ""
    if baseline_path is not None:
        try:
            own = Path(baseline_path).resolve().relative_to(REPO_ROOT).as_posix()
        except ValueError:
            own = ""

    status = _git_output("status", "--porcelain") or ""
    dirty = any(
        line[3:].strip() and line[3:].strip() != own
        for line in status.splitlines() if line.strip()
    )

    behind = None
    if head and origin_main:
        raw = _git_output("rev-list", "--count", f"{head}..{origin_main}")
        behind = int(raw) if raw and raw.isdigit() else None

    return {
        "instrument": INSTRUMENT_VERSION,
        "head": head,
        "branch": branch,
        "origin_main": origin_main,
        "behind_origin_main": behind,
        "dirty": dirty,
        "written_at": datetime.datetime.now(datetime.timezone.utc)
                      .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "non_main": (branch != "main" or dirty
                     or (bool(head) and bool(origin_main) and head != origin_main)),
    }


def _baseline_refusal(provenance, anyway):
    """(code, message) : 0 = ecriture permise, 3 = refusee."""
    if anyway or not provenance.get("non_main"):
        return 0, ""
    lines = [
        "error: --baseline refuse : l'arbre n'est pas `main` propre.",
        f"  HEAD        = {provenance.get('head') or '?'}",
        f"  origin/main = {provenance.get('origin_main') or '?'}",
        f"  branche     = {provenance.get('branch') or '?'}"
        f"   dirty = {str(provenance.get('dirty')).lower()}",
        "  Un baseline ecrit hors de `main` absorbe en silence les carnets",
        "  entres dans le deficit entre-temps (#22121). Re-deriver sur main a",
        "  jour, ou relancer avec --baseline-anyway : la provenance portera",
        "  alors `non_main: true`.",
    ]
    return 3, "\n".join(lines)


def load_baseline(path=None):
    path = Path(path or BASELINE_PATH)
    if not path.is_file():
        return None
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError):
        return None


def write_baseline(report, path=None, provenance=None):
    path = Path(path or BASELINE_PATH)
    doc = _baseline_doc(report, provenance or _git_provenance(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(doc, f, ensure_ascii=False, indent=2, sort_keys=True)
        f.write("\n")
    return path


def _render(report, new_folders, baseline_present, max_list):
    out = [
        f"Couverture de la barre de navigation -- {report['folders_total']} dossier(s), "
        f"{report['notebooks_with_bar']} carnet(s) avec barre, "
        f"{report['notebooks_without_bar']} sans",
        f"  dossiers utilisant la convention : {report['folders_with_convention']}"
        f"  (dont {report['folders_deficit']} en deficit)",
        f"  dossiers sans convention (hors mesure) : {report['folders_no_convention']}",
    ]
    if not baseline_present:
        out.append("  baseline : absent -- tous les carnets en deficit sont "
                   "« nouveaux » (mode advisory)")
    if new_folders:
        out.append("")
        out.append(f"DEFICIT NOUVEAU -- {sum(len(f['new']) for f in new_folders)} "
                   f"carnet(s) dans {len(new_folders)} dossier(s) :")
        for entry in new_folders:
            out.append(f"  {entry['folder']}  ({entry['with_bar']} avec barre / "
                       f"{entry['without_bar']} sans)")
            for nb in entry["new"][:max_list]:
                out.append(f"    - {nb}")
            if len(entry["new"]) > max_list:
                out.append(f"    ... et {len(entry['new']) - max_list} autre(s)")
    else:
        out.append("")
        out.append("Aucun deficit nouveau.")
    return "\n".join(out)


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Deficit de barre de navigation par dossier (#24224).")
    parser.add_argument("--root", metavar="DIR",
                        help="Scanner une racine arbitraire (tests, audit hors depot).")
    parser.add_argument("--baseline", action="store_true",
                        help="Ecrire le baseline (snapshot courant du deficit).")
    parser.add_argument("--baseline-anyway", action="store_true", dest="baseline_anyway",
                        help="Ecrire le baseline meme si l'arbre n'est pas `main` propre.")
    parser.add_argument("--baseline-path", metavar="FILE", dest="baseline_path",
                        help="Chemin du baseline (defaut : scripts/tests/...).")
    parser.add_argument("--check", action="store_true",
                        help="Cliquet : code 1 si un carnet entre dans le deficit.")
    parser.add_argument("--max-list", type=int, default=8, metavar="N",
                        help="Carnets affiches par dossier (defaut : 8).")
    parser.add_argument("--json", action="store_true", help="Sortie JSON.")
    parser.add_argument("--quiet", action="store_true", help="Sortie minimale (CI).")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve() if args.root else None
    if root is not None and not root.is_dir():
        print(f"error: --root introuvable : {root}", file=sys.stderr)
        return 2

    folders, errors = collect(root)
    report = analyse(folders)
    report["instrument"] = INSTRUMENT_VERSION
    report["errors"] = errors

    baseline = load_baseline(args.baseline_path)
    new_folders, new_notebooks = _new_deficit(report, baseline)

    if args.baseline:
        provenance = _git_provenance(args.baseline_path or BASELINE_PATH)
        code, message = _baseline_refusal(provenance, args.baseline_anyway)
        if code:
            print(message, file=sys.stderr)
            return code
        written = write_baseline(report, args.baseline_path, provenance)
        if not args.quiet:
            total = sum(len(v) for v in _baseline_doc(report, provenance)["deficit"].values())
            print(f"baseline ecrite : {written} ({total} carnet(s) en deficit, "
                  f"{report['folders_deficit']} dossier(s))")
            if provenance.get("non_main"):
                print("  provenance non_main: true -- le baseline ne vaut pas "
                      "re-derivation sur `main`", file=sys.stderr)
        return 0

    if args.json:
        report["baseline_present"] = baseline is not None
        report["new"] = new_folders
        report["new_notebooks"] = new_notebooks
        print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    elif not args.quiet:
        print(_render(report, new_folders, baseline is not None, args.max_list))
        if errors:
            print(f"\n{len(errors)} carnet(s) illisible(s), hors mesure :", file=sys.stderr)
            for rel in errors[: args.max_list]:
                print(f"  {rel}", file=sys.stderr)

    if args.check and new_notebooks:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
