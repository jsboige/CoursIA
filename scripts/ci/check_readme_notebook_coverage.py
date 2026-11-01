#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Couverture README -> carnet -- organe du critere 3 de #13504.

Le critere 3 de l'EPIC #13504 s'enoncait « chaque notebook de ``02`` et
``03`` a une ligne dans le README de son dossier », et son bloc de fraicheur
du 2026-10-28 recommandait explicitement d'en faire un **organe** plutot
qu'une case cochee a la main une fois par trimestre.

Ce que ce controle ajoute, et pourquoi il n'existait pas :

  - ``scripts/ci/check_site_links.py`` couvre la direction **README -> carnet**
    (un lien du README qui pointe vers un fichier absent, 404) ;
  - la direction **inverse** -- un carnet present sur disque qu'aucune ligne
    du README de son dossier ne nomme -- n'etait couverte par aucun organe.
    C'est pourtant celle qui laisse un carnet invisible pour un lecteur qui
    n'ouvre que le README.

Convention mesuree avant conception, et qui dicte les classes :

  - un dossier « a convention en force » est un dossier dont le README nomme
    au moins un carnet : la, l'absence d'une ligne est un **defaut** ;
  - sur ``origin/main`` au 2026-10-31 : 1722 carnets suivis, 464 dossiers
    portant un README, 1593 couverts, 28 manquants, 12 jumeaux ``_en``
    manquants, 89 carnets sous un dossier sans README, 6 dossiers a
    convention OFF ;
  - les jumeaux ``_en`` sont **advisory** et jamais bloquants : la convention
    mesuree (ex. ``GenAI/Texte/FineTuning``) est de ne pas les lister. Un
    controle qui les rougirait fabriquerait du travail de masse sans
    fondement ;
  - les dossiers sans README et ceux a convention OFF sont **advisory** :
    l'absence de README n'est pas une derive, c'est un etat.

Le stock ne rougit personne (precedent ``prose-counts``, #17636) : en scan
complet les 28 manquants sont **rapportes**, pas sanctionnes. En mode delta
(``--diff-base``), un carnet **ajoute par la PR** dans un dossier a
convention en force et sans ligne au README est un **echec** -- c'est le seul
geste que la PR peut corriger elle-meme.

Piege de mesure ecarte : ``3.9d`` vit sous ``_archive/`` et n'a pas a figurer
au README. Un comptage naif le rend « manquant ». Il est ecarte par lecture
du chemin, jamais par suppression du controle.

Usage :

    python scripts/ci/check_readme_notebook_coverage.py
    python scripts/ci/check_readme_notebook_coverage.py --json
    python scripts/ci/check_readme_notebook_coverage.py --diff-base origin/main
    python scripts/ci/check_readme_notebook_coverage.py --strict   # warnings = exit 1
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Racine pedagogique par defaut. Les carnets hors de cette racine (scripts,
# tests) ne sont pas concernes par la convention README de dossier.
DEFAULT_ROOT = "MyIA.AI.Notebooks"

# Dossiers dont le contenu est archive, jetable ou genere : l'absence de ligne
# au README y est normale, et les exclure ici vaut mieux que de les tolerer
# plus loin comme faux positifs.
SKIP_DIR_NAMES = frozenset({
    "_archive",
    ".ipynb_checkpoints",
    "node_modules",
    ".lake",
    ".ipynb",
})

# Classes de verdicts. Seule `missing_in_readme` peut faire echouer le delta ;
# les autres sont des avertissements (advisory), promus par `--strict`.
MISSING = "missing_in_readme"
EN_SIBLING = "en_sibling_missing"
NO_README = "no_dir_readme"
CONVENTION_OFF = "convention_off"

ADVISORY_CLASSES = (EN_SIBLING, NO_README, CONVENTION_OFF)


@dataclass
class Finding:
    """Un carnet et le verdict qui le concerne."""

    path: str
    kind: str
    detail: str

    def as_dict(self) -> dict[str, str]:
        return {"path": self.path, "kind": self.kind, "detail": self.detail}


@dataclass
class Report:
    """Resultat d'une passe, pret a etre rendu en texte ou en JSON."""

    totals: dict[str, int] = field(default_factory=dict)
    findings: list[Finding] = field(default_factory=list)
    added: list[str] = field(default_factory=list)
    delta: bool = False

    def blocking(self) -> list[Finding]:
        """Manquants qui comptent : le stock en scan complet, le delta sinon."""

        missing = [f for f in self.findings if f.kind == MISSING]
        if not self.delta:
            return []
        added = set(self.added)
        return [f for f in missing if f.path in added]


def _git_list(repo_root: Path, pattern: str) -> list[str] | None:
    """Chemins suivis par git pour un motif, ou ``None`` si git est indisponible.

    ``-z`` : les chemins accentues ou espaces ne sont pas echappes, donc aucun
    demultiplexage fragile. Un ``None`` n'est pas une erreur : c'est le signal
    qu'il faut retomber sur le disque (tests, export sans git).
    """

    proc = subprocess.run(
        ["git", "-C", str(repo_root), "ls-files", "-z", "--", pattern],
        capture_output=True, text=True, encoding="utf-8", errors="surrogateescape",
    )
    if proc.returncode != 0:
        return None
    return [p for p in proc.stdout.split("\0") if p.strip()]


def _enumerate(repo_root: Path, root_rel: str, suffix: str) -> list[str]:
    """Chemins relatifs au depot, **suivis** quand git repond, disque sinon.

    Lire le suivi plutot que le disque n'est pas un detail : un carnet ignore
    (``MyIA.AI.Notebooks/GradeBook.ipynb`` l'est) n'existe pas dans un
    checkout CI mais existe sur un poste, ce qui ferait diverger les comptes
    entre les deux sans qu'aucun des deux ne soit faux. Un organe de mesure
    mesure ce qui est publie.
    """

    tracked = _git_list(repo_root, f"{root_rel}/**/*{suffix}")
    if tracked is not None:
        return sorted(p for p in tracked
                      if not (set(Path(p).parts) & SKIP_DIR_NAMES))
    base = repo_root / root_rel
    out = [p.relative_to(repo_root).as_posix() for p in base.rglob(f"*{suffix}")
           if p.is_file() and not (set(p.parts) & SKIP_DIR_NAMES)]
    return sorted(out)


def _readme_texts(repo_root: Path, readme_paths: list[str]) -> dict[str, str]:
    """Texte concatene des README d'un dossier, indexe par dossier."""

    by_dir: dict[str, list[str]] = {}
    for rel in readme_paths:
        by_dir.setdefault(str(Path(rel).parent.as_posix()), []).append(rel)
    texts: dict[str, str] = {}
    for directory, readmes in by_dir.items():
        chunks = []
        for rel in sorted(readmes):
            try:
                chunks.append((repo_root / rel).read_text(
                    encoding="utf-8", errors="replace"))
            except OSError:
                continue
        if chunks:
            texts[directory] = "\n".join(chunks)
    return texts


def scan(repo_root: Path, root_rel: str = DEFAULT_ROOT) -> Report:
    """Passe complete : classe chaque carnet du perimetre."""

    report = Report()
    if not (repo_root / root_rel).is_dir():
        report.totals = {"notebooks": 0}
        return report

    notebooks = _enumerate(repo_root, root_rel, ".ipynb")
    readmes = _readme_texts(repo_root, _enumerate(repo_root, root_rel, "README*.md"))

    per_dir: dict[str, list[str]] = {}
    for rel in notebooks:
        per_dir.setdefault(str(Path(rel).parent.as_posix()), []).append(rel)

    covered = 0
    for directory, members in per_dir.items():
        text = readmes.get(directory)
        names = {rel: Path(rel).name for rel in members}

        if text is None:
            for rel in members:
                report.findings.append(Finding(
                    rel, NO_README, "le dossier ne porte aucun README"))
            continue

        if not any(name in text for name in names.values()):
            # README present mais aucun carnet liste : la convention n'y est
            # pas en force, l'absence de ligne n'est donc pas un defaut.
            for rel in members:
                report.findings.append(Finding(
                    rel, CONVENTION_OFF,
                    "le README du dossier ne liste aucun carnet"))
            continue

        for rel in members:
            if names[rel] in text:
                covered += 1
                continue
            kind = EN_SIBLING if names[rel].endswith("_en.ipynb") else MISSING
            detail = (
                "jumeau `_en` non liste (convention : les jumeaux ne le sont pas)"
                if kind == EN_SIBLING
                else "absent du README de son dossier, qui en liste d'autres"
            )
            report.findings.append(Finding(rel, kind, detail))

    counts: dict[str, int] = {MISSING: 0, EN_SIBLING: 0, NO_README: 0,
                              CONVENTION_OFF: 0}
    for finding in report.findings:
        counts[finding.kind] = counts.get(finding.kind, 0) + 1
    counts["notebooks"] = len(notebooks)
    counts["covered"] = covered
    # Dossiers qui portent a la fois des carnets et un README : c'est le seul
    # ensemble ou la question « ce carnet a-t-il sa ligne ? » a un sens.
    counts["dirs_with_notebooks_and_readme"] = sum(
        1 for d in per_dir if d in readmes)
    report.totals = counts
    return report


def added_notebooks(repo_root: Path, diff_base: str,
                    root_rel: str = DEFAULT_ROOT) -> list[str]:
    """Carnets ajoutes entre ``diff_base`` et HEAD, restreints au perimetre."""

    # `encoding=` est obligatoire : un chemin accentue (le corpus en porte)
    # ferait lever un UnicodeDecodeError sous la locale cp1252 de Windows.
    proc = subprocess.run(
        ["git", "-C", str(repo_root), "diff", "--diff-filter=A",
         "--name-only", f"{diff_base}...HEAD"],
        capture_output=True, text=True, encoding="utf-8",
        errors="surrogateescape",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git diff a echoue contre {diff_base!r}: {proc.stderr.strip()}")
    prefix = root_rel.rstrip("/") + "/"
    out = []
    for line in proc.stdout.splitlines():
        rel = line.strip()
        if not rel.endswith(".ipynb") or not rel.startswith(prefix):
            continue
        if set(Path(rel).parts) & SKIP_DIR_NAMES:
            continue
        out.append(rel)
    return sorted(out)


def run(repo_root: Path, root_rel: str = DEFAULT_ROOT,
        diff_base: str | None = None) -> Report:
    """Passe complete, optionnellement restreinte a un delta de PR."""

    report = scan(repo_root, root_rel)
    if diff_base:
        report.delta = True
        report.added = added_notebooks(repo_root, diff_base, root_rel)
    return report


def render(report: Report, stream=None) -> None:
    """Rapport lisible par un humain."""

    if stream is None:
        # Defaut resolu a l'appel, jamais a l'import : `sys.stdout` fige au
        # chargement du module echappe a la capture (pytest, redirection shell).
        stream = sys.stdout
    t = report.totals
    print(f"Perimetre : {t.get('notebooks', 0)} carnets, "
          f"{t.get('dirs_with_notebooks_and_readme', 0)} dossiers a carnets "
          f"portant un README, {t.get('covered', 0)} couverts", file=stream)
    print(f"Classes : {MISSING}={t.get(MISSING, 0)}, "
          f"{EN_SIBLING}={t.get(EN_SIBLING, 0)}, "
          f"{NO_README}={t.get(NO_README, 0)}, "
          f"{CONVENTION_OFF}={t.get(CONVENTION_OFF, 0)}", file=stream)

    if report.delta:
        print(f"Delta contre {len(report.added)} carnet(s) ajoute(s)", file=stream)
        blocking = report.blocking()
        if blocking:
            print("ECHEC -- carnet(s) ajoute(s) sans ligne au README "
                  "d'un dossier a convention en force :", file=stream)
            for finding in blocking:
                print(f"  - {finding.path}", file=stream)
            print("  Corriger : ajouter la ligne au README du dossier dans "
                  "cette PR.", file=stream)
        else:
            print("OK -- aucun carnet ajoute sans ligne au README", file=stream)
    else:
        missing = [f for f in report.findings if f.kind == MISSING]
        if missing:
            print(f"Stock : {len(missing)} carnet(s) sans ligne au README "
                  "(rapporte, non sanctionne -- le stock ne rougit personne) :",
                  file=stream)
            for finding in missing[:20]:
                print(f"  - {finding.path}", file=stream)
            if len(missing) > 20:
                print(f"  ... et {len(missing) - 20} autre(s)", file=stream)

    advisory = [f for f in report.findings if f.kind in ADVISORY_CLASSES]
    if advisory:
        print(f"Advisory : {len(advisory)} constat(s) non bloquant(s)",
              file=stream)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Couverture README -> carnet (critere 3 de #13504)")
    parser.add_argument("--repo-root", default=str(REPO_ROOT),
                        help="racine du depot (defaut : deduite du script)")
    parser.add_argument("--root", default=DEFAULT_ROOT,
                        help=f"racine pedagogique scannee (defaut : {DEFAULT_ROOT})")
    parser.add_argument("--diff-base", default=None,
                        help="ref de base : ne fait echouer que les carnets AJOUTES")
    parser.add_argument("--json", action="store_true",
                        help="sortie machine")
    parser.add_argument("--strict", action="store_true",
                        help="les constats advisory deviennent bloquants")
    args = parser.parse_args(argv)

    # Un carnet au nom accentue dans une console cp1252 (Windows) ferait lever
    # un UnicodeEncodeError au milieu du rapport : l'organe mourrait avec un
    # code non concluant au lieu de rendre son verdict. On force l'encodage de
    # sortie, sans echouer si le flux ne se reconfigure pas (capture, pipe).
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, OSError, ValueError):
            pass

    repo_root = Path(args.repo_root).resolve()
    try:
        report = run(repo_root, args.root, args.diff_base)
    except RuntimeError as exc:
        print(f"incident d'entree: {exc}", file=sys.stderr)
        return 2

    blocking = report.blocking()
    advisory = [f for f in report.findings if f.kind in ADVISORY_CLASSES]
    failed = bool(blocking) or (args.strict and bool(advisory))

    if args.json:
        print(json.dumps({
            "totals": report.totals,
            "delta": report.delta,
            "added": report.added,
            "blocking": [f.as_dict() for f in blocking],
            "advisory": [f.as_dict() for f in advisory],
            "findings": [f.as_dict() for f in report.findings],
            "verdict": "FAIL" if failed else "OK",
        }, ensure_ascii=False, indent=2))
    else:
        render(report)
        if args.strict and advisory and not blocking:
            print(f"ECHEC (--strict) : {len(advisory)} constat(s) advisory",
                  file=sys.stderr)

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
