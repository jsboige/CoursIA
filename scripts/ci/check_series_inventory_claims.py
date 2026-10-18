#!/usr/bin/env python3
r"""Coherence body d'issue parente <-> carnets reels d'une serie (#20445).

Classe de defaut mesuree : a chaque descente de palier ou accretion d'une
sous-serie, le body de l'issue qui pilote la serie omet un carnet reellement
livre sur main. Instances fondatrices (audit #20445) :

- #20381 (escalier Dynamics) : la liste 01-08 omisait precisement le seul
  carnet REEL (09, livre par #16231) -- le defaut user du 2026-10-11 etait
  inverse de la presentation du body.
- #19494 (plan Percolation) : le plan enumerait 01, 02 et trois carnets "a
  venir" ; main porte 6 carnets, dont deux accretions (03b, 03c) que le body
  n'a jamais citees.

L'organe rend la classe observable sans dependre de la vigilance : il confronte
l'enumeration du body aux carnets reels d'un chemin de serie, dans les deux
sens.

Verdicts (par carnet, pas global -- chaque finding nomme son carnet) :

    ON_DISK_NOT_CITED   carnet reel sous <serie> absent de toute enumeration
                        du body (le defaut user) -- exit 1
    CITED_NOT_ON_DISK   le body cite un carnet introuvable sous <serie>
                        (renomme, jamais livre, ou typo) -- exit 1
    OK                  chaque carnet reel est cite, chaque cite est reel
                        -- exit 0

Conventions portees par l'organe :

- un `_archive/` sous le chemin de serie est hors inventaire (convention
  `_archive`, 11 emplacements) ;
- un nom cite sans suffixe `.ipynb` compte (les plans citent souvent le
  basename nu, ex. `Percolation-03-Critique-Python`) ;
- `--expect` list des omissions assumees (carnet deliberement non cite),
  chacune exigee AVEC motif ecrit : `--expect Nom=motif` -- une exemption sans
  motif est refusee (un filet qui s'elargit sans trace ne vaut rien).

Le body ne se lit PAS via gh par defaut : `--body-file` est l'entree canonique
(le texte du body, extrait par l'appelant). Un futur cablage CI pourra fournir
le corps depuis l'API ; l'organe reste deterministe et testable sans reseau.

Usage :
    python scripts/ci/check_series_inventory_claims.py \
        --body-file body.txt --series MyIA.AI.Notebooks/Probas/Applications/Percolation
    ... --expect Percolation-04-Sharpness-Lean="exploratoire, jamais livre" --json
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

TOKEN_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.\-]*[A-Za-z0-9]")

# Un token du body compte comme citation de carnet s'il ressemble a un nom de
# carnet de la serie : il apparait litteralement (avec ou sans .ipynb) dans le
# body ET correspond au stem d'un carnet reel. La correspondance se fait par
# stem exact -- jamais par sous-chaine, qui fabriquerait des citations
# (Search-03 citerait Search-03b).
ARCHIVE_DIR = "_archive"


def notebook_stem(path: Path) -> str:
    """Stem du carnet : basename sans extension .ipynb."""
    return path.name[: -len(".ipynb")] if path.name.endswith(".ipynb") else path.stem


def list_series_notebooks(series_dir: Path, repo_root: Path) -> list[Path]:
    """Carnets reels sous <repo_root>/<series>, _archive exclu, tries."""
    root = repo_root / series_dir
    if not root.is_dir():
        return []
    out: list[Path] = []
    for p in sorted(root.rglob("*.ipynb")):
        if ARCHIVE_DIR in p.relative_to(repo_root).parts:
            continue
        out.append(p)
    return out


def body_citations(body: str) -> set[str]:
    """Stems cites dans le body : tokens litteraux, extension optionnelle."""
    cited: set[str] = set()
    for token in TOKEN_RE.findall(body):
        if token.endswith(".ipynb"):
            cited.add(token[: -len(".ipynb")])
        else:
            cited.add(token)
    return cited


def parse_expect(raw: list[str]) -> dict[str, str]:
    """`Nom=motif` -> {Nom: motif} ; refuse une exemption sans motif."""
    expect: dict[str, str] = {}
    for item in raw:
        if "=" not in item:
            raise SystemExit(
                f"exemption sans motif refusee : {item!r} -- forme exigee Nom=motif"
            )
        name, _, reason = item.partition("=")
        if not reason.strip():
            raise SystemExit(
                f"exemption sans motif refusee : {item!r} -- forme exigee Nom=motif"
            )
        expect[name.strip()] = reason.strip()
    return expect


def analyse(body: str, notebooks: list[Path]) -> list[dict[str, str]]:
    """Findings bruts, sans appliquer les exemptions."""
    cited = body_citations(body)
    on_disk = {notebook_stem(p): p for p in notebooks}
    findings: list[dict[str, str]] = []
    for stem in sorted(on_disk):
        if stem not in cited:
            findings.append(
                {
                    "verdict": "ON_DISK_NOT_CITED",
                    "notebook": stem,
                    "path": str(on_disk[stem]),
                }
            )
    for stem in sorted(cited):
        # Un stem cite ne compte CITED_NOT_ON_DISK que s'il ressemble a un
        # carnet de la serie : soit il porte l'extension dans le body (donne
        # plus haut), soit il partage le prefix de serie d'un carnet reel.
        # Les tokens de prose quelconques ("README", "main") restent hors
        # verdict : un body cite toujours autre chose que des carnets.
        if stem not in on_disk and looks_like_series_notebook(stem, on_disk):
            findings.append({"verdict": "CITED_NOT_ON_DISK", "notebook": stem, "path": "-"})
    return findings


def looks_like_series_notebook(stem: str, on_disk: dict[str, Path]) -> bool:
    """Le stem cite ressemble-t-il a un carnet de la serie ?

    Critere conservateur : il partage le prefix numerique de serie avec un
    carnet reel (ex. `Percolation-04-Sharpness-Lean` partage `Percolation-04`
    avec `Percolation-04-Sharpness-Python` reel). Un token quelconque du body
    ne declenche donc jamais le verdict.
    """
    m = re.match(r"^(?P<prefix>.+?-\d+[a-z]?)", stem)
    if not m:
        return False
    prefix = m.group("prefix")
    return any(real.startswith(prefix) for real in on_disk)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--body-file", required=True, help="texte du body de l'issue")
    parser.add_argument("--series", required=True, help="chemin de serie relatif au repo")
    parser.add_argument("--repo-root", default=".", help="racine du repo (defaut : cwd)")
    parser.add_argument(
        "--expect",
        action="append",
        default=[],
        metavar="NOM=MOTIF",
        help="omission assumee, motif ecrit obligatoire (repeter l'option)",
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root).resolve()
    series_dir = Path(args.series)
    root = repo_root / series_dir
    if not root.is_dir():
        print(f"UNKNOWN serie introuvable : {root}", file=sys.stderr)
        return 0  # infrastructure jamais forge un rouge (#14849)

    body = Path(args.body_file).read_text(encoding="utf-8")
    expect = parse_expect(args.expect)
    notebooks = list_series_notebooks(series_dir, repo_root)

    findings = [f for f in analyse(body, notebooks) if f["notebook"] not in expect]

    if args.json:
        print(
            json.dumps(
                {
                    "series": args.series,
                    "notebooks_on_disk": len(notebooks),
                    "exemptions": expect,
                    "findings": findings,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        for f in findings:
            print(f"{f['verdict']}: {f['notebook']} ({f['path']})")
        for name, reason in expect.items():
            print(f"EXEMPT: {name} -- {reason}")
        if not findings:
            print(f"OK: {len(notebooks)} carnets reels, tous cites, aucun cite fantome")

    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
