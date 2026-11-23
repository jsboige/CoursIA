#!/usr/bin/env python
"""Module CLI de l'organe manifeste des dependances (#27544).

Scission du 20/11 (#26364, cliquet de taille des scripts) : le module
d'origine depassait le plafond des scripts neufs. Les responsabilites
sont separees, la facade `dependency_manifest.py` garde le chemin
d'appel et re-expose l'API.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from dependency_manifest_lecture import (
    DEFAULT_OUT_DIR,
    _REPO_ROOT,
)
from dependency_manifest_construction import (
    build_manifest,
)
from dependency_manifest_rendu import (
    _diff_paths,
    _normalize_for_freshness,
    _normalize_markdown,
    render_markdown,
)
def check_freshness(repo_root: Path, out_dir: Path) -> tuple[str, list[str]]:
    """Compare les sorties versionnees a une regeneration de l'etat courant.

    Rend ``(etat, ecarts)`` avec ``etat`` dans ``{"frais", "perime",
    "incident"}``. ``incident`` signifie que la sortie committe est absente ou
    illisible : ce n'est pas une preuve de perimetre, c'est un **verdict
    inconnu**, et les deux ne se confondent jamais.
    """
    json_path = out_dir / "manifeste-dependances.json"
    md_path = out_dir / "manifeste-dependances.md"
    if not json_path.is_file():
        return "incident", ["sortie absente : %s" % json_path]
    try:
        committed = json.loads(json_path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001 - une sortie illisible est un incident
        return "incident", ["sortie illisible : %s (%s)" % (json_path, exc)]
    manifest = build_manifest(repo_root)
    diffs = _diff_paths(
        _normalize_for_freshness(committed), _normalize_for_freshness(manifest)
    )
    if md_path.is_file():
        committed_md = _normalize_markdown(md_path.read_text(encoding="utf-8"))
        fresh_md = _normalize_markdown(render_markdown(manifest))
        if committed_md != fresh_md:
            diffs.append(
                "manifeste-dependances.md : contenu different de la regeneration"
            )
    return ("perime", diffs) if diffs else ("frais", [])


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Manifeste des dependances du cursus par famille de noyau (#27544)."
        )
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=_REPO_ROOT,
        help="racine du depot (par defaut : la racine du script)",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help=f"repertoire de sortie (defaut : {DEFAULT_OUT_DIR})",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="ecrit les sorties versionnees (manifeste-dependances.md / .json)",
    )
    parser.add_argument(
        "--print",
        action="store_true",
        help="affiche le rendu Markdown sur la sortie standard",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "garde de fraicheur : compare les sorties versionnees a une "
            "regeneration de l'etat courant (0 frais, 1 perime, 2 incident)"
        ),
    )
    args = parser.parse_args(argv)

    repo_root = args.repo_root.resolve()

    if args.check:
        out_dir = (args.out_dir or (repo_root / DEFAULT_OUT_DIR)).resolve()
        etat, ecarts = check_freshness(repo_root, out_dir)
        if etat == "frais":
            print("FRAIS : le manifeste committe decrit l'etat courant.")
            return 0
        if etat == "incident":
            print("INCIDENT : la garde de fraicheur n'a pas pu conclure.")
            for line in ecarts:
                print("  - %s" % line)
            return 2
        print(
            "PERIME : %d ecart(s) entre le manifeste committe et sa regeneration."
            % len(ecarts)
        )
        for line in ecarts[:20]:
            print("  - %s" % line)
        if len(ecarts) > 20:
            print("  ... %d ecart(s) supplementaire(s)" % (len(ecarts) - 20))
        return 1

    manifest = build_manifest(repo_root)
    markdown = render_markdown(manifest)

    if args.write:
        out_dir = (args.out_dir or (repo_root / DEFAULT_OUT_DIR)).resolve()
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "manifeste-dependances.md").write_text(
            markdown, encoding="utf-8", newline="\n"
        )
        (out_dir / "manifeste-dependances.json").write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
            newline="\n",
        )
    elif args.print or not args.write:
        print(markdown)

    complete = all(entry["verdict"] for entry in manifest["groups"])
    conflicts_named = all(
        conflict.get("resolution") for conflict in manifest["conflicts"]
    )
    return 0 if complete and conflicts_named else 1


