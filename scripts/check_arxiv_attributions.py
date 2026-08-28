#!/usr/bin/env python3
"""Vérifie que les attributions arXiv corrigées restent présentes dans leurs notebooks.

Ce script lit `arxiv_attributions_registry.yaml` (par défaut à la racine du dépôt)
et pour chaque entrée :
  1. Ouvre le notebook indiqué
  2. Cherche la chaîne `expected_citation` dans la cellule `cell_index`
  3. Si absente : lève rouge (exit 1) avec un rapport détaillé
  4. Si présente : enregistre PASS

Quand un notebook est renommé ou restructuré, mettre à jour le registre —
**ne pas adapter le check pour qu'il passe en silence** (règle Stop & Repair :
corriger la cause, pas maquiller la sortie).

Usage:
  python scripts/check_arxiv_attributions.py
  python scripts/check_arxiv_attributions.py --registry /path/to/registry.yaml
  python scripts/check_arxiv_attributions.py --paths scope1/**/*.ipynb scope2/**/*.ipynb
  python scripts/check_arxiv_attributions.py --json

Options:
  --registry PATH    Chemin du registre YAML (défaut: arxiv_attributions_registry.yaml)
  --paths GLOB ...   Limiter la vérification aux notebooks matchant les globs
  --json             Sortie JSON structurée (pour CI)
  --strict           Traiter les renames (notebook déplacé) comme un échec rouge
                     (défaut: WARN avec suggestion de mise à jour du registre)
  --repo-root PATH   Racine du dépôt (défaut: répertoire parent du script)
"""

from __future__ import annotations

import argparse
import glob
import io
import json
import os
import re
import sys
from pathlib import Path

# Force UTF-8 sur stdout/stderr (Windows cp1252 ne supporte pas ✓ ✗ ~)
if sys.platform == "win32":
    try:
        sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
        sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding="utf-8", errors="replace")
    except Exception:
        pass

try:
    import yaml
except ImportError:
    sys.stderr.write(
        "ERREUR: PyYAML manquant. Installer via `pip install pyyaml`.\n"
    )
    sys.exit(2)


def _default_repo_root() -> Path:
    """Racine du dépôt: parent du dossier scripts/."""
    return Path(__file__).resolve().parent.parent


def _default_registry_path(repo_root: Path) -> Path:
    """Cherche le registre à la racine du dépôt."""
    return repo_root / "arxiv_attributions_registry.yaml"


def _strip_ipynb_quotes(path: str | Path) -> Path:
    """Normalise un chemin qui peut être entouré de quotes."""
    s = str(path).strip().strip('"').strip("'")
    return Path(s)


def _glob_to_paths(patterns: list[str], repo_root: Path) -> list[Path]:
    """Étend une liste de globs (relatifs à repo_root) en chemins absolus."""
    paths: set[Path] = set()
    for pat in patterns:
        # Glob récursif
        matches = glob.glob(str(repo_root / pat), recursive=True)
        for m in matches:
            paths.add(Path(m).resolve())
    return sorted(paths)


def _load_registry(registry_path: Path) -> list[dict]:
    """Charge le YAML et retourne la liste d'attributions."""
    if not registry_path.exists():
        sys.stderr.write(f"ERREUR: registre introuvable: {registry_path}\n")
        sys.exit(2)
    with registry_path.open("r", encoding="utf-8") as f:
        data = yaml.safe_load(f)
    if not isinstance(data, dict) or "attributions" not in data:
        sys.stderr.write(
            f"ERREUR: registre mal formé (clé 'attributions' manquante): {registry_path}\n"
        )
        sys.exit(2)
    attributions = data["attributions"]
    if not isinstance(attributions, list):
        sys.stderr.write("ERREUR: 'attributions' doit être une liste.\n")
        sys.exit(2)
    return attributions


def _matches_paths(notebook_rel: str, scope: list[Path] | None) -> bool:
    """Vérifie si `notebook_rel` est dans le scope des pathspecs.

    Si scope est None, retourne True (tout est inclus).
    Sinon, match exact sur les chemins résolus.
    """
    if scope is None:
        return True
    nb_path = _strip_ipynb_quotes(notebook_rel).resolve()
    for sp in scope:
        try:
            nb_path.relative_to(sp)
            return True
        except ValueError:
            continue
    return False


def _read_notebook_cell(notebook_path: Path, cell_index: int) -> str:
    """Lit la cellule `cell_index` (0-based) et retourne son texte concaténé.

    Le texte concaténé = sources markdown + sources code (pour les cellules
    de type `markdown` ou `code`). Lève IndexError si cell_index hors borne.
    """
    if not notebook_path.exists():
        raise FileNotFoundError(f"Notebook introuvable: {notebook_path}")
    with notebook_path.open("r", encoding="utf-8") as f:
        nb = json.load(f)
    cells = nb.get("cells", [])
    if cell_index < 0 or cell_index >= len(cells):
        raise IndexError(
            f"cell_index {cell_index} hors borne (notebook a {len(cells)} cellules)"
        )
    cell = cells[cell_index]
    return "".join(cell.get("source", []))


def _check_attribution(
    entry: dict, repo_root: Path, strict: bool
) -> dict:
    """Vérifie une entrée du registre. Retourne un dict résultat."""
    arxiv_id = entry["arxiv_id"]
    nb_rel = entry["notebook"]
    cell_idx = entry["cell_index"]
    expected = entry["expected_citation"]
    source_pr = entry.get("source_pr", "?")

    nb_path = _strip_ipynb_quotes(nb_rel)
    if not nb_path.is_absolute():
        nb_path = repo_root / nb_path
    nb_path = nb_path.resolve()

    result = {
        "arxiv_id": arxiv_id,
        "notebook": nb_rel,
        "cell_index": cell_idx,
        "source_pr": source_pr,
        "status": "PASS",
        "detail": "",
    }

    if not nb_path.exists():
        # Notebook déplacé ou renommé — suggère de mettre à jour le registre
        # En mode --strict, on remonte comme FAIL pour empêcher la dérive silencieuse.
        result["status"] = "RENAMED"
        result["detail"] = (
            f"Notebook introuvable sur disque: {nb_rel}. "
            f"Si renommé, mettre à jour 'notebook' dans le registre "
            f"(source: {source_pr})."
        )
        if strict:
            # En mode strict, on conserve le label RENAMED pour le diagnostic
            # mais on transforme le verdict final en échec (voir main()).
            # On retourne ici le résultat "brut" — main() appliquera la sévérité.
            pass
        return result

    try:
        cell_text = _read_notebook_cell(nb_path, cell_idx)
    except IndexError as e:
        result["status"] = "FAIL"
        result["detail"] = (
            f"cell_index {cell_idx} hors borne ({e}). "
            f"Notebook restructuré ? Mettre à jour 'cell_index' (source: {source_pr})."
        )
        return result
    except (json.JSONDecodeError, OSError) as e:
        result["status"] = "FAIL"
        result["detail"] = f"Erreur lecture notebook {nb_rel}: {e}"
        return result

    if expected not in cell_text:
        result["status"] = "FAIL"
        # Tenter de détecter si la cellule est devenue vide ou si l'attribution
        # a été ré-écrite (règle Stop & Repair : il faut comprendre la cause)
        cell_excerpt = cell_text[:120].replace("\n", " ")
        result["detail"] = (
            f"expected_citation absent cellule {cell_idx} de {nb_rel}. "
            f"Contenu actuel (120 premiers chars): {cell_excerpt!r}. "
            f"Source originale: {source_pr}."
        )
        return result

    return result


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Vérifie les attributions arXiv du registre."
    )
    parser.add_argument(
        "--registry",
        type=Path,
        default=None,
        help="Chemin du registre YAML (défaut: arxiv_attributions_registry.yaml à la racine).",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Racine du dépôt (défaut: parent de scripts/).",
    )
    parser.add_argument(
        "--paths",
        nargs="+",
        default=None,
        help="Limiter aux notebooks matchant ces globs (relatifs à repo-root).",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Traiter les renames (notebook déplacé) comme FAIL au lieu de RENAMED.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Sortie JSON structurée (utile en CI).",
    )
    args = parser.parse_args()

    repo_root = (args.repo_root or _default_repo_root()).resolve()
    registry = args.registry or _default_registry_path(repo_root)

    attributions = _load_registry(registry)
    scope = _glob_to_paths(args.paths, repo_root) if args.paths else None

    results: list[dict] = []
    for entry in attributions:
        if not _matches_paths(entry["notebook"], scope):
            continue
        results.append(_check_attribution(entry, repo_root, args.strict))

    # Synthèse
    counts = {"PASS": 0, "FAIL": 0, "RENAMED": 0}
    for r in results:
        counts[r["status"]] = counts.get(r["status"], 0) + 1

    if args.json:
        payload = {
            "registry": str(registry),
            "scope": [str(p) for p in scope] if scope else None,
            "checked": len(results),
            "summary": counts,
            "results": results,
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(f"# Check arXiv attributions — {len(results)} entrée(s)")
        print(f"# Registre: {registry}")
        if scope:
            print(f"# Scope: {len(scope)} pathspec(s)")
        print()
        for r in results:
            tag = {"PASS": "✓", "FAIL": "✗", "RENAMED": "~"}.get(r["status"], "?")
            line = f"{tag} [{r['status']}] {r['arxiv_id']} @ {r['notebook']}#{r['cell_index']} (source: {r['source_pr']})"
            print(line)
            if r["detail"]:
                print(f"    {r['detail']}")
        print()
        print(f"# Summary: {counts['PASS']} PASS, {counts['FAIL']} FAIL, {counts['RENAMED']} RENAMED")

    if counts["FAIL"] > 0 or (args.strict and counts["RENAMED"] > 0):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
