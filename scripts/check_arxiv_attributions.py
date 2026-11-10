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

Mode détection `--detect` (#22566)
----------------------------------
Le registre est un CLIQUET : il ne voit que les attributions déjà enregistrées.
Un identifiant FAUX jamais enregistré y est structurellement invisible (cas
fondateur #22537 : `arXiv:1505.04322` citait un article réel mais sans rapport).
Le mode `--detect` complète le cliquet en DETECTEUR :

  1. Énumère tous les identifiants `arXiv:NNNN.NNNNN` du dépôt HORS registre.
     Périmètre couvert : cellules des notebooks (`*.ipynb`), sources Python
     (`*.py`, docstrings comprises) et documentation (`docs/**/*.md`), en
     excluant les répertoires vendus/non gérés (`.lake`, `node_modules`,
     `foundry-lib`, `_archives`, checkpoints).
  2. Résout chaque identifiant via l'API arXiv (organe natif
     `notebook_tools.verify_arxiv_ids.verify_ids`) et contrôle l'IDENTITÉ :
     la part des tokens salients du titre résolu présente dans le contexte
     de citation (±240 caractères autour de l'occurrence). En dessous de 50 %,
     le fichier attribue l'identifiant au MAUVAIS article → rouge.
     Un identifiant inexistant (verdict `notfound`) est aussi rouge : l'identité
     échoue a fortiori. Un échec de réseau (`transport`) ne prononce AUCUN
     verdict → SKIPPED, jamais rouge (l'infra n'est pas une mesure).

Usage:
  python scripts/check_arxiv_attributions.py
  python scripts/check_arxiv_attributions.py --registry /path/to/registry.yaml
  python scripts/check_arxiv_attributions.py --paths scope1/**/*.ipynb scope2/**/*.ipynb
  python scripts/check_arxiv_attributions.py --json
  python scripts/check_arxiv_attributions.py --detect
  python scripts/check_arxiv_attributions.py --detect --paths "MyIA.AI.Notebooks/**/*.ipynb"

Options:
  --registry PATH    Chemin du registre YAML (défaut: arxiv_attributions_registry.yaml)
  --paths GLOB ...   Mode registre : limiter aux notebooks matchant les globs.
                     Mode --detect : globs de fichiers (fnmatch sur le chemin
                     relatif POSIX) limitant l'énumération.
  --detect           Mode détection (identifiants hors registre + contrôle
                     d'identité via l'API arXiv) au lieu du mode registre.
  --json             Sortie JSON structurée (pour CI)
  --strict           Traiter les renames (notebook déplacé) comme un échec rouge
                     (défaut: WARN avec suggestion de mise à jour du registre)
  --repo-root PATH   Racine du dépôt (défaut: répertoire parent du script)

Seam de test : `ARXIV_DETECT_RESOLUTIONS=<fichier JSON>` — `{id: {verdict,
title, authors}}` rejoué à la place de l'API (déterminisme hors réseau ;
l'organe lui-même n'a aucun comportement mock, seul le transport est substitué).
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


# ---------------------------------------------------------------------------
# Mode détection (#22566) — identifiants hors registre + contrôle d'identité
# ---------------------------------------------------------------------------

#: Forme explicite des identifiants : `arXiv:NNNN.NNNNN` (version optionnelle).
ARXIV_ID_RE = re.compile(r"arXiv:(\d{4}\.\d{4,5})(?:v\d+)?")

#: Répertoires vendus / non gérés : hors périmètre du détecteur (le périmètre
#: est le contenu propre du dépôt, pas les dépendances).
_DETECT_EXCLUDE_DIRS = frozenset({
    ".git", ".lake", "node_modules", ".ipynb_checkpoints",
    "_archives", "foundry-lib", ".tmp", "scratchpad",
})

#: Sous-répertoires de racine où les `.md` sont dans le périmètre de détection.
_DETECT_MD_UNDER = ("docs",)

#: Part minimale des tokens salients du titre résolu, présents dans le contexte
#: de citation, pour que l'attribution soit considérée concordante. En dessous
#: : le fichier attribue l'identifiant au mauvais article (#22537).
_IDENTITY_THRESHOLD = 0.5

#: Rayon du contexte de citation (caractères de part et d'autre de l'occurrence).
_CONTEXT_RADIUS = 240

#: Tokens sans signal pour l'identité (fr + en), minuscules.
_TITLE_STOP = frozenset(
    "a an the of on in for and to with over under from by is are be as at "
    "les le la un une du de des en dans par sur sous entre au aux vers"
    .split()
)


def _detect_files(repo_root: Path, scope_patterns: list[str] | None) -> list[Path]:
    """Fichiers du périmètre de détection : `*.ipynb`, `*.py`, `docs/**/*.md`."""
    out: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(repo_root):
        dirnames[:] = [d for d in dirnames if d not in _DETECT_EXCLUDE_DIRS]
        rel_parts = Path(dirpath).relative_to(repo_root).parts
        for fn in filenames:
            p = Path(dirpath) / fn
            suffix = p.suffix.lower()
            if suffix in (".ipynb", ".py"):
                take = True
            elif suffix == ".md" and rel_parts and rel_parts[0] in _DETECT_MD_UNDER:
                take = True
            else:
                take = False
            if take:
                out.append(p)
    if scope_patterns:
        import fnmatch
        out = [
            p for p in out
            if any(fnmatch.fnmatch(p.relative_to(repo_root).as_posix(), pat)
                   for pat in scope_patterns)
        ]
    return sorted(out)


def _file_text(p: Path) -> str:
    """Texte parcourable : toutes les cellules d'un notebook (markdown + code),
    texte brut pour `.py`/`.md`."""
    if p.suffix.lower() == ".ipynb":
        try:
            nb = json.loads(p.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            return ""
        return "\n".join("".join(c.get("source", [])) for c in nb.get("cells", []))
    try:
        return p.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _enumerate_arxiv_ids(repo_root: Path,
                         scope_patterns: list[str] | None) -> dict[str, list[str]]:
    """{identifiant: [chemins relatifs]} pour chaque occurrence du périmètre."""
    found: dict[str, list[str]] = {}
    for p in _detect_files(repo_root, scope_patterns):
        for m in ARXIV_ID_RE.finditer(_file_text(p)):
            found.setdefault(m.group(1), []).append(
                p.relative_to(repo_root).as_posix())
    return {k: sorted(set(v)) for k, v in found.items()}


def _resolve_ids(ids: list[str], fixture: str | None) -> list[dict]:
    """Résout les IDs via l'API arXiv (organe natif `verify_arxiv_ids`), ou via
    le fixture JSON du seam de test `ARXIV_DETECT_RESOLUTIONS`."""
    if fixture:
        data = json.loads(Path(fixture).read_text(encoding="utf-8"))
        return [
            {"id": i,
             "verdict": data.get(i, {}).get("verdict", "notfound"),
             "title": data.get(i, {}).get("title"),
             "authors": data.get(i, {}).get("authors", []),
             "error": None}
            for i in ids
        ]
    from notebook_tools.verify_arxiv_ids import verify_ids
    return verify_ids(ids)


def _title_tokens(title: str) -> set[str]:
    """Tokens salients d'un titre : minuscules, ponctuation retirée,
    stopwords exclus, longueur >= 4."""
    words = re.findall(r"[a-z0-9]+", (title or "").lower())
    return {w for w in words if len(w) >= 4 and w not in _TITLE_STOP}


def _identity_ratio(resolved_title: str, context: str) -> float | None:
    """Part des tokens salients du titre résolu présents dans le contexte.
    None si non mesurable (aucun token salient)."""
    tokens = _title_tokens(resolved_title)
    if not tokens:
        return None
    ctx = set(re.findall(r"[a-z0-9]+", (context or "").lower()))
    return len(tokens & ctx) / len(tokens)


def _check_detect_id(arxiv_id: str, locations: list[str],
                     text_cache: dict[str, str], resolution: dict) -> dict:
    """Verdict d'identité d'un identifiant hors registre."""
    result: dict = {
        "arxiv_id": arxiv_id, "locations": locations, "status": "OK", "detail": "",
    }
    if resolution.get("verdict") == "transport":
        result["status"] = "SKIPPED"
        result["detail"] = (
            f"API injoignable ({resolution.get('error')}) — aucun verdict prononcé"
        )
        return result
    if resolution.get("verdict") != "ok":
        result["status"] = "MISMATCH"
        result["detail"] = (
            "identifiant non résolu par l'API arXiv — le fichier attribue un "
            "article inexistant"
        )
        return result
    title = resolution.get("title") or ""
    best: float | None = None
    for loc in locations:
        for m in ARXIV_ID_RE.finditer(text_cache.get(loc, "")):
            if m.group(1) != arxiv_id:
                continue
            window = m.string[max(0, m.start() - _CONTEXT_RADIUS):
                               m.end() + _CONTEXT_RADIUS]
            r = _identity_ratio(title, window)
            if r is not None and (best is None or r > best):
                best = r
    if best is None:
        result["status"] = "SKIPPED"
        result["detail"] = "titre non mesurable (aucun token salient)"
        return result
    if best < _IDENTITY_THRESHOLD:
        result["status"] = "MISMATCH"
        result["detail"] = (
            f"titre résolu « {title} » ne concorde pas avec le contexte de "
            f"citation (concordance {best:.0%} < seuil {_IDENTITY_THRESHOLD:.0%})"
        )
    else:
        result["detail"] = f"identité OK (concordance {best:.0%}) — titre : {title}"
    return result


def run_detect(repo_root: Path, registry: list[dict],
               scope_patterns: list[str] | None,
               fixture: str | None, as_json: bool) -> int:
    """Mode détection (#22566). Rouge si un identifiant hors registre est
    résolu mais non concordant, ou inexistant."""
    # `str()` : un `arxiv_id` non quoté dans le YAML serait lu comme float et
    # détruirait l'exclusion des IDs enregistrés.
    registered = {str(a["arxiv_id"]) for a in registry}
    found = _enumerate_arxiv_ids(repo_root, scope_patterns)
    unreg = {i: l for i, l in found.items() if i not in registered}
    resolutions = {r["id"]: r for r in _resolve_ids(sorted(unreg), fixture)}
    text_cache: dict[str, str] = {}
    results: list[dict] = []
    for iid in sorted(unreg):
        for loc in unreg[iid]:
            text_cache.setdefault(loc, _file_text(repo_root / loc))
        results.append(_check_detect_id(
            iid, unreg[iid], text_cache,
            resolutions.get(iid, {"id": iid, "verdict": "notfound"})))
    counts = {"OK": 0, "MISMATCH": 0, "SKIPPED": 0}
    for r in results:
        counts[r["status"]] = counts.get(r["status"], 0) + 1

    if as_json:
        print(json.dumps({
            "mode": "detect",
            "registered": len(registered),
            "enumerated": len(found),
            "unregistered": len(unreg),
            "summary": counts,
            "results": results,
        }, indent=2, ensure_ascii=False))
    else:
        print(f"# Détection arXiv — {len(found)} identifiant(s) énuméré(s), "
              f"{len(unreg)} hors registre")
        for r in results:
            tag = {"OK": "✓", "MISMATCH": "✗", "SKIPPED": "~"}.get(r["status"], "?")
            print(f"{tag} [{r['status']}] {r['arxiv_id']} @ "
                  f"{', '.join(r['locations'])}")
            if r["detail"]:
                print(f"    {r['detail']}")
        print(f"# Summary: {counts['OK']} OK, {counts['MISMATCH']} MISMATCH, "
              f"{counts['SKIPPED']} SKIPPED")

    return 1 if counts["MISMATCH"] > 0 else 0


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
        "--detect",
        action="store_true",
        help="Mode détection (#22566) : énumérer les identifiants hors registre et "
             "contrôler leur identité via l'API arXiv. --paths = globs de fichiers.",
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

    if args.detect:
        fixture = os.environ.get("ARXIV_DETECT_RESOLUTIONS")
        return run_detect(repo_root, attributions, args.paths, fixture, args.json)

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
