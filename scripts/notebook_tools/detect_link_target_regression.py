#!/usr/bin/env python3
"""Detecte les regressions d'accents dans les TARGETS de liens markdown (registre #2876).

Pourquoi cet outil existe
-------------------------
Le registre #2876 (restauration des accents francais dans les cellules markdown)
doit preserver l'integrite des cibles de liens markdown `[texte](cible)`.

Or l'outil ad-hoc applique une regex globale `\b(mot)\b` sur le source markdown,
qui touche les cibles `[texte](cible)` exactement comme le texte du lien. Si le
nom de fichier Notebook contient un accent (ou en gagnait un par coherence
linguistique), la cure casse silencieusement la cible :

    AVANT : | [Infer-10-Model-Selection](Infer-10-Model-Selection.ipynb) |
    APRES : | [Infer-10-Model-sélection](Infer-10-Model-sélection.ipynb) |  <-- cassé

Sur disque le fichier s'appelle `Infer-10-Model-Selection.ipynb` (sans accent),
donc le lien resolu `Infer-10-Model-sélection.ipynb` n'existe pas.

Pourquoi ce defaut passe les gardes existants
---------------------------------------------
- `detect_accent_stripping.py` ne regarde que les mots du source markdown sans
  distinguer texte-cliquable / cible-de-lien.
- `check_identifier_regression.py` (PR #7157) couvre les identifiants de CODE,
  pas les cibles markdown.
- `detect_caps_regression.py` (PR #7198 po-2026) couvre les pertes de
  majuscules en debut de cellule / ligne / tableau, pas les cibles.
- `check_notebook_navlinks.py` signale les cibles INEXISTANTES au moment de
  l'audit, mais ne peut pas distinguer une regression accent (cible accentuee
  dans la PR alors que la base est desaccentuee + le fichier canonique n'a pas
  d'accent) d'une simple typo ou d'un fichier manquant.

Cet outil ferme le 3e axe de la triade (identifiants #7157 + caps #7198 +
**link-targets** ICI) en comparant les cibles de liens markdown d'une PR a
l'etat attendu (resolution sur disque + comparaison a la base git).

Comment ca marche
-----------------
Pour chaque PR (diff vs base git, defaut origin/main) :
  1. extraire toutes les cibles de liens markdown en BASE et en HEAD ;
  2. matcher par position (cell_idx, line_no) avec fallback strip-accents ;
  3. pour chaque match, comparer target_base vs target_head :
       - si strip_accents(head_target) == strip_accents(base_target) ET
         head_target != base_target => **ACCENT_REGRESSION** ;
  4. verifier sur disque :
       - si le head_target n'existe pas ET que la version strippee existe =>
         **BROKEN_LINK_ACCENT_REGRESSION** (le pire cas) ;
       - sinon => **ACCENT_REGRESSION** (le fichier a ete renomme en coherence
         avec les accents, mais c'est un changement editorial etonnament rare).

Usage
-----
    # un notebook, diff vs origin/main
    python detect_link_target_regression.py NB.ipynb
    python detect_link_target_regression.py NB.ipynb --base origin/main --head origin/fix/ma-branche
    # exit 1 si regression detectee (CI-ready)
    python detect_link_target_regression.py NB.ipynb --check
    # sortie machine
    python detect_link_target_regression.py NB.ipynb --json

Exit codes
----------
    0 -- aucune regression de cible de lien detectee (ou mode non --check)
    1 -- une ou plusieurs cibles de lien accentuees en regression (--check)
    2 -- erreur (notebook illisible, ref git introuvable)

Voir aussi
----------
- check_identifier_regression.py (PR #7157) -- axe 1 : identifiants de code
- detect_caps_regression.py (PR #7198 po-2026) -- axe 2 : majuscules en debut
- detect_accent_stripping.py -- moitie DETECTION du registre #2876
- check_notebook_navlinks.py -- broken links au moment de l'audit
- Memoire : c.635 G.1 self-correction (3 PRs defectueuses de la partition OWN)
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import unicodedata
from pathlib import Path
from urllib.parse import unquote

LINK_PATTERN = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def strip_accents(s: str) -> str:
    """NFD + strip combining marks (canon). ASCII-fold francais (oe/ae)."""
    decomposed = unicodedata.normalize("NFD", s)
    stripped = "".join(ch for ch in decomposed if unicodedata.category(ch) != "Mn")
    return stripped.replace("œ", "oe").replace("æ", "ae")


def extract_md_cells(nb: dict) -> list[tuple[int, list[str]]]:
    """Retourne [(cell_idx, source_lines)] pour les cellules markdown seulement."""
    cells = []
    for idx, c in enumerate(nb.get("cells", [])):
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source", [])
        if isinstance(src, str):
            src = src.splitlines()
        cells.append((idx, src))
    return cells


def collect_link_targets(md_cells: list[tuple[int, list[str]]]) -> list[dict]:
    """Collecte toutes les cibles de liens (link target) avec metadata.

    Retourne liste de dicts {cell_idx, line_no, text, target}.
    """
    out = []
    for cell_idx, src in md_cells:
        for line_no, line in enumerate(src, start=1):
            for m in LINK_PATTERN.finditer(line):
                text = m.group(1)
                target = m.group(2)
                # Filtre meme logique que check_notebook_navlinks._is_checkable_target
                if not target:
                    continue
                if target.startswith(("{", "<", "http:", "https:", "mailto:", "#", "/")):
                    continue
                if target.endswith("/"):
                    continue
                if "%" in target:
                    continue
                base = target.split("#")[0]
                if "/" not in base and "." not in Path(base).name:
                    continue
                out.append({
                    "cell_idx": cell_idx,
                    "line_no": line_no,
                    "text": text,
                    "target": target,
                })
    return out


def resolve_target(nb_path: Path, target: str) -> Path:
    """Resoud target relativement au dossier parent du notebook."""
    if "#" in target:
        target = target.split("#", 1)[0]
    target = unquote(target)
    if not target:
        return nb_path
    return (nb_path.parent / target).resolve()


def diff_targets(base_targets: list[dict], head_targets: list[dict]) -> list[dict]:
    """Matche les cibles par position et isole les regressions d'accents.

    Strategie : on apparie chaque lien a la meme position (cell_idx, line_no),
    PUIS on compare target_base vs target_head pour chaque match positionnel.
    Pour detecter une regression d'accents, on compare les deux chaines apres
    strip_accents ET case-fold : si elles sont identiques mais les formes
    avec accents different, c'est une ACCENT_REGRESSION.

    NB : on apparie sur la position seule (pas le texte du lien ni le target)
    car la cure #2876 peut deplacer des accents dans le texte du lien en
    meme temps que dans le target. Le matching positionnel est robuste tant
    que la PR ne reordonne pas les cellules/lignes.

    Retourne liste de diagnostics :
      - kind=ACCENT_REGRESSION : cible modifiee uniquement par accents.
    """
    # Index base par (cell_idx, line_no)
    base_by_pos: dict[tuple, list[dict]] = {}
    for d in base_targets:
        key = (d["cell_idx"], d["line_no"])
        base_by_pos.setdefault(key, []).append(d)

    regressions = []
    seen: set[tuple] = set()
    for head in head_targets:
        key = (head["cell_idx"], head["line_no"])
        base_matches = base_by_pos.get(key, [])
        for base in base_matches:
            if base["target"] == head["target"]:
                continue  # pas de changement
            # Comparaison case-insensitive + strip_accents
            head_norm = strip_accents(head["target"]).lower()
            base_norm = strip_accents(base["target"]).lower()
            if head_norm != base_norm:
                continue  # changement de fond, pas un pur accent
            # Les deux cibles sont identiques up-to-accents-and-case
            diag_key = (head["cell_idx"], head["line_no"], head["text"], base["target"], head["target"])
            if diag_key in seen:
                continue
            seen.add(diag_key)
            regressions.append({
                "kind": "ACCENT_REGRESSION",
                "text": head["text"],
                "target_added": head["target"],
                "target_removed": base["target"],
                "head_cell_idx": head["cell_idx"],
                "head_line_no": head["line_no"],
                "base_cell_idx": base["cell_idx"],
                "base_line_no": base["line_no"],
            })
    return regressions


def read_notebook_at_ref(nb_path: Path, ref: str) -> dict | None:
    """Lit le contenu d'un notebook a un ref git donne via `git show ref:path`."""
    rel = nb_path.as_posix()
    try:
        out = subprocess.run(
            ["git", "show", f"{ref}:{rel}"],
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
    except (FileNotFoundError, OSError):
        return None
    if out.returncode != 0 or not out.stdout:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def scan_notebook(nb_path: Path, base_ref: str, head_ref: str | None = None) -> dict:
    """Compare les cibles de liens markdown d'un notebook entre base_ref et head_ref."""
    if head_ref is None:
        try:
            nb_head = json.loads(nb_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            return {"notebook": str(nb_path), "error": f"head unreadable: {e}"}
        head_label = "working_tree"
    else:
        nb_head = read_notebook_at_ref(nb_path, head_ref)
        if nb_head is None:
            return {"notebook": str(nb_path), "error": f"head_ref {head_ref} unreadable"}
        head_label = head_ref

    nb_base = read_notebook_at_ref(nb_path, base_ref)
    if nb_base is None:
        return {"notebook": str(nb_path), "error": f"base_ref {base_ref} unreadable"}

    base_md = collect_link_targets(extract_md_cells(nb_base))
    head_md = collect_link_targets(extract_md_cells(nb_head))

    regressions = diff_targets(base_md, head_md)

    final = []
    for reg in regressions:
        added_target = reg["target_added"]
        removed_target = reg["target_removed"]
        resolved_added = resolve_target(nb_path, added_target)
        resolved_removed = resolve_target(nb_path, removed_target)
        reg["resolved_path_added"] = str(resolved_added)
        reg["resolved_path_removed"] = str(resolved_removed)
        reg["resolved_exists_added"] = resolved_added.exists()
        reg["resolved_exists_removed"] = resolved_removed.exists()
        # Verdict : si la cible ajoutee n'existe pas mais la retiree existe,
        # c'est un BROKEN LINK accent-regression (le pire cas).
        if not resolved_added.exists() and resolved_removed.exists():
            reg["kind"] = "BROKEN_LINK_ACCENT_REGRESSION"
        final.append(reg)

    return {
        "notebook": str(nb_path),
        "base_ref": base_ref,
        "head_ref": head_label,
        "regressions": final,
        "stats": {
            "base_links": len(base_md),
            "head_links": len(head_md),
            "regressions_count": len(final),
        },
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("notebook", type=Path, help="Chemin vers le .ipynb")
    p.add_argument("--base", default="origin/main", help="Ref git de la base (defaut origin/main)")
    p.add_argument("--head", default=None, help="Ref git du head (defaut working tree)")
    p.add_argument("--check", action="store_true", help="Exit 1 si regression detectee (CI)")
    p.add_argument("--json", action="store_true", help="Sortie JSON machine")
    args = p.parse_args(argv)

    if not args.notebook.exists():
        print(f"ERROR: notebook introuvable: {args.notebook}", file=sys.stderr)
        return 2

    result = scan_notebook(args.notebook, args.base, args.head)

    if "error" in result:
        print(f"ERROR: {result['error']}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        nb = result["notebook"]
        stats = result["stats"]
        regs = result["regressions"]
        print(f"[NOTEBOOK] {nb}")
        print(f"[BASE]     {result['base_ref']}")
        print(f"[HEAD]     {result['head_ref']}")
        print(f"[STATS]    base_links={stats['base_links']} head_links={stats['head_links']} regressions={stats['regressions_count']}")
        if regs:
            print("\n[REGRESSIONS]")
            for r in regs:
                print(f"  - cell {r['head_cell_idx']}:{r['head_line_no']} [{r['text']}]({r['target_added']})")
                print(f"      base = ({r['target_removed']}) kind={r['kind']}")
                print(f"      resolved_added   = {r['resolved_path_added']} (exists={r['resolved_exists_added']})")
                print(f"      resolved_removed = {r['resolved_path_removed']} (exists={r['resolved_exists_removed']})")

    if args.check and result["regressions"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())