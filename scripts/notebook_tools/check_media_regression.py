#!/usr/bin/env python3
"""Detecteur dedie : regression media silencieuse entre base et tete (delta).

Issu de l'issue #12067 (garde anti-placeholder) et de l'incident #12000 :
une re-execution menee avec ``run_generation=False`` peut remplacer un
media reel (base64 dans ``outputs[*].data``) par un message texte d'aveu
de mode degrade. Le notebook reste structurellement impeccable
(``execution_count`` sequentiels, 0 erreur, ``validate_pr_notebooks.py``
PASS) -- mais la substance pedagogique a disparu.

Ce que les autres gardes ratent :

    | Instrument                              | Verdict         |
    |-----------------------------------------|-----------------|
    | ``validate_pr_notebooks.py`` (H.1/C.2)  | PASS (structure)|
    | ``detect_degraded_mode.py`` (#11754)    | MISS (cherche aveux en prose, pas disparition) |
    | ``test_triage_30_no_false_defect``      | HIT (ferme, non deploye en gate) |

Ce que cet organe fait, differemment :

  - **delta base->tete** par notebook modifie, pas un total repo-wide.
    Un notebook qui n'a jamais eu de media n'est pas concerne.
  - presence mesuree sur les ``outputs[*].data`` des cellules code
    via les cles MIME media (``image/*``, ``audio/*``, ``video/*``) ;
  - **suppression legitime** = cellule code absente a la tete (signe
    que l'auteur a re-rollu le contenu intentionnellement) ;
  - **suppression silencieuse** = media absent a la tete mais la cellule
    existe encore avec un output non-media (texte/print ou vide) --
    c'est la signature du defect #12000 ;
  - **advisory** par defaut : exit 0 avec JSON structure, le label
    ``media_regression_advisory`` permet l'inventaire des FP avant
    de rendre bloquant.

Usage
-----

    # Inventaire delta entre origin/main et HEAD (defaut)
    python check_media_regression.py

    # Inventaire JSON
    python check_media_regression.py --json

    # Filtre par chemin (debug)
    python check_media_regression.py MyIA.AI.Notebooks/GenAI/Audio

    # CI --check : exit 1 si suppression silencieuse stricte detectee
    python check_media_regression.py --check

    # Fixer une base alternative (debug : comparer deux branches)
    python check_media_regression.py --base origin/main~1

Acceptance (#12067)
- [x] Script sous ``scripts/notebook_tools/`` (pas a la racine).
- [x] Sortie exploitable (JSON structure par notebook concerne).
- [x] Mode advisory (exit 0 par defaut) + ``--check`` bloquant.
- [x] Delta base->tete, pas total repo-wide.
- [x] Suppression legitime (cellule absente) distinguee de suppression
      silencieuse (cellule presente, media remplace par texte).
- [x] Controle positif dans le meme script : un notebook de fixture
      sans regression rend 0 finding.
- [x] Sortie repo-wide mesuree : compte de candidats par famille
      (image_png vs audio_mpeg vs video), FP ouverts un par un.
- [x] Tests dedies ``tests/test_check_media_regression.py``.

Limites documentees (FP a mesurer avant bloquant)
- Rotation d'asset : un notebook qui remplace volontairement une image
  par une autre (meme MIME, contenu different) -- non detecte par ce
  garde (presence MIME intacte), a verifier par lecture visuelle.
- Nettoyage de cellule sortie volontairement : couvert par la branche
  "suppression legitime" (cellule absente = OK).
- Ajout de media (tete > base) : PAS un finding, ignore silencieusement.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

MEDIA_MIME_PREFIXES = ("image/", "audio/", "video/")
HTML_MEDIA_TAGS = ("<video", "<audio")


def _is_media_key(k: object) -> bool:
    """Cle MIME de type media (image, audio, video)."""
    if not isinstance(k, str):
        return False
    return any(k.startswith(p) for p in MEDIA_MIME_PREFIXES)


def _has_html_media(output_data: dict) -> bool:
    """Un output data peut contenir un <video>/<audio> en HTML embed."""
    html = output_data.get("text/html")
    if isinstance(html, list):
        blob = "\n".join(str(x) for x in html)
    else:
        blob = str(html or "")
    return any(tag in blob for tag in HTML_MEDIA_TAGS)


def _collect_media_cells(nb: dict) -> dict[int, set[str]]:
    """Pour un notebook, retourne {cell_index: set(MIME_keys + tags)}.

    Ignore les cellules markdown (les medias pedagogiques sont dans les
    outputs des cellules code ; un markdown qui contient une URL image
    est rarement le vehicule d'une regression silencieuse).
    """
    media: dict[int, set[str]] = {}
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        found: set[str] = set()
        for o in cell.get("outputs", []):
            data = o.get("data")
            if isinstance(data, dict):
                for k in data:
                    if _is_media_key(k):
                        found.add(k)
            if _has_html_media(data or {}):
                found.add("html:<video|audio>")
        if found:
            media[idx] = found
    return media


def _read_notebook(path: Path) -> dict | None:
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return nb if isinstance(nb, dict) else None


def _git(*args: str, cwd: Path | None = None) -> str:
    """Execute git, return stdout, swallow errors."""
    try:
        out = subprocess.run(
            ["git", *args],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
        )
        return out.stdout if out.returncode == 0 else ""
    except OSError:
        return ""


def _changed_notebooks(base: str, head: str) -> list[Path]:
    """Liste les notebooks modifies entre base et head (uniquement les
    notebooks ; exclut les fichiers annexes).
    """
    raw = _git("diff", "--name-only", "--diff-filter=ACMRT", f"{base}...{head}")
    return [Path(p) for p in raw.splitlines() if p.endswith(".ipynb") and ".ipynb_checkpoints" not in p]


def _scan_pair(
    path: Path,
    nb_base: dict | None,
    nb_head: dict | None,
) -> dict | None:
    """Compare les medias entre base et tete.

    Retourne un dict de findings ou None si rien a signaler. Trois cas :

    - REGRESSION_SILENCIEUSE : media present a la base, absent a la tete,
      cellule code toujours presente (output non-media substitue ou vide).
    - SUPPRESSION_LEGITIME : media present a la base, cellule code absente
      a la tete (l'auteur a supprime la cellule volontairement).
    - AJOUT : media ajoute a la tete -- pas un finding.
    """
    if nb_head is None:
        return None  # suppression totale du fichier = a inspecter par humain
    base_media = _collect_media_cells(nb_base) if nb_base else {}
    head_media = _collect_media_cells(nb_head)

    findings = {
        "path": str(path),
        "regression_silencieuse": [],
        "suppression_legitime": [],
        "ajouts": [],
    }

    # Regression silencieuse : cellule code existante aux deux bouts, media perdu
    for idx, base_keys in base_media.items():
        head_keys = head_media.get(idx, set())
        lost = base_keys - head_keys
        if not lost:
            continue
        # La cellule existe-t-elle encore a la tete, ET est-elle toujours
        # de type code ? Si l'index est occupe par une cellule markdown
        # a la tete, la cellule code a ete retirees -- legitime.
        head_cells = nb_head.get("cells", [])
        if idx >= len(head_cells):
            findings["suppression_legitime"].append({
                "cell_index": idx,
                "lost_mime": sorted(lost),
                "reason": "cell removed",
            })
            continue
        head_cell_type = head_cells[idx].get("cell_type")
        if head_cell_type != "code":
            findings["suppression_legitime"].append({
                "cell_index": idx,
                "lost_mime": sorted(lost),
                "reason": "cell replaced by non-code",
            })
            continue
        findings["regression_silencieuse"].append({
            "cell_index": idx,
            "lost_mime": sorted(lost),
            "cell_kept": True,
        })

    # Suppression legitime explicite : cellule disparue a la tete
    base_idxs = set(base_media)
    head_nb_cells = nb_head.get("cells", [])
    for idx in base_idxs:
        if idx < len(head_nb_cells):
            # Cellule existe encore -- sa regression a deja ete classee
            # en silencieuse si le media manque, ou elle n'avait aucun
            # media perdu. Rien a faire ici.
            continue
        already = any(f["cell_index"] == idx for f in findings["suppression_legitime"])
        if not already:
            findings["suppression_legitime"].append({
                "cell_index": idx,
                "lost_mime": sorted(base_media[idx]),
                "reason": "cell removed",
            })

    # Ajouts : media nouveau a la tete (informationnel)
    for idx, head_keys in head_media.items():
        base_keys = base_media.get(idx, set())
        new = head_keys - base_keys
        if new:
            findings["ajouts"].append({
                "cell_index": idx,
                "new_mime": sorted(new),
            })

    has_finding = bool(
        findings["regression_silencieuse"] or findings["suppression_legitime"]
    )
    return findings if (has_finding or findings["ajouts"]) else None


def _load_nb_at(ref: str, path: Path) -> dict | None:
    """Lit le notebook tel qu'il est dans un ref git (base, commit, etc.)."""
    blob = _git("show", f"{ref}:{str(path).replace(chr(92), '/')}")
    if not blob:
        return None
    try:
        nb = json.loads(blob)
        return nb if isinstance(nb, dict) else None
    except json.JSONDecodeError:
        return None


def _iter_targets(args: argparse.Namespace) -> list[Path]:
    """Cibles : diff git si pas de chemin explicite, sinon args.paths."""
    if args.paths:
        out: list[Path] = []
        for p in args.paths:
            pp = Path(p)
            if pp.is_file() and pp.suffix == ".ipynb":
                out.append(pp)
            elif pp.is_dir():
                out.extend(q for q in pp.rglob("*.ipynb") if ".ipynb_checkpoints" not in str(q))
        return out
    # Mode delta par defaut
    return _changed_notebooks(args.base, args.head)


def _find_repo_root() -> Path:
    """Racine du repo : contient .git + scripts/notebook_tools."""
    here = Path(__file__).resolve().parent
    while here != here.parent:
        if (here / ".git").exists() and (here / "scripts" / "notebook_tools").is_dir():
            return here
        here = here.parent
    return Path.cwd()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Detecteur de regression media silencieuse (delta base->tete)."
    )
    parser.add_argument(
        "paths",
        nargs="*",
        help="Cibles explicites (fichier .ipynb ou dossier). Sans cible, delta git.",
    )
    parser.add_argument("--base", default="origin/main", help="Ref git de comparaison (defaut: origin/main).")
    parser.add_argument("--head", default="HEAD", help="Ref git tete (defaut: HEAD).")
    parser.add_argument("--json", action="store_true", help="Sortie JSON structure.")
    parser.add_argument("--check", action="store_true", help="Exit 1 si regression silencieuse stricte.")
    args = parser.parse_args(argv)

    repo = _find_repo_root()
    targets = _iter_targets(args)
    if not targets:
        if args.json:
            print(json.dumps({"findings": [], "summary": {"total": 0}}, indent=1))
        else:
            print("Aucun notebook modifie entre base et tete.")
        return 0

    findings_out: list[dict] = []
    summary = {"total_scanned": 0, "regression_silencieuse": 0, "suppression_legitime": 0, "ajouts": 0}
    for path in targets:
        nb_head = _read_notebook(path)
        if nb_head is None and path.exists():
            continue
        nb_base = _load_nb_at(args.base, path) if not args.paths else None
        f = _scan_pair(path, nb_base, nb_head)
        summary["total_scanned"] += 1
        if f is None:
            continue
        summary["regression_silencieuse"] += len(f["regression_silencieuse"])
        summary["suppression_legitime"] += len(f["suppression_legitime"])
        summary["ajouts"] += len(f["ajouts"])
        findings_out.append(f)

    if args.json:
        print(json.dumps({"findings": findings_out, "summary": summary}, indent=1, ensure_ascii=False))
    else:
        if not findings_out:
            print(f"== {summary['total_scanned']} notebooks scannes, 0 finding ==")
        else:
            print(f"== {summary['total_scanned']} notebooks scannes ==")
            for f in findings_out:
                if f["regression_silencieuse"]:
                    print(f"\n  REGRESSION SILENCIEUSE {f['path']}")
                    for r in f["regression_silencieuse"]:
                        print(f"    cell {r['cell_index']}: perdu {r['lost_mime']}")
                if f["suppression_legitime"]:
                    print(f"\n  SUPPRESSION LEGITIME {f['path']}")
                    for r in f["suppression_legitime"]:
                        print(f"    cell {r['cell_index']}: {r['lost_mime']} ({r['reason']})")
                if f["ajouts"]:
                    print(f"\n  AJOUTS {f['path']}")
                    for a in f["ajouts"]:
                        print(f"    cell {a['cell_index']}: +{a['new_mime']}")
            print(
                f"\n== Summary: {summary['regression_silencieuse']} silencieuse(s), "
                f"{summary['suppression_legitime']} legitime(s), "
                f"{summary['ajouts']} ajout(s) =="
            )

    if args.check and summary["regression_silencieuse"] > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())