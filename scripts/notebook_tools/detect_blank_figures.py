#!/usr/bin/env python3
"""Detecte les figures degenerees committees comme si elles etaient de vrais graphiques (Prong-A, registre #3801).

Pourquoi cet outil existe
-------------------------
Le sweep Prong-A (#3801) traque les sorties FABRIQUEES : une cellule code qui
pretend produire une visualisation mais commit un placeholder. `detect_ascii_workaround.py`
couvre le cas ASCII (un chart dessine en caracteres). Cet outil couvre l'AUTRE
moitie : une cellule qui commit une image DEGENERECE en lieu et place d'un vrai
graphique -- typiquement le PNG 1x1 de 70 octets que matplotlib emet quand la
figure est vide, que le backend Agg n'a rien trace, ou que `QuantBook()` n'a
jamais tourne. Incident fondateur #6891 : 8 quantbook.ipynb QuantConnect committes
chacun avec un unique PNG 1x1 de 70 octets (+ des tableaux fabriques),
execution_count peuple partout = "fabrication consacree" (une sortie vide
maquillee en figure).

Un vrai graphique matplotlib pedagogique fait des centaines de pixels et des
dizaines de Ko (baseline mesuree sur `research.ipynb` QC : 690x590 a 1389x989,
41-236 Ko). Un PNG 1x1 de 70 octets n'est jamais une figure legitime. La
separation est nette et DETERMINISTE (dimensions IHDR + taille decodee), pas
heuristique -- donc, contrairement au detecteur ASCII, pas de risque de faux
positif sur les vrais plots.

Il DETECTE, il ne CORRIGE PAS. La correction = re-executer la cellule dans le
vrai environnement (QC Cloud research pour QuantBook, kernel local pour
matplotlib) et committer la vraie figure -- Stop&Repair, JAMAIS scrubber ni
supprimer pour cacher (regle secrets-hygiene 6 + sota-not-workaround Prong-A).
L'outil guide le sweep en listant les fabrications ; le verdict (RECOVERABLE-*)
et la re-exec restent un travail de substance par notebook.

Ce qui est flagge (DETERMINISTE)
--------------------------------
Une sortie `image/png` (ou `image/jpeg`) d'une cellule code est DEGENERECE si :
  - ses dimensions sont minuscules : width <= MIN_DIM ou height <= MIN_DIM
    (defaut 8 px -- un 1x1 est le cas canonique #6891) ; OU
  - sa taille decodee est infime : < MIN_BYTES (defaut 1024 o -- le PNG 1x1
    fait 70 o ; un vrai plot fait des dizaines de Ko).
Les deux signaux concordent sur le cas #6891 ; chacun est rapporte separement
pour que l'humain juge (une image JPEG dont on ne parse pas les dimensions n'est
retenue que sur la taille).

Known blind spots (hors scope par design)
-----------------------------------------
- FIGURE PLEINE MAIS VIDE : un PNG full-size (ex 690x590) entierement blanc /
  transparent (un plot qui a trace des axes vides). Detecter ca demande une
  analyse pixel (variance de couleur) -- plus lourd et bruite. Hors scope : cet
  outil cible la degenerescence de dimension/taille (le cas #6891 verifie), pas
  le contenu semantique de l'image.
- IMAGE LEGITIMEMENT PETITE : une icone / un sprite / un QR code volontairement
  petit. Rare en notebook pedagogique (les sorties image sont des figures). Si
  rencontre, l'exclure au cas par cas -- l'outil est read-only.

Usage
-----
    python detect_blank_figures.py NB.ipynb                 # un notebook
    python detect_blank_figures.py --family QuantConnect    # une famille
    python detect_blank_figures.py                          # tous les notebooks
    python detect_blank_figures.py NB.ipynb --json          # sortie machine
    python detect_blank_figures.py NB.ipynb --check         # exit 1 si figures degenerees (CI-ready)
    python detect_blank_figures.py NB.ipynb --min-dim 8 --min-bytes 1024   # seuils explicites

Exit codes
----------
    0 -- aucune figure degenerece (ou mode non --check)
    1 -- une ou plusieurs figures degenerees (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_ascii_workaround.py` (#3801) -- moitie ASCII du sweep Prong-A
- `.claude/rules/sota-not-workaround.md` -- Prong-A : vrai outil, pas workaround/fabrication
- `.claude/rules/secrets-hygiene.md` regle 6 -- Stop&Repair : re-executer, jamais scrubber
- #6891 -- incident fondateur (8 quantbook.ipynb QC blank-PNG)

Part of #3801 (EPIC SOTA axe-2).
"""
from __future__ import annotations

import argparse
import base64
import binascii
import json
import sys
from pathlib import Path

# Seuils de degenerescence. Calibres sur la baseline QC #6891 :
#   degenere  : 70 octets, 1x1  (le PNG vide de matplotlib)
#   legitime  : 41-236 Ko, 690x590 a 1389x989  (vrais plots research.ipynb)
# La separation est de plusieurs ordres de grandeur -> aucun chevauchement.
MIN_DIM = 8         # px : une figure < 8px de cote n'est pas une viz reelle
MIN_BYTES = 1024    # o  : un PNG decode < 1 Ko ne porte pas de vraie figure
# Porte de sortie par contenu (#8634) : un petit PNG peut etre legitime s'il est
# riche en couleurs (pixel-art, grille de broderie, sprite, heatmap miniature). La
# taille du payload mesure la resolution, pas le contenu -- ce sont deux axes
# independants. On ne declenche tiny_payload QUE si l'image porte aussi trop peu
# de couleurs distinctes (ou si elle est indecodable, auquel cas on retombe sur la
# taille pour ne pas regresser la couverture de #6891).
MIN_DISTINCT_COLORS = 4  # nb de couleurs RGB distinctes en dessous duquel une
                         # petite image est consideree sans contenu reel

_IMAGE_MIMES = ("image/png", "image/jpeg")
_PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"


def _cell_outputs(cell: dict) -> list[dict]:
    return cell.get("outputs", []) or []


def _decode_image(b64: object) -> bytes | None:
    """Decode a notebook image payload (str or list[str]) into raw bytes."""
    if isinstance(b64, list):
        b64 = "".join(b64)
    if not isinstance(b64, str):
        return None
    try:
        return base64.b64decode(b64, validate=False)
    except (binascii.Error, ValueError):
        return None


def _png_dimensions(raw: bytes) -> tuple[int, int] | None:
    """Return (width, height) from a PNG IHDR, or None if not a parseable PNG.

    PNG layout: 8-byte signature, then the IHDR chunk whose data begins at
    offset 16 with big-endian 4-byte width then 4-byte height.
    """
    if len(raw) < 24 or raw[:8] != _PNG_SIGNATURE:
        return None
    if raw[12:16] != b"IHDR":
        return None
    width = int.from_bytes(raw[16:20], "big")
    height = int.from_bytes(raw[20:24], "big")
    return (width, height)


def _flattened_pixels(im):
    """Return the flat pixel sequence of a PIL image, across Pillow versions.

    `Image.getdata()` is deprecated since Pillow 12 and REMOVED in Pillow 14
    (2027-10-15) in favour of `get_flattened_data()`. Both return the same
    sequence for an RGB image (verified). Calling the deprecated name is not a
    cosmetic warning here: see `_has_real_content` below for why it would
    silently disable the content gate.
    """
    getter = getattr(im, "get_flattened_data", None) or im.getdata
    return getter()


def _has_real_content(raw: bytes, min_colors: int = MIN_DISTINCT_COLORS) -> bool | None:
    """Return True if the image carries enough distinct colors to be a real figure.

    Returns False if it decodes but is monochrome / near-monochrome (canvas blanc,
    placeholder uni). Returns None if PIL is unavailable or the image cannot be
    decoded -- in which case the caller keeps the size-based behaviour (no
    coverage regression, #6891). PIL is a repo dependency (Image notebooks) but
    the detector must remain functional without it.

    The `None` fallback is deliberate but load-bearing, and that makes the Pillow
    API surface a correctness concern rather than a lint one: anything raising in
    here degrades to `None`, i.e. back to the size-only rule that #8634 was filed
    to fix. Under `python -W error::DeprecationWarning` -- how a CI run pins
    warnings -- a deprecated call raises, is swallowed, and the pixel-art of
    #8634 is flagged again with no error and no failing test. Hence
    `_flattened_pixels`: the supported API is called on the nominal path, so the
    gate cannot revert by warning.
    """
    try:
        from PIL import Image
        import io

        im = Image.open(io.BytesIO(raw)).convert("RGB")
        return len(set(_flattened_pixels(im))) >= min_colors
    except Exception:
        return None


def _classify_image(mime: str, raw: bytes, min_dim: int, min_bytes: int) -> dict | None:
    """Return a finding dict if the image is degenerate, else None."""
    reasons = []
    size = len(raw)
    dims = _png_dimensions(raw) if mime == "image/png" else None

    if dims is not None:
        w, h = dims
        if w <= min_dim or h <= min_dim:
            reasons.append(f"degenerate_dimensions({w}x{h})")

    if size < min_bytes:
        # Porte de sortie par contenu (#8634) : une petite image riche en couleurs
        # (pixel-art, grille de broderie 24x16 a 17 couleurs) n'est pas degeneree.
        # On ne flagge tiny_payload que si l'image n'a PAS assez de contenu, ou si
        # elle est indecodable (None -> fallback taille, pas de regression #6891).
        if _has_real_content(raw) is not True:
            reasons.append(f"tiny_payload({size}B)")

    if not reasons:
        return None
    return {
        "mime": mime,
        "bytes": size,
        "dimensions": list(dims) if dims else None,
        "reasons": reasons,
    }


def detect_cell(cell: dict, min_dim: int = MIN_DIM, min_bytes: int = MIN_BYTES) -> list[dict]:
    """Return findings (one per degenerate image output) for a code cell."""
    findings = []
    for oi, out in enumerate(_cell_outputs(cell)):
        data = out.get("data", {}) if isinstance(out, dict) else {}
        for mime in _IMAGE_MIMES:
            if mime not in data:
                continue
            raw = _decode_image(data[mime])
            if raw is None:
                continue
            finding = _classify_image(mime, raw, min_dim, min_bytes)
            if finding:
                findings.append({"output_index": oi, **finding})
    return findings


def scan_notebook(path: Path, min_dim: int = MIN_DIM, min_bytes: int = MIN_BYTES) -> dict:
    """Return a result dict for one notebook: path, hits[], error."""
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": []}

    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for finding in detect_cell(cell, min_dim, min_bytes):
            hits.append({"cell_index": ci, **finding})
    return {"path": str(path), "kernel": _kernel(nb), "hits": hits, "error": None}


def _kernel(nb: dict) -> str:
    return nb.get("metadata", {}).get("kernelspec", {}).get("name", "?")


# Marcheur + SKIP_DIRS canonique centralises dans notebook_walk (#8650) :
# source unique pour le perimetre des scanners (ferme la derive detectee).
# Artefacts papermill (*_output.ipynb) : la source canonique est le livrable, le
# _output re-genere peut porter une figure stale -- on scanne la source.
from notebook_walk import SKIP_DIRS, _OUTPUT_SUFFIX, iter_notebooks  # noqa: E402


def _should_skip(rel: Path) -> bool:
    if any(part in SKIP_DIRS for part in rel.parts):
        return True
    return rel.name.endswith(_OUTPUT_SUFFIX)


def _iter_notebooks(root: Path, family: str | None):
    # Delegue au marcheur partage : SKIP_DIRS canonique + filtre git tracked_only
    # (exclut deterministement les arbres gitignores - lean-workspace, _output).
    yield from iter_notebooks(root / "MyIA.AI.Notebooks", family=family)


def _human_report(results: list[dict]) -> str:
    total_hits = sum(len(r["hits"]) for r in results)
    affected = [r for r in results if r["hits"]]
    errored = [r for r in results if r.get("error")]
    lines = [
        f"Notebooks scanned  : {len(results)}",
        f"Degenerate figures : {total_hits}",
        f"Affected notebooks : {len(affected)}",
        "",
    ]
    if not affected:
        lines.append("No degenerate figures detected (deterministic dimension/size check).")
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        for h in r["hits"]:
            reasons = ", ".join(h["reasons"])
            lines.append(f"  - cell [{h['cell_index']}] output[{h['output_index']}] {h['mime']}: {reasons}")
        lines.append("")
    lines.append(
        "FIX: re-execute the cell in the real environment (QC Cloud research for "
        "QuantBook, local kernel for matplotlib) and commit the real figure -- "
        "Stop&Repair, never scrub/delete to hide (secrets-hygiene rule 6)."
    )
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook to scan (default: all pedagogical)")
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. QuantConnect)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any degenerate figure (CI-ready)")
    parser.add_argument("--min-dim", type=int, default=MIN_DIM, help=f"Min figure side px (default {MIN_DIM})")
    parser.add_argument("--min-bytes", type=int, default=MIN_BYTES, help=f"Min decoded bytes (default {MIN_BYTES})")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    if args.notebook:
        paths = [Path(args.notebook)]
        if not paths[0].is_absolute():
            paths[0] = root / paths[0]
        if not paths[0].exists():
            print(f"error: notebook not found: {paths[0]}", file=sys.stderr)
            return 2
    else:
        paths = list(_iter_notebooks(root, args.family))
        if args.family and not paths:
            print(f"error: family not found: {args.family}", file=sys.stderr)
            return 2

    results = [scan_notebook(p, args.min_dim, args.min_bytes) for p in paths]
    total_hits = sum(len(r["hits"]) for r in results)

    if args.json:
        payload = {"notebooks_scanned": len(results), "total_hits": total_hits, "results": results}
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_human_report(results))

    if args.check and total_hits > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
