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
- FIGURE PLEINE MAIS VIDE : un PNG full-size entierement blanc / transparent
  (un plot qui a trace des axes vides). Couvert en phase **advisory** depuis
  #10319 par la metrique per-tile (`partial_empty_tiles`) : grille dont une
  majorite de tuiles sont quasi-uniformes (pstdev canal < UNIFORM_TILE_STD)
  alors que d'autres sont riches. Phase 1 = label (ne fait PAS echouer
  `--check`); `--strict` pour escalader, mesure du taux de FP d'abord.
- IMAGE LEGITIMEMENT PETITE : une icone / un sprite / un QR code volontairement
  petit. Rare en notebook pedagogique (les sorties image sont des figures). Si
  rencontre, l'exclure au cas par cas -- l'outil est read-only. Les images
  trop petites pour etre tile-analysees (coté < _MIN_SIDE_FOR_TILING) sont
  ignorees par la metrique per-tile (pas de regression de la porte #8634).

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

# --- Per-region (tile) uniformity gate (#10319) ---
# Le detecteur global (dimensions + bytes + distinct colors) rate le cas
# "grille partiellement vide" : une grande image globalement riche peut
# cacher des regions vides au milieu de regions pleines. Le cas fondateur
# est la cellule 12 de 02-7-CogVideoX-Text-to-Video.ipynb (PR #10305) :
# une grille 4x4 1440x960 / 955 KB / 134k couleurs globales OU les rangées
# 1-2 sont des cadres vides (std canal ~4-12) et les rangées 3-4 des
# pommes rendues (std ~57-71). Aucune metrique globale ne le voit, le
# signal est INTRA-image (contraste vide/plein).
#
# On ajoute une metrique per-tile : nombre de tuiles OU la dispersion par
# canal (pstdev) est quasi nulle. Le seuil UNIFORM_TILE_STD=15.0 est
# calibre sur le cas fondateur (vides std=4-12, pleines std=57+) avec
# marge suffisante pour absorber les palettes matplotlib academic sur
# blanc (L781-L2) qui presentent un std modere par tuile.
#
# Phase 1 (acceptance #10319 critere 4) : ADVISORY (label) -- les
# findings "partial_empty_tiles" sont rapportes mais ne font PAS
# echouer `--check`. Le blocage strict est cable via `--strict` (off
# par defaut) pour permettre la mesure du taux de faux positifs avant
# de basculer en regle dure dans un second grain.
UNIFORM_TILE_STD = 15.0          # pstdev canal < ce seuil => tuile quasi vide
PARTIAL_EMPTY_FRACTION = 0.5     # >= cette fraction de tuiles low-variance => signal
_MIN_TILES_FOR_ANALYSIS = 4      # ne pas tile-analyser les images trop petites
_MIN_SIDE_FOR_TILING = 16        # chaque cote doit faire >= ce nb de px apres division

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


def _tile_uniformity_finding(
    raw: bytes,
    tiles: tuple[int, int] | None = None,
) -> dict | None:
    """Detect a 'partial-empty grid' (grille partiellement vide) signature (#10319).

    Renvoie un finding si au moins `PARTIAL_EMPTY_FRACTION` des tuiles sont
    quasi-uniformes (pstdev canal < `UNIFORM_TILE_STD`) ET qu'au moins une
    tuile est riche : c'est le CONTRASTE intra-image qui porte le signal
    (pas le niveau absolu -- une image entierement vide est traitee
    separement par `_has_real_content` et sort en `tiny_payload`/`partial`
    via d'autres voies).

    Si `tiles` est fourni (rows, cols), la grille est figee ; sinon on prend
    `g = clamp(min(w,h)//128, 2, 8)` -> g x g (4x4 sur l'image reelle 1440x960
    du cas fondateur #10305). Renvoie `None` si PIL indisponible, image
    indecodable, trop petite pour tuiler (gardes `_MIN_TILES_FOR_ANALYSIS`
    et `_MIN_SIDE_FOR_TILING`) -- pas de regression de couverture pour les
    images legitimes mais petites (pixel-art #8634, QR codes).
    """
    try:
        import io
        import statistics

        from PIL import Image

        im = Image.open(io.BytesIO(raw)).convert("RGB")
    except Exception:
        return None

    w, h = im.size
    if w == 0 or h == 0:
        return None

    if tiles is not None:
        rows, cols = tiles
    else:
        # Adaptive grid (#10319) : on maille pour qu'un cote de tuile fasse
        # ~64 px, soit ~4 sous-graphes sur la dimension la plus courte d'une
        # figure pedagogique typique. Le clamp [2, 8] borne le cout (8x8=64
        # tuiles, chacune scannee integralement) et donne au minimum 2x2=4
        # tuiles sur les figures modulaires compactes (un 2x2 subplots).
        # Verifie firsthand sur l'image reelle #10305 (1440x960) : g=8 ->
        # 50% tuiles low-variance (les rangées vides), finding emis.
        g = max(2, min(8, min(w, h) // 64))
        rows, cols = g, g

    total = rows * cols
    if total < _MIN_TILES_FOR_ANALYSIS:
        return None
    tile_w = w // cols
    tile_h = h // rows
    if tile_w < _MIN_SIDE_FOR_TILING or tile_h < _MIN_SIDE_FOR_TILING:
        return None

    low = 0
    for r in range(rows):
        for c in range(cols):
            box = (c * tile_w, r * tile_h, (c + 1) * tile_w, (r + 1) * tile_h)
            tile = im.crop(box)
            pixels = _flattened_pixels(tile)
            rs = [p[0] for p in pixels]
            gs = [p[1] for p in pixels]
            bs = [p[2] for p in pixels]
            mean_std = (
                statistics.pstdev(rs) + statistics.pstdev(gs) + statistics.pstdev(bs)
            ) / 3.0
            if mean_std < UNIFORM_TILE_STD:
                low += 1

    rich = total - low
    if rich < 1:
        # Toutes les tuiles quasi-vides : c'est un autre cas (image entierement
        # plate, pas un grille partiellement vide). Le gate global l'a deja
        # remonte via _has_real_content / taille si applicable. On ne double
        # pas le diagnostic ici.
        return None
    if low / total < PARTIAL_EMPTY_FRACTION:
        return None

    return {
        "reason": (
            f"partial_empty_tiles({low}/{total} low-variance @{rows}x{cols}, "
            f"std<{UNIFORM_TILE_STD})"
        ),
        "tiles": [rows, cols],
        "low_variance_tiles": low,
        "rich_tiles": rich,
    }


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


def _classify_image(
    mime: str,
    raw: bytes,
    min_dim: int,
    min_bytes: int,
    tiles: tuple[int, int] | None = None,
) -> dict | None:
    """Return a finding dict if the image is degenerate, else None.

    Blocking findings (degenerate_dimensions, tiny_payload) are the canonical
    gate -- they FAIL `--check`. The per-region tile uniformity metric (#10319)
    is ADVISORY: only emitted when the image PASSES the global checks (the
    documented blind spot), and tagged with `advisory=True` so the CLI can
    choose whether to escalate to a hard failure (--strict).
    """
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

    if reasons:
        return {
            "mime": mime,
            "bytes": size,
            "dimensions": list(dims) if dims else None,
            "reasons": reasons,
            "advisory": False,
        }

    # Phase advisory per-region (#10319) : on ne tile-analyse QUE les images
    # qui passent les 3 metriques globales -- c'est precisement le trou
    # documente (grille partiellement vide). Les images deja flaggees par
    # les metriques globales n'ont pas besoin du deuxieme avis.
    tile = _tile_uniformity_finding(raw, tiles=tiles)
    if tile:
        return {
            "mime": mime,
            "bytes": size,
            "dimensions": list(dims) if dims else None,
            "reasons": [tile["reason"]],
            "advisory": True,
            "tile_detail": {k: tile[k] for k in ("tiles", "low_variance_tiles", "rich_tiles")},
        }

    return None


def detect_cell(
    cell: dict,
    min_dim: int = MIN_DIM,
    min_bytes: int = MIN_BYTES,
    tiles: tuple[int, int] | None = None,
) -> list[dict]:
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
            finding = _classify_image(mime, raw, min_dim, min_bytes, tiles=tiles)
            if finding:
                findings.append({"output_index": oi, **finding})
    return findings


def scan_notebook(
    path: Path,
    min_dim: int = MIN_DIM,
    min_bytes: int = MIN_BYTES,
    tiles: tuple[int, int] | None = None,
) -> dict:
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
        for finding in detect_cell(cell, min_dim, min_bytes, tiles=tiles):
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
    total_advisory = sum(1 for r in results for h in r["hits"] if h.get("advisory"))
    total_blocking = total_hits - total_advisory
    affected = [r for r in results if r["hits"]]
    errored = [r for r in results if r.get("error")]
    lines = [
        f"Notebooks scanned  : {len(results)}",
        f"Degenerate figures : {total_hits} (blocking {total_blocking}, advisory {total_advisory})",
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
            tag = "ADVISORY" if h.get("advisory") else "BLOCKING"
            lines.append(f"  - [{tag}] cell [{h['cell_index']}] output[{h['output_index']}] {h['mime']}: {reasons}")
        lines.append("")
    lines.append(
        "FIX: re-execute the cell in the real environment (QC Cloud research for "
        "QuantBook, local kernel for matplotlib) and commit the real figure -- "
        "Stop&Repair, never scrub/delete to hide (secrets-hygiene rule 6). "
        "ADVISORY findings (#10319) do not fail `--check`; pass `--strict` "
        "to escalate them, but measure FP rate first."
    )
    return "\n".join(lines)


def _parse_tiles_arg(value: str) -> tuple[int, int]:
    """Parse '4x4' / '4X4' / '4×4' into (rows, cols)."""
    sep_chars = ("x", "X", "×", ",")
    for sep in sep_chars:
        if sep in value:
            r, c = value.split(sep, 1)
            return (int(r.strip()), int(c.strip()))
    raise argparse.ArgumentTypeError(f"--tiles expects RxC (e.g. '4x4'), got {value!r}")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook to scan (default: all pedagogical)")
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. QuantConnect)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any blocking degenerate figure (CI-ready)")
    parser.add_argument("--strict", action="store_true", help="Also fail --check on ADVISORY partial-empty-tiles findings (#10319)")
    parser.add_argument("--min-dim", type=int, default=MIN_DIM, help=f"Min figure side px (default {MIN_DIM})")
    parser.add_argument("--min-bytes", type=int, default=MIN_BYTES, help=f"Min decoded bytes (default {MIN_BYTES})")
    parser.add_argument(
        "--tiles",
        type=_parse_tiles_arg,
        default=None,
        help="Force tile grid RxC for the per-region uniformity check (default: adaptive g=clamp(min/128,2,8))",
    )
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

    results = [scan_notebook(p, args.min_dim, args.min_bytes, tiles=args.tiles) for p in paths]
    blocking_hits = sum(1 for r in results for h in r["hits"] if not h.get("advisory"))
    advisory_hits = sum(1 for r in results for h in r["hits"] if h.get("advisory"))
    total_hits = blocking_hits + advisory_hits

    if args.json:
        payload = {
            "notebooks_scanned": len(results),
            "total_hits": total_hits,
            "blocking_hits": blocking_hits,
            "advisory_hits": advisory_hits,
            "results": results,
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_human_report(results))

    if args.check:
        if blocking_hits > 0:
            return 1
        if args.strict and advisory_hits > 0:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
