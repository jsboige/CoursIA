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

# Metrique per-tile advisory (#10319) : une figure-grille dont une fraction des
# tuiles est quasi-uniforme (vide/blanc) tandis que d'autres sont riches (vrai
# contenu) est une "grille partiellement vide" que les trois metriques globales
# (dimensions, payload, couleurs de toute l'image) ne peuvent pas voir -- le
# contenu des tuiles pleines dilue le vide des autres dans l'agregat. Cas revele
# par 02-7 CogVideoX : grille 4x4 dont 2 rangees sur 4 etaient vides (pomme
# absente), 955 Ko, passee au vert par les metriques globales. Phase advisory
# (label) : signale sans bloquer --check ; le durcissement vient apres mesure
# du taux de faux positifs sur les assets existants.
MIN_DISTINCT_COLORS_PER_TILE = 16    # tuile "uniforme" si < 16 couleurs RGB distinctes
RICH_DISTINCT_COLORS_PER_TILE = 100  # tuile "riche" si >= 100 couleurs (vrai contenu)
PARTIAL_BLANK_UNIFORM_FRAC = 0.25    # >= 25 % de tuiles uniformes ...
PARTIAL_BLANK_RICH_FRAC = 0.25       # ... ET >= 25 % de tuiles riches = contraste intra-image
MIN_UNIFORM_RUN = 2                  # >= 2 rangees (ou colonnes) completes contigues de
                                      # tuiles uniformes : la signature d'un BLOC de panneaux
                                      # vides (rangees de subplots absents). Discrimine le
                                      # vrai defaut (panneaux contigus) des marges blanches
                                      # d'une figure simple (tuiles uniformes eparpillees aux
                                      # coins) -> 0 FP sur 981 notebooks (scan #10319).
DEFAULT_TILES = (4, 4)               # grille par defaut (lignes, colonnes)
_TILE_SAMPLE_PX = 64                 # sous-echantillonnage des tuiles pour le denombrement

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


def _tile_distinct_colors(im, rows: int, cols: int) -> list[int]:
    """Return the distinct-RGB-color count of each tile in a rows x cols grid.

    Tiles larger than _TILE_SAMPLE_PX on either side are downsampled before
    counting, bounding the work on big figures. Downsampling preserves the
    uniform/rich distinction (a blank tile stays ~1 color, a content tile stays
    many) while capping per-tile cost at _TILE_SAMPLE_PX**2 pixels.
    """
    from PIL import Image  # noqa: F401  (resize available on the crop instance)
    w, h = im.size
    tw, th = w // cols, h // rows
    counts = []
    for r in range(rows):
        for c in range(cols):
            tile = im.crop((c * tw, r * th, (c + 1) * tw, (r + 1) * th))
            if tile.size[0] > _TILE_SAMPLE_PX or tile.size[1] > _TILE_SAMPLE_PX:
                tile = tile.resize((_TILE_SAMPLE_PX, _TILE_SAMPLE_PX))
            counts.append(len(set(_flattened_pixels(tile))))
    return counts


def _max_uniform_run(counts: list[int], rows: int, cols: int, axis: int) -> int:
    """Longest run of fully-uniform tiles along ``axis`` (0=rows, 1=cols).

    A "fully-uniform row" = every tile in that row is below
    MIN_DISTINCT_COLORS_PER_TILE. Returns the longest streak of such rows
    (resp. columns) -- 0 if none. This is the contiguity signal that separates
    a block of blank subplot panels (contiguous) from the scattered uniform
    tiles of a single figure's whitespace margins.
    """
    best = cur = 0
    outer, inner = (rows, cols) if axis == 0 else (cols, rows)
    for o in range(outer):
        full = True
        for i in range(inner):
            idx = o * inner + i if axis == 0 else i * outer + o
            if counts[idx] >= MIN_DISTINCT_COLORS_PER_TILE:
                full = False
                break
        if full:
            cur += 1
            best = max(best, cur)
        else:
            cur = 0
    return best


def partial_blank_fraction(raw: bytes, rows: int, cols: int) -> dict | None:
    """Per-tile uniform/rich fractions + contiguity for a grid figure, or None.

    Detects a *partially blank* grid (#10319): a figure where a significant
    fraction of tiles is quasi-uniform (blank/near-blank) while others are rich.
    The signal is the intra-image contrast -- both uniform AND rich tiles must be
    present. A fully blank figure (caught by the global metrics) and a fully
    filled one do not qualify.

    Returns ``{uniform_frac, rich_frac, n_uniform, n_rich, n_tiles,
    max_uniform_row_run, max_uniform_col_run}`` or None if the image cannot be
    decoded or is too small to tile meaningfully (< 8 px per tile side).
    """
    try:
        from PIL import Image
        import io
        im = Image.open(io.BytesIO(raw)).convert("RGB")
    except Exception:
        return None
    w, h = im.size
    if w < cols * 8 or h < rows * 8:
        return None
    counts = _tile_distinct_colors(im, rows, cols)
    n_tiles = len(counts)
    n_uniform = sum(1 for c in counts if c < MIN_DISTINCT_COLORS_PER_TILE)
    n_rich = sum(1 for c in counts if c >= RICH_DISTINCT_COLORS_PER_TILE)
    return {
        "uniform_frac": n_uniform / n_tiles,
        "rich_frac": n_rich / n_tiles,
        "n_uniform": n_uniform,
        "n_rich": n_rich,
        "n_tiles": n_tiles,
        "max_uniform_row_run": _max_uniform_run(counts, rows, cols, 0),
        "max_uniform_col_run": _max_uniform_run(counts, rows, cols, 1),
    }


def _classify_partial_blank(mime: str, raw: bytes, rows: int, cols: int) -> dict | None:
    """Return an *advisory* finding if the image is a partially-blank grid.

    Advisory findings carry ``"level": "advisory"`` and do NOT fail ``--check``
    (phase advisory, #10319). They are reported separately from hard degenerate
    findings so the exit code of existing CI gates is unchanged.

    Three conjuncts must hold: (1) enough uniform tiles, (2) enough rich tiles
    (intra-image contrast), and (3) a contiguous block of >= MIN_UNIFORM_RUN
    fully-uniform rows or columns -- the signature of missing subplot panels.
    Conjunct (3) is the precision gate: it rejects single figures whose
    whitespace margins scatter uniform tiles at the corners (0 FP on 981
    notebooks, scan #10319) while keeping the real defect (>= 2 blank rows of a
    subplot grid).
    """
    stats = partial_blank_fraction(raw, rows, cols)
    if stats is None:
        return None
    has_contrast = (stats["uniform_frac"] >= PARTIAL_BLANK_UNIFORM_FRAC
                    and stats["rich_frac"] >= PARTIAL_BLANK_RICH_FRAC)
    has_block = (stats["max_uniform_row_run"] >= MIN_UNIFORM_RUN
                 or stats["max_uniform_col_run"] >= MIN_UNIFORM_RUN)
    if has_contrast and has_block:
        dims = _png_dimensions(raw) if mime == "image/png" else None
        return {
            "mime": mime,
            "bytes": len(raw),
            "dimensions": list(dims) if dims else None,
            "reasons": [
                f"partial_blank_grid("
                f"uniform={stats['n_uniform']}/{stats['n_tiles']},"
                f"rich={stats['n_rich']}/{stats['n_tiles']},"
                f"run={max(stats['max_uniform_row_run'], stats['max_uniform_col_run'])},"
                f"tiles={rows}x{cols})"
            ],
            "level": "advisory",
        }
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


def detect_cell(cell: dict, min_dim: int = MIN_DIM, min_bytes: int = MIN_BYTES,
                tiles: tuple[int, int] | None = None) -> list[dict]:
    """Return findings (one per degenerate OR advisory image output) for a code cell.

    Advisory findings (#10319, ``level == "advisory"``) flag partially-blank grids
    and are only emitted for images that passed the hard degenerate checks (a hard
    finding already covers a fully-blank image). They do NOT fail ``--check``.
    """
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
                continue  # hard finding couvre deja cette image
            if tiles is not None:
                adv = _classify_partial_blank(mime, raw, *tiles)
                if adv:
                    findings.append({"output_index": oi, **adv})
    return findings


def scan_notebook(path: Path, min_dim: int = MIN_DIM, min_bytes: int = MIN_BYTES,
                  tiles: tuple[int, int] | None = None) -> dict:
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
        for finding in detect_cell(cell, min_dim, min_bytes, tiles):
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
    total_hits = sum(len([h for h in r["hits"] if h.get("level") != "advisory"]) for r in results)
    total_adv = sum(len([h for h in r["hits"] if h.get("level") == "advisory"]) for r in results)
    affected = [r for r in results if r["hits"]]
    errored = [r for r in results if r.get("error")]
    lines = [
        f"Notebooks scanned  : {len(results)}",
        f"Degenerate figures : {total_hits}",
        f"Advisory (partial) : {total_adv}",
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
            tag = "  [advisory]" if h.get("level") == "advisory" else ""
            lines.append(f"  - cell [{h['cell_index']}] output[{h['output_index']}] {h['mime']}: {reasons}{tag}")
        lines.append("")
    lines.append(
        "FIX: re-execute the cell in the real environment (QC Cloud "
        "research for QuantBook, local kernel for matplotlib) and commit the real "
        "figure -- Stop&Repair, never scrub/delete to hide (secrets-hygiene rule 6)."
    )
    if total_adv:
        lines.append(
            "NOTE (advisory, #10319): a partially-blank grid is signalled, not blocked. "
            "Inspect by eye (a lane that sees) before acting -- it may be a legitimate "
            "sparse layout or a real missing-content defect."
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
    parser.add_argument("--tiles", default="4x4",
                        help="Per-tile advisory grid RxC for partially-blank detection "
                        f"(#10319, default {DEFAULT_TILES[0]}x{DEFAULT_TILES[1]}); "
                        "pass 'off' to disable.")
    parser.add_argument("--strict", action="store_true",
                        help="Also exit 1 on advisory findings (default: advisories do not fail --check)")
    args = parser.parse_args(argv)

    tiles = None
    if args.tiles and args.tiles.lower() != "off":
        try:
            r_s, c_s = args.tiles.lower().split("x")
            tiles = (int(r_s), int(c_s))
            if tiles[0] < 1 or tiles[1] < 1:
                raise ValueError
        except ValueError:
            print(f"error: --tiles expects RxC (e.g. 4x4), got {args.tiles!r}", file=sys.stderr)
            return 2

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

    results = [scan_notebook(p, args.min_dim, args.min_bytes, tiles) for p in paths]
    # Hard hits only for --check exit code (advisories do not block, unless --strict).
    hard_hits = sum(len([h for h in r["hits"] if h.get("level") != "advisory"]) for r in results)
    adv_hits = sum(len([h for h in r["hits"] if h.get("level") == "advisory"]) for r in results)

    if args.json:
        payload = {
            "notebooks_scanned": len(results),
            "total_hits": hard_hits,
            "advisory_hits": adv_hits,
            "results": results,
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_human_report(results))

    if args.check and hard_hits > 0:
        return 1
    if args.check and args.strict and adv_hits > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
