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
    # Advisory sparse-grid (#10319) -- figure pleine mais partiellement vide :
    python detect_blank_figures.py NB.ipynb --sparse                   # advisory, tuiles adaptatives
    python detect_blank_figures.py NB.ipynb --sparse --tiles 4x4       # tuiles explicites
    python detect_blank_figures.py NB.ipynb --check-sparse             # bloquant (apres mesure FP)
    python detect_blank_figures.py --sparse --family GenAI             # sweep advisory d'une famille

Exit codes
----------
    0 -- aucune figure degenerece (ou mode non --check)
    1 -- une ou plusieurs figures degenerees (--check seulement ; --check-sparse y ajoute les sparse)
    2 -- erreur (notebook illisible, famille introuvable)

Advisory sparse-grid (#10319)
-----------------------------
Une figure pleine et riche en couleurs mais dont une fraction significative des
sous-regions (tuiles) est quasi-uniforme, tandis que d'autres sont riches. Cas
fondateur (#10305 cellule 12) : grille matplotlib 4x4 (2 prompts x 2 seeds x 4
instants) ou 2 rangees sont beige quasi-vide et 2 rangees sont des pommes
rendues correctement -> passe les metriques globales au vert alors que la moitie
du contenu pedagogique est absent.

La metrique par-tile decoupe l'image en grille (pilotable par --tiles RxC,
adaptative par defaut), compte les couleurs distinctes de chaque tuile (apres
downsample), et signale quand >= SPARSE_MIN_FRACTION des tuiles sont
quasi-uniformes tandis qu'au moins une reste riche. C'est le CONTRASTE
INTRA-IMAGE qui porte le signal : une figure entierement blanche ou entierement
riche n'est PAS signalee. ADVISORY par defaut (--check ne faille pas) ; le
blocage --check-sparse n'est a activer qu'apres mesure du taux de FP.

Voir aussi
----------
- `detect_ascii_workaround.py` (#3801) -- moitie ASCII du sweep Prong-A
- `scan_figure_visual_signature.py` -- signature visuelle RGB (aussi globale, meme limite per-region)
- `.claude/rules/sota-not-workaround.md` -- Prong-A : vrai outil, pas workaround/fabrication
- `.claude/rules/secrets-hygiene.md` regle 6 -- Stop&Repair : re-executer, jamais scrubber
- #6891 -- incident fondateur (8 quantbook.ipynb QC blank-PNG)
- #10319 -- extension per-tile (grille partiellement vide)

Part of #3801 (EPIC SOTA axe-2).
"""
from __future__ import annotations

import argparse
import base64
import binascii
import io
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

# --- Advisory sparse-grid (#10319) ---------------------------------------
# Seuil "tuile quasi-uniforme" : une tuile de vrai contenu (courbe, nuage de
# points, heatmap, photo) a des centaines de couleurs distinctes meme apres
# downsample 64x64 ; une tuile beige/blanche vide en a < 10. Un seuil a 32
# discrimine nettement (calibre sur le cas #10305 : rangees vides ~3-6 couleurs,
# rangees pomme ~150-400 apres downsample).
SPARSE_TILE_MIN_COLORS = 32
# Fraction minimale de tuiles quasi-uniformes pour signaler : le cas #10305 est
# 8/16 = 0.50. Un seul subplot vide dans une 2x2 = 0.25 -> NON signale (legitime).
# 0.40 laisse une marge sous le cas reel tout en tolerant 1-2 tuiles vides.
SPARSE_MIN_FRACTION = 0.40
# Downsample par tuile avant comptage des couleurs (vitesse : 64x64 = 4096 px au
# lieu de 256x256 = 65k). Preserve la diversite chromatique (suffisant pour
# distinguer 1 couleur de 200).
SPARSE_SAMPLE_DIM = 64
# Dimension minimale pour auto-tiler : en dessous, une image est trop petite
# pour qu'une grille de sous-graphes ait un sens (et trop peu de pixels pour
# stabiliser les stats par tuile). Evite les FP sur les petites figures.
SPARSE_AUTO_MIN_DIM = 400
# Taille de grille auto par defaut quand l'auteur ne fournit pas --tiles.
# 4x4 couvre le cas #10305 (2 prompts x 2 seeds x 4 frames) et la plupart des
# grilles de comparaison pedagogiques. Adaptee si l'image est tres allongee.
SPARSE_AUTO_TILES = (4, 4)

_IMAGE_MIMES = ("image/png", "image/jpeg")
_PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"

# Pillow est requis uniquement pour la couche advisory sparse-grid (le
# content-gate #8634 importe deja PIL de facon lazy dans _has_real_content).
# Import module-level + flag : la couche degenerescence deterministe reste
# fonctionnelle sans Pillow, et la couche sparse est juste sautee si absente.
try:  # pragma: no cover - depend de l'environnement d'execution
    from PIL import Image as _PILImage  # type: ignore

    _HAS_PIL = True
except ImportError:  # pragma: no cover
    _HAS_PIL = False


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
        "kind": "degenerate",
        "mime": mime,
        "bytes": size,
        "dimensions": list(dims) if dims else None,
        "reasons": reasons,
    }


# ---------------------------------------------------------------------------
# Advisory sparse-grid (per-tile metric, #10319)
# ---------------------------------------------------------------------------


def _parse_tiles(spec: str | None) -> tuple[int, int] | None:
    """Parse a ``RxC`` tile spec (e.g. ``"4x4"``, ``"2x3"``) into (rows, cols).

    Returns ``None`` for a falsy spec or ``"auto"`` (signal: use the adaptive
    default). Raises ``ValueError`` on a malformed spec so the CLI surfaces it
    instead of silently degrading.
    """
    if not spec:
        return None
    if spec.lower() == "auto":
        return None
    try:
        r_s, c_s = spec.lower().split("x")
        rows, cols = int(r_s), int(c_s)
    except ValueError as exc:
        raise ValueError(f"--tiles expects RxC (e.g. 4x4) or 'auto', got {spec!r}") from exc
    if rows < 1 or cols < 1:
        raise ValueError(f"--tiles rows/cols must be >= 1, got {rows}x{cols}")
    return (rows, cols)


def _auto_tiles(w: int, h: int) -> tuple[int, int] | None:
    """Adaptive tile layout for an image of (w, h).

    Returns ``None`` when the image is too small to auto-tile (below
    ``SPARSE_AUTO_MIN_DIM``). For sufficiently large images, uses
    ``SPARSE_AUTO_TILES`` unless the image is strongly elongated (>= 3:1), in
    which case the layout is stretched along the long axis.
    """
    if w < SPARSE_AUTO_MIN_DIM or h < SPARSE_AUTO_MIN_DIM:
        return None
    base_r, base_c = SPARSE_AUTO_TILES
    if w >= 3 * h:
        return (base_r, base_c * 2)
    if h >= 3 * w:
        return (base_r * 2, base_c)
    return (base_r, base_c)


def _tile_color_count(im, box: tuple[int, int, int, int]) -> int:
    """Count distinct RGB colors in *box* after downsampling to SPARSE_SAMPLE_DIM.

    Downsampling preserves the diversity signal (1 color stays 1, 200 stays
    ~hundreds) while bounding the cost regardless of the original resolution.
    """
    tile = im.crop(box)
    tw, th = tile.size
    if tw <= 0 or th <= 0:
        return 0
    if tw > SPARSE_SAMPLE_DIM or th > SPARSE_SAMPLE_DIM:
        tile = tile.resize((SPARSE_SAMPLE_DIM, SPARSE_SAMPLE_DIM))
    if tile.mode != "RGB":
        tile = tile.convert("RGB")
    return len(set(_flattened_pixels(tile)))


def _tile_color_counts(im, rows: int, cols: int) -> list[list[int]]:
    """Return a rows x cols matrix of distinct-color counts per tile."""
    w, h = im.size
    counts: list[list[int]] = []
    for r in range(rows):
        row_counts = []
        for c in range(cols):
            box = (
                int(w * c / cols),
                int(h * r / rows),
                int(w * (c + 1) / cols),
                int(h * (r + 1) / rows),
            )
            row_counts.append(_tile_color_count(im, box))
        counts.append(row_counts)
    return counts


def _sparse_grid_finding(
    mime: str,
    raw: bytes,
    tiles: tuple[int, int] | None,
    min_colors_tile: int = SPARSE_TILE_MIN_COLORS,
    min_fraction: float = SPARSE_MIN_FRACTION,
) -> dict | None:
    """Return an advisory sparse-grid finding, or ``None``.

    The image is tiled into *rows* x *cols* (or an adaptive layout when *tiles*
    is ``None``). Each tile is classified quasi-uniform (distinct colors below
    *min_colors_tile*) or rich. The image is flagged when the quasi-uniform
    fraction is >= *min_fraction* AND at least one rich tile exists (the
    intra-image contrast is what carries the signal ; a fully-blank or
    fully-rich image is not flagged).
    """
    if not _HAS_PIL:
        return None
    try:
        im = _PILImage.open(io.BytesIO(raw))
        im.load()
    except Exception:
        return None
    w, h = im.size
    if tiles is not None:
        rows, cols = tiles
    else:
        auto = _auto_tiles(w, h)
        if auto is None:
            return None
        rows, cols = auto
    if rows < 1 or cols < 1:
        return None
    if w < rows * 4 or h < cols * 4:
        # Trop petit pour que la decoupe ait un sens (moins de ~4 px par tuile).
        return None

    counts = _tile_color_counts(im, rows, cols)
    flat = [c for row in counts for c in row]
    total = len(flat)
    uniform = [c for c in flat if c < min_colors_tile]
    rich = [c for c in flat if c >= min_colors_tile]
    if not rich:
        # Pas de contraste intra-image -> pas le defaut vise (figure toute vide
        # ou toute riche). On ne signale pas.
        return None
    fraction_uniform = len(uniform) / total
    if fraction_uniform < min_fraction:
        return None
    return {
        "kind": "sparse_grid",
        "mime": mime,
        "bytes": len(raw),
        "dimensions": [w, h],
        "tiles": [rows, cols],
        "uniform_tiles": len(uniform),
        "total_tiles": total,
        "uniform_fraction": round(fraction_uniform, 3),
        "min_colors_tile": min_colors_tile,
        "threshold_fraction": min_fraction,
        "reasons": [
            f"sparse_grid({len(uniform)}/{total} tiles quasi-uniform "
            f"(< {min_colors_tile} colors), {len(rich)} rich; "
            f"fraction {fraction_uniform:.0%} >= {min_fraction:.0%})"
        ],
        "advisory": True,
    }


def detect_cell(
    cell: dict,
    min_dim: int = MIN_DIM,
    min_bytes: int = MIN_BYTES,
    tiles: tuple[int, int] | None = None,
) -> list[dict]:
    """Return findings for a code cell.

    Hard degenerate findings (``kind="degenerate"``) are always computed. When
    *tiles* is not ``None`` (sparse layer requested), an advisory sparse-grid
    pass (``kind="sparse_grid"``) is added for images that passed the hard
    check. Both kinds carry an ``output_index``.
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
                # Une image degeneree (1x1 / < 1 Ko) n'a pas de grille a analyser.
                continue
            if tiles is not None:
                sparse = _sparse_grid_finding(mime, raw, tiles)
                if sparse:
                    findings.append({"output_index": oi, **sparse})
    return findings


def scan_notebook(
    path: Path,
    min_dim: int = MIN_DIM,
    min_bytes: int = MIN_BYTES,
    tiles: tuple[int, int] | None = None,
) -> dict:
    """Return a result dict for one notebook: path, hits[], sparse[], error.

    ``hits`` = hard degenerate findings (deterministic). ``sparse`` = advisory
    sparse-grid findings (#10319). The split lets ``--check`` fail only on hard
    hits while sparse is reported but non-blocking by default.
    """
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": [], "sparse": []}

    hits = []
    sparse = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for finding in detect_cell(cell, min_dim, min_bytes, tiles):
            entry = {"cell_index": ci, **finding}
            if finding.get("kind") == "sparse_grid":
                sparse.append(entry)
            else:
                hits.append(entry)
    return {"path": str(path), "kernel": _kernel(nb), "hits": hits, "sparse": sparse, "error": None}


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
    total_sparse = sum(len(r.get("sparse", []) or []) for r in results)
    affected = [r for r in results if r["hits"]]
    sparse_affected = [r for r in results if r.get("sparse")]
    errored = [r for r in results if r.get("error")]
    lines = [
        f"Notebooks scanned  : {len(results)}",
        f"Degenerate figures : {total_hits}",
        f"Sparse-grid (adv)  : {total_sparse}",
        f"Affected notebooks : {len(affected)}",
        "",
    ]
    if not affected and not sparse_affected:
        lines.append("No degenerate figures detected (deterministic dimension/size check).")
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        if not sparse_affected:
            return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        for h in r["hits"]:
            reasons = ", ".join(h["reasons"])
            lines.append(f"  - cell [{h['cell_index']}] output[{h['output_index']}] {h['mime']}: {reasons}")
        lines.append("")
    if sparse_affected:
        lines.append("## Advisory: sparse-grid figures (#10319, non-blocking)")
        lines.append("These full-size images have a significant fraction of near-empty tiles")
        lines.append("alongside rich ones -- possibly missing subplots. Review by eye (lanes")
        lines.append("MiniMax / ai-01); this is advisory until FP rate is measured.")
        lines.append("")
        for r in sparse_affected:
            short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
            lines.append(f"### {short}  [{r['kernel']}]")
            for s in r["sparse"]:
                reasons = ", ".join(s["reasons"])
                lines.append(
                    f"  - cell [{s['cell_index']}] output[{s['output_index']}] "
                    f"{s['mime']} {s.get('dimensions')}: {reasons}"
                )
            lines.append("")
    lines.append(
        "FIX (degenerate): re-execute the cell in the real environment (QC Cloud "
        "research for QuantBook, local kernel for matplotlib) and commit the real "
        "figure -- Stop&Repair, never scrub/delete to hide (secrets-hygiene rule 6)."
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
    # --- Advisory sparse-grid (#10319) ---
    parser.add_argument(
        "--sparse",
        action="store_true",
        help="Enable advisory sparse-grid detection (per-tile metric, #10319). "
        "Uses an adaptive tile layout unless --tiles is given.",
    )
    parser.add_argument(
        "--tiles",
        default=None,
        help="Tile layout 'RxC' for sparse-grid detection (e.g. 4x4), or 'auto' "
        "(adaptive default). Implies --sparse.",
    )
    parser.add_argument(
        "--check-sparse",
        action="store_true",
        help="Also exit 1 on advisory sparse-grid findings (use only AFTER measuring "
        "the false-positive rate on the real base, per #10319 acceptance).",
    )
    args = parser.parse_args(argv)

    # La couche advisory ne s'active que si --sparse ou --tiles est demande :
    # comportement par defaut inchange (0 regression garantie sur la base actuelle).
    tiles: tuple[int, int] | None = None
    if args.tiles is not None or args.sparse:
        # None => _sparse_grid_finding utilisera _auto_tiles
        tiles = _parse_tiles(args.tiles)

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
    total_hits = sum(len(r["hits"]) for r in results)
    total_sparse = sum(len(r.get("sparse", []) or []) for r in results)

    if args.json:
        payload = {
            "notebooks_scanned": len(results),
            "total_hits": total_hits,
            "total_sparse": total_sparse,
            "results": results,
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_human_report(results))

    if args.check and total_hits > 0:
        return 1
    if args.check_sparse and total_sparse > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
