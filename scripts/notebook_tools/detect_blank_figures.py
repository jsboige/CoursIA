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
retenue que sur la taille). Ces deux signaux sont BLOQUANTS (--check exit 1).

Signaux ADVISORY par region (#10319, NON bloquants)
---------------------------------------------------
Un grand PNG riche en couleurs peut quand meme avoir la moitie de son contenu
absent : une grille matplotlib dont certaines rangées de sous-graphes sont vides
(cas #10319 : 4x4 dont 2 rangees uniformes). Les trois signaux ci-dessus
raisonnent sur l'image ENTIERE et ne voient pas le trou. Une 4e métrique, par
TUILE, ajoute le contraste INTRA-image : on decoupe l'image en grille (adaptive
~64 px par tuile, ou `--tiles RxC`), on calcule par tuile l'ecart-type max par
canal, et on signale (advisory) quand une fraction significative des tuiles est
quasi-uniforme (>= MIN_UNIFORM_FRACTION) COEXISTANT avec une fraction
significative de tuiles riches (>= MIN_CONTENT_FRACTION). Le signal est le
CONTRASTE, pas le niveau absolu : une image entierement uniforme ou entierement
riche n'est PAS flaggee. Advisory = rapporte mais ne fait PAS rougir --check
(phase 1 : on mesure le taux de FP avant tout blocage, #10319 critere 4).

Known blind spots (hors scope par design)
-----------------------------------------
- FIGURE PLEINE MAIS VIDE : un PNG full-size (ex 690x590) entierement blanc /
  transparent (un plot qui a trace des axes vides, SANS region riche). La
  métrique par tuile (#10319) ne le voit PAS : elle exige du contraste intra-
  image (uniforme + riche). Le cas « tout vide » reste hors scope (variance
  globale faible -- bruité, couvert partiellement par _has_real_content quand
  l'image a < MIN_DISTINCT_COLORS).
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
    python detect_blank_figures.py NB.ipynb --tiles 4x4    # grille par-region advisory explicite

Exit codes
----------
    0 -- aucune figure degeneree bloquante (ou mode non --check). Les findings
         advisory (#10319) ne font JAMAIS remonter exit 1.
    1 -- une ou plusieurs figures degenerees BLOQUANTES (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable, --tiles mal forme)

Voir aussi
----------
- `detect_ascii_workaround.py` (#3801) -- moitie ASCII du sweep Prong-A
- `.claude/rules/sota-not-workaround.md` -- Prong-A : vrai outil, pas workaround/fabrication
- `.claude/rules/secrets-hygiene.md` regle 6 -- Stop&Repair : re-executer, jamais scrubber
- #6891 -- incident fondateur (8 quantbook.ipynb QC blank-PNG)
- #10319 -- grille partiellement vide (advisory par-region, non bloquant)

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

# Detection par region (#10319) -- grille partiellement vide.
# Les trois seuils ci-dessus (dim / bytes / couleurs) raisonnent sur des agrégats
# de l'image ENTIÈRE : une grille matplotlib dont seule une partie des sous-graphes
# est vide est un grand PNG riche en couleurs -- elle passe les trois au vert alors
# que la moitie de son contenu pedagogique est absent (cas #10319 : 4x4 dont 2
# rangées vides). La métrique par tuile ci-dessous ajoute le contraste INTRA-image
# comme 4e signal (advisory, non bloquant -- phase 1).
TILE_TARGET_PX = 64          # cote de tuile vise en mode adaptatif (grille choisie
                             # pour que chaque tuile fasse ~>= 64 px, min 2x2). Une
                             # tuile plus fine qu'un sous-graphe marche aussi bien :
                             # un sous-graphe vide de 172x147 couvre ~3x3 tuiles, qui
                             # contribuent toutes au compte "uniforme".
MIN_TILES_AXIS = 2           # ne pas subdivider en dessous de 2x2 (une tuile unique
                             # = l'image entiere = le cas global deja couvert).
UNIFORM_TILE_STD = 10.0      # ecart-type max (0-255) par canal en dessous duquel une
                             # tuile est "quasi-uniforme" (fond uni, cadre vide).
CONTENT_TILE_STD = 25.0      # ecart-type min au-dessus duquel une tuile porte un
                             # vrai contenu. La bande [10, 25] = ambigue, exclue des
                             # deux comptes (conservateur : ne gonfle ni uniforme ni
                             # riche, donc ne fabrique pas de contraste artificiel).
LARGE_UNIFORM_REGION = 0.40  # Une GRANDE region uniforme CONNEXE couvrant >= 40 % des
                             # tuiles est la signature d'un sous-graphe vide (cas
                             # #10319 : la moitie superieure de la grille est vide ->
                             # une composante 4-connexe de tuiles uniformes couvre ~50 %
                             # de l'image). Un plot matplotlib normal a son blanc de
                             # fond EPARPILLE entre les tuiles de contenu -> ses
                             # composantes uniformes connexes sont petites (marges,
                             # interstices) -> non flaggue. Seuil phase 1 calibre sur
                             # le corpus (1100 figures candidates) : p50=0.11, p90=0.33,
                             # p95=0.43 -> 0.40 est juste au-dela de p90 et laisse 94 %
                             # des figures muettes, ne surfacent que la queue ~6 % pour
                             # tri visuel. Taux advisory mesure a d'autres seuils :
                             # 0.20->27 %, 0.30->13 %, 0.40->6 %, 0.50->2 %. A retuner
                             # apres tri visuel des candidats par les lanes qui voient
                             # (MiniMax/ai-01) -- #10319 critere 4.
MIN_CONTENT_FRACTION = 0.15  # ... ET >= 15 % de tuiles riches => il y a BIEN du
                             # contenu quelque part (sinon c'est le cas "figure pleine
                             # mais vide", hors scope).

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


def _partially_empty_metric(
    raw: bytes,
    tiles: tuple[int, int] | None = None,
) -> dict | None:
    """Detect a grid figure that is PARTIALLY empty (#10319).

    Returns a detail dict when the image carries intra-image contrast -- a
    significant fraction of near-uniform tiles coexisting with a significant
    fraction of rich tiles -- which is the signature of a matplotlib subplot
    grid where some rows rendered empty (uniform canvas) while others carry
    real content. Returns None otherwise (fully-rich real plot, fully-uniform
    white canvas, PIL/numpy absent, or undecodable image).

    Why per-tile and not whole-image: the three blocking metrics above reason
    on aggregates of the ENTIRE image. A 4x4 grid whose top half is empty is a
    large, byte-heavy, many-colored PNG -- it passes dimension, payload AND
    distinct-color checks, because the rich bottom half supplies enough colors.
    Only a per-region statistic can see that half the content is missing.

    The signal is CONTRAST, not absolute level: a fully-empty image (all tiles
    uniform, none rich) is NOT flagged here -- that is the separate, already
    documented "figure pleine mais vide" blind spot, out of this metric's
    scope. Only the *partially*-empty case (both uniform AND rich fractions
    above threshold) produces an advisory.

    numpy is used for the per-tile std-dev (fast vectorised). It is optional:
    if numpy or PIL is unavailable, or the image is undecodable, returns None
    and the caller keeps the blocking size/dimension behaviour (no coverage
    regression -- same degrade-gracefully contract as `_has_real_content`).

    `tiles` overrides the adaptive grid as (rows, cols); None = adaptive
    (grid chosen so each tile ~= TILE_TARGET_PX, floored at MIN_TILES_AXIS).
    """
    try:
        import io
        import numpy as np
        from PIL import Image
    except Exception:
        return None
    try:
        im = Image.open(io.BytesIO(raw)).convert("RGB")
        arr = np.asarray(im)  # (H, W, 3) uint8
    except Exception:
        return None
    if arr.ndim != 3 or arr.shape[2] < 3:
        return None
    h, w = int(arr.shape[0]), int(arr.shape[1])
    if h < MIN_TILES_AXIS or w < MIN_TILES_AXIS:
        return None  # too small to subdivide meaningfully

    if tiles is None:
        cols = max(MIN_TILES_AXIS, round(w / TILE_TARGET_PX))
        rows = max(MIN_TILES_AXIS, round(h / TILE_TARGET_PX))
    else:
        rows, cols = tiles
    rows = max(MIN_TILES_AXIS, int(rows))
    cols = max(MIN_TILES_AXIS, int(cols))

    row_edges = np.linspace(0, h, rows + 1, dtype=int)
    col_edges = np.linspace(0, w, cols + 1, dtype=int)

    # Carte par tuile : 0 = uniforme, 1 = contenu, -1 = ambigue.
    tile_map = [[-1] * cols for _ in range(rows)]
    uniform = 0
    content = 0
    total = 0
    for ri in range(rows):
        for ci in range(cols):
            tile = arr[row_edges[ri]:row_edges[ri + 1], col_edges[ci]:col_edges[ci + 1]]
            if tile.size == 0:
                continue
            total += 1
            # max-channel std across all pixels of the tile (0-255 scale)
            std = float(tile.reshape(-1, tile.shape[-1]).std(axis=0).max())
            if std < UNIFORM_TILE_STD:
                uniform += 1
                tile_map[ri][ci] = 0
            elif std >= CONTENT_TILE_STD:
                content += 1
                tile_map[ri][ci] = 1
    if total == 0:
        return None

    c_frac = content / total
    # Le signal discriminant est la CONTIGUITE, pas la fraction. Un plot normal
    # a ses tuiles uniformes (blanc de fond) EPARPILLEES entre les tuiles de
    # contenu -> la plus grande region uniforme connexe est petite. Une grille
    # dont des sous-graphes entiers sont vides a une GRANDE region uniforme
    # connexe (ex. la moitie superieure de l'image). On mesure donc la plus
    # grande composante 4-connexe de tuiles uniformes (#10319). Sans ce test,
    # 64 % des notebooks pedagogiques (plot matplotlib clairsemes sur fond
    # blanc) etaient flaggues advisory -- bruit inutilisable.
    largest_region = _largest_uniform_region(tile_map, rows, cols)
    region_frac = largest_region / total if total else 0.0
    if region_frac >= LARGE_UNIFORM_REGION and c_frac >= MIN_CONTENT_FRACTION:
        return {
            "uniform_fraction": round(uniform / total, 3),
            "content_fraction": round(c_frac, 3),
            "largest_uniform_region": round(region_frac, 3),
            "tiles": f"{rows}x{cols}",
            "uniform_tiles": uniform,
            "content_tiles": content,
            "total_tiles": total,
        }
    return None


def _largest_uniform_region(tile_map: list[list[int]], rows: int, cols: int) -> int:
    """Size of the largest 4-connected component of uniform (0) tiles.

    Pure-Python flood fill on the (small) tile grid -- the grid is at most a few
    hundred tiles, so no scipy dependency is warranted. Used by
    `_partially_empty_metric` to distinguish a contiguous empty subplot block
    (large region) from scattered background-white tiles of a normal plot
    (small regions).
    """
    visited = [[False] * cols for _ in range(rows)]
    largest = 0
    for sr in range(rows):
        for sc in range(cols):
            if tile_map[sr][sc] != 0 or visited[sr][sc]:
                continue
            # BFS over uniform tiles
            size = 0
            stack = [(sr, sc)]
            visited[sr][sc] = True
            while stack:
                r, c = stack.pop()
                size += 1
                for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                    nr, nc = r + dr, c + dc
                    if (
                        0 <= nr < rows
                        and 0 <= nc < cols
                        and not visited[nr][nc]
                        and tile_map[nr][nc] == 0
                    ):
                        visited[nr][nc] = True
                        stack.append((nr, nc))
            if size > largest:
                largest = size
    return largest


def _classify_image(
    mime: str,
    raw: bytes,
    min_dim: int,
    min_bytes: int,
    tiles: tuple[int, int] | None = None,
) -> dict | None:
    """Return a finding dict if the image is degenerate or partially empty, else None.

    Findings carry a ``severity`` field: ``"blocking"`` for the deterministic
    dimension/payload defects (#6891), ``"advisory"`` for the per-region
    partially-empty signal (#10319). A ``"blocking"`` finding trips ``--check``;
    an ``"advisory"`` finding never does (phase 1: measure the FP rate before
    any blocking, per #10319 acceptance criterion 4).
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
        # Defaut deterministe (dim/taille) -> bloquant.
        return {
            "mime": mime,
            "bytes": size,
            "dimensions": list(dims) if dims else None,
            "reasons": reasons,
            "severity": "blocking",
        }

    # L'image a passe les seuils bloquants : examiner le contraste intra-image
    # (#10319). Advisory seulement -- ne fait pas rougir le gate.
    region = _partially_empty_metric(raw, tiles)
    if region is None:
        return None
    return {
        "mime": mime,
        "bytes": size,
        "dimensions": list(dims) if dims else None,
        "reasons": [
            f"partially_empty_grid(largest_empty_region={region['largest_uniform_region']}, "
            f"content={region['content_fraction']}, tiles={region['tiles']})"
        ],
        "severity": "advisory",
        "region_detail": region,
    }


def detect_cell(
    cell: dict,
    min_dim: int = MIN_DIM,
    min_bytes: int = MIN_BYTES,
    tiles: tuple[int, int] | None = None,
) -> list[dict]:
    """Return findings (one per degenerate/partially-empty image output) for a code cell."""
    findings = []
    for oi, out in enumerate(_cell_outputs(cell)):
        data = out.get("data", {}) if isinstance(out, dict) else {}
        for mime in _IMAGE_MIMES:
            if mime not in data:
                continue
            raw = _decode_image(data[mime])
            if raw is None:
                continue
            finding = _classify_image(mime, raw, min_dim, min_bytes, tiles)
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
    # Les findings advisory (#10319, par-region) ne sont pas des degenerescences
    # deterministes : on les rapporte dans une section dediee, sans faire monter le
    # compteur "Degenerate figures" (qui pilote historiquement le gate --check).
    blocking: list[tuple[dict, dict]] = []
    advisory: list[tuple[dict, dict]] = []
    for r in results:
        for h in r["hits"]:
            (advisory if h.get("severity") == "advisory" else blocking).append((r, h))
    nb_blocking = len({id(r) for r, _ in blocking})
    errored = [r for r in results if r.get("error")]
    lines = [
        f"Notebooks scanned  : {len(results)}",
        f"Degenerate figures : {len(blocking)}",
        f"Affected notebooks : {nb_blocking}",
        "",
    ]
    if not blocking and not advisory:
        lines.append("No degenerate figures detected (deterministic dimension/size check).")
        if errored:
            lines.append("")
            lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
        return "\n".join(lines)
    # Findings bloquants (deterministes dim/taille -- #6891).
    for r, h in blocking:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}  [{r['kernel']}]")
        lines.append(f"  - cell [{h['cell_index']}] output[{h['output_index']}] {h['mime']}: {', '.join(h['reasons'])}")
    if blocking:
        lines.append("")
        lines.append(
            "FIX: re-execute the cell in the real environment (QC Cloud research for "
            "QuantBook, local kernel for matplotlib) and commit the real figure -- "
            "Stop&Repair, never scrub/delete to hide (secrets-hygiene rule 6)."
        )
    # Findings advisory (par-region, #10319, NON bloquants).
    if advisory:
        lines.append("")
        lines.append(f"## Advisory -- partially-empty grids (#10319, non-blocking): {len(advisory)}")
        for r, h in advisory:
            short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
            lines.append(f"  - {short} cell [{h['cell_index']}] output[{h['output_index']}]: {', '.join(h['reasons'])}")
        lines.append(
            "NOTE: advisory only -- a region of the figure is near-uniform while another "
            "carries content. Verify by eye (vision lanes); --check does not fail on this "
            "(FP-rate measure phase, #10319 acceptance criterion 4)."
        )
    if errored:
        lines.append("")
        lines.append(f"NOTE: {len(errored)} notebook(s) unreadable (see --json for details).")
    return "\n".join(lines)


def _parse_tiles(spec: str | None) -> tuple[int, int] | None:
    """Parse a ``--tiles RxC`` spec (e.g. ``"4x4"``) into a (rows, cols) tuple.

    Accepts ``x`` or ``X`` as the separator. Returns None for an empty/None
    spec (adaptive grid). Raises ValueError on a malformed spec so argparse
    surfaces it as a usage error.
    """
    if not spec:
        return None
    parts = spec.lower().replace("x", "X").split("X")
    if len(parts) != 2:
        raise ValueError(f"--tiles expects RxC (e.g. 4x4), got {spec!r}")
    rows, cols = int(parts[0]), int(parts[1])
    if rows < MIN_TILES_AXIS or cols < MIN_TILES_AXIS:
        raise ValueError(
            f"--tiles rows and cols must be >= {MIN_TILES_AXIS} (got {spec!r})"
        )
    return (rows, cols)


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
    parser.add_argument(
        "--tiles",
        default=None,
        help=(
            "Per-region grid for the partially-empty advisory (#10319), as RxC "
            "(e.g. 4x4). Default: adaptive (~64px tiles). Advisory only, never "
            "trips --check."
        ),
    )
    args = parser.parse_args(argv)

    try:
        tiles = _parse_tiles(args.tiles)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
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
    # --check ne rougit QUE sur les findings bloquants (dim/taille, #6891). Les
    # advisory partially_empty_grid (#10319) sont rapportes mais non bloquants
    # (phase 1 : mesure du taux de FP avant tout blocage).
    blocking_hits = sum(
        1 for r in results for h in r["hits"] if h.get("severity") != "advisory"
    )
    advisory_hits = sum(
        1 for r in results for h in r["hits"] if h.get("severity") == "advisory"
    )
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

    if args.check and blocking_hits > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
