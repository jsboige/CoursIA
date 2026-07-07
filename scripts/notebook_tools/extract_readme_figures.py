"""extract_readme_figures - extrait les figures PNG des outputs de notebooks
vers ``<Serie>/assets/readme/`` + trace la provenance dans ``MANIFEST.md``.

EPIC #5654 (illustration des READMEs, P0 outillage). La doctrine #5654 fixe
trois sources d'images pour aerer les READMEs, par ordre de preference :
figures extraites des outputs de notebooks (source par defaut, celle-ci),
images generees par le pipeline GenAI, captures d'ecran. Ce module outille la
source 1 : le gisement des figures DEJA commitees comme preuve d'execution
des notebooks (~150 notebooks porteurs, inventaire ai-01 2026-07-07).

Deux modes (alignes sur le body de l'EPIC) :

  - :func:`list_figures` - inventorie les outputs ``image/png`` des notebooks
    d'une serie (notebook, cellule, dimensions, poids estime). C'est le
    *gisement* pour choisir quelles figures illustrer en P1/P2 ; on ne committe
    aucune image a ce stade, seulement l'inventaire.
  - :func:`extract_figure` - extrait UNE figure d'une cellule donnee vers
    ``assets/readme/<nom>.png``, l'optimise (PIL si dispo : redimensionnement
    <= 1200px + compression), puis append l'entree ``MANIFEST.md`` (notebook
    source + index de cellule + alt-text FR obligatoire).

Regles HARD (#5654, non-negociables pour les PRs filles) :

  - **Emplacement** : ``MyIA.AI.Notebooks/<Serie>/assets/readme/`` (convention
    unique). Pas d'image a la racine du repo.
  - **Poids** : <= 200 KB/image, <= 1,5 MB/README. Pas de LFS. Si l'extraction
    brute depasse le plafond, PIL downscales (max 1200px) puis recompresses ;
    si PIL absent, l'extraction raw est ecrite + un avertissement demande une
    optimisation manuelle.
  - **Provenance tracee** : chaque ``assets/readme/`` contient un
    ``MANIFEST.md`` (fichier -> notebook source + cellule, source 1). Une image
    sans provenance = ``CHANGES_REQUESTED``.
  - **Alt-text FR descriptif** obligatoire (accessibilite).
  - **Jamais de re-execution de notebook juste pour une figure** (C.3) : on
    extrait des outputs DEJA committes. Si la figure souhaitee n'existe pas,
    c'est un enrichissement de notebook (PR separee) d'abord.
  - **CATALOG-STATUS byte-identiques** : ce module ne touche jamais aux
    READMEs ; il cree/append ``assets/readme/`` et ``MANIFEST.md`` uniquement.

Dependances : stdlib (``json``, ``base64``, ``pathlib``, ``struct``) pour
l'inventaire et l'extraction raw PNG ; :mod:`PIL` (Pillow) OPTIONNEL pour
l'optimisation (redimensionnement + compression). Un PNG se parse sans PIL
via son en-tete IHDR (octets 16-24 : largeur/hauteur big-endian).
Reference : EPIC #5654, mandat user 2026-07-07.
"""

from __future__ import annotations

import base64
import json
import re
from pathlib import Path
from typing import Iterator, List, Optional

# Plafonds poids (regles HARD #5654).
MAX_BYTES_DEFAULT: int = 200 * 1024       # 200 KB/image
MAX_DIM_DEFAULT: int = 1200               # downscale Pil au-dela (px, grand cote)
PNG_IHDR_WIDTH_OFFSET: int = 16           # offset octet du champ largeur IHDR
PNG_IHDR_HEIGHT_OFFSET: int = 20          # offset octet du champ hauteur IHDR
_PNG_MAGIC: bytes = b"\x89PNG\r\n\x1a\n"


# --------------------------------------------------------------------------- #
#  Parsing notebook + outputs (stdlib)                                        #
# --------------------------------------------------------------------------- #
def _iter_notebooks(root: Path) -> Iterator[Path]:
    """Yield les fichiers ``.ipynb`` d'une serie (exclut les checkpoints."""
    for p in sorted(root.rglob("*.ipynb")):
        if ".ipynb_checkpoints" in p.parts:
            continue
        yield p


def _load_notebook(path: Path) -> dict:
    """Charge un notebook en dict (JSON). Echec = JSONDecodeError propagee."""
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def _png_dimensions(raw: bytes) -> Optional[tuple]:
    """Largeur/hauteur d'un PNG depuis l'en-tete IHDR (stdlib, sans PIL).

    Retourne ``(width, height)`` ou ``None`` si la signature PNG est absente /
    l'en-tete est tronque. Le PNG commence par la magic (8 octets) puis IHDR
    (longueur 4 + type 4 + donnees dont largeur 4 + hauteur 4 BE).
    """
    if len(raw) < PNG_IHDR_HEIGHT_OFFSET + 4:
        return None
    if raw[:8] != _PNG_MAGIC:
        return None
    width = int.from_bytes(
        raw[PNG_IHDR_WIDTH_OFFSET:PNG_IHDR_WIDTH_OFFSET + 4], "big")
    height = int.from_bytes(
        raw[PNG_IHDR_HEIGHT_OFFSET:PNG_IHDR_HEIGHT_OFFSET + 4], "big")
    return width, height


def _cell_outputs(cell: dict) -> List[dict]:
    """Outputs d'une cellule (code uniquement ; markdown n'en a pas)."""
    if cell.get("cell_type") != "code":
        return []
    return cell.get("outputs", []) or []


def _png_output_bytes(output: dict) -> Optional[bytes]:
    """Bytes PNG d'un output si celui-ci porte du ``image/png`` (base64).

    Couvre les outputs ``display_data`` et ``execute_result`` (cle ``data``)
    ainsi que ``error``/``stream`` (ignores). Retourne ``None`` si pas de PNG.
    """
    data = output.get("data", {})
    b64 = data.get("image/png")
    if not b64:
        return None
    if isinstance(b64, list):           # nbformat : source-like (rare pour data)
        b64 = "".join(b64)
    try:
        return base64.b64decode(b64)
    except (ValueError, base64.binascii.Error):
        return None


def _figure_records(notebook_path: Path, nb: dict) -> List[dict]:
    """Tous les records de figures PNG d'un notebook.

    Un record = ``{notebook, cell_index, output_index, width, height, bytes}``.
    Plusieurs outputs d'une meme cellule donnent plusieurs records (l'index
    d'output les differencie). Les dimensions sont lues via IHDR (sans PIL) ;
    si le PNG est malforme, ``width``/``height`` sont ``None``.
    """
    records: List[dict] = []
    for cell_index, cell in enumerate(nb.get("cells", [])):
        for output_index, output in enumerate(_cell_outputs(cell)):
            raw = _png_output_bytes(output)
            if raw is None:
                continue
            dims = _png_dimensions(raw)
            records.append({
                "notebook": str(notebook_path),
                "cell_index": cell_index,
                "output_index": output_index,
                "width": dims[0] if dims else None,
                "height": dims[1] if dims else None,
                "bytes": len(raw),
            })
    return records


# --------------------------------------------------------------------------- #
#  Resolution de path (repo-relatif / serie-relatif / absolu)                 #
# --------------------------------------------------------------------------- #
def resolve_repo_path(arg, repo_root, notebooks_subdir="MyIA.AI.Notebooks") -> Path:
    """Resout un path notebook/serie robuste quel que soit le cwd de l'appelant.

    ``arg`` peut etre :

      - un **path absolu** (``/d/dev/.../RL/x.ipynb``) -> retourne tel quel ;
      - un **path repo-relatif complet** (``MyIA.AI.Notebooks/RL/x.ipynb``) ->
        retourne ``repo_root / arg`` (existe sur disque, on ne double PAS le
        prefixe) ;
      - un **path serie-relatif** (``RL/x.ipynb``) -> retourne
        ``repo_root / notebooks_subdir / arg`` (prefixage convention).

    On essaie d'abord ``repo_root / arg`` : s'il existe, c'est un repo-relatif
    complet (pas de double-prefixe). Sinon, on prefixe ``notebooks_subdir``.
    Rend le CLI robuste invoque depuis la racine du repo OU depuis
    ``MyIA.AI.Notebooks/`` (cross-review F2, po-2026).

    ``notebooks_subdir`` : sous-repertoire des series (defaut
    ``MyIA.AI.Notebooks``). Retourne un :class:`~pathlib.Path` absolu resolu.
    """
    p = Path(arg)
    if p.is_absolute():
        return p
    candidate = Path(repo_root) / arg
    if candidate.exists():
        return candidate.resolve()
    return (Path(repo_root) / notebooks_subdir / arg).resolve()


# --------------------------------------------------------------------------- #
#  Mode 1 : inventaire (--list)                                               #
# --------------------------------------------------------------------------- #
def list_figures(serie_path, relative_to=None) -> dict:
    """Inventorie les figures PNG des notebooks d'une serie.

    ``serie_path`` : chemin de la serie (ex. ``MyIA.AI.Notebooks/RL``). Parcourt
    recursivement les ``.ipynb`` (hors checkpoints) et collecte tous les
    outputs ``image/png`` committes. Retourne un dict :

    ::

        {
          "serie": "<nom>",
          "root": "<chemin>",
          "n_notebooks_with_figures": int,
          "n_figures": int,
          "total_bytes": int,
          "figures": [ <record>, ... ],     # records tries par notebook puis cellule
        }

    C'est le *gisement* pour choisir les figures a illustrer (P1/P2) ; aucun
    fichier n'est ecrit. Les records au-dela du plafond poids (200 KB) sont
    marques ``"over_weight": True`` pour orienter l'optimisation a l'extraction.

    ``relative_to`` : si fourni, les chemins ``notebook`` des records et le
    champ ``root`` sont relativises a ce repertoire (avec separateurs POSIX).
    Utilise pour produire des inventaires portables (committes) ; par defaut
    (``None``) les chemins sont laisses tels que resolus par l'appelant.
    """
    root = Path(serie_path)
    if not root.is_dir():
        raise FileNotFoundError(f"Serie introuvable : {serie_path}")
    base = Path(relative_to) if relative_to is not None else None

    def _rel(path: Path) -> str:
        if base is None:
            return str(path)
        try:
            return str(path.resolve().relative_to(base.resolve())).replace("\\", "/")
        except ValueError:
            return str(path)

    figures: List[dict] = []
    for nb_path in _iter_notebooks(root):
        try:
            nb = _load_notebook(nb_path)
        except (json.JSONDecodeError, OSError):
            continue
        for rec in _figure_records(nb_path, nb):
            rec["notebook"] = _rel(nb_path)
            rec["over_weight"] = rec["bytes"] > MAX_BYTES_DEFAULT
            figures.append(rec)
    figures.sort(key=lambda r: (r["notebook"], r["cell_index"], r["output_index"]))
    notebooks_with = {r["notebook"] for r in figures}
    return {
        "serie": root.name,
        "root": _rel(root),
        "n_notebooks_with_figures": len(notebooks_with),
        "n_figures": len(figures),
        "total_bytes": sum(r["bytes"] for r in figures),
        "figures": figures,
    }


# --------------------------------------------------------------------------- #
#  Mode 2 : extraction (--extract) + optimisation + MANIFEST                  #
# --------------------------------------------------------------------------- #
def _optimize_with_pil(raw: bytes, max_dim: int) -> tuple:
    """Optimise un PNG avec PIL : downscale (grand cote <= max_dim) + recompression.

    Retourne ``(optimized_bytes, used_pil)``. Si PIL est absent, retourne la
    raw a l'identique + ``used_pil=False`` (l'appelant avertit pour optimisation
    manuelle). Ne leve jamais : une erreur PIL retombe sur la raw.
    """
    try:
        from PIL import Image                  # import local (optionnel)
        import io
        img = Image.open(io.BytesIO(raw))
        if img.mode in ("RGBA", "LA") and img.mode != "RGBA":
            img = img.convert("RGBA")
        w, h = img.size
        scale = min(1.0, max_dim / max(w, h)) if max(w, h) > 0 else 1.0
        if scale < 1.0:
            img = img.resize(
                (max(1, int(w * scale)), max(1, int(h * scale))),
                Image.LANCZOS,
            )
        buf = io.BytesIO()
        img.save(buf, format="PNG", optimize=True)
        out = buf.getvalue()
        # On ne retient l'optimise que s'il est effectivement plus leger.
        return (out, True) if len(out) < len(raw) else (raw, True)
    except Exception:
        return raw, False


def extract_figure(nb_path, cell_index: int, output_index: int,
                   output_path, alt_text_fr: str,
                   max_dim: int = MAX_DIM_DEFAULT,
                   max_bytes: int = MAX_BYTES_DEFAULT,
                   serie_root=None) -> dict:
    """Extrait une figure PNG d'une cellule de notebook vers ``assets/readme/``.

    Lit le PNG a l'index ``(cell_index, output_index)`` du notebook, l'optimise
    (PIL : downscale <= ``max_dim`` + compression, dans la limite de
    ``max_bytes``), l'ecrit dans ``output_path``, puis append l'entree
    ``MANIFEST.md`` a cote (provenance source 1 : notebook + cellule + alt-text).

    ``alt_text_fr`` est obligatoire (regle HARD accessibilite #5654) ; une
    chaine vide leve :class:`ValueError`.

    ``serie_root`` (optionnel) : si fourni, le chemin relatif du notebook dans
    le manifest est calcule depuis cette racine (plus lisible). Sinon, chemin
    absolu.

    Retourne le record d'extraction :

    ::

        {
          "output": "<chemin png ecrit>",
          "notebook": "<source>",
          "cell_index": int, "output_index": int,
          "bytes": int, "used_pil": bool, "over_weight": bool,
        }

    Leve :class:`ValueError` si la cellule/output n'existe pas ou ne porte pas
    de PNG, ou si ``alt_text_fr`` est vide.
    """
    if not alt_text_fr or not alt_text_fr.strip():
        raise ValueError("alt_text_fr obligatoire (accessibilite, regle #5654)")
    nb_path = Path(nb_path)
    nb = _load_notebook(nb_path)
    cells = nb.get("cells", [])
    if cell_index < 0 or cell_index >= len(cells):
        raise ValueError(
            f"cell_index {cell_index} hors plage (0..{len(cells) - 1})")
    outputs = _cell_outputs(cells[cell_index])
    if output_index < 0 or output_index >= len(outputs):
        raise ValueError(
            f"output_index {output_index} hors plage "
            f"(cellule {cell_index} a {len(outputs)} outputs)")
    raw = _png_output_bytes(outputs[output_index])
    if raw is None:
        raise ValueError(
            f"La cellule {cell_index} output {output_index} ne porte pas de PNG")

    optimized, used_pil = _optimize_with_pil(raw, max_dim)
    out_path = Path(output_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "wb") as fh:
        fh.write(optimized)

    entry = {
        "output": str(out_path),
        "notebook": str(nb_path),
        "cell_index": cell_index,
        "output_index": output_index,
        "bytes": len(optimized),
        "used_pil": used_pil,
        "over_weight": len(optimized) > max_bytes,
    }
    _append_manifest(out_path.parent, entry, alt_text_fr, serie_root)
    return entry


def _append_manifest(assets_dir, entry: dict, alt_text_fr: str,
                     serie_root=None) -> None:
    """Append une entree de provenance au ``MANIFEST.md`` de ``assets_dir``.

    Format source 1 (extraction de notebook) :

    ::

        ## <filename>.png

        - **Source** : notebook `<relpath>` (cellule N, output M)
        - **Alt-text (FR)** : <alt_text_fr>
        - **Poids** : NN KB (PIL optimise / raw)

    Idempotent : si une entree pour le meme fichier existe deja (meme nom de
    section), elle est remplacee (evite les doublons sur re-extraction).
    """
    assets_dir = Path(assets_dir)
    assets_dir.mkdir(parents=True, exist_ok=True)
    manifest = assets_dir / "MANIFEST.md"
    fname = Path(entry["output"]).name
    nb_path = Path(entry["notebook"])
    if serie_root is not None:
        try:
            rel = nb_path.relative_to(Path(serie_root))
            src_display = str(rel).replace("\\", "/")
        except ValueError:
            src_display = str(nb_path)
    else:
        src_display = str(nb_path)
    weight_kb = entry["bytes"] / 1024.0
    optimized_tag = "PIL optimise" if entry["used_pil"] else "raw (PIL absent)"
    block = (
        f"## {fname}\n\n"
        f"- **Source** : notebook `{src_display}` "
        f"(cellule {entry['cell_index']}, output {entry['output_index']})\n"
        f"- **Alt-text (FR)** : {alt_text_fr}\n"
        f"- **Poids** : {weight_kb:.1f} KB ({optimized_tag})\n"
    )
    existing = manifest.read_text(encoding="utf-8") if manifest.exists() else ""
    header = (
        "# MANIFEST des figures README\n\n"
        "Provenance des images de `assets/readme/` "
        "(EPIC #5654, source 1 = extraction d'outputs de notebooks).\n\n"
    )
    if not existing.strip():
        manifest.write_text(header + block, encoding="utf-8")
        return
    # Remplace un bloc existant pour ce fichier (regex ancrée sur le nom).
    pattern = re.compile(
        r"^## " + re.escape(fname) + r"\n.*?(?=\n## |\Z)",
        flags=re.DOTALL | re.MULTILINE,
    )
    if pattern.search(existing):
        new_body = pattern.sub(block.rstrip("\n"), existing)
    else:
        new_body = existing.rstrip("\n") + "\n\n" + block
    # Preserve le header si deja present, sinon l'ajoute (cas fichier sans header).
    if "# MANIFEST des figures README" not in new_body:
        new_body = header + new_body
    manifest.write_text(new_body, encoding="utf-8")
