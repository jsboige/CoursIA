#!/usr/bin/env python3
r"""Detecte une sortie riche (SVG) IMPRIMEE EN TEXTE au lieu d'etre rendue.

Pourquoi cet outil existe
-------------------------
Concern user du 16/11/2026 a 09:59Z sur la PR #26921 (Dynamics-03 C#) :
« le svg n'est pas affiché dans le notebook. Prévoir l'organe au CI qui
attrape le défaut. »

Vérification du coordinateur a la tete `f28443ae` : la cellule 9 ecrit le
SVG sur la **sortie standard**, sous forme de sortie `stream`
(`name: stdout`). Le carnet montre donc le texte balisé `<svg …>…</svg>`, et
non l'image. Aucune garde ne le voyait :

  * `execution_count` est renseigne, aucune erreur n'est levee ;
  * les ratchets de sortie mesurent le VOLUME, pas le type MIME ;
  * les quatre detecteurs SVG existants (broken-geometry, decimal-commas,
    empty-display, offscreen-flat) verifient la GEOMETRIE du SVG emis, pas
    son support ;
  * `detect_svg_html_only.py` (#26783) attrape le SVG qui ne vit qu'en
    `text/html` -- un mime riche, donc deja rendu. Le cas d'ici est
    different : le SVG n'a **aucun** mime riche, il est **du texte**.

Ce que l'outil DETECTE (DETERMINISTE)
-------------------------------------
Pour chaque cellule de code d'un notebook :

  1. la sortie porte un payload **textuel** (`stream`, ou `text/plain` d'un
     `display_data` / `execute_result`) qui contient un element `<svg …>`
     **ferme** (`</svg>`) ;
  2. et le bundle ne porte **ni** `image/svg+xml` **ni** `image/png` : une
     sortie qui presente une representation native est rendue, elle n'est
     pas un defaut.

Zero faux-positif par construction sur les sorties rendues : un SVG
doublé d'`image/svg+xml` (le fix cible) ou accompagne d'un fallback
`image/png` n'est pas flagge. Une chaine qui contient le mot « svg » sans
balise n'est pas flaggee non plus -- et un `<svg …>` **non ferme** ne l'est
pas davantage : l'element doit etre complet.

Ce qu'il NE corrige PAS
-----------------------
Il DETECTE, il ne CORRIGE PAS. Recettes de correction (a verifier sur carnet
reel avant de les figer ailleurs -- la re-execution reelle reste due, C.2) :

  - .NET Interactive : `Console.WriteLine(svgString)` ->
    `svgString.DisplayAs("image/svg+xml")` ;
  - Python : `print(svg_string)` -> `display(SVG(svg_string))`.

Stop & Repair : corriger la cellule source puis RE-EXECUTER le kernel, jamais
editer la sortie a la main (secrets-hygiene regle 6).

Statut du ratchet : **ADVISORY d'abord** (branchement `blocking=False` dans
`fast_lane_registry.py`, precedent Source-collapse #15901 et
`detect_svg_html_only.py`). Le stock de main n'est pas juge : seule une
**hausse** du compte sur la branche est signalee. Une sortie d'archive
reprise telle quelle ne bloque pas.

Modes
-----
  census  : `check_rich_output_as_text.py [NB.ipynb | --family F]` --
            inventaire (toutes les occurrences, stock de main compris) ;
  ratchet : `check_rich_output_as_text.py <base_ref>` -- notebooks changes
            (ACMR vs merge-base), **AJOUTS SEULS** juges ;
  self    : `--self-test` -- controles positif/negatif + replay du cas
            fondateur (#26921 a `f28443ae`).

Usage
-----
    python check_rich_output_as_text.py NB.ipynb            # census d'un carnet
    python check_rich_output_as_text.py --family Probas     # census d'une famille
    python check_rich_output_as_text.py                     # census de tout main
    python check_rich_output_as_text.py NB.ipynb --json     # sortie machine
    python check_rich_output_as_text.py origin/main         # ratchet ajouts-seuls
    python check_rich_output_as_text.py --self-test         # controles + replay

Exit codes
----------
    0 -- aucune occurrence (census) / aucun ajout (ratchet) / self-test OK
    1 -- occurrences (census --check) / ajoutes (ratchet) / self-test KO
    2 -- erreur (notebook illisible, ref git introuvable, famille absente)

Voir aussi
----------
- #26979 -- l'issue qui porte l'organe (Concern user + mandat).
- detect_svg_html_only.py (#26783) -- le complement : le SVG est dans un
  mime riche (`text/html`), donc rendu par les surfaces qui le supportent ;
  celui-ci attrape « le SVG est du texte ».
- detect_svg_empty_display.py (#6971) -- l'AUTRE moitie du rendu : la cellule
  n'emet AUCUN output.
- check_output_failure_text.py (#11685) -- le lecteur partage (notebooks
  modifies, base/head, renommages) : il est **importe**, jamais recopie.

See #26979 (organe) + #26921 (Concern fondateur).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

# Le lecteur partage (#11685) : stdlib seul, expose la lecture base/head, les
# notebooks modifies et les renommages. Il est IMPORTE, jamais recopie
# (organe d'abord -- regle `organ-first-implementation`).
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_output_failure_text import (  # noqa: E402
    changed_notebooks,
    git,
    read_notebook_at,
    renamed_notebooks,
)

#: Un element SVG **ferme**. L'ouverture seule (`<svg`) n'est pas un element :
#: une cellule qui imprime une balise isolee n'est pas un defaut d'affichage.
_SVG_ELEMENT_RE = re.compile(r"<svg\b[^>]*>.*?</svg\s*>", re.IGNORECASE | re.DOTALL)

#: Types MIME qui rendent le SVG sans passer par du texte : leur presence
#: dans le bundle exempte la sortie (meme contrat que #26783).
_REDEEMING_MIMES = ("image/svg+xml", "image/png")

#: Sorties porteuses d'un payload textuel juge.
_TEXT_STREAM_TYPES = ("stream",)
_TEXT_BUNDLE_TYPES = ("display_data", "execute_result")

EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")
BS = chr(92)


# ---------------------------------------------------------------------------
# Detection pure
# ---------------------------------------------------------------------------

def _payload_text(payload) -> str:
    """Join a JSON string-or-list mime payload into one string."""
    if isinstance(payload, list):
        return "".join(str(part) for part in payload)
    return str(payload)


def svg_as_text_outputs(nb: dict) -> list[dict]:
    """Occurrences du defaut dans un notebook, dans l'ordre des cellules.

    Chaque occurrence : {cell_index, cell_id, output_index, output_type,
    svg_bytes, svg_sha1} -- le sha1 sert de signature stable pour le diff
    base/head (une occurrence renumerotee ne doit pas compter comme un
    ajout).
    """
    hits = []
    for ci, cell in enumerate(nb.get("cells", []) or []):
        if cell.get("cell_type") != "code":
            continue
        for oi, out in enumerate(cell.get("outputs", []) or []):
            if not isinstance(out, dict):
                continue
            otype = out.get("output_type")
            if otype in _TEXT_STREAM_TYPES:
                payload = out.get("text")
            elif otype in _TEXT_BUNDLE_TYPES:
                data = out.get("data")
                if not isinstance(data, dict):
                    continue
                if any(m in data for m in _REDEEMING_MIMES):
                    continue  # rendu par une representation native : exempt
                payload = data.get("text/plain")
            else:
                continue
            if payload is None:
                continue
            texte = _payload_text(payload)
            match = _SVG_ELEMENT_RE.search(texte)
            if not match:
                continue
            element = match.group(0)
            hits.append({
                "cell_index": ci,
                "cell_id": cell.get("id"),
                "output_index": oi,
                "output_type": otype,
                "svg_bytes": len(element),
                "svg_sha1": hashlib.sha1(
                    element.encode("utf-8")).hexdigest()[:12],
            })
    return hits


def scan_notebook(path: Path) -> dict:
    """Census d'un notebook : toutes les occurrences, stock compris."""
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": []}
    return {"path": str(path), "hits": svg_as_text_outputs(nb),
            "error": None}


def _iter_census_paths(root: Path, family: str | None, notebook: str | None):
    if notebook:
        p = Path(notebook)
        if not p.is_absolute():
            p = root / p
        return [p]
    from notebook_walk import iter_notebooks  # noqa: PLC0415 (usage local)
    return list(iter_notebooks(root / "MyIA.AI.Notebooks", family=family))


# ---------------------------------------------------------------------------
# Ratchet base-vs-PR : ajouts seuls, le stock de base n'est pas juge.
# ---------------------------------------------------------------------------

def resolve_base(base: str, cwd=None) -> str:
    """Resolve `base` to merge-base(base, HEAD), repli sur base."""
    out = git("merge-base", base, "HEAD", cwd=cwd)
    return out.strip() if out and out.strip() else base


def _worktree_path(path: str, cwd=None) -> Path:
    """Le chemin du carnet dans l'ARBRE DE TRAVAIL, resolu.

    Le lecteur partage lit l'arbre de travail depuis le **processus** cwd
    (relatif), pas depuis le `cwd` du depot : dans un appel a `ratchet()`
    avec un depot different (un test sur un depot jetable), la lecture
    porterait sur le mauvais repertoire et rendrait ZERO occurrence -- un
    vert muet. On resout donc le chemin contre la racine du depot.
    """
    base = Path(cwd) if cwd else Path(__file__).resolve().parents[2]
    p = Path(path)
    return p if p.is_absolute() else base / p


def ratchet(base: str, cwd=None) -> dict:
    """Ajouts seuls : occurrences a HEAD absentes de la base, par carnet.

    Cle d'occurrence : (cell_id, svg_sha1). Un carnet NOUVEAU n'a pas de base :
    toutes ses occurrences sont des ajouts. Un carnet RENOMME, lui, a une
    base -- a son ancien chemin (``renamed_notebooks``), sans quoi le
    renommage compte comme ajouts.
    """
    base = resolve_base(base, cwd=cwd)
    paths = changed_notebooks(base, cwd=cwd)
    renames = renamed_notebooks(base, cwd=cwd)
    rows, total = [], 0
    for path in paths:
        base_nb = read_notebook_at(base, renames.get(path, path), cwd=cwd)
        head_nb = read_notebook_at(None, str(_worktree_path(path, cwd)),
                                   cwd=cwd)
        if head_nb is None:
            continue
        head_hits = svg_as_text_outputs(head_nb)
        base_keys = set()
        if base_nb is not None:
            base_keys = {(h["cell_id"], h["svg_sha1"])
                         for h in svg_as_text_outputs(base_nb)}
        added = [h for h in head_hits
                 if (h["cell_id"], h["svg_sha1"]) not in base_keys]
        if added:
            rows.append({"notebook": path, "added": added,
                         "stock_at_base": len(base_keys)})
            total += len(added)
    return {"base": base, "notebooks_changed": len(paths),
            "notebooks_flagged": len(rows), "added_total": total, "rows": rows}


# ---------------------------------------------------------------------------
# Self-test : controles positif/negatif + replay du cas fondateur (#26921).
# ---------------------------------------------------------------------------

_SVG = ("<svg xmlns='http://www.w3.org/2000/svg' width='800' height='360'>"
        "<rect width='800' height='360' fill='white'/></svg>")


def _nb(outputs_by_cell: dict) -> dict:
    cells = []
    for cell_id, outputs in outputs_by_cell.items():
        cells.append({"cell_type": "code", "id": cell_id, "source": "x = 1",
                      "outputs": outputs, "execution_count": 1})
    return {"cells": cells, "metadata": {"kernelspec": {"name": ".net-csharp"}}}


def _stream(text: str, name: str = "stdout") -> dict:
    return {"output_type": "stream", "name": name, "text": text}


def _out(data: dict, otype: str = "display_data") -> dict:
    return {"output_type": otype, "data": data}


def self_test() -> list[str]:
    """Controles positif/negatif + replay du cas fondateur. Liste d'echecs."""
    failures = []

    def _hits(outputs_by_cell):
        return svg_as_text_outputs(_nb(outputs_by_cell))

    # 1. CONTROLE POSITIF -- le cas fondateur : le SVG ecrit sur stdout.
    hits = _hits({"c9": [_stream(_SVG)]})
    if not hits:
        failures.append("positive control (svg printed as text) NOT flagged")
    else:
        if hits[0]["cell_id"] != "c9":
            failures.append("positive control: wrong cell id "
                            + repr(hits[0].get("cell_id")))
        if hits[0]["output_type"] != "stream":
            failures.append("positive control: wrong output type "
                            + repr(hits[0].get("output_type")))

    # 2. NEGATIF -- un SVG rendu par image/svg+xml : rien a signaler.
    if _hits({"c1": [_out({"image/svg+xml": _SVG,
                           "text/plain": _SVG})]}):
        failures.append("image/svg+xml output flagged (must be exempt)")

    # 3. NEGATIF -- un fallback image/png : rien a signaler.
    if _hits({"c1": [_out({"image/png": "iVBORw0KGgo=",
                           "text/plain": _SVG})]}):
        failures.append("image/png fallback flagged (must be exempt)")

    # 4. NEGATIF -- une chaine qui contient le mot « svg » sans balise.
    if _hits({"c1": [_stream("le mot svg apparait ici, sans balise")]}):
        failures.append("plain word 'svg' flagged (must be exempt)")

    # 5. NEGATIF -- une balise ouverte SANS fermeture : pas un element.
    if _hits({"c1": [_stream("<svg width='10' height='10'>")]}):
        failures.append("unclosed <svg> flagged (must be exempt)")

    # 6. REPLAY du cas fondateur reel (#26921 a f28443ae, cellule 9). Le
    # commit peut etre absent du clone : le replay est alors SKIPPE et
    # signale, jamais silencieusement passe.
    nb_26921 = ("MyIA.AI.Notebooks/GameTheory/Dynamics/"
                "Dynamics-03-Sympathie-vs-Engagement-CSharp.ipynb")
    sha_26921 = "f28443aed00639ca75038235de986fcae1819779"
    if git("cat-file", "-e", sha_26921) is None:
        print("SKIP #26921 replay: " + sha_26921[:12] + " not in this clone")
    else:
        nb = read_notebook_at(sha_26921, nb_26921)
        if nb is None:
            failures.append("#26921 replay: notebook unreadable at "
                            + sha_26921[:12])
        else:
            hits = svg_as_text_outputs(nb)
            if not hits:
                failures.append("#26921 replay: the founding notebook is NOT "
                                "flagged (the detector does not fire)")
            elif hits[0]["cell_index"] != 9:
                failures.append("#26921 replay: first occurrence at cell "
                                + str(hits[0]["cell_index"]) + " (expected 9)")
            else:
                print("replay #26921: " + str(len(hits)) + " occurrence(s), "
                      "first at cell " + str(hits[0]["cell_index"]))
    return failures


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _series_of(path: str) -> str:
    """La serie d'un carnet : les deux segments apres MyIA.AI.Notebooks/."""
    parts = path.replace(BS, "/").split("/")
    if "MyIA.AI.Notebooks" in parts:
        rest = parts[parts.index("MyIA.AI.Notebooks") + 1:]
        if len(rest) >= 2:
            return rest[0] + "/" + rest[1]
    return "(hors serie)"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Detecte un SVG IMPRIME EN TEXTE dans les sorties "
                    "commitees des carnets.")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (mode ratchet : ajouts seuls)")
    ap.add_argument("notebook", nargs="?",
                    help="Census d'un carnet (mode census)")
    ap.add_argument("--family", default=None,
                    help="Census d'une famille de carnets")
    ap.add_argument("--check", action="store_true",
                    help="Census : exit 1 si occurrence trouvee")
    ap.add_argument("--self-test", action="store_true",
                    help="Controles positif/negatif + replay #26921")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    root = Path(__file__).resolve().parents[2]

    if args.self_test:
        failures = self_test()
        for f in failures:
            print("SELF-TEST FAIL: " + f)
        if failures:
            return 1
        print("SELF-TEST OK: controls matched, benign text silent, "
              "replay fired")
        return 0

    if args.base and not args.notebook:
        report = ratchet(args.base)
        if args.as_json:
            print(json.dumps(report, indent=2, ensure_ascii=False))
        else:
            print("RATCHET (ajouts seuls) base=" + str(report["base"])
                  + " | carnets modifies=" + str(report["notebooks_changed"])
                  + " | carnets signales=" + str(report["notebooks_flagged"])
                  + " | ajouts=" + str(report["added_total"]))
            for row in report["rows"]:
                print("  " + row["notebook"] + " : "
                      + str(len(row["added"])) + " ajout(s)")
        return 1 if report["added_total"] else 0

    paths = _iter_census_paths(root, args.family, args.notebook)
    rows = []
    total = 0
    for path in paths:
        found = scan_notebook(path)
        if found["hits"]:
            rel = found["path"]
            rows.append({
                "notebook": rel,
                "series": _series_of(rel),
                "hits": found["hits"],
            })
            total += len(found["hits"])
    par_serie: dict[str, int] = {}
    for row in rows:
        par_serie[row["series"]] = par_serie.get(row["series"], 0) + len(
            row["hits"])
    if args.as_json:
        print(json.dumps({"mode": "census", "notebooks": len(rows),
                          "occurrences": total,
                          "by_series": par_serie, "rows": rows},
                         indent=2, ensure_ascii=False))
    else:
        print("CENSUS : " + str(len(rows)) + " carnet(s), "
              + str(total) + " occurrence(s) SVG_AS_TEXT")
        for serie, n in sorted(par_serie.items(), key=lambda kv: -kv[1]):
            print("  " + serie + " : " + str(n))
        for row in rows:
            print("  " + row["notebook"] + " : "
                  + str(len(row["hits"])) + " cellule(s) ["
                  + ", ".join(str(h["cell_index"]) for h in row["hits"]) + "]")
    if args.check and total:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
