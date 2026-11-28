#!/usr/bin/env python3
r"""Detecte les sorties dont le SVG ne vit qu'en text/html, sans image/svg+xml.

Pourquoi cet outil existe
-------------------------
Concern user (#26613, 14/11 22:37Z) : « Le SVG n'est pas affiche ». Hypothese
d'origine (ai-01) : un `<svg>` emis seulement en `text/html` ne serait pas rendu
par GitHub. L'etape 0 de #26783 (capture d'ecran par un agent qui voit, DOM
cross-checke) a REFUTE cette hypothese sur la surface blob/viewer pour les deux
carnets tests (tete de #26613 : 4 SVG text/html-seul rendus a 776x349 ;
Infer-07 sur main : 6 SVG text/html-seul rendus) ; la surface Files changed est
restee inobservable en sonde anonyme (diffs .ipynb bloques a « Loading »).

La classe reste un deficit de PORTABILITE reel : l'affichage d'un SVG inline
depend de la surface de rendu (viewer GitHub, rich diff de PR, nbviewer, VS
Code, exports HTML ne sanitizent pas `text/html` pareil), et 198 sorties en
`text/html` seul vivent sur main (87 carnets, 54 en C#). Le doublage
`image/svg+xml` est l'amelioration mecanique claire : c'est le type MIME prevu
pour un SVG, rendu par toute surface qui rend les notebooks.

Les quatre detecteurs SVG existants (broken-geometry, decimal-commas,
empty-display, offscreen-flat) verifient la GEOMETRIE du SVG emis, pas son type
MIME : cette classe leur est invisible par construction.

Ce que l'outil DETECTE (DETERMINISTE)
-------------------------------------
Pour chaque sortie `display_data` / `execute_result` d'un notebook :

  1. le mime bundle contient `text/html` dont le payload contient `<svg` ; ET
  2. le mime bundle ne contient NI `image/svg+xml` NI `image/png`.

Zero faux-positif par construction sur les sorties doubled : un SVG double de
`image/svg+xml` (le fix cible) ou accompagne d'un fallback `image/png`
(Plotly-classique) n'est pas flagge -- le SVG a alors une representation que
toute surface rend.

Ce qu'il NE corrige PAS
-----------------------
Il DETECTE, il ne CORRIGE PAS. Recettes de correction (a verifier sur carnet
reel avant de les figer ailleurs -- la re-execution reelle reste due, C.2) :

  - .NET Interactive : `display(HTML(svgString))` ->
    `svgString.DisplayAs("image/svg+xml")` ;
  - Python : `display(HTML(svgString))` ->
    `display(IPython.display.SVG(svgString))`.

Stop & Repair : corriger la cellule source puis RE-EXECUTER le kernel, jamais
editer la sortie a la main (secrets-hygiene regle 6).

Statut du ratchet : ADVISORY d'abord (branchement `blocking=False`,
`fast_lane_registry.py`, precedent Source-collapse #15901). L'etape 0 n'a pas
demontre le defaut VISUEL sur une surface identifiee : un gate bloquant sur un
defaut non demontre est interdit (gate-fp). Une capture AUTHENTIFIEE de la
surface Files changed montrant le SVG absent fait basculer le garde en
bloquant -- un commit d'une ligne, sans refonte.

Modes
-----
  census  : `detect_svg_html_only.py [NB.ipynb | --family F]` -- inventaire
            (toutes les occurrences, stock de main compris) ;
  ratchet : `detect_svg_html_only.py <base_ref>` -- notebooks changes
            (ACMR vs merge-base), AJOUTS SEULS juges : une occurrence presente
            a la base n'est pas re-flaggee (le stock de main n'est pas juge,
            contrat de l'issue #26783) ;
  self    : `--self-test` -- controles positif/negatif + replay du cas
            fondateur (un detecteur qu'on ne peut pas faire tirer est
            indiscernable d'un detecteur debranche).

Usage
-----
    python detect_svg_html_only.py NB.ipynb            # census d'un carnet
    python detect_svg_html_only.py --family Probas     # census d'une famille
    python detect_svg_html_only.py                     # census de tout main
    python detect_svg_html_only.py NB.ipynb --json     # sortie machine
    python detect_svg_html_only.py origin/main         # ratchet ajouts-seuls
    python detect_svg_html_only.py --self-test         # controles + replay

Exit codes
----------
    0 -- aucune occurrence (census) / aucun ajout (ratchet) / self-test OK
    1 -- occurrences (census --check) / ajoutes (ratchet) / self-test KO
    2 -- erreur (notebook illisible, ref git introuvable, famille absente)

Voir aussi
----------
- #26783 -- l'issue qui porte l'organe (etape 0, fournees par famille).
- detect_svg_empty_display.py (#6971) -- l'AUTRE moitie du rendu : la cellule
  display() un chart mais n'emet AUCUN output. Celui-ci attrape « le chart est
  emis mais seulement en text/html », celui-la « le chart n'est pas emis ».
- check_source_collapse.py (#15901) -- le precedent de branchement advisory
  d'un ratchet natif base-vs-PR avec self-test.

See #26783 (organe) + #26613 (Concern fondateur).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

# Un bloc <svg ...> dans un payload (meme regex que les detecteurs soeurs).
_SVG_RE = re.compile(r"<svg\b", re.IGNORECASE)

# Types MIME qui rendent un SVG independamment du sanitizer text/html : leur
# presence dans le bundle exempte la sortie (contrat #26783 : pas de faux
# positif sur un SVG doubled image/svg+xml OU accompagne d'un image/png).
_REDEEMING_MIMES = ("image/svg+xml", "image/png")

# Sorties jugees : celles qui portent un mime bundle riche.
_JUDGED_OUTPUT_TYPES = ("display_data", "execute_result")

EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")
BS = chr(92)


def git(*args, cwd=None):
    """Run a git command, returning stdout (utf-8) or None on failure."""
    try:
        out = subprocess.run(["git", "-c", "core.quotePath=false", *args], cwd=cwd, capture_output=True,
                             encoding="utf-8", errors="replace", check=False)
    except OSError:
        return None
    if out.returncode != 0:
        return None
    return out.stdout


def _payload_text(payload) -> str:
    """Join a JSON string-or-list mime payload into one string."""
    if isinstance(payload, list):
        return "".join(str(part) for part in payload)
    return str(payload)


def svg_html_only_outputs(nb: dict) -> list[dict]:
    """Occurrences du defaut dans un notebook, dans l'ordre des cellules.

    Chaque occurrence : {cell_index, cell_id, output_index, output_type,
    svg_bytes} -- svg_bytes sert de signature stable pour le diff base/head.
    """
    hits = []
    for ci, cell in enumerate(nb.get("cells", []) or []):
        if cell.get("cell_type") != "code":
            continue
        for oi, out in enumerate(cell.get("outputs", []) or []):
            if not isinstance(out, dict):
                continue
            if out.get("output_type") not in _JUDGED_OUTPUT_TYPES:
                continue
            data = out.get("data", {})
            if not isinstance(data, dict):
                continue
            html = data.get("text/html")
            if html is None:
                continue
            if not _SVG_RE.search(_payload_text(html)):
                continue
            if any(m in data for m in _REDEEMING_MIMES):
                continue
            hits.append({
                "cell_index": ci,
                "cell_id": cell.get("id"),
                "output_index": oi,
                "output_type": out.get("output_type"),
                "svg_bytes": len(_payload_text(html)),
                "svg_sha1": hashlib.sha1(
                    _payload_text(html).encode("utf-8")).hexdigest()[:12],
            })
    return hits


def scan_notebook(path: Path) -> dict:
    """Census d'un notebook : toutes les occurrences, stock compris."""
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": str(path), "error": str(exc), "hits": []}
    return {"path": str(path), "hits": svg_html_only_outputs(nb),
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


def changed_notebooks(base: str, head: str = "HEAD", cwd=None) -> list[str]:
    """Notebooks added/copied/modified/renamed entre base et head."""
    out = git("diff", "--name-only", "--diff-filter=ACMR", base, head,
              "--", "*.ipynb", cwd=cwd)
    if out is None:
        return []
    paths = []
    for line in out.splitlines():
        posix = line.strip().replace(BS, "/")
        if posix and not any(m in "/" + posix for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def renamed_notebooks(base: str, head: str = "HEAD", cwd=None) -> dict:
    """{chemin tete: chemin base} pour les carnets RENOMMES.

    Organe autonome (imports stdlib seulement) : copie locale de la lecture
    partagee de check_output_failure_text.renamed_notebooks -- meme contrat,
    mesure fondatrice #26381. Sans cette resolution, le chemin de tete est
    absent de la base et un pur renommage de carnet porteur de SVG compte
    toutes ses occurrences comme des ajouts.
    """
    out = git("diff", "-M", "--name-status", "--diff-filter=R", base, head,
              "--", "*.ipynb", cwd=cwd)
    renames: dict[str, str] = {}
    if out is None:
        return renames
    for line in out.splitlines():
        parts = [p for p in line.split("\t") if p]
        if len(parts) == 3 and parts[0].startswith("R"):
            renames[parts[2].strip().replace(BS, "/")] = (
                parts[1].strip().replace(BS, "/"))
    return renames


def read_notebook_at(ref: str | None, path: str, cwd=None):
    """Notebook JSON a un ref git (None = arbre de travail), None si absent."""
    if ref is None:
        try:
            return json.loads(Path(path).read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return None
    raw = git("show", ref + ":" + path, cwd=cwd)
    if raw is None:
        return None
    try:
        return json.loads(raw)
    except ValueError:
        return None


def ratchet(base: str, cwd=None) -> dict:
    """Ajouts seuls : occurrences a HEAD absentes de la base, par notebook.

    Cle d'occurrence : (cell_id, svg_sha1). Un carnet NOUVEAU n'a pas de base :
    toutes ses occurrences sont des ajouts. Un carnet RENOMME, lui, a une base
    -- a son ancien chemin (``renamed_notebooks``), sans quoi le renommage
    compte comme ajouts. Le stock inchange n'est pas juge (contrat #26783 :
    « le stock de main n'est pas juge »).
    """
    base = resolve_base(base, cwd=cwd)
    paths = changed_notebooks(base, cwd=cwd)
    renames = renamed_notebooks(base, cwd=cwd)
    rows, total = [], 0
    for path in paths:
        base_nb = read_notebook_at(base, renames.get(path, path), cwd=cwd)
        head_nb = read_notebook_at(None, path, cwd=cwd)
        if head_nb is None:
            continue
        head_hits = svg_html_only_outputs(head_nb)
        base_keys = set()
        if base_nb is not None:
            base_keys = {(h["cell_id"], h["svg_sha1"])
                         for h in svg_html_only_outputs(base_nb)}
        added = [h for h in head_hits
                 if (h["cell_id"], h["svg_sha1"]) not in base_keys]
        if added:
            rows.append({"notebook": path, "added": added,
                         "stock_at_base": len(base_keys)})
            total += len(added)
    return {"base": base, "notebooks_changed": len(paths),
            "notebooks_flagged": len(rows), "added_total": total, "rows": rows}


# ---------------------------------------------------------------------------
# Self-test : controles positif/negatif + replay du cas fondateur (#26613).
# ---------------------------------------------------------------------------

_SVG = ("<svg xmlns='http://www.w3.org/2000/svg' width='800' height='360'>"
        "<rect width='800' height='360' fill='white'/></svg>")


def _nb(outputs_by_cell: dict) -> dict:
    cells = []
    for cell_id, outputs in outputs_by_cell.items():
        cells.append({"cell_type": "code", "id": cell_id, "source": "x = 1",
                      "outputs": outputs, "execution_count": 1})
    return {"cells": cells, "metadata": {"kernelspec": {"name": ".net-csharp"}}}


def _out(data: dict, otype: str = "display_data") -> dict:
    return {"output_type": otype, "data": data}


def self_test() -> list[str]:
    failures = []

    def _hits(outputs_by_cell):
        return svg_html_only_outputs(_nb(outputs_by_cell))

    # 1. CONTROLE POSITIF -- le cas fondateur : SVG seulement en text/html.
    hits = _hits({"c13": [_out({"text/html": _SVG})]})
    if not hits:
        failures.append("positive control (text/html-only svg) NOT flagged")
    # 2. negatif : SVG doubled image/svg+xml (le fix cible) -- exempt.
    if _hits({"c1": [_out({"text/html": _SVG,
                           "image/svg+xml": _SVG})]}):
        failures.append("doubled image/svg+xml flagged (must be exempt)")
    # 3. negatif : fallback image/png -- exempt (contrat #26783).
    if _hits({"c1": [_out({"text/html": _SVG,
                           "image/png": "iVBORw0KGgo="})]}):
        failures.append("image/png fallback flagged (must be exempt)")
    # 4. negatif : text/html sans <svg> -- hors scope.
    if _hits({"c1": [_out({"text/html": "<p>hello</p>"})]}):
        failures.append("text/html without svg flagged")
    # 5. negatif : sortie stream -- pas un mime bundle riche.
    if _hits({"c1": [{"output_type": "stream", "text": _SVG}]}):
        failures.append("stream output flagged")
    # 6. negatif : SVG en image/svg+xml SEUL -- representation native, exempt.
    if _hits({"c1": [_out({"image/svg+xml": _SVG})]}):
        failures.append("image/svg+xml-only flagged (must be exempt)")
    # 7. payload liste (serialization nbformat par fragments) -- meme verdict.
    if not _hits({"c1": [_out({"text/html": ["<div>", _SVG, "</div>"]})]}):
        failures.append("list-serialized text/html payload not flagged")
    # 8. execute_result -- juge comme display_data.
    if not _hits({"c1": [_out({"text/html": _SVG}, "execute_result")]}):
        failures.append("execute_result not flagged")

    # 9. REPLAY RATCHET -- ajout seul juge, stock exempt :
    #    base = 1 occurrence (cell a), head = meme occurrence + 1 nouvelle
    #    (cell b). Le ratchet doit rendre exactement l'ajout (cell b).
    base_nb = _nb({"a": [_out({"text/html": _SVG})]})
    head_nb = _nb({"a": [_out({"text/html": _SVG})],
                   "b": [_out({"text/html": _SVG.replace("800", "400")})]})
    base_keys = {(h["cell_id"], h["svg_sha1"])
                 for h in svg_html_only_outputs(base_nb)}
    head_hits = svg_html_only_outputs(head_nb)
    added = [h for h in head_hits
             if (h["cell_id"], h["svg_sha1"]) not in base_keys]
    if [h["cell_id"] for h in added] != ["b"]:
        failures.append("ratchet replay: added-only keying broken "
                        f"(got {[h['cell_id'] for h in added]})")
    if len(base_keys) != 1 or len(head_hits) != 2:
        failures.append("ratchet replay: census counts unexpected "
                        f"(base={len(base_keys)}, head={len(head_hits)})")
    # 10. REPLAY FONDATEUR (forme #26613) -- le SVG vit dans un text/html
    #     produit par du C# (StringBuilder), display(HTML(svg)) : flagge.
    z3_shape = ("<svg xmlns='http://www.w3.org/2000/svg' width='800'"
                " height='360'>generated by HistogramSvg</svg>")
    if not _hits({"c20": [_out({"text/html": z3_shape})]}):
        failures.append("founding-case shape (C# svg string) not flagged")

    return failures


def _human_census(results: list[dict]) -> str:
    total = sum(len(r["hits"]) for r in results)
    affected = [r for r in results if r["hits"]]
    lines = [
        f"Notebooks scanned : {len(results)}",
        f"html-only SVG outputs : {total}",
        f"Affected notebooks : {len(affected)}",
        "",
    ]
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}")
        for h in r["hits"]:
            lines.append(f"  - cell [{h['cell_index']}] ({h['cell_id']}) "
                         f"{h['output_type']} svg~{h['svg_bytes']}B "
                         f"sha1:{h['svg_sha1']}")
        lines.append("")
    lines.append(
        "FIX: emitter should also provide image/svg+xml -- .NET: "
        "`svgString.DisplayAs(\"image/svg+xml\")` instead of "
        "`display(HTML(svgString))`; Python: `display(SVG(svgString))` "
        "instead of `display(HTML(svgString))`. Then RE-EXECUTE the kernel "
        "(C.2) -- never hand-edit the committed output."
    )
    return "\n".join(lines)


def _human_ratchet(report: dict) -> str:
    lines = [
        f"Base (merge-base) : {report['base']}",
        f"Notebooks changed : {report['notebooks_changed']}",
        f"Notebooks flagged : {report['notebooks_flagged']}",
        f"ADDED html-only SVG outputs : {report['added_total']}",
        "",
    ]
    for row in report["rows"]:
        lines.append(f"## {row['notebook']} "
                     f"(stock at base: {row['stock_at_base']})")
        for h in row["added"]:
            lines.append(f"  - cell [{h['cell_index']}] ({h['cell_id']}) "
                         f"{h['output_type']} svg~{h['svg_bytes']}B")
        lines.append("")
    lines.append(
        "ADVISORY (#26783 etape 0) : le defaut visuel n'est pas demontre sur "
        "une surface identifiee -- le garde ne rougit pas la PR. Une capture "
        "authentifiee de Files changed montrant le SVG absent fait basculer "
        "le garde en bloquant (une ligne dans fast_lane_registry.py)."
    )
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook_or_base", nargs="?",
                        help="Notebook (census) OU base ref git (ratchet)")
    parser.add_argument("--family",
                        help="Top-level family under MyIA.AI.Notebooks/")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true",
                        help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true",
                        help="Census: exit 1 if any occurrence (CI-ready)")
    parser.add_argument("--self-test", action="store_true",
                        help="Positive/negative controls + founding replay")
    args = parser.parse_args(argv)

    if args.self_test:
        failures = self_test()
        for f in failures:
            print(f"SELF-TEST FAIL: {f}", file=sys.stderr)
        print(f"self-test: {'OK' if not failures else 'KO'} "
              f"({len(failures)} failure(s))")
        return 1 if failures else 0

    root = Path(args.root).resolve()

    # Ratchet : l'argument est un ref git qui existe.
    if args.notebook_or_base and git("rev-parse", "--verify", "--quiet",
                                     args.notebook_or_base + "^{commit}",
                                     cwd=root):
        report = ratchet(args.notebook_or_base, cwd=root)
        if args.json:
            print(json.dumps(report, ensure_ascii=False, indent=2))
        else:
            print(_human_ratchet(report))
        return 1 if report["added_total"] else 0

    # Census : un chemin de notebook, une famille, ou tout le depot.
    paths = _iter_census_paths(root, args.family, args.notebook_or_base)
    if args.notebook_or_base and not paths:
        print(f"error: not a notebook path nor a git ref: "
              f"{args.notebook_or_base}", file=sys.stderr)
        return 2
    if args.family and not paths:
        print(f"error: family not found: {args.family}", file=sys.stderr)
        return 2
    results = [scan_notebook(p) for p in paths]
    total = sum(len(r["hits"]) for r in results)
    if args.json:
        print(json.dumps({"notebooks_scanned": len(results),
                          "total_hits": total, "results": results},
                         ensure_ascii=False, indent=2))
    else:
        print(_human_census(results))
    if args.check and total:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
