#!/usr/bin/env python3
"""Detecte les residus de glyphes CJK (corruption LLM-translation) dans les notebooks.

Pourquoi cet outil existe
-------------------------
Le defect fleet-wide #8428 : des mots chinois inseres mid-prose francaise/anglaise
pendant la generation/enrichissement des notebooks par un LLM (ex `风险管理` risk
management, `胜利=1` victoire, `分布式约束优化` distributed constraint optimization,
`dataset支撑`, `arbre de分支`). 8 PRs sur 2026-07-25 (#8430/#8433/#8434/#8437/#8455/
#8461/#8465/#8523) ont elimine ces residus a la main, un notebook a la fois. Chaque
defaut est decouvert tardivement, ad-hoc, par le worker qui tombe dessus.

Ce tool formalise la moitie DETECTION : il liste toute cellule (markdown OU code) qui
contient un glyphe CJK inattendu, pour empecher la classe de defect de RECIDIVER
(regression-guard). C'est la fermeture naturelle de #8428 : apres le sweep manuel,
le guard veille que le reservoir ne se re-remplit pas silencieusement.

Il DETECTE, il ne CORRIGE PAS. La correction (remplacer la phrase CJK par le terme
francais/anglais correct en contexte) est un travail de substance par notebook
(byte-surgical raw-text replacement, cf #8428 fix pattern). Cet outil guide la
vigilance en listant les candidats au commit/CI.

Discriminateur (G.1, lecons des faux positifs)
----------------------------------------------
Un genuine CJK residue = un glyphe des plages CJK (`　-鿿` unified ideographs
+ symbols, `＀-￯` halfwidth/fullwidth forms) dans un notebook pedagogique
FR/EN, SANS justification multilingue. Le_detecteur est CONSERVATEUR : il signale
tout glyphe CJK non explicitement allowlisté.

Filtres faux-positifs (EXCLUS — CJK legitime)
---------------------------------------------
- Notebooks multilingues legiTIME : la demo TTS japonaise
  `GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb` contient volontairement du
  japonais (`こんにちは！多言語音声合成のデモンストレーションです。`) pour demontrer
  la synthese multilingue. Allowliste avec raison documentee.
- Notebooks multilingues legiTIME (suite) : `GenAI/Texte/9_Production_Patterns.ipynb`
  cell[20] demontre une salutation multilingue (`你好，世界！` = « Hello World » mandarin,
  aux cotes de l'italien). Allowliste avec raison documentee.
- Residu gated connu : a titre exceptionnel, un notebook dont le residu CJK exige une
  re-exec gated (ex QuantBook via QC Cloud) peut etre allowliste de façon temporaire,
  documente comme « known gated residual — fix needs <env> re-exec », pour ne pas bloquer
  le CI sur un defect connu et tracé. Retirer de l'allowlist des que re-executed.
  ATTENTION G.1 : verifier que le special-exec est REELLEMENT requis (kernel type, usage
  QuantBook) — le filename/famille ne suffit pas. « Allowlisted/needs-special-exec » n'est
  pas un bouton defer : un residu en commentaire ou un notebook Python local n'a pas besoin
  de QC Cloud. (Incident c.889 : QC-Py-Cloud-03 etait faussement allowliste « needs
  QC-Cloud » alors qu'il est Python local — defect fixe par re-exec locale en #8553.)

ALLOWED = dictionnaire {substring de chemin: raison}. Un notebook dont le chemin
contient une cle de ALLOWED est skip entierement (toutes ses cellules CJK sont
legitimes/connues). La liste est volontairement courte et documentee : ajouter une
entree exige de justifier la legitimite du CJK (vraie demo multilingue) ou de
tracer un gated residual.

Usage
-----
    python detect_cjk_residue.py NB.ipynb                 # un notebook
    python detect_cjk_residue.py --family Probas          # une famille
    python detect_cjk_residue.py                           # toute la flotte
    python detect_cjk_residue.py NB.ipynb --json          # sortie machine
    python detect_cjk_residue.py --check                  # exit 1 si hits (CI-ready)

Exit codes
----------
    0 -- aucun residu inattendu detecte (ou mode non --check)
    1 -- un ou plusieurs residus detectes (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- `detect_ascii_workaround.py` (#3801) -- pattern de detecteur read-only + filtres FP
- `detect_accent_stripping.py` (#6806) -- baseline honnete + convention detect_*
- #8428 -- le defect fleet-wide que ce guard cloture (anti-recidive)

See #8428.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# --- Plages CJK (alignees sur la def #8428) ---
# 　-〿 : CJK symbols and punctuation
# ぀-ゟ : Hiragana  (JP TTS demo legitime -> allowlist)
# ゠-ヿ : Katakana
# 一-鿿 : CJK unified ideographs (le reservoir principal des residus chinois)
# ＀-￯ : Halfwidth and Fullwidth forms
CJK_RE = re.compile(r"[　-〿぀-ゟ゠-ヿ一-鿿＀-￯]")

# --- Allowlist CJK legitime / residu gated connu ---
# Un notebook dont le chemin (relatif au root) contient une cle est skip.
# Chaque entree DOIT documenter la raison (demo multilingue legiTIME OU gated residual).
ALLOWED: dict[str, str] = {
    "GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb":
        "demo TTS multilingue legiTIME (japonais volontaire pour la synthese)",
    "GenAI/Texte/9_Production_Patterns.ipynb":
        "demo multilingue legiTIME (cell[20]: 你好，世界！ = 'Hello World' mandarin, aux cotes de Ciao mondo! italien)",
}


def _cell_source(cell: dict) -> str:
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def detect_cell(src: str) -> dict | None:
    """Return a finding dict if `src` (any cell type) carries unexpected CJK glyphs, else None.

    Returns the count + the distinct glyphs + the first context window, so a human
    can judge whether it is genuine residue or a new legitimate multilingual case
    (which should then be added to ALLOWED with a reason).
    """
    glyphs = CJK_RE.findall(src)
    if not glyphs:
        return None
    first = CJK_RE.search(src)
    start = first.start() if first else 0
    context = src[max(0, start - 30): start + 30].replace("\n", " ")
    return {
        "count": len(glyphs),
        "glyphs": sorted(set(glyphs)),
        "context": context,
    }


def _is_allowed(rel_path: str) -> str | None:
    """Return the allow reason if the notebook path matches an ALLOWED entry, else None."""
    for needle, reason in ALLOWED.items():
        if needle in rel_path:
            return reason
    return None


def scan_notebook(path: Path, root: Path) -> dict:
    """Return a result dict for one notebook: path, allowed, hits[], error."""
    try:
        rel = str(path.relative_to(root)).replace("\\", "/")
    except ValueError:
        rel = str(path).replace("\\", "/")
    allowed_reason = _is_allowed(rel)
    if allowed_reason:
        return {"path": rel, "allowed": allowed_reason, "hits": [], "error": None}
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"path": rel, "allowed": None, "hits": [], "error": str(exc)}
    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        src = _cell_source(cell)
        finding = detect_cell(src)
        if finding:
            hits.append({"cell_index": ci, "cell_type": cell.get("cell_type", "?"), **finding})
    return {"path": rel, "allowed": None, "hits": hits, "error": None}


# Dossiers a ignorer (alignes sur detect_ascii_workaround.py:SKIP_DIRS).
SKIP_DIRS = {
    ".lake", ".git", "__pycache__", "_archives", "archive", "_archive",
    ".ipynb_checkpoints", ".pytest_cache", "worktrees",
    "foundry-lib",  # lib vendored tierce
}
_OUTPUT_SUFFIX = "_output.ipynb"


def _should_skip(rel: Path) -> bool:
    if any(part in SKIP_DIRS for part in rel.parts):
        return True
    return rel.name.endswith(_OUTPUT_SUFFIX)


def _iter_notebooks(root: Path, family: str | None):
    base = root / "MyIA.AI.Notebooks"
    if family:
        base = base / family
    if not base.exists():
        return
    for nb in sorted(base.rglob("*.ipynb")):
        try:
            rel = nb.relative_to(base)
        except ValueError:
            continue
        if _should_skip(rel):
            continue
        yield nb


def _human_report(results: list[dict]) -> str:
    scanned = [r for r in results if r["allowed"] is None and r["error"] is None]
    allowed = [r for r in results if r["allowed"]]
    errors = [r for r in results if r["error"]]
    total_hits = sum(len(r["hits"]) for r in scanned)
    affected = [r for r in scanned if r["hits"]]
    lines = [
        f"Notebooks scanned : {len(scanned)}",
        f"Cells with CJK residue : {total_hits}",
        f"Affected notebooks : {len(affected)}",
        f"Allowed (skipped) : {len(allowed)}",
        "",
    ]
    if errors:
        lines.append(f"Read errors : {len(errors)}")
        for r in errors:
            lines.append(f"  - {r['path']}: {r['error']}")
        lines.append("")
    if not affected:
        lines.append("No unexpected CJK residue detected (fleet clean vs #8428).")
        if allowed:
            lines.append("")
            lines.append("Allowed notebooks (CJK legitime / gated residual documente) :")
            for r in allowed:
                lines.append(f"  - {r['path']}  -- {r['allowed']}")
        return "\n".join(lines)
    for r in affected:
        short = r["path"].split("MyIA.AI.Notebooks")[-1].lstrip("\\/")
        lines.append(f"## {short}")
        for h in r["hits"]:
            glyphs = "".join(h["glyphs"])
            ctx = f"  | ...{h['context']}..." if h["context"] else ""
            lines.append(
                f"  - cell [{h['cell_index']}] ({h['cell_type']}): "
                f"{h['count']} glyph(s) [{glyphs}]{ctx}"
            )
        lines.append("")
    lines.append(
        "NOTE: conservative detector. Verify each hit firsthand -- if a notebook "
        "carries LEGITIMATE multilingual CJK (demo TTS, language course), add it to "
        "ALLOWED in detect_cjk_residue.py with a documented reason rather than "
        "stripping the glyphs."
    )
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("notebook", nargs="?", help="Notebook to scan (default: all pedagogical)")
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. Probas, ML)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any unexpected CJK hit (CI-ready)")
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

    results = [scan_notebook(p, root) for p in paths]
    total_hits = sum(len(r["hits"]) for r in results if r["allowed"] is None)

    if args.json:
        payload = {
            "notebooks_scanned": sum(1 for r in results if r["allowed"] is None),
            "total_hits": total_hits,
            "results": results,
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_human_report(results))

    if args.check and total_hits > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
