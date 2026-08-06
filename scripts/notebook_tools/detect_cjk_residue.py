#!/usr/bin/env python3
"""Detecte les residus CJK (corruption LLM-translation) dans les notebooks ET les sources trackees.

Pourquoi cet outil existe
-------------------------
Le defect fleet-wide #8428 : des mots chinois/japonais inseres mid-prose
francaise/anglaise pendant la generation/enrichissement par un LLM (ex `dataset支撑`,
`arbre de分支`, `均匀ément`, `de重建`). 8 PRs sur 2026-07-25 ont elimine ces residus
a la main. Ce tool formalise la moitie DETECTION pour empecher la recidive.

#8826 : le guard existait mais etait cable sur RIEN (aucun workflow ne l appelait)
et ne voyait que les .ipynb. Le reservoir s est donc re-rempli silencieusement :
#8823 a introduit `«经验 manquante»` dans un .py -- invisible au detecteur (scope
ipynb) et de toute facon jamais execute (pas de cablage). Ce tool desormais
(a) est cable par .github/workflows/cjk-residue-advisory.yml, (b) couvre les .ipynb
ET les .py/.md/.cs trackees. Il DETECTE, il ne CORRIGE PAS -- la correction est un
grain de substance separe (byte-surgical replacement, cf #8428).

Discriminateur #8826 (inverser le ratio signal/bruit)
-----------------------------------------------------
Le defect a une signature mecanisable : un mot chinois/japonais SOUDE ou depose en
pleine prose latine. La regle : un run CJK est une FUITE si son scope englobant
(un span protege backtick/double-quote/guillemet, ou la ligne hors span) contient a
la FOIS du CJK et une lettre latine [A-Za-z+A-y]. Le CJK legitime vit dans un scope
PUR-CJK (terme backticke `风险管理`, fixture `"你好"`, ligne de demo entierement CJK)
-- sans lettre latine -- et est laisse tranquille.

Un backtick span qui MIXE CJK+Latin (ex `dataset支撑`) reste une fuite : le CJK y est
un mot latin corrompu, meme s il est backticke. Les fichiers qui DOCUMENTENT les
patterns de fuite (ce detecteur, son README, ses tests, les ledgers) sont allowlistes
par chemin -- ALLOWED est l echappatoire pour le legit irreductible (prompt
fonctionnel comfyui, kanji visible dans une image, demo multilingue, verbatim preserve
par l extracteur de traduction), PAS le mecanisme principal.

Les Halfwidth/Fullwidth forms (U+FF00-FFEF : ￢ not logique, ：deux-points pleine-
chasse) sont EXCLUES : variantes typographiques d ASCII, pas des mots chinois. Aucune
des 7 fuites mesurees n utilise la pleine-chasse ; l inclure ferait hurler les slides
de logique (￢) et les regex (：) pour du bruit. Les blocs de code fences sont ignores
(leur CJK est du config/output, pas de la prose).

Mesure sur origin/main : 5 fuites reelles (MANIFEST/README .md) detectees, 0 faux
positif, 12 fichiers legit allowlistes -- ratio signal/bruit redresse.

ALLOWED = dictionnaire {substring de chemin: raison}. Un fichier dont le chemin
contient une cle est skip entierement. Liste courte et documentee : chaque entree
justifie le caractere irreductible du CJK (fonctionnel, docs, fixture).

Usage
-----
    python detect_cjk_residue.py                        # toute la flotte (notebooks + sources)
    python detect_cjk_residue.py NB.ipynb               # un notebook
    python detect_cjk_residue.py path/leak.md           # un fichier source
    python detect_cjk_residue.py --family Probas        # une famille
    python detect_cjk_residue.py --json                 # sortie machine
    python detect_cjk_residue.py --check                # exit 1 si fuite (CI-ready)

Exit codes
----------
    0 -- aucune fuite CJK detectee (ou mode non --check)
    1 -- une ou plusieurs fuites detectees (--check seulement)
    2 -- erreur (fichier illisible, famille introuvable)

Voir aussi
----------
- `.github/workflows/cjk-residue-advisory.yml` (#8826) -- cablage advisory (label)
- `detect_ascii_workaround.py` (#3801), `detect_accent_stripping.py` (#6806) -- pattern detect_*
- #8428 (defect fondateur), #8826 (discriminateur + scope sources + cablage)

See #8428, #8826.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# --- Plages CJK (alignees sur la classe de residu #8428/#8826) ---
# 　-〿 : CJK symbols and punctuation
# ぀-ゟ : Hiragana  (JP TTS demo legitime -> allowlist)
# ゠-ヿ : Katakana
# 一-鿿 : CJK unified ideographs (le reservoir principal des residus)
# Les Halfwidth/Fullwidth forms (＀-￯, ex. ￢ not logique U+FFE2,
# ： deux-points pleine-chasse U+FF1A) sont EXCLUES : variantes typographiques
# d ASCII, pas des mots chinois. Le defect #8428/#8826 est des MOTS chinois/
# japonais (ideographes + kana) soudes a la prose (均匀ément, de重建,
# 可能性が高い) -- aucune des 7 fuites mesurees n utilise la pleine-chasse.
# Inclure ＀-￯ ferait hurler les slides de logique (￢) et les regex
# (：) pour du bruit, inversant le ratio signal/bruit que #8826 veut redresser.
CJK_RE = re.compile(r"[　-〿぀-ゟ゠-ヿ一-鿿]")

# --- Allowlist CJK legitime / residu gated connu ---
# Un notebook dont le chemin (relatif au root) contient une cle est skip.
# Chaque entree DOIT documenter la raison (demo multilingue legiTIME OU gated residual).
ALLOWED: dict[str, str] = {
    # --- Notebooks: deliberate multilingual demos (CJK is the subject) ---
    "GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb":
        "demo TTS multilingue legiTIME (japonais volontaire pour la synthese)",
    "GenAI/Texte/9_Production_Patterns.ipynb":
        "demo multilingue legiTIME (cell[20]: 你好，世界！ = 'Hello World' mandarin, aux cotes de Ciao mondo! italien)",
    # --- Source files: irreducible legit CJK that mixes with Latin (#8826) ---
    # The detector itself DOCUMENTS the leak class in its docstring (cites
    # `dataset支撑`, `arbre de分支` as examples) -- those mixed spans are the
    # spec, not residue. A guard must not flag its own rule book.
    "scripts/notebook_tools/detect_cjk_residue.py":
        "self -- docstring cite les patterns de fuite en exemple (spec, pas residu)",
    # The detector's own test suite carries the leak phrases as POSITIVE
    # fixtures (it must, to prove detection) -- mixed CJK+Latin by design.
    "scripts/notebook_tools/tests/test_detect_cjk_residue.py":
        "fixtures de test positif (patterns de fuite volontaires pour piner le contrat)",
    # Functional model prompt: the Wan/Qwen negative prompt is canonically
    # Chinese and mixes CJK with Latin tokens like `JPEG` (e.g. JPEG压缩残留).
    # Not prose -- a model input. Replacing it would break generation.
    "GenAI/shared/helpers/comfyui_client.py":
        "negative prompt canonique du modele Wan/Qwen (CJK fonctionnel, pas prose)",
    # GenAI Image MANIFEST: the CJK is a kanji VISIBLE IN the described image
    # (e.g. 北小路 on a sign) -- the prose names what the image shows. Functional.
    "GenAI/Image/02-Advanced/assets/readme/MANIFEST.md":
        "kanji visible dans l image decrite (le prose nomme le contenu de l image)",
    # SOTA-axe2 ledger: DISCUSSES the CJK-residue defect class as its subject
    # (cites 绑定, 完整 to document findings). Quoting leaks to analyse them != leaking.
    "docs/ledgers/3801-sota-axe2.md":
        "ledger qui cite le defect CJK comme sujet d analyse (pas de la prose leak)",
    # notebooks_tools README: documents the leak examples (`dataset支撑`, etc.)
    # in backticks -- the spec of what the detector hunts, not residue.
    "scripts/notebook_tools/README.md":
        "documente les patterns de fuite en exemple (spec du detecteur)",
    # Translation-sync test: a deliberate `"你好 world 123"` fixture proving the
    # script detector sees CJK in a mixed Latin string. Mixed by design.
    "scripts/tests/test_check_translation_sync.py":
        "fixture de test volontaire (string CJK+Latin pour piner le detecteur de script)",
    # Translations READMEs: the CJK (完整, etc.) is preserved VERBATIM by the
    # deterministic extractor (a sha256-16 anchor would drift otherwise). The
    # whole point is to keep the original glyph exact -- not residue.
    "translations/sudoku/README.md":
        "CJK preserve verbatim par l extracteur deterministe (ancrage sha256)",
    "translations/search-part1/README.md":
        "CJK preserve verbatim par l extracteur deterministe (ancrage sha256)",
    "translations/search-part2/README.md":
        "CJK preserve verbatim par l extracteur deterministe (ancrage sha256)",
}

# --- Discriminateur #8826 : CJK mixe a du Latin = fuite ; CJK pur = legitime ---
# Un residu #8428/#8826 a une signature mecanisable : un mot chinois/japonais
# SOUDE ou depose en pleine prose latine -- `均匀ément`, `de重建`, `la 拥挤 city`,
# `«经验 manquante»`, `—可能性が高い c'est`. Le CJK et le Latin cohabitent dans
# le meme SCOPE (un span protege backtick/guillemet, ou la ligne hors span).
# A l'inverse, le CJK legitime vit dans un scope PUR-CJK (terme backticke
# `风险管理`, fixture de test `"你好"`, ligne de demo multilingue entierement CJK)
# -- sans aucune lettre latine. Cette regle separe les 7 vraies fuites des ~59
# cas legitimes SANS allowlist par defaut (mesure #8826).
LATIN_RE = re.compile(r"[A-Za-zÀ-ÿ]")

# Spans proteges : backtick (inline code markdown), doubles quotes droites/
# courbes, guillemets francais. Le CONTENU d'un span est legitime s'il est
# pur-CJK ; s'il MIXE CJK+Latin (ex `«经验 manquante»`), le CJK est une fuite
# (un mot latin corrompu). Les simples quotes sont EXCLUES : les apostrophes
# francaises (l', d', c'est) rendent l'appariement non fiable (masquerait de
# vraies fuites ou inventerait des spans fantomes).
_SPAN_RE = re.compile(
    r"(`[^`\n]*`)"        # backtick
    r"|(\"[^\"\n]*\")"    # double quote droite
    r"|(«[^»\n]*»)"       # guillemets francais
    r"|(“[^”\n]*”)"       # double quote courbe
)

# Ouverture de bloc de code fence (``` ou ~~~). Les lignes DANS un fence sont
# du config/output colle, pas de la prose : on les ignore.
_FENCE_RE = re.compile(r"^\s*(`{3,}|~{3,})")


def _context(line: str) -> str:
    """A ~60-char window around the first CJK glyph in ``line`` (single-line)."""
    m = CJK_RE.search(line)
    start = m.start() if m else 0
    return line[max(0, start - 30): start + 30].replace("\n", " ")


def _judge_segment(seg: str, lineno: int, line: str, leaks: list, *, protected: bool) -> None:
    """Append a leak if ``seg`` carries CJK AND a Latin letter (the defect
    signature). Pure-CJK segments (no Latin) are legitimate -- do nothing."""
    glyphs = CJK_RE.findall(seg)
    if not glyphs:
        return
    if LATIN_RE.search(seg):
        leaks.append({
            "lineno": lineno,
            "glyphs": glyphs,
            "protected": protected,
            "context": _context(line),
            "reason": ("CJK mixe a du Latin dans un span protege (mot latin corrompu)"
                       if protected else
                       "CJK en pleine prose latine (hors backticks/guillemets)"),
        })
    # else: scope pur-CJK (terme backticke, fixture, ligne de demo) -> legitime.


def classify_cjk_leaks(text: str) -> list[dict]:
    """Return the CJK *leaks* in ``text`` (a notebook cell source OR a source
    file body). See the discriminator block above for the rule.

    Each leak dict: ``{lineno, glyphs, protected, context, reason}``. A text
    with only legitimate CJK (backticked terms, pure-CJK quoted strings, CJK-only
    lines, fenced code blocks) yields an empty list.
    """
    leaks: list[dict] = []
    in_fence = False
    for lineno, line in enumerate(text.split("\n"), start=1):
        if _FENCE_RE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        # Decoupe la ligne en spans proteges + fragments libres; juge chaque
        # segment porteur de CJK sur la presence concurrente de Latin.
        pos = 0
        for m in _SPAN_RE.finditer(line):
            _judge_segment(line[pos:m.start()], lineno, line, leaks, protected=False)
            _judge_segment(m.group(0), lineno, line, leaks, protected=True)
            pos = m.end()
        _judge_segment(line[pos:], lineno, line, leaks, protected=False)
    return leaks


def _cell_source(cell: dict) -> str:
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def detect_cell(src: str) -> dict | None:
    """Return a finding dict if `src` (any cell type) carries a CJK *leak*
    (CJK mixed into Latin prose), else None.

    Uses the #8826 discriminator (``classify_cjk_leaks``): pure-CJK content
    (backticked terms, quoted fixtures, multilingual demo lines) is legitimate
    and returns None. The count/glyphs/context describe the LEAK glyphs only,
    so a human can judge whether it is genuine residue or a new legitimate
    multilingual case (which should then be added to ALLOWED with a reason).
    """
    leaks = classify_cjk_leaks(src)
    if not leaks:
        return None
    all_glyphs: list[str] = []
    for lk in leaks:
        all_glyphs.extend(lk["glyphs"])
    return {
        "count": len(all_glyphs),
        "glyphs": sorted(set(all_glyphs)),
        "context": leaks[0]["context"],
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


# Extensions de source que le guard couvre desormais (#8826) en plus des .ipynb.
SOURCE_EXTS = (".py", ".md", ".cs")


def scan_source_file(path: Path, root: Path) -> dict:
    """Return a result dict for one tracked source file (.py/.md/.cs): path,
    allowed, hits[], error. Uses the same #8826 discriminator as notebook cells
    -- a CJK leak is CJK mixed into Latin prose, not any CJK glyph."""
    try:
        rel = str(path.relative_to(root)).replace("\\", "/")
    except ValueError:
        rel = str(path).replace("\\", "/")
    allowed_reason = _is_allowed(rel)
    if allowed_reason:
        return {"path": rel, "allowed": allowed_reason, "hits": [], "error": None}
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        return {"path": rel, "allowed": None, "hits": [], "error": str(exc)}
    leaks = classify_cjk_leaks(text)
    hits = [
        {"lineno": lk["lineno"], "glyphs": lk["glyphs"],
         "context": lk["context"], "reason": lk["reason"]}
        for lk in leaks
    ]
    return {"path": rel, "allowed": None, "hits": hits, "error": None}


# Marcheur + SKIP_DIRS canonique centralises dans notebook_walk (#8650).
from notebook_walk import SKIP_DIRS, _OUTPUT_SUFFIX, iter_notebooks  # noqa: E402


def _should_skip(rel: Path) -> bool:
    if any(part in SKIP_DIRS for part in rel.parts):
        return True
    return rel.name.endswith(_OUTPUT_SUFFIX)


def _iter_notebooks(root: Path, family: str | None):
    # Delegue au marcheur partage : SKIP_DIRS canonique + filtre git tracked_only.
    yield from iter_notebooks(root / "MyIA.AI.Notebooks", family=family)


def _submodule_paths(root: Path) -> set[str]:
    """Submodule mount paths (posix, repo-root-relative), to exclude source
    scanning defensively. ``git ls-files`` already omits submodule *contents*
    (they are gitlinks, not files), but a checked-out submodule working tree can
    leave files on disk -- belt-and-suspenders for #8826's 'submodules exclus'."""
    try:
        result = subprocess.run(
            ["git", "submodule", "status"],
            cwd=str(root), capture_output=True, text=True, timeout=30,
        )
    except (FileNotFoundError, OSError):
        return set()
    if result.returncode != 0:
        return set()
    paths: set[str] = set()
    for line in result.stdout.splitlines():
        parts = line.strip().split()
        if len(parts) >= 2:
            paths.add(parts[1].replace("\\", "/"))
    return paths


def _iter_tracked_sources(root: Path, family: str | None):
    """Yield git-tracked .py/.md/.cs paths under ``root``, excluding SKIP_DIRS
    and submodule mounts. Enumerates via ``git ls-files`` (source of truth for
    'tracked' -- naturally drops gitignored trees and submodule contents)."""
    try:
        result = subprocess.run(
            ["git", "ls-files", "-z", "--", "*.py", "*.md", "*.cs"],
            cwd=str(root), capture_output=True, text=False, timeout=180,
        )
    except (FileNotFoundError, OSError):
        return
    if result.returncode != 0:
        return
    sub_paths = _submodule_paths(root)
    prefix = f"MyIA.AI.Notebooks/{family}/" if family else None
    entries = result.stdout.decode("utf-8", "replace").strip("\x00").split("\x00")
    for e in entries:
        if not e:
            continue
        rel = e.replace("\\", "/")
        parts = rel.split("/")
        if any(part in SKIP_DIRS for part in parts):
            continue
        if any(rel == sp or rel.startswith(sp + "/") for sp in sub_paths):
            continue
        if prefix and not rel.startswith(prefix):
            continue
        yield root / rel


def _human_report(results: list[dict]) -> str:
    scanned = [r for r in results if r["allowed"] is None and r["error"] is None]
    allowed = [r for r in results if r["allowed"]]
    errors = [r for r in results if r["error"]]
    total_hits = sum(len(r["hits"]) for r in scanned)
    affected = [r for r in scanned if r["hits"]]
    lines = [
        f"Files scanned (notebooks + sources) : {len(scanned)}",
        f"CJK leak lines : {total_hits}",
        f"Affected files : {len(affected)}",
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
            if "cell_index" in h:
                loc = f"cell [{h['cell_index']}] ({h['cell_type']})"
                n = h.get("count", len(h["glyphs"]))
            else:
                loc = f"line {h['lineno']}"
                n = len(h["glyphs"])
            reason = f"  -- {h['reason']}" if h.get("reason") else ""
            lines.append(f"  - {loc}: {n} glyph(s) [{glyphs}]{ctx}{reason}")
        lines.append("")
    lines.append(
        "NOTE: discriminating detector (#8826). A hit is CJK mixed into Latin "
        "prose -- verify each firsthand. If a file carries LEGITIMATE mixed CJK "
        "(functional prompt, docstring citing examples, multilingual demo), add it "
        "to ALLOWED with a documented reason rather than stripping the glyphs."
    )
    return "\n".join(lines)


def _scan_one(path: Path, root: Path) -> dict:
    """Dispatch a single target: notebook (.ipynb) -> scan_notebook, source
    (.py/.md/.cs) -> scan_source_file. Other extensions are read as text."""
    if path.suffix == ".ipynb":
        return scan_notebook(path, root)
    return scan_source_file(path, root)


# Extensions the PR-diff (--stdin) mode scans. Mirrors the fleet scope
# (notebooks + tracked .py/.md/.cs): a .yml/.json/.lock in the diff is NOT read
# as Latin prose, so it is skipped rather than risk a content-judgement false hit.
_SCANNABLE_EXT = {".ipynb", ".py", ".md", ".cs"}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "target", nargs="?",
        help="Notebook OR source file (.py/.md/.cs) to scan (default: whole fleet)",
    )
    parser.add_argument("--family", help="Top-level family under MyIA.AI.Notebooks/ (e.g. Probas, ML)")
    parser.add_argument("--root", default=".", help="Repo root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="Machine-readable JSON output")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any CJK leak (CI-ready)")
    parser.add_argument(
        "--stdin",
        action="store_true",
        help="Read paths to scan from stdin (one per line, as `git diff "
             "--name-only` emits). Decides the leak verdict on exactly the PR's "
             "changed files, not the whole fleet -- so a label can be attributed "
             "to the PR that introduced the leak rather than to every PR while "
             "main carries pre-existing residue (#8829 review).",
    )
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    if args.stdin:
        # PR-diff mode (#8829 review): scan only the leak-bearing files the PR
        # touches. The fleet scan (below, in the workflow) stays informational.
        # Filter to scannable extensions so a .yml/.json in the diff is not read
        # as prose (would match the fleet scope: notebooks + .py/.md/.cs only).
        results = []
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            p = Path(line)
            if not p.is_absolute():
                p = root / p
            if p.suffix not in _SCANNABLE_EXT or not p.exists():
                continue
            # #8846/#8858: SKIP_DIRS parity with the fleet mode (applied at
            # L374/L140 on the RELATIVE path). The check must operate on the
            # components RELATIVE TO the repo root, not on `p.parts` -- `p` was
            # absolutised two lines above (`p = root / p`), so the absolute parts
            # include the repo's parent directories. If the repo is cloned under a
            # name that belongs to SKIP_DIRS (`worktrees`, `archive`, ...), every
            # path matched and the scan returned 0 hit on the ENTIRE diff -- a
            # total silence worse than #8846's false accusation (#8858). A leak
            # under a pedagogical archive (docs/archive/**, .lake/, _output/, ...)
            # is never attributed to a PR diff; the fleet scan skips the same.
            try:
                rel_parts = p.relative_to(root).parts
            except ValueError:
                # An explicit absolute path outside the repo: fall back to the
                # current behaviour rather than raise.
                rel_parts = p.parts
            if any(part in SKIP_DIRS for part in rel_parts):
                continue
            results.append(_scan_one(p, root))
    elif args.target:
        p = Path(args.target)
        if not p.is_absolute():
            p = root / p
        if not p.exists():
            print(f"error: target not found: {p}", file=sys.stderr)
            return 2
        results = [_scan_one(p, root)]
    else:
        # Fleet scan (#8826): pedagogical notebooks + tracked source files
        # (.py/.md/.cs) so the reservoir cannot refill in prose OR code.
        nb_paths = list(_iter_notebooks(root, args.family))
        src_paths = list(_iter_tracked_sources(root, args.family))
        results = (
            [scan_notebook(p, root) for p in nb_paths]
            + [scan_source_file(p, root) for p in src_paths]
        )
        if args.family and not nb_paths and not src_paths:
            print(f"error: family not found: {args.family}", file=sys.stderr)
            return 2

    total_hits = sum(len(r["hits"]) for r in results if r["allowed"] is None)
    scanned = sum(1 for r in results if r["allowed"] is None and r["error"] is None)

    if args.json:
        payload = {
            "scanned": scanned,
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
