#!/usr/bin/env python3
"""Pure-CSV multilingual translation drift audit for the CoursIA ``translations/`` corpus.

Fork of Argumentum's ``tools/multilingual-drift-audit.py`` (453 LOC @ 7e72f3e5d),
adapted to CoursIA's uniform 21-column CSV schema produced by
``extract_cells_to_csv.py`` (T1, Epic #4957 / #1650).

Dispatched by ai-01 (msg-20260807T221110-tfqe70, R4 greenlit) as grain 1 of #6949:
the *measurable precursor* to the translation engine (grain 2 = fork of
``translate_game_rules.py``). Read-only, zero notebook I/O — it audits the CSV
cells themselves to answer the question the sterile resync-masse PRs could not:
*are we translating, or shuffling hashes?*

Drift classes detected (FR reference ``text_fr`` vs 7 target langs):

    MISSING       ``text_fr`` non-empty, ``text_<lang>`` empty (coverage gap).
    ORPHAN        ``text_<lang>`` non-empty, ``text_fr`` empty (no source).
    FR_CONTAM     ``text_<lang>`` == ``text_fr`` verbatim, normalised length >= 4
                  (untranslated FR copy leaked into a target column).
    WRONG_SCRIPT  a non-Latin lang (ru/ar/fa/zh) cell carries Latin letters but
                  NONE of its expected script (Cyrillic/Arabic/CJK) — the #761
                  lesson: a non-Latin leak is invisible if only FR/EN are audited.
    COGNATE       N/A for our cell-based model (no name/prose field distinction);
                  documented per the #7714 precedent in ``check_translation_sync.py``.

Complementary, NOT redundant, to ``check_translation_sync.py``: that tool detects
*notebook <-> CSV synchronisation* drift (SRC_DRIFT / TRAD_DRIFT, it reads the
notebooks to recompute hashes). This tool is a pure-CSV *coverage / quality* audit
— it never opens a notebook, so it measures how much is actually translated
regardless of whether the source moved.

Limitation (documented, not auto-detected): within-language *semantic* drift
(e.g. a wrong-but-valid CJK glyph choice) is NOT machine-detectable — both forms
are valid script. This audit catches coverage gaps + copy + script leakage;
semantic correctness needs human review (cited as residual).

Usage::

    python scripts/translation/multilingual_drift_audit.py                 # all CSVs, human summary
    python scripts/translation/multilingual_drift_audit.py translations/   # explicit root
    python scripts/translation/multilingual_drift_audit.py --json          # full detail JSON to stdout
    python scripts/translation/multilingual_drift_audit.py --check         # exit 0 always (CI)

Exit code 0 always (this is an audit, not a gate). See #6949 / #1650.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import sys
from collections import defaultdict
from typing import Iterable

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# 7 target languages = l'univers ordonné de source unique ``check_perimeter``
# (#10109). Aucune copie locale : une permutation divergente est un bug latent.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_perimeter import TARGET_LANGS as LANGS  # noqa: E402
NON_LATIN = {"ru", "ar", "fa", "zh"}  # langs whose cells should carry non-Latin script

# Drift classes.
CLASSES = ["MISSING", "ORPHAN", "FR_CONTAM", "WRONG_SCRIPT"]

# FR_CONTAM threshold: a 1-3 char coincidence (e.g. "ok", "1.") is not real drift.
FR_CONTAM_MIN_LEN = 4

# --- Script detection (ported from Argumentum, verified correct) -----------
RE_CYRILLIC = re.compile(r"[Ѐ-ӿ]")
RE_ARABIC = re.compile(r"[؀-ۿݐ-ݿࢠ-ࣿ]")
RE_CJK = re.compile(r"[一-鿿㐀-䶿]")
RE_LATIN_LETTER = re.compile(r"[A-Za-zÀ-ÖØ-öø-ÿ]")  # incl. FR diacritics


def has_expected_script(lang: str, val: str) -> bool:
    """True if ``val`` carries at least one glyph of ``lang``'s expected script."""
    if lang == "ru":
        return bool(RE_CYRILLIC.search(val))
    if lang in ("ar", "fa"):
        return bool(RE_ARABIC.search(val))
    if lang == "zh":
        return bool(RE_CJK.search(val))
    return True  # Latin langs always pass


def is_wrong_script(lang: str, val: str) -> bool:
    """A non-Latin lang cell with Latin letters but NONE of its expected script.

    => FR/Latin text leaked into a Cyrillic/Arabic/CJK column.
    """
    if lang not in NON_LATIN:
        return False
    if not val.strip():
        return False
    if has_expected_script(lang, val):
        return False
    return bool(RE_LATIN_LETTER.search(val))


def norm(s: str | None) -> str:
    return re.sub(r"\s+", " ", (s or "").strip())


def discover_csvs(root: str) -> list[str]:
    """Return all ``translations/*.csv`` paths under ``root``, sorted."""
    out: list[str] = []
    for dirpath, _dirs, files in os.walk(root):
        for fn in sorted(files):
            if fn.endswith(".csv"):
                out.append(os.path.join(dirpath, fn))
    return sorted(out)


def audit_csv(rel_path: str) -> dict:
    """Audit one CSV. Returns a per-lang count dict for the 4 drift classes."""
    path = os.path.join(REPO, rel_path) if not os.path.isabs(rel_path) else rel_path
    with open(path, "r", encoding="utf-8-sig", newline="") as f:
        reader = csv.DictReader(f)
        fieldnames = reader.fieldnames or []
        rows = list(reader)

    fr_col = "text_fr"
    has_fr = fr_col in fieldnames
    # Per-lang counters.
    counts: dict[str, dict[str, int]] = {
        lang: {cls: 0 for cls in CLASSES} for lang in LANGS
    }
    meta = {
        "path": rel_path.replace("\\", "/"),
        "rows": len(rows),
        "has_fr_column": has_fr,
        "src_langs": sorted({(r.get("src_lang") or "").strip() for r in rows if (r.get("src_lang") or "").strip()}),
        "lang_columns_present": [l for l in LANGS if f"text_{l}" in fieldnames],
        "samples": {cls: [] for cls in CLASSES},
    }

    for row in rows:
        fr_val = norm(row.get(fr_col, "")) if has_fr else ""
        fr_present = bool(fr_val)
        for lang in LANGS:
            col = f"text_{lang}"
            if col not in fieldnames:
                continue
            val = norm(row.get(col, ""))
            present = bool(val)

            # MISSING: FR filled, this lang empty.
            if fr_present and not present:
                counts[lang]["MISSING"] += 1
                if len(meta["samples"]["MISSING"]) < 6:
                    meta["samples"]["MISSING"].append(
                        {"lang": lang, "csv": meta["path"], "cell_id": (row.get("cell_id") or "")[:12],
                         "fr": fr_val[:60]}
                    )
                continue

            # ORPHAN: lang filled, FR empty.
            if present and not fr_present:
                counts[lang]["ORPHAN"] += 1
                if len(meta["samples"]["ORPHAN"]) < 6:
                    meta["samples"]["ORPHAN"].append(
                        {"lang": lang, "csv": meta["path"], "cell_id": (row.get("cell_id") or "")[:12],
                         "val": val[:60]}
                    )
                continue

            # Both present — check contamination + script.
            if present and fr_present:
                if len(val) >= FR_CONTAM_MIN_LEN and val == fr_val:
                    counts[lang]["FR_CONTAM"] += 1
                    if len(meta["samples"]["FR_CONTAM"]) < 6:
                        meta["samples"]["FR_CONTAM"].append(
                            {"lang": lang, "csv": meta["path"], "cell_id": (row.get("cell_id") or "")[:12],
                             "val": val[:60]}
                        )
                    continue
                if is_wrong_script(lang, val):
                    counts[lang]["WRONG_SCRIPT"] += 1
                    if len(meta["samples"]["WRONG_SCRIPT"]) < 6:
                        meta["samples"]["WRONG_SCRIPT"].append(
                            {"lang": lang, "csv": meta["path"], "cell_id": (row.get("cell_id") or "")[:12],
                             "val": val[:60]}
                        )

    return {"meta": meta, "counts": counts}


def aggregate(per_csv: list[dict]) -> dict:
    """Sum per-lang counts across all CSVs."""
    total: dict[str, dict[str, int]] = {lang: {cls: 0 for cls in CLASSES} for lang in LANGS}
    for res in per_csv:
        for lang, classes in res["counts"].items():
            for cls in CLASSES:
                total[lang][cls] += classes[cls]
    return total


def render_markdown(total: dict, per_csv: list[dict]) -> str:
    lines: list[str] = []
    lines.append("# Multilingual translation drift audit — `translations/` corpus\n")
    lines.append("Pure-CSV audit (no notebook I/O). Reference = `text_fr`. 7 target langs.\n")

    # Grand total table: rows = class, cols = lang.
    total_cells = sum(sum(c.values()) for c in total.values())
    lines.append("## Grand total — drift count by class x lang\n")
    header = "| class | " + " | ".join(LANGS) + " | TOTAL |"
    sep = "|---" * (len(LANGS) + 2) + "|"
    lines += [header, sep]
    for cls in CLASSES:
        row_vals = [str(total[lang][cls]) for lang in LANGS]
        row_sum = sum(total[lang][cls] for lang in LANGS)
        lines.append(f"| **{cls}** | " + " | ".join(row_vals) + f" | **{row_sum}** |")
    # coverage row: how many non-FR cells filled vs MISSING (per lang)
    lines.append("| _drift total_ | " + " | ".join(str(sum(total[l].values())) for l in LANGS) +
                 f" | **{total_cells}** |")
    lines.append("")

    # Per-CSV breakdown (top contributors).
    lines.append("## Per-CSV breakdown\n")
    lines.append("| CSV | rows | " + " | ".join(LANGS) + " |")
    lines.append("|---|---" * (len(LANGS) + 1) + "|")
    for res in per_csv:
        m = res["meta"]
        per_lang_total = [str(sum(res["counts"][l].values())) for l in LANGS]
        lines.append(f"| `{m['path']}` | {m['rows']} | " + " | ".join(per_lang_total) + " |")
    lines.append("")

    # Samples (for human triage).
    all_samples: dict[str, list] = defaultdict(list)
    for res in per_csv:
        for cls, samp in res["meta"]["samples"].items():
            all_samples[cls].extend(samp)
    lines.append("## Samples (up to 6/class across corpus, for triage)\n")
    for cls in CLASSES:
        samp = all_samples.get(cls, [])
        lines.append(f"### {cls} ({len(samp)} shown)\n")
        if not samp:
            lines.append("_none_\n")
            continue
        for s in samp:
            shown = s.get("val", s.get("fr", ""))
            lines.append(f"- `{s['lang']}` {s['csv']} cell `{s['cell_id']}`: \"{shown}\"")
        lines.append("")
    return "\n".join(lines)


def main(argv: Iterable[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("root", nargs="?", default="translations/",
                   help="CSV file or directory to audit (default: translations/)")
    p.add_argument("--json", action="store_true", help="emit full detail JSON to stdout")
    p.add_argument("--report", metavar="PATH", help="write markdown report to PATH")
    p.add_argument("--check", action="store_true",
                   help="CI mode: always exit 0 (audit, not a gate)")
    args = p.parse_args(list(argv) if argv is not None else None)

    target = args.root
    if os.path.isdir(target):
        csvs = discover_csvs(target)
    elif os.path.isfile(target):
        csvs = [target]
    else:
        print(f"error: {target!r} is not a file or directory", file=sys.stderr)
        return 0 if args.check else 2

    if not csvs:
        print(f"warning: no CSVs found under {target!r}", file=sys.stderr)

    per_csv = [audit_csv(os.path.relpath(c, REPO) if os.path.isabs(c) else c) for c in csvs]
    total = aggregate(per_csv)

    if args.json:
        json.dump({"per_csv": per_csv, "total": total}, sys.stdout, ensure_ascii=False, indent=1)
        sys.stdout.write("\n")
    else:
        md = render_markdown(total, per_csv)
        if args.report:
            with open(args.report, "w", encoding="utf-8") as f:
                f.write(md)
            print(f"report written to {args.report}", file=sys.stderr)
        else:
            print(md)

    return 0  # audit, never a gate


if __name__ == "__main__":
    sys.exit(main())
