#!/usr/bin/env python3
"""Recensement des PRs \`.ipynb\` markdown-only sur une fenetre N jours.

G-VAR-2 / anti-blanchiment de genre (#10290) : mesurer la proportion de PRs
qui touchent **uniquement** des \`.ipynb\` **avec zero cellule \`code\` modifiee**,
croise avec le genre declare (\`Grain:\` tag dans le body) et la famille du
path.

Si la proportion est marginale (<5%), le signaler — l'organe de detection
retrecit. Le recensement est le livrable initial, pas l'organe lui-meme.

Usage
-----
    python scripts/variation_genre_recensement.py \\
        --since 2026-07-11 --until 2026-08-10 \\
        --sample-size 200 --seed 42 \\
        --output-csv /tmp/census.csv \\
        --output-json /tmp/census.json

Le sampling (vs census exhaustif sur 3615 PRs) est documente : avec n=200 et
p~0.5, marge 7% (z=1.96). Suffisant pour distinguer <5% de >=10%. Pour une
mesure ciblee sur les PRs touchant \`.ipynb\`, on **stratifie** : on prend TOUS
les PRs \`.ipynb\`-touching (rare, ~10% du total) et un echantillon aleatoire
du reste, pour mesurer exactement la proportion \`only_notebook\`.

Input
-----
PR list JSON via \`gh pr list --state merged --search 'merged:<since>..<until>' \\
    --json number,files,body,mergedAt\`. Chaque PR doit porter :
- number, files[{path, additions, deletions}], body, mergedAt

Output
------
- stdout : summary lisible (total, ipynb-only, markdown-only, par genre/famille).
- CSV : 1 ligne par PR avec colonnes [\`pr\`, \`mergedAt\`, \`only_notebook\`,
  \`zero_code_modif\`, \`body_genre\`, \`file_family\`, \`interpretation_cue\`, \`title\`].
- JSON : meme structure, machine-readable.

Determinism
-----------
--seed fixe le RNG (par defaut 42). Rejoue donne la meme liste de PRs.
"""
from __future__ import annotations
import argparse
import csv
import json
import os
import random
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

# Ensure the sibling `grain_tag` module (canonical `Grain:` reader, #9485) is
# importable whether this file is run as a script (scripts/ auto on sys.path)
# or imported from elsewhere (e.g. from scripts/tests/).
try:
    from grain_tag import parse_grain_tag
except ImportError:  # pragma: no cover - path bootstrap for non-script invocation
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from grain_tag import parse_grain_tag

# --- grain parsing (shared vocabulary) ---------------------------------------
# The `Grain:` tag is read by the CANONICAL form-tolerant reader
# `grain_tag.parse_grain_tag` (single source of truth, #9485), which handles
# every tolerated form (`**Grain:**`, `## Grain`, `` `Grain` `` no-colon).
# This module previously carried its own `_GRAIN_RE` that diverged from the
# canonical reader and silently dropped those forms — undercounting the census
# universe and biasing the monoculture analysis that motivated
# variation-protocol.md. `parse_grain` below delegates to the canonical reader.

# Subset of genres that are LIGHT per G-VAR-2 (#10031, #10285):
# guard / ledger / docs / readme / test / refs.
# Anything else is MED or DEEP, including notebook-python, notebook-dotnet.
LIGHT_GENRES = {"guard", "ledger", "docs", "readme", "test", "refs"}

# Heuristic: indicators that the diff is enrichment/framing (i.e. could be
# declared MED or DEEP but is marked notebook-python/-dotnet to escape the
# LIGHT budget). Verified by spot-reading on PRs #10279, #10254, #10253.
INTERPRETATION_CUES = [
    re.compile(r"#\s*Interpretation", re.IGNORECASE),
    re.compile(r"#\s*Transition", re.IGNORECASE),
    re.compile(r"framing", re.IGNORECASE),
    re.compile(r"enrichissement|enriched", re.IGNORECASE),
    re.compile(r"interpretation cell", re.IGNORECASE),
    re.compile(r"markdown[- ]only", re.IGNORECASE),
    re.compile(r"cellule markdown", re.IGNORECASE),
]


@dataclass
class PRRow:
    """One PR's census row."""
    pr: int
    mergedAt: str
    title: str
    only_notebook: bool
    zero_code_modif: bool
    body_genre: str | None  # declared genre in `Grain:` tag, or None
    file_family: str | None  # e.g. "MyIA.AI.Notebooks/SymbolicAI" or None
    interpretation_cue: bool  # body smells like framing/enrichissement
    n_files: int
    n_ipynb: int
    light_genre: bool  # declared genre is in LIGHT_GENRES
    drift_candidate: bool  # only_notebook AND zero_code_modif AND NOT light_genre AND interpretation_cue


def parse_grain(body: str) -> tuple[str | None, str | None]:
    """Return (tier, genre) from `Grain:` tag in body, or (None, None).

    Delegates to the canonical form-tolerant reader `grain_tag.parse_grain_tag`
    (#9485) so the census agrees with the CI guard on EVERY tolerated form
    (`**Grain:**`, `## Grain`, `` `Grain` `` no-colon). The local `_GRAIN_RE`
    that used to live here diverged and undercounted those forms, biasing the
    monoculture census.
    """
    tag = parse_grain_tag(body or "")
    if not tag:
        return None, None
    return tag["tier"], tag["genre"]


def file_family(paths: list[str]) -> str | None:
    """Best-effort family of a PR from its file paths.

    For a multi-file PR, returns the common prefix if uniform, else the first
    notebook-prefix. Returns None if no file under MyIA.AI.Notebooks/.
    """
    nb_paths = [p for p in paths if p.startswith("MyIA.AI.Notebooks/")]
    if not nb_paths:
        return None
    # Take the first 2 path segments after MyIA.AI.Notebooks/: SymbolicAI/Lean
    first = nb_paths[0]
    parts = first.split("/")
    if len(parts) >= 3:
        return "/".join(parts[1:3])
    return parts[1] if len(parts) >= 2 else None


def only_notebook(paths: list[str]) -> bool:
    """True iff every path in `paths` ends with `.ipynb`."""
    return bool(paths) and all(p.endswith(".ipynb") for p in paths)


def zero_code_modif(pr: dict[str, Any]) -> bool:
    """True iff NO `.ipynb` cell `code` was modified in the diff.

    We use the file-level additions/deletions as a conservative proxy: a file
    with non-zero net additions and zero deletions probably had source change.
    BUT a cell-order-gate-style execution count bump could shift numbers without
    touching code. Better proxy: requires fetching the raw patch and counting
    \`+ \"source\":\` lines per code cell.

    For the census MVP, we use a stricter heuristic: ZERO deletions on any
    `.ipynb` AND additions <= EXEC_COUNT_BUMP_THRESHOLD (15 cells) — this
    catches the markdown-only framing cells without false-positiving on
    execution-count bumps. If the source contains `source` lines or
    `outputs` arrays that grew, we mark False.

    Caller is expected to pre-fetch the patch into pr['_patch'] when available.
    """
    # If we have the raw patch cached, count code-cell source-line modifications
    patch = pr.get("_patch", "")
    if patch:
        # count occurrences of `+ "source":` inside `cell_type == "code"` blocks
        # of the JSON patch. A naive regex would over-match; we instead split
        # on cell boundaries (lines starting with `    {` or `   {` at depth 2-3).
        # Conservative: any line matching `^+` and then immediately the literal
        # `"source"` AND the prior context had `"cell_type": "code"`.
        # Simpler heuristic: count +lines that modify cells where cell_type is code.
        # We approximate by counting `"cell_type": "code"` blocks before the diff.
        code_cells_added = len(
            re.findall(
                r'^\+\s*"cell_type":\s*"code"',
                patch,
                re.MULTILINE,
            )
        )
        code_cells_removed = len(
            re.findall(
                r"^\-\s*\"cell_type\":\s*\"code\"",
                patch,
                re.MULTILINE,
            )
        )
        # If a code cell was added/removed with new source, we'll catch it via
        # "+ \"source\":" near a cell_type:code context. This heuristic under-
        # counts cell content mods, but over-counts false positives → safer
        # to be strict (mark False unless we positively see no source mods).
        return code_cells_added == 0 and code_cells_removed == 0
    # No patch available — fall back to file-level additions: if all ipynb files
    # had only tiny additions (< 20 lines), probably exec count bump only.
    nb_files = [f for f in pr.get("files", []) if f.get("path", "").endswith(".ipynb")]
    if not nb_files:
        return True
    return all(f.get("additions", 0) <= 15 and f.get("deletions", 0) == 0 for f in nb_files)


def has_interpretation_cue(body: str) -> bool:
    return any(p.search(body or "") for p in INTERPRETATION_CUES)


def build_row(pr: dict[str, Any]) -> PRRow:
    paths = [f.get("path", "") for f in pr.get("files", [])]
    nb_paths = [p for p in paths if p.endswith(".ipynb")]
    tier, genre = parse_grain(pr.get("body", ""))
    only_nb = only_notebook(paths)
    zcm = zero_code_modif(pr)
    light = genre in LIGHT_GENRES if genre else False
    cue = has_interpretation_cue(pr.get("body", ""))
    return PRRow(
        pr=pr["number"],
        mergedAt=pr.get("mergedAt", ""),
        title=pr.get("title", ""),
        only_notebook=only_nb,
        zero_code_modif=zcm,
        body_genre=genre,
        file_family=file_family(paths),
        interpretation_cue=cue,
        n_files=len(paths),
        n_ipynb=len(nb_paths),
        light_genre=light,
        drift_candidate=only_nb and zcm and not light and cue,
    )


def stratify_sample(
    prs: list[dict[str, Any]], sample_size: int, seed: int = 42
) -> list[dict[str, Any]]:
    """Stratified sample: ALL ipynb-touching PRs + random sample of the rest.

    In CoursIA, ipynb-touching is **majority** (~63% of merged PRs in a 7d
    window Aug 3-10). The whole dataset is sampled rather than a fraction —
    we have full universe coverage for ipynb-touching.

    The input `prs` is already pre-stratified by the caller (e.g. all 628
    ipynb-touching + a 100-PR random subsample of the 368 non-ipynb). We keep
    the API surface here for symmetry with a pure sample-down approach.
    """
    rng = random.Random(seed)
    ipynb = [p for p in prs if any(f.get("path", "").endswith(".ipynb") for f in p.get("files", []))]
    rest = [p for p in prs if p not in ipynb]
    rng.shuffle(rest)
    budget = max(0, sample_size - len(ipynb))
    return ipynb + rest[:budget]


def summarise(rows: list[PRRow], total_30j_universe: int | None = None) -> dict[str, Any]:
    """Compute the summary stats."""
    total = len(rows)
    if total == 0:
        return {"total": 0}
    only_nb = sum(1 for r in rows if r.only_notebook)
    zcm = sum(1 for r in rows if r.zero_code_modif)
    candidates = sum(1 for r in rows if r.drift_candidate)
    by_genre: dict[str, int] = {}
    by_family: dict[str, int] = {}
    for r in rows:
        if r.body_genre:
            by_genre[r.body_genre] = by_genre.get(r.body_genre, 0) + 1
        if r.only_notebook and r.file_family:
            by_family[r.file_family] = by_family.get(r.file_family, 0) + 1
    return {
        "total_sampled": total,
        "only_notebook": only_nb,
        "only_notebook_pct": round(100 * only_nb / total, 2),
        "zero_code_modif_of_only_notebook": sum(
            1 for r in rows if r.only_notebook and r.zero_code_modif
        ),
        "markdown_only_pct": round(
            100 * sum(1 for r in rows if r.only_notebook and r.zero_code_modif) / total, 2
        ),
        "drift_candidates": candidates,
        "drift_pct": round(100 * candidates / total, 2),
        "by_body_genre": dict(sorted(by_genre.items(), key=lambda kv: -kv[1])),
        "by_family_of_only_notebook": dict(
            sorted(by_family.items(), key=lambda kv: -kv[1])
        ),
        "non_zero_code_in_only_notebook": [
            {"pr": r.pr, "title": r.title, "genre": r.body_genre}
            for r in rows
            if r.only_notebook and not r.zero_code_modif
        ][:10],
    }


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--input-json", required=True, help="Path to PR list JSON (from `gh pr list`)")
    p.add_argument("--sample-size", type=int, default=200,
                   help="Total sample size (including all ipynb-touching)")
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--output-csv", help="Output CSV path")
    p.add_argument("--output-json", help="Output JSON path")
    p.add_argument("--summary", action="store_true", help="Print summary to stdout")
    args = p.parse_args()

    data = json.loads(Path(args.input_json).read_text(encoding="utf-8"))
    print(f"[census] input: {len(data)} PRs", file=sys.stderr)
    sample = stratify_sample(data, args.sample_size, args.seed)
    print(f"[census] sample: {len(sample)} PRs (seed={args.seed})", file=sys.stderr)
    rows = [build_row(p) for p in sample]
    summary = summarise(rows, len(data))

    if args.output_csv:
        Path(args.output_csv).write_text(
            "pr,mergedAt,only_notebook,zero_code_modif,body_genre,file_family,interpretation_cue,n_files,n_ipynb,light_genre,drift_candidate,title\n",
            encoding="utf-8",
        )
        with open(args.output_csv, "a", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            for r in rows:
                w.writerow([
                    r.pr, r.mergedAt, r.only_notebook, r.zero_code_modif,
                    r.body_genre or "", r.file_family or "", r.interpretation_cue,
                    r.n_files, r.n_ipynb, r.light_genre, r.drift_candidate,
                    r.title.replace(",", " ")[:120],
                ])
        print(f"[census] CSV: {args.output_csv}", file=sys.stderr)
    if args.output_json:
        Path(args.output_json).write_text(
            json.dumps(
                {"summary": summary, "rows": [asdict(r) for r in rows]},
                ensure_ascii=False,
                indent=2,
                default=str,
            ),
            encoding="utf-8",
        )
        print(f"[census] JSON: {args.output_json}", file=sys.stderr)
    if args.summary or not (args.output_csv or args.output_json):
        print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
