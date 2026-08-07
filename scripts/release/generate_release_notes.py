#!/usr/bin/env python3
"""Generate release notes for a CoursIA semester tag (v<annee>.S<semestre>) from
the on-disk COURSE_CATALOG.generated.json (issue #9856).

WHY THIS EXISTS (per #9856): "0 tag / 0 release pour ~95 forks etudiants --
poser v2026.S2 et generer les notes". The acceptance is explicit:

    gh release list renvoie au moins une release, dont les notes citent
    des comptes **lus dans le catalogue**, jamais recopies a la main.

This script makes the acceptance literal: every number in the rendered
markdown comes from the JSON, recomputed at tag-time. Re-running the script
on a newer catalogue produces a newer set of counts -- there is no notion of
"stale hand-typed count" because there is no hand-typed count anywhere.

DESIGN (per #9856 design decision): the tag schema is v<annee>.S<semestre>.
The next tag is v2026.S2. Pedagogical repository = semester-based, not semver
(no API to version). Argument ``--tag v2026.S2`` is the only positional
required. Argument ``--catalogue`` defaults to the standard path on main
(the cron-regenerated file). Argument ``--out`` defaults to stdout.

CONSTRAINTS (these exist for reasons):

  - Stdlib-only. CI advisory tools in this repo (grain_tag.py,
    variation_light_cap.py, check_lane_claim.py) are all stdlib-only so the
    CI matrix does not depend on a per-script venv. A release-notes generator
    is no different: it ships with the PR that introduced it.

  - Counts are derived, not interpolated. If a user runs the script with a
    catalogue that says 6 in some count, the markdown says 6. No smoothing,
    no rounding to nearest 10.

  - The "series added since rentree" section is OPTIONAL (--since YYYY-MM-DD).
    If omitted, that section is skipped -- we never fabricate series additions
    we cannot attest from the catalogue.

  - The series README links are derived from the ``serie`` field via the
    standard MyIA.AI.Notebooks/<serie>/README.md convention. If a README does
    not exist on disk, the link is rendered with a leading "(README absent) "
    prefix and a verification command is printed -- NOT silently dropped.

USAGE

    # default: read catalogue from standard path, write markdown to stdout
    python scripts/release/generate_release_notes.py --tag v2026.S2

    # write to file
    python scripts/release/generate_release_notes.py --tag v2026.S2 \
        --out RELEASE_NOTES_v2026.S2.md

    # with "added since rentree" section
    python scripts/release/generate_release_notes.py --tag v2026.S2 \
        --since 2026-09-01

EXIT CODES

  - 0: success. Notes are written (or printed).
  - 2: catalogue missing or unreadable JSON.
  - 3: catalogue is empty (no entries). We refuse to emit a release on an
       empty catalogue -- better to fail loud than ship a release with a
       single zero-line table.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

# The standard location, on main, of the catalogue the cron regenerates daily.
DEFAULT_CATALOGUE = Path("COURSE_CATALOG.generated.json")

# Conventional README path per serie. The script does NOT assert these exist --
# it renders the link anyway and annotates "(README absent, verifier: ...)"
# when the file is missing on disk. This is the same anti-fabrication
# discipline as the rest of the file.
SERIE_README = {
    "CaseStudies": "MyIA.AI.Notebooks/CaseStudies/README.md",
    "GameTheory": "MyIA.AI.Notebooks/GameTheory/README.md",
    "GenAI": "MyIA.AI.Notebooks/GenAI/README.md",
    "IIT": "MyIA.AI.Notebooks/IIT/README.md",
    "ML": "MyIA.AI.Notebooks/ML/README.md",
    "Probas": "MyIA.AI.Notebooks/Probas/README.md",
    "QuantConnect": "MyIA.AI.Notebooks/QuantConnect/README.md",
    "RL": "MyIA.AI.Notebooks/RL/README.md",
    "Search": "MyIA.AI.Notebooks/Search/README.md",
    "Sudoku": "MyIA.AI.Notebooks/Sudoku/README.md",
    "SymbolicAI": "MyIA.AI.Notebooks/SymbolicAI/README.md",
}


def load_catalogue(path: Path) -> list[dict]:
    """Load and minimally validate the catalogue.

    A successful load returns a list of entry dicts (the canonical shape
    observed on main). A failure raises -- the caller decides the exit code.
    """
    if not path.exists():
        raise FileNotFoundError(f"catalogue not found at {path}")
    with path.open("r", encoding="utf-8") as fh:
        data = json.load(fh)
    if not isinstance(data, list):
        # The historical shape was a dict {"entries": [...]} on an early
        # cron iteration. We tolerate both for forward-compat with archives.
        if isinstance(data, dict) and "entries" in data and isinstance(data["entries"], list):
            return data["entries"]
        raise ValueError(
            f"catalogue at {path} is neither a list nor a dict-with-entries; got {type(data).__name__}"
        )
    return data


def count_by(entries: list[dict], key: str) -> dict[str, int]:
    """Count occurrences of entries[key], skipping entries that lack the key.

    Counts are derived from the live data -- not interpolated. ``None`` and
    missing keys are bucketed under ``"(unknown)"`` so they appear in the
    table rather than vanishing silently.
    """
    out: Counter[str] = Counter()
    for e in entries:
        v = e.get(key)
        out[str(v) if v is not None else "(unknown)"] += 1
    return dict(sorted(out.items(), key=lambda kv: (-kv[1], kv[0])))


def entries_added_since(entries: list[dict], since: datetime) -> list[dict]:
    """Filter entries whose last_success_sha landed in the catalogue on/after
    ``since``. The catalogue does not track *creation* date -- only the last
    successful execution (``executed_at``) -- so this is the closest honest
    proxy: a notebook that has NEVER been executed has ``executed_at = None``
    and is excluded, which is the correct conservative choice for "added
    since rentree".
    """
    out = []
    for e in entries:
        ts = e.get("executed_at")
        if not ts:
            continue
        try:
            # ``executed_at`` carries a TZ offset like ``+02:00`` -- the parser
            # below round-trips it correctly via fromisoformat (3.11+).
            dt = datetime.fromisoformat(ts)
        except ValueError:
            continue
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        if dt >= since:
            out.append(e)
    return out


def render_series_readme_link(serie: str, repo_root: Path) -> str:
    """Render the README link for ``serie``. Annotates "(README absent)" if the
    file does not exist on disk so the operator can verify before cutting the
    release -- we do not silently drop the link or invent one.
    """
    rel = SERIE_README.get(serie)
    if rel is None:
        return f"`{serie}` (no README convention registered)"
    target = repo_root / rel
    if not target.exists():
        return f"[`{rel}`]({rel}) (README absent: verifier `ls {rel}`)"
    return f"[`{rel}`]({rel})"


def render_notes(
    entries: list[dict],
    *,
    tag: str,
    since: datetime | None,
    repo_root: Path,
    generated_at: datetime,
) -> str:
    """Build the full release-notes markdown. Pure function of its inputs --
    given the same catalogue and tag, it produces byte-identical markdown
    (within the generated_at timestamp). Determinism matters: a reviewer
    diffing two release notes must see only the catalogue diff, not the
    generator diff.
    """
    if not entries:
        raise ValueError("refusing to emit release notes for an empty catalogue")

    by_serie = count_by(entries, "serie")
    by_status = count_by(entries, "status")
    by_maturity = count_by(entries, "maturity")
    by_kernel = count_by(entries, "kernel")
    total = len(entries)

    # Generated timestamp is injected as a UTC ISO 8601 string (the canonical
    # format across this repo's tooling). We use Z-suffix explicit UTC,
    # never local-time-with-Z (lesson: incident 2026-08-07 dashboard stamp).
    gen_utc = generated_at.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    lines: list[str] = []
    lines.append(f"# Release `{tag}`")
    lines.append("")
    lines.append(
        f"Notes generees depuis `COURSE_CATALOG.generated.json` "
        f"a l'instant du tag. "
        f"Catalogue comptant **{total} notebooks** au moment de la generation."
    )
    lines.append("")
    lines.append(f"_Genere le {gen_utc} (UTC)._")
    lines.append("")

    # --- Totaux ---------------------------------------------------------------
    lines.append("## Totaux")
    lines.append("")
    lines.append(f"- Notebooks catalogues : **{total}**")
    lines.append(f"- Series distinctes : **{len(by_serie)}**")
    lines.append(f"- Kernels distincts : **{len(by_kernel)}**")
    lines.append("")

    # --- Repartition par statut ---------------------------------------------
    lines.append("## Repartition par statut")
    lines.append("")
    lines.append("| Statut | Compte |")
    lines.append("| --- | ---: |")
    for st, n in by_status.items():
        lines.append(f"| {st} | {n} |")
    lines.append("")

    # --- Repartition par maturite -------------------------------------------
    lines.append("## Repartition par maturite")
    lines.append("")
    lines.append("| Maturite | Compte |")
    lines.append("| --- | ---: |")
    for m, n in by_maturity.items():
        lines.append(f"| {m} | {n} |")
    lines.append("")

    # --- Repartition par kernel ---------------------------------------------
    lines.append("## Repartition par kernel")
    lines.append("")
    lines.append("| Kernel | Compte |")
    lines.append("| --- | ---: |")
    for k, n in by_kernel.items():
        lines.append(f"| {k} | {n} |")
    lines.append("")

    # --- Repartition par serie ----------------------------------------------
    lines.append("## Repartition par serie")
    lines.append("")
    lines.append("| Serie | Compte | README |")
    lines.append("| --- | ---: | --- |")
    for s, n in by_serie.items():
        lines.append(f"| {s} | {n} | {render_series_readme_link(s, repo_root)} |")
    lines.append("")

    # --- Sub-grain optionnel : ajouts depuis rentree ------------------------
    if since is not None:
        added = entries_added_since(entries, since)
        lines.append("## Notebooks executes depuis la rentree")
        lines.append("")
        lines.append(
            f"Filtre : `executed_at >= {since.date().isoformat()}`. "
            f"Compte : **{len(added)}**. "
            "Le catalogue ne suit pas la date de creation du notebook ; "
            "ce proxy reflete les notebooks *executes au moins une fois* "
            "depuis la date de reference, ce qui est la definition la plus "
            "conservatrice d'activite dans la periode."
        )
        lines.append("")
        if added:
            by_serie_added = count_by(added, "serie")
            lines.append("| Serie | Compte (executions depuis rentree) |")
            lines.append("| --- | ---: |")
            for s, n in by_serie_added.items():
                lines.append(f"| {s} | {n} |")
        else:
            lines.append("_Aucun notebook ne satisfait le filtre._")
        lines.append("")

    # --- Source de verite ----------------------------------------------------
    lines.append("## Source de verite")
    lines.append("")
    lines.append(
        "Ces notes sont generees par `scripts/release/generate_release_notes.py`. "
        "Les comptes ci-dessus sont lus dans `COURSE_CATALOG.generated.json` "
        "et recalcules a chaque execution. Pour regenerer apres une mise a "
        "jour du catalogue (cron quotidien sur `main`), relancer la commande "
        "du PR d'introduction. Aucun compte n'est recopie a la main."
    )
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Generate CoursIA semester-tag release notes from the catalogue.",
    )
    p.add_argument(
        "--tag",
        required=True,
        help="Release tag (e.g. v2026.S2). Used as the title and the anchor.",
    )
    p.add_argument(
        "--catalogue",
        type=Path,
        default=DEFAULT_CATALOGUE,
        help=f"Path to COURSE_CATALOG.generated.json (default: {DEFAULT_CATALOGUE}).",
    )
    p.add_argument(
        "--since",
        type=str,
        default=None,
        help=(
            "Optional ISO date (YYYY-MM-DD). If set, emits a 'since rentree' "
            "section filtered on executed_at >= <since>. NOT set by default "
            "because 'rentree' is school-year-specific -- the operator picks."
        ),
    )
    p.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output file path. If omitted, prints to stdout.",
    )
    p.add_argument(
        "--repo-root",
        type=Path,
        default=Path("."),
        help="Repository root, used to verify serie README paths exist (default: cwd).",
    )
    args = p.parse_args(argv)

    since: datetime | None = None
    if args.since:
        try:
            since = datetime.fromisoformat(args.since).replace(tzinfo=timezone.utc)
        except ValueError:
            print(f"error: --since must be YYYY-MM-DD, got {args.since!r}", file=sys.stderr)
            return 2

    try:
        entries = load_catalogue(args.catalogue)
    except (FileNotFoundError, ValueError, json.JSONDecodeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if not entries:
        print(
            f"error: catalogue at {args.catalogue} contains 0 entries; refusing to emit",
            file=sys.stderr,
        )
        return 3

    notes = render_notes(
        entries,
        tag=args.tag,
        since=since,
        repo_root=args.repo_root,
        generated_at=datetime.now(timezone.utc),
    )

    if args.out is None:
        sys.stdout.write(notes)
    else:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(notes, encoding="utf-8")
        print(f"wrote {len(notes)} bytes to {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
