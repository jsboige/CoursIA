#!/usr/bin/env python3
"""Advisory per-PR gate: names the cells whose SOURCE this PR modifies while
they carry a deposited translation, without the CSV row being resynced (#15322).

The repo-wide ratchet (``scripts/translation/tests/test_hot_subset_ratchet.py``,
#13551) keeps the hot subset -- ``SRC_DRIFT`` rows with at least one non-empty
``text_<lang>`` -- at zero on ``main``. Its weakness is ATTRIBUTION, not
coverage: when a prose-realignment PR merges without resyncing the CSV, the
ratchet goes red on ``main`` and therefore on EVERY open PR that inherits it
(36 PRs red at once; documented incidents #15253 / #15136 / #15216). The lane
that sees the red reads it as its own defect and burns a cycle on a diff it
did not break. This gate answers, per PR, the only question the ratchet cannot:
did THIS PR put cells into the hot subset?

Predicate reuse (issue constraint: no second predicate that could diverge from
the ratchet it protects): the hot classification comes from
``check_translation_sync.check_csv`` itself -- an ``SRC_DRIFT`` anomaly at head
on a row with a deposited translation. The only new ingredient is the DELTA:
cells whose ``cell_hash`` differs between the merge base and head of the
changed notebooks. A cell already drifted on the base, untouched by this PR,
never flags; a cell the PR re-modifies while it was already drifted DOES flag
(the new modification is unresynced too). The base is resolved through
``merge-base`` (never ``pull_request.base.sha``, which points at main -- the
stale-base lesson of #15427).

Formally-synced-but-semantically-stale rows (a resync that re-pins
``text_fr``/``src_hash`` without re-translating a material change) are OUT OF
SCOPE here by design: the hot predicate is hash-formal, and judging materiality
per-cell is the suspended ruling of #6949. This gate reports exactly what the
ratchet would report, minus the inherited debt.

Advisory per the issue (acceptance 3): findings publish under a neutral
check-run naming the cells; the switch to blocking waits on a measured trigger
rate. Wired as ``blocking=False`` in the fast lane TRANCHE2.

Usage:
    python check_pr_translation_drift.py <base-ref> [--json]
    python check_pr_translation_drift.py --self-test
    python check_pr_translation_drift.py <base-ref> --head <sha> [--json]  # replay

Exit 1 iff at least one cell enters the hot subset because of this diff (the
fast-lane engine renders that as an advisory neutral, never a gate).
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import sys
import tempfile
from pathlib import Path

THIS_DIR = Path(__file__).resolve().parent
REPO_ROOT = THIS_DIR.parent.parent
sys.path.insert(0, str(THIS_DIR))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))

import check_translation_sync as t2  # noqa: E402
from check_output_failure_text import (  # noqa: E402
    changed_notebooks,
    git,
    read_notebook_at,
    resolve_base,
)
from check_perimeter import TARGET_LANGS  # noqa: E402

# Founding occurrence replayed by --self-test (issue table): the #15136 merge
# left cell b07ca49a of image.csv behind -- source edited, translation
# deposited, CSV row untouched. The other two incidents (#15253 finetuning,
# #15216 casestudies) are replayed by the pytest suite.
SELF_TEST_BASE = "378af0229^"
SELF_TEST_HEAD = "378af0229"
SELF_TEST_NOTEBOOK = "MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-2-GPT-5-Image-Generation.ipynb"
SELF_TEST_CELLS = ("b07ca49a",)


def cell_hash_map(nb: dict | None) -> dict[str, str]:
    """{cell_id: hash} over a PARSED notebook, mirroring t2.load_notebook_cells.

    Same cell filter and same ``t2.cell_hash`` as the CSV rows -- the parsed-JSON
    variant exists only because the git plumbing hands back parsed notebooks,
    while ``load_notebook_cells`` takes a path.
    """
    out: dict[str, str] = {}
    for cell in (nb or {}).get("cells", []) or []:
        cid = cell.get("id")
        if not cid or cell.get("cell_type") not in ("markdown", "code"):
            continue
        out[cid] = t2.cell_hash("".join(cell.get("source", [])))
    return out


def changed_source_cells(base: str, nb_rel: str, head: str | None,
                         cwd: Path) -> set[str]:
    """cell_ids whose source hash differs between base and head of one notebook.

    A cell NEW in head (no base counterpart) counts as changed: if a CSV row
    somehow references that id, the drift is still this diff's doing. A notebook
    unreadable at head returns an empty set -- a deleted/unreadable source is
    ORPHAN territory (#15326), not the hot subset this gate protects.
    """
    head_nb = read_notebook_at(head, nb_rel, cwd=cwd)
    if head_nb is None:
        return set()
    base_map = cell_hash_map(read_notebook_at(base, nb_rel, cwd=cwd))
    return {
        cid for cid, h in cell_hash_map(head_nb).items()
        if base_map.get(cid) != h
    }


def deposited_by_cell(csv_path: Path) -> dict[str, list[str]]:
    """{cell_id: langs with a deposited text_<lang>} -- the ratchet's deposited
    filter (``hot_anomalies`` in test_hot_subset_ratchet.py), kept identical."""
    out: dict[str, list[str]] = {}
    with csv_path.open(encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            cid = row.get("cell_id", "")
            if not cid:
                continue
            langs = [l for l in TARGET_LANGS
                     if (row.get(f"text_{l}", "") or "").strip()]
            if langs:
                out[cid] = langs
    return out


def evaluate(nb_changed: dict[str, set[str]], covering: dict[Path, set[str]],
             repo_root: Path) -> list[dict]:
    """The core: hot-at-head (via t2.check_csv) intersected with the PR delta.

    ``covering`` maps each candidate CSV to the changed notebooks it references;
    ``t2.check_csv`` runs on each once (the expensive part -- it loads the
    notebooks referenced by the CSV -- exactly the cost the repo-wide ratchet
    already pays per PR).
    """
    findings: list[dict] = []
    for csv_path, nb_rels in sorted(covering.items()):
        for anomaly in t2.check_csv(csv_path, repo_root):
            if anomaly.get("verdict") != "SRC_DRIFT":
                continue
            cid = anomaly.get("cell_id", "")
            if cid not in nb_changed.get(anomaly.get("notebook", ""), ()):
                continue
            langs = deposited_by_cell(csv_path).get(cid, [])
            if not langs:
                continue
            findings.append({
                "csv": csv_path.name,
                "notebook": anomaly["notebook"],
                "cell_id": cid,
                "langs": langs,
                "detail": anomaly.get("detail", ""),
            })
    return findings


def csvs_covering_worktree(translations_dir: Path,
                           nb_rels: set[str]) -> dict[Path, set[str]]:
    """Scan the working-tree CSVs for rows referencing any changed notebook."""
    covering: dict[Path, set[str]] = {}
    if not translations_dir.is_dir():
        return covering
    for csv_path in sorted(translations_dir.rglob("*.csv")):
        hits = set()
        with csv_path.open(encoding="utf-8-sig") as f:
            for row in csv.DictReader(f):
                if row.get("notebook") in nb_rels:
                    hits.add(row["notebook"])
        if hits:
            covering[csv_path] = hits
    return covering


def run(base_ref: str, head_ref: str | None = None,
        repo_root: Path | None = None) -> dict:
    """Live (or replayed) evaluation: delta first, then the reused predicate."""
    repo_root = (repo_root or Path.cwd()).resolve()
    head = head_ref or "HEAD"
    if head_ref is None:
        # Live mode: merge-base against the checked-out branch (never
        # pull_request.base.sha, which points at main -- #15427).
        base = resolve_base(base_ref, cwd=repo_root)
    else:
        # Replay: merge-base between the two historical refs.
        out = git("merge-base", base_ref, head_ref, cwd=repo_root)
        base = out.strip() if out and out.strip() else base_ref
    changed_nbs = changed_notebooks(base, head=head, cwd=repo_root)
    nb_changed: dict[str, set[str]] = {}
    for nb_rel in changed_nbs:
        cells = changed_source_cells(base, nb_rel, head, repo_root)
        if cells:
            nb_changed[nb_rel] = cells

    result: dict = {
        "base_ref": base_ref, "merge_base": base, "head": head,
        "changed_notebooks": changed_nbs,
        "covered_notebooks": sorted(nb_changed),
    }

    if not nb_changed:
        result["flagged"] = []
        return result

    if head_ref is None:
        covering = csvs_covering_worktree(
            repo_root / "translations", set(nb_changed))
        result["flagged"] = evaluate(nb_changed, covering, repo_root)
        result["csvs_scanned"] = len(covering)
        return result

    # Replay at a historical sha: materialize the CSV + the CHANGED notebooks
    # at that sha in a temp snapshot. Rows referencing unchanged notebooks
    # become ORPHAN in the snapshot and are filtered out -- their hot status
    # cannot enter the findings anyway (the delta intersection is empty).
    with tempfile.TemporaryDirectory(prefix="pr-translation-drift-") as tmp:
        tmp_root = Path(tmp)
        covering: dict[Path, set[str]] = {}
        for csv_path in sorted((repo_root / "translations").rglob("*.csv")):
            rel = csv_path.relative_to(repo_root).as_posix()
            raw = git("show", f"{head_ref}:{rel}", cwd=repo_root)
            if raw is None:
                continue  # CSV did not exist at that sha
            hits = set()
            # StringIO, not splitlines(): quoted fields carry embedded
            # newlines (translations are multi-line) and csv must see them.
            for row in csv.DictReader(io.StringIO(raw)):
                if row.get("notebook") in nb_changed:
                    hits.add(row["notebook"])
            if not hits:
                continue
            snap_csv = tmp_root / rel
            snap_csv.parent.mkdir(parents=True, exist_ok=True)
            with snap_csv.open("w", encoding="utf-8", newline="") as f:
                f.write(raw)
            covering[snap_csv] = hits
        for nb_rel in nb_changed:
            raw = git("show", f"{head_ref}:{nb_rel}", cwd=repo_root)
            if raw is None:
                continue
            snap_nb = tmp_root / nb_rel
            snap_nb.parent.mkdir(parents=True, exist_ok=True)
            with snap_nb.open("w", encoding="utf-8", newline="") as f:
                f.write(raw)
        result["flagged"] = evaluate(nb_changed, covering, tmp_root)
        result["csvs_scanned"] = len(covering)
    return result


# ---------------------------------------------------------------------------
# Self-test: a detector that cannot be shown to fire is indistinguishable from
# one that is unplugged (same contract as the output ratchets, #11685/#12817).
# ---------------------------------------------------------------------------

def _write_nb(path: Path, cells: list[tuple[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": [
            {"cell_type": "markdown", "id": cid, "metadata": {},
             "source": text.splitlines(keepends=True)}
            for cid, text in cells
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


def _write_csv(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    header = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash",
              "text_fr", "text_en", "text_es", "text_ar", "text_fa",
              "text_zh", "text_ru", "text_pt", "hash_fr", "hash_en",
              "hash_es", "hash_ar", "hash_fa", "hash_zh", "hash_ru",
              "hash_pt", "translate_policy"]
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=header, lineterminator="\n")
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in header})


def _synthetic_repo(tmp: Path) -> tuple[Path, Path]:
    """One notebook, three cells, one CSV: hot / pivot-only / synced."""
    nb_rel = "series/demo.ipynb"
    _write_nb(tmp / nb_rel, [
        ("cell-hot", "# Titre chaud\n\nTexte actuel du hot."),
        ("cell-pivot", "# Titre pivot\n\nTexte actuel du pivot."),
        ("cell-sync", "# Titre sync\n\nTexte actuel du sync."),
    ])
    current = t2.cell_hash("# Titre sync\n\nTexte actuel du sync.")
    csv_path = tmp / "translations" / "demo.csv"
    _write_csv(csv_path, [
        {"notebook": nb_rel, "cell_id": "cell-hot",
         "cell_type": "markdown", "src_lang": "fr",
         "src_hash": "deadbeefdeadbeef",
         "text_fr": "# Titre chaud\n\nTexte ancien.",
         "text_en": "# Hot title\n\nOld text."},
        {"notebook": nb_rel, "cell_id": "cell-pivot",
         "cell_type": "markdown", "src_lang": "fr",
         "src_hash": "deadbeefdeadbeef",
         "text_fr": "# Titre pivot\n\nTexte ancien."},
        {"notebook": nb_rel, "cell_id": "cell-sync",
         "cell_type": "markdown", "src_lang": "fr",
         "src_hash": current,
         "text_fr": "# Titre sync\n\nTexte actuel du sync.",
         "text_en": "# Sync title\n\nCurrent text."},
    ])
    return csv_path, tmp / nb_rel


def self_test(cwd: Path | None = None) -> int:
    """Positive + negative control on synthetic fixtures, then the founding
    replay (#15136: image.csv cell b07ca49a) when the repo history is present."""
    failures: list[str] = []

    with tempfile.TemporaryDirectory(prefix="t2-selftest-") as tmp_s:
        tmp = Path(tmp_s)
        csv_path, _ = _synthetic_repo(tmp)

        # Positive control: all three cells changed by the "PR" -> only the
        # cell with a deposited translation flags.
        flagged = evaluate(
            {"series/demo.ipynb": {"cell-hot", "cell-pivot", "cell-sync"}},
            {csv_path: {"series/demo.ipynb"}}, tmp)
        ids = sorted(f["cell_id"] for f in flagged)
        if ids != ["cell-hot"]:
            failures.append(f"controle positif: attendu ['cell-hot'], eu {ids}")

        # Attribution control: the same repo state, PR touches nothing ->
        # pre-existing drift never flags.
        flagged = evaluate({"series/demo.ipynb": set()},
                           {csv_path: {"series/demo.ipynb"}}, tmp)
        if flagged != []:
            failures.append(
                f"controle attribution: la derive pre-existante a flagge: {flagged}")

        # Re-modification control: a cell ALREADY drifted on the base, whose
        # source the PR changes again, must flag (the new edit is unresynced).
        flagged = evaluate({"series/demo.ipynb": {"cell-hot", "cell-pivot"}},
                           {csv_path: {"series/demo.ipynb"}}, tmp)
        ids = sorted(f["cell_id"] for f in flagged)
        if ids != ["cell-hot"]:
            failures.append(f"controle re-modification: attendu ['cell-hot'], eu {ids}")

    # Founding replay (#15136). Hermetic contexts (no git history) degrade to
    # a note -- the synthetic controls above still prove the detector fires.
    if cwd is None:
        cwd = REPO_ROOT
    if git("rev-parse", "--verify", "--quiet", SELF_TEST_HEAD + "^{commit}",
           cwd=cwd) is not None:
        res = run(SELF_TEST_BASE, head_ref=SELF_TEST_HEAD, repo_root=cwd)
        got = tuple(sorted(f["cell_id"] for f in res["flagged"]))
        if got != SELF_TEST_CELLS:
            failures.append(
                f"replay {SELF_TEST_HEAD}: attendu {SELF_TEST_CELLS}, eu {got}")
    else:
        print("NOTE: historique git absent -- replay du cas fondateur saute "
              "(controles synthetiques uniquement).")

    if failures:
        for f in failures:
            print("SELF-TEST FAIL: " + f, file=sys.stderr)
        return 1
    print("self-test OK: positif/negatif/attribution + replay fondateur.")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Advisory gate: cells entering the translation hot subset "
                    "because of THIS PR (source edited under a deposited "
                    "translation, CSV row not resynced). Issue #15322.")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--head",
                    help="Head sha for replay (default: working tree HEAD)")
    ap.add_argument("--self-test", action="store_true",
                    help="Positive + negative + attribution controls, then "
                         "replay of the founding occurrence (#15136)")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if not args.base:
        ap.error("base ref required (or --self-test)")

    res = run(args.base, head_ref=args.head)
    flagged = res["flagged"]

    if args.as_json:
        print(json.dumps(res, indent=2, ensure_ascii=False))
    else:
        print(f"base {args.base} -> merge-base {res['merge_base'][:12]}"
              f" | {len(res['changed_notebooks'])} changed notebook(s)"
              f" | {len(res['covered_notebooks'])} covered by translations/"
              f" | {len(flagged)} cell(s) flagged (advisory)")
        for f in flagged:
            print(f"\nFLAGGED (advisory) {f['notebook']} cell {f['cell_id']}"
                  f" [{', '.join(f['langs'])}] via {f['csv']}")
            print("  Cette PR modifie la source d'une cellule portant une"
                  " traduction deposee sans resynchroniser sa ligne CSV.")
        if flagged:
            print("\nRemede per-cell (mise a jour text_fr/src_hash/hash_fr +"
                  " re-traduction si le changement est materiel) -- JAMAIS la"
                  " re-extraction globale, qui orpheline les traductions"
                  " deposees (#13551).")
        else:
            print("AUCUNE cellule n'entre dans le sous-ensemble chaud du fait"
                  " de cette PR.")
    return 1 if flagged else 0


if __name__ == "__main__":
    sys.exit(main())
