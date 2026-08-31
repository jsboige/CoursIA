"""Hot-subset ratchet for translation SRC_DRIFT (#13551).

Issue #13551 fixed the 47 hot cells repo-wide — cells whose source notebook
drifted (``SRC_DRIFT``) WHILE carrying at least one deposited translation
(``text_<lang>`` non-empty for a target language). Those rows are the ones
where drift destroys real linguistic work: the deposited translation no
longer matches the notebook it claims to translate. The 2000 remaining
``SRC_DRIFT`` rows have NO deposited translation (pre-T3 pivot-only rows) —
resyncing them is the "resync-only" pattern suspended by the coordinator
ruling on #6949 (2026-07-28), so the ratchet deliberately does NOT cover
them.

This test pins the hot subset at zero: from now on, any FR edit to a cell
that already carries a translation, landed without resyncing its CSV row,
turns the suite red — exactly the regression #13551 was opened for. The fix
procedure is per-cell (update ``text_fr``/``src_hash``/``hash_fr`` from the
current notebook source, re-translate ``text_<lang>``/``hash_<lang>`` when
the change is material) — NEVER a global re-extraction, which orphans the
deposited translations (the trap documented in the issue).

Two layers:
- ``test_hot_subset_is_zero`` — the ratchet over the real repo tree
  (skipped when the repo layout is absent, e.g. hermetic packaging runs).
- ``test_hot_subset_semantics`` — a hermetic tmp_path fixture pinning the
  *definition* of the hot subset (SRC_DRIFT + deposited translation), so a
  future refactor of ``check_csv`` that drops the SRC_DRIFT verdict or
  renames the ``text_<lang>`` columns is caught independently of the repo
  state.

stdlib-only, no network. Mirrors the skip style of
``test_translation_sync_t4_scope.py``.
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
REPO_ROOT = TRANSLATION_DIR.parent.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import check_translation_sync as t2  # noqa: E402
from check_perimeter import TARGET_LANGS  # noqa: E402

HEADER = [
    "notebook", "cell_id", "cell_type", "src_lang", "src_hash", "text_fr",
    "text_en", "text_es", "text_ar", "text_fa", "text_zh", "text_ru", "text_pt",
    "hash_fr", "hash_en", "hash_es", "hash_ar", "hash_fa", "hash_zh",
    "hash_ru", "hash_pt", "translate_policy",
]


def hot_anomalies(csv_path: Path, repo_root: Path) -> list[dict]:
    """SRC_DRIFT anomalies on rows that carry at least one deposited translation."""
    anomalies = t2.check_csv(csv_path, repo_root)
    with csv_path.open(encoding="utf-8-sig") as f:
        deposited = {
            row.get("cell_id", ""): any(
                (row.get(f"text_{lang}", "") or "").strip()
                for lang in TARGET_LANGS
            )
            for row in csv.DictReader(f)
            if row.get("cell_id")
        }
    return [
        a for a in anomalies
        if a.get("verdict") == "SRC_DRIFT" and deposited.get(a.get("cell_id", ""), False)
    ]


# ---------------------------------------------------------------------------
# Ratchet over the real repo
# ---------------------------------------------------------------------------


def test_hot_subset_is_zero():
    """Repo-wide SRC_DRIFT rows carrying a deposited translation == 0 (#13551).

    If this fails: an FR notebook edit landed on a cell that has a
    translation, without resyncing its CSV row. Fix per-cell (see the issue
    procedure) — do NOT run a global re-extraction, it orphans translations.
    """
    translations = REPO_ROOT / "translations"
    notebooks = REPO_ROOT / "MyIA.AI.Notebooks"
    if not translations.is_dir() or not notebooks.is_dir():
        pytest.skip("repo tree not present (test expects repo checkout)")
    hot: list[dict] = []
    for csv_path in sorted(translations.rglob("*.csv")):
        hot.extend(hot_anomalies(csv_path, REPO_ROOT))
    assert hot == [], (
        f"{len(hot)} hot cell(s): SRC_DRIFT on rows with deposited "
        f"translations — resync per-cell (never global extraction, #13551). "
        f"First offenders: {[ (a['notebook'], a['cell_id']) for a in hot[:5] ]}"
    )


# ---------------------------------------------------------------------------
# Hermetic semantics of the hot-subset definition
# ---------------------------------------------------------------------------


def _write_nb(path: Path, cells: list[tuple[str, str]]) -> None:
    import json
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
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=HEADER, lineterminator="\n")
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in HEADER})


def test_hot_subset_semantics(tmp_path):
    """SRC_DRIFT counts as hot ONLY when a translation is deposited.

    Three rows against one notebook whose cells have drifted past their
    stored src_hash: one with an EN translation (hot), one RU-only (hot),
    one pivot-only with no translation (NOT hot — resync-only territory,
    suspended per #6949).
    """
    nb_rel = "series/demo.ipynb"
    _write_nb(tmp_path / nb_rel, [
        ("cell-a", "# Titre A\n\nTexte A actuel." + " " * 10),  # drift + padding
        ("cell-b", "# Titre B\n\nTexte B actuel." + " " * 10),
        ("cell-c", "# Titre C\n\nTexte C actuel." + " " * 10),
    ])
    csv_path = tmp_path / "translations" / "demo.csv"
    _write_csv(csv_path, [
        {
            "notebook": nb_rel, "cell_id": "cell-a", "cell_type": "markdown",
            "src_lang": "fr", "src_hash": "deadbeefdeadbeef",
            "text_fr": "# Titre A\n\nTexte A ancien.",
            "text_en": "# Title A\n\nOld A text.",
        },
        {
            "notebook": nb_rel, "cell_id": "cell-b", "cell_type": "markdown",
            "src_lang": "fr", "src_hash": "deadbeefdeadbeef",
            "text_fr": "# Titre B\n\nTexte B ancien.",
            "text_ru": "# Заголовок B\n\nСтарый текст B.",
        },
        {
            "notebook": nb_rel, "cell_id": "cell-c", "cell_type": "markdown",
            "src_lang": "fr", "src_hash": "deadbeefdeadbeef",
            "text_fr": "# Titre C\n\nTexte C ancien.",
        },
    ])
    hot = hot_anomalies(csv_path, tmp_path)
    hot_ids = sorted(a["cell_id"] for a in hot)
    assert hot_ids == ["cell-a", "cell-b"], (
        f"hot subset must be exactly the SRC_DRIFT rows with deposited "
        f"translations, got {hot_ids}"
    )
    # And once the CSV rows are resynced to the current source, hot -> 0.
    with csv_path.open(encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    for r in rows:
        new_fr = {
            "cell-a": "# Titre A\n\nTexte A actuel." + " " * 10,
            "cell-b": "# Titre B\n\nTexte B actuel." + " " * 10,
            "cell-c": "# Titre C\n\nTexte C actuel." + " " * 10,
        }[r["cell_id"]]
        h = t2.cell_hash(new_fr)
        r["text_fr"], r["src_hash"], r["hash_fr"] = new_fr, h, h
    _write_csv(csv_path, rows)
    assert hot_anomalies(csv_path, tmp_path) == []


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
