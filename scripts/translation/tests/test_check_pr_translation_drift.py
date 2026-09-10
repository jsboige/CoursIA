"""Per-PR translation hot-drift attribution gate (#15322).

The repo-wide ratchet (``test_hot_subset_ratchet.py``, #13551) keeps the hot
subset at zero on main; its weakness is attribution -- when a prose-realignment
PR lands without resyncing the CSV, every open PR inherits the red. This gate
answers, per PR: which cells does THIS diff put into the hot subset?

The tests pin, in order of increasing scope:
- the exact flag set on a synthetic repo (hot flags; pivot-only and synced
  rows stay silent),
- the ATTRIBUTION property (pre-existing base drift, untouched by the PR,
  never flags; a re-modified drifted cell does),
- a NEW cell without any CSV row never flags,
- the replay of the three documented incidents (#15253 / #15136 / #15216) at
  their landing commits -- exact cell sets, the acceptance-4 positive control
  (a guard is validated by its false negatives, not its hits).

stdlib-only, no network. Mirrors the skip style of the sibling tests.
"""
from __future__ import annotations

import sys
import tempfile
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
REPO_ROOT = TRANSLATION_DIR.parent.parent
sys.path.insert(0, str(TRANSLATION_DIR))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))

import check_pr_translation_drift as g  # noqa: E402

# Documented incidents (issue #15322 table), replayed at their landing
# commits: (head sha, expected flagged cell ids).
DOCUMENTED_INCIDENTS = [
    ("917fbe0d5", {"cell-70d4b526", "cell-ebb412ad"}),   # #15253 finetuning
    ("378af0229", {"b07ca49a"}),                          # #15136 image
    ("272cbf3a7", {"43b69f3c", "fcebb55c", "8ba2019f", "a4b715be"}),  # #15216
]


@pytest.fixture()
def synthetic(tmp_path):
    csv_path, _ = g._synthetic_repo(tmp_path)
    return tmp_path, csv_path


def _flagged_ids(repo, nb_changed):
    csv_path = repo / "translations" / "demo.csv"
    return sorted(
        f["cell_id"] for f in g.evaluate(
            nb_changed, {csv_path: set(nb_changed)}, repo)
    )


def test_hot_cell_flags_pivot_and_synced_stay_silent(synthetic):
    repo, _ = synthetic
    ids = _flagged_ids(repo, {"series/demo.ipynb":
                              {"cell-hot", "cell-pivot", "cell-sync"}})
    assert ids == ["cell-hot"], (
        "seule la cellule derivee portant une traduction deposee doit flagger ;"
        f" recu {ids}"
    )


def test_attribution_preexisting_drift_never_flags(synthetic):
    """La derive pre-existante sur la base, non touchee par la PR, est
    invisible : c'est la propriete d'attribution qui manque au cliquet."""
    repo, _ = synthetic
    assert _flagged_ids(repo, {"series/demo.ipynb": set()}) == []


def test_remodified_drifted_cell_still_flags(synthetic):
    """Une cellule DEJA derivee sur la base, dont la PR re-modifie la source,
    doit flagger : la nouvelle modification est non-resynchronisee aussi.
    (Une difference d'ensembles hot@head - hot@base la raterait.)"""
    repo, _ = synthetic
    ids = _flagged_ids(repo, {"series/demo.ipynb": {"cell-hot", "cell-pivot"}})
    assert ids == ["cell-hot"]


def test_new_cell_without_csv_row_never_flags(synthetic):
    repo, _ = synthetic
    ids = _flagged_ids(repo, {"series/demo.ipynb": {"cell-brand-new"}})
    assert ids == []


def test_resynced_row_leaves_no_hot_anomaly(synthetic):
    """Le remede par-cellule (resynchro CSV) eteint le flag -- preuve que le
    signal suit le geste attendu de l'auteur, pas la forme du diff."""
    repo, _ = synthetic
    csv_path = repo / "translations" / "demo.csv"
    current = g.t2.cell_hash("# Titre chaud\n\nTexte actuel du hot.")
    import csv as _csv
    with csv_path.open(encoding="utf-8-sig") as f:
        rows = list(_csv.DictReader(f))
    for r in rows:
        if r["cell_id"] == "cell-hot":
            r["src_hash"] = current
            r["hash_fr"] = current
    g._write_csv(csv_path, rows)
    ids = _flagged_ids(repo, {"series/demo.ipynb": {"cell-hot"}})
    assert ids == []


def test_replay_documented_incidents():
    """Controle positif (acceptance 4) : les trois incidents documentes
    rejoues a leur atterrissage flaggent EXACTEMENT les cellules listees.
    Saute si l'historique est absent (clone shallow / hermetique)."""
    if not (REPO_ROOT / "translations").is_dir():
        pytest.skip("repo tree not present")
    for sha, expected in DOCUMENTED_INCIDENTS:
        probe = g.git("rev-parse", "--verify", "--quiet", sha + "^{commit}",
                      cwd=REPO_ROOT)
        if probe is None:
            pytest.skip(f"{sha} absent de l'historique local")
        res = g.run(sha + "^", head_ref=sha, repo_root=REPO_ROOT)
        got = {f["cell_id"] for f in res["flagged"]}
        assert got == expected, (
            f"replay {sha}: attendu {sorted(expected)}, recu {sorted(got)}"
        )


def test_self_test_passes():
    if not (REPO_ROOT / "translations").is_dir():
        pytest.skip("repo tree not present")
    assert g.self_test(cwd=REPO_ROOT) == 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
