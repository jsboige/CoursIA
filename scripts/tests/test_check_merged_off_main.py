#!/usr/bin/env python3
"""Tests for ``scripts/check_merged_off_main.py`` (#12723).

Why this file exists
--------------------
A merged PR with a feature-branch base can carry content that never
reaches ``main`` -- two pedagogical deliverables sat lost with zero
signal anywhere. The guard classifies delivered-new paths against
``main`` by **path and content** (renames excluded by blob), and the
classification has exactly one trap: added-ness must be measured against
the base state **before** the PR's own merge (merge-base), because the
base tip now *contains* that merge. A detector that measures against the
tip renders 0 on a live loss -- the zero-of-denominator trap the issue
forbids -- and these tests pin that.

The founding positive control: on the 2026-08-25 repo state the scan of
600 merged PRs flags EXACTLY #12423 (MGS-26 notebook absent from main,
base consumed) and clears #12458 (repaired via #12736 landing 3.2 on
main), #12405, #11938, #11931 and #12727.

Run::

    python -m pytest scripts/tests/test_check_merged_off_main.py -v
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_merged_off_main as g  # noqa: E402


def _pr(number, base, head, files, body="See #12373"):
    return {
        "number": number,
        "title": f"PR #{number}",
        "baseRefName": base,
        "headRefName": head,
        "mergedAt": "2026-08-23T04:52:06Z",
        "body": body,
        "files": [{"path": p, "additions": a} for p, a in files],
    }


class FakeRepo:
    """World state for one test: refs, trees, blob map."""

    def __init__(self, *, main_paths, main_blobs, pre_base_paths,
                 head_paths, head_blob_shas, refs_exist=True):
        self.main_paths = set(main_paths)
        self.main_blobs = dict(main_blobs)
        self.pre_base_paths = set(pre_base_paths)
        self.head_paths = set(head_paths)
        self.head_blob_shas = dict(head_blob_shas)
        self.refs_exist = refs_exist

    def install(self, monkeypatch):
        monkeypatch.setattr(g, "_tree_paths", self._tree_paths)
        monkeypatch.setattr(g, "_tree_blob_map", lambda ref: self.main_blobs)
        monkeypatch.setattr(g, "_ref_exists",
                            lambda ref: self.refs_exist)
        monkeypatch.setattr(g, "_merge_base",
                            lambda a, b: "sha-mb" if self.refs_exist else None)
        monkeypatch.setattr(
            g, "_run",
            lambda cmd: self._rev_parse(cmd) if cmd[:2] == ["git", "rev-parse"]
            else None,
        )

    def _tree_paths(self, ref):
        if ref == "origin/main":
            return self.main_paths
        if ref == "sha-mb":
            return self.pre_base_paths
        if ref.startswith("origin/"):
            return self.head_paths  # base or head branch tips
        return set()

    def _rev_parse(self, cmd):
        # git rev-parse origin/<head>:<path>
        ref_path = cmd[2] if len(cmd) > 2 else ""
        ref, _, path = ref_path.partition(":")
        sha = self.head_blob_shas.get(path)
        return sha + "\n" if sha else None


LOST_NB = "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-26-EquilibriumOptimizer-vs-Mealpy.ipynb"


def test_base_consumed_shape_flags_lost(monkeypatch):
    """#12423 shape: base consumed before the child -- the deliverable
    sits on a branch nobody pulls. Added on head lineage, absent from
    main, blob nowhere on main -> LOST, flagged."""
    world = FakeRepo(
        main_paths=["README.md"],
        main_blobs={"README.md": "sha-readme"},
        pre_base_paths=["README.md"],
        head_paths=[LOST_NB, "README.md"],
        head_blob_shas={LOST_NB: "sha-mgs26"},
    )
    world.install(monkeypatch)
    monkeypatch.setattr(g, "gh_merged_prs",
                        lambda n: [_pr(12423, "feature/12403-mgs25-woa",
                                       "feature/mgs26-eo",
                                       [(LOST_NB, 900), ("README.md", 5)])])
    flagged = g.scan(600, post=False)
    assert len(flagged) == 1
    v = flagged[0]
    assert v.number == 12423
    assert [lv.path for lv in v.lost] == [LOST_NB]
    assert 12373 in v.linked_issues


def test_base_open_shape_still_flags_lost(monkeypatch):
    """#12458-original shape: base PR still open, the deliverable lives
    in its diff. Same detection path (the shapes differ in repair
    gesture, not in detection)."""
    world = FakeRepo(
        main_paths=["README.md"],
        main_blobs={"README.md": "sha-readme"},
        pre_base_paths=["README.md"],
        head_paths=["3.2-Optimisateurs.ipynb"],
        head_blob_shas={"3.2-Optimisateurs.ipynb": "sha-32"},
    )
    world.install(monkeypatch)
    monkeypatch.setattr(g, "gh_merged_prs",
                        lambda n: [_pr(12458, "feature/12407-dl31",
                                       "feature/12408-dl32",
                                       [("3.2-Optimisateurs.ipynb", 1358)])])
    flagged = g.scan(600, post=False)
    assert len(flagged) == 1
    assert flagged[0].lost[0].path == "3.2-Optimisateurs.ipynb"


def test_repaired_by_other_pr_is_clean(monkeypatch):
    """#12458-today shape: another PR landed the path on main -- the
    flag must clear (PRESENT), not linger on the historical merge."""
    world = FakeRepo(
        main_paths=["README.md", "3.2-Optimisateurs.ipynb"],
        main_blobs={"README.md": "sha-readme",
                    "3.2-Optimisateurs.ipynb": "sha-32"},
        pre_base_paths=["README.md"],
        head_paths=["3.2-Optimisateurs.ipynb"],
        head_blob_shas={"3.2-Optimisateurs.ipynb": "sha-32"},
    )
    world.install(monkeypatch)
    monkeypatch.setattr(g, "gh_merged_prs",
                        lambda n: [_pr(12458, "feature/12407-dl31",
                                       "feature/12408-dl32",
                                       [("3.2-Optimisateurs.ipynb", 1358)])])
    assert g.scan(600, post=False) == []


def test_renamed_blob_lands_elsewhere_not_lost(monkeypatch):
    """A delivered path absent from main because the target was RENAMED
    elsewhere is not a loss -- the blob exists on main under another
    path. A guard that over-accuses is disarmed after two false
    positives (#12723: fichiers renommes)."""
    world = FakeRepo(
        main_paths=["README.md", "ML/zero-pad-renamed.ipynb"],
        main_blobs={"README.md": "sha-readme",
                    "ML/zero-pad-renamed.ipynb": "sha-same-content"},
        pre_base_paths=["README.md"],
        head_paths=["ML/GameTheory-4b.ipynb"],
        head_blob_shas={"ML/GameTheory-4b.ipynb": "sha-same-content"},
    )
    world.install(monkeypatch)
    monkeypatch.setattr(g, "gh_merged_prs",
                        lambda n: [_pr(11999, "feature/x", "feature/y",
                                       [("ML/GameTheory-4b.ipynb", 400)])])
    flagged = g.scan(600, post=False)
    assert flagged == []
    # And the classification says RENAMED with the landing path.


def test_renamed_verdict_carries_landing_path(monkeypatch):
    world = FakeRepo(
        main_paths=["ML/zero-pad-renamed.ipynb"],
        main_blobs={"ML/zero-pad-renamed.ipynb": "sha-same-content"},
        pre_base_paths=[],
        head_paths=["ML/GameTheory-4b.ipynb"],
        head_blob_shas={"ML/GameTheory-4b.ipynb": "sha-same-content"},
    )
    world.install(monkeypatch)
    monkeypatch.setattr(g, "gh_merged_prs",
                        lambda n: [_pr(11999, "feature/x", "feature/y",
                                       [("ML/GameTheory-4b.ipynb", 400)])])
    pr = _pr(11999, "feature/x", "feature/y",
             [("ML/GameTheory-4b.ipynb", 400)])
    v = g.classify_pr(pr, world.main_paths, world.main_blobs)
    renamed = [rv for rv in v.verdicts if rv.status == "RENAMED"]
    assert renamed and renamed[0].landed_at == "ML/zero-pad-renamed.ipynb"
    assert not v.flagged


def test_modified_file_not_flagged(monkeypatch):
    """A path that pre-existed on the merge-base was MODIFIED by the PR,
    not delivered-new: even absent from main (later unrelated rename),
    it must not be attributed as this PR's loss."""
    world = FakeRepo(
        main_paths=[],
        main_blobs={},
        pre_base_paths=["docs/OLD-NAME.md"],
        head_paths=["docs/OLD-NAME.md"],
        head_blob_shas={"docs/OLD-NAME.md": "sha-doc"},
    )
    world.install(monkeypatch)
    monkeypatch.setattr(g, "gh_merged_prs",
                        lambda n: [_pr(11938, "feature/11829", "feature/y",
                                       [("docs/OLD-NAME.md", 40)])])
    assert g.scan(600, post=False) == []


def test_branch_gone_reports_base_gone_without_guessing(monkeypatch):
    """Without live branches we cannot establish added-ness; report
    BASE-GONE rather than guessing (a wrong guess hides a loss or cries
    wolf). Never flagged on a guess."""
    world = FakeRepo(
        main_paths=[], main_blobs={}, pre_base_paths=[], head_paths=[],
        head_blob_shas={}, refs_exist=False,
    )
    world.install(monkeypatch)
    monkeypatch.setattr(g, "gh_merged_prs",
                        lambda n: [_pr(11638, "feature/gone", "feature/also",
                                       [("lost.ipynb", 100)])])
    assert g.scan(600, post=False) == []


def test_base_main_prs_are_never_scanned(monkeypatch):
    """The guard's population is baseRefName != main, by construction."""
    world = FakeRepo(
        main_paths=["README.md"], main_blobs={"README.md": "sha-r"},
        pre_base_paths=[], head_paths=["lost.ipynb"],
        head_blob_shas={"lost.ipynb": "sha-lost"},
    )
    world.install(monkeypatch)
    monkeypatch.setattr(
        g, "gh_merged_prs",
        lambda n: [_pr(1, "main", "feature/a", [("whatever.ipynb", 10)]),
                   _pr(2, "feature/b", "feature/c", [("lost.ipynb", 10)])])
    # Give #2 a loss shape.
    world.main_paths = set()
    flagged = g.scan(600, post=False)
    assert [v.number for v in flagged] == [2]


def test_linked_issues_parsed_from_body():
    body = "Grain: ...\n\nSee #12373 for the epic. Closes #12418. Part of #42."
    assert g.linked_issues_from_body(body) == [42, 12373, 12418]
    assert g.linked_issues_from_body("") == []


def test_comment_names_paths_branch_and_label():
    pr = _pr(12423, "feature/12403-mgs25-woa", "feature/mgs26-eo",
             [(LOST_NB, 900)])
    v = g.PrVerdict(number=12423, title=pr["title"], base=pr["baseRefName"],
                    head=pr["headRefName"], merged_at=pr["mergedAt"],
                    verdicts=[g.PathVerdict(LOST_NB, "LOST")],
                    linked_issues=[12373])
    text = g.render_comment(v)
    assert g.LABEL in text
    assert LOST_NB in text
    assert "feature/mgs26-eo" in text
    assert "#12723" in text


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
