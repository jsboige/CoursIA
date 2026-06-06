"""Tests for scripts/update_navigation.py — GameTheory navigation link updater."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from update_navigation import (
    STRUCTURE,
    SIDE_TRACKS,
    create_main_navigation,
    create_side_track_navigation,
    get_notebook_filename,
    get_side_track_filename,
    update_internal_references,
)


# ---------------------------------------------------------------------------
# get_notebook_filename / get_side_track_filename
# ---------------------------------------------------------------------------

class TestFilenames:
    def test_main_filename(self):
        assert get_notebook_filename(1, "Setup") == "GameTheory-1-Setup.ipynb"

    def test_side_track_filename(self):
        assert get_side_track_filename("2b") == "GameTheory-2b.ipynb"

    def test_complex_name(self):
        assert get_notebook_filename(4, "NashEquilibrium") == "GameTheory-4-NashEquilibrium.ipynb"


# ---------------------------------------------------------------------------
# create_main_navigation
# ---------------------------------------------------------------------------

class TestMainNavigation:
    def test_first_notebook_no_prev(self):
        nav = create_main_navigation(1, "Setup", [])
        assert "[<< " not in nav
        assert "[Index](README.md)" in nav
        assert "2-NormalForm" in nav

    def test_last_notebook_no_next(self):
        nav = create_main_navigation(17, "MultiAgent-RL", [])
        assert ">>" not in nav  # Last notebook has no next link
        assert "16-MechanismDesign" in nav
        assert "18-" not in nav

    def test_middle_notebook_both_links(self):
        nav = create_main_navigation(5, "ZeroSum-Minimax", [])
        assert "4-" in nav
        assert "6-" in nav
        assert "[Index](README.md)" in nav

    def test_side_tracks_included(self):
        nav = create_main_navigation(4, "NashEquilibrium", ["4b-Lean-NashExistence", "4c-NashExistence-Python"])
        assert "4b-Lean-NashExistence" in nav
        assert "4c-NashExistence-Python" in nav
        assert "Side tracks" in nav

    def test_no_side_tracks_line_when_empty(self):
        nav = create_main_navigation(3, "Topology2x2", [])
        assert "Side tracks" not in nav


# ---------------------------------------------------------------------------
# create_side_track_navigation
# ---------------------------------------------------------------------------

class TestSideTrackNavigation:
    def test_basic_side_track(self):
        nav = create_side_track_navigation("2b")
        assert "2-NormalForm" in nav
        assert "Index" in nav

    def test_sibling_links(self):
        nav = create_side_track_navigation("4b")
        assert "4c-NashExistence-Python" in nav
        assert "Autres side tracks" in nav

    def test_no_siblings(self):
        nav = create_side_track_navigation("2b")
        assert "Autres side tracks" not in nav


# ---------------------------------------------------------------------------
# update_internal_references
# ---------------------------------------------------------------------------

class TestUpdateReferences:
    def test_replaces_old_names(self, tmp_path):
        f = tmp_path / "test.txt"
        f.write_text("See GameTheory-8-BackwardInduction and GameTheory-17-Lean-Definitions", encoding="utf-8")
        mapping = {
            "GameTheory-8-BackwardInduction": "GameTheory-9-BackwardInduction",
            "GameTheory-17-Lean-Definitions": "GameTheory-2b-Lean-Definitions",
        }
        result = update_internal_references(str(f), mapping)
        assert result is True
        content = f.read_text(encoding="utf-8")
        assert "GameTheory-9-BackwardInduction" in content
        assert "GameTheory-2b-Lean-Definitions" in content
        assert "GameTheory-8-BackwardInduction" not in content

    def test_no_changes_needed(self, tmp_path):
        f = tmp_path / "test.txt"
        f.write_text("Already updated", encoding="utf-8")
        result = update_internal_references(str(f), {"old": "new"})
        assert result is False

    def test_multiple_occurrences(self, tmp_path):
        f = tmp_path / "test.txt"
        f.write_text("A-old-B-old-C", encoding="utf-8")
        result = update_internal_references(str(f), {"old": "new"})
        assert result is True
        assert f.read_text(encoding="utf-8") == "A-new-B-new-C"


# ---------------------------------------------------------------------------
# STRUCTURE / SIDE_TRACKS consistency
# ---------------------------------------------------------------------------

class TestStructureConsistency:
    def test_all_side_tracks_reference_valid_parent(self):
        for track_id, (parent_num, _desc) in SIDE_TRACKS.items():
            assert parent_num in STRUCTURE, f"Side track {track_id} references missing parent {parent_num}"

    def test_side_track_ids_match_structure(self):
        for num, (_name, tracks) in STRUCTURE.items():
            for track in tracks:
                track_id = track.split("-")[0]
                assert track_id in SIDE_TRACKS, f"Track {track_id} in STRUCTURE but not in SIDE_TRACKS"

    def test_structure_has_17_entries(self):
        assert len(STRUCTURE) == 17
        assert set(STRUCTURE.keys()) == set(range(1, 18))
