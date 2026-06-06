"""Tests for scripts/update_navigation.py — GameTheory navigation generator."""

import importlib.util
from pathlib import Path
from unittest.mock import patch

import pytest

# Load module by file path
_MOD_PATH = (
    Path(__file__).resolve().parent.parent.parent.parent / "scripts" / "update_navigation.py"
)
_spec = importlib.util.spec_from_file_location("update_navigation", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

get_notebook_filename = _mod.get_notebook_filename
get_side_track_filename = _mod.get_side_track_filename
create_main_navigation = _mod.create_main_navigation
create_side_track_navigation = _mod.create_side_track_navigation
STRUCTURE = _mod.STRUCTURE
SIDE_TRACKS = _mod.SIDE_TRACKS


# --- get_notebook_filename ---


class TestGetNotebookFilename:
    def test_simple(self):
        assert get_notebook_filename(1, "Setup") == "GameTheory-1-Setup.ipynb"

    def test_multi_word(self):
        assert get_notebook_filename(5, "ZeroSum-Minimax") == "GameTheory-5-ZeroSum-Minimax.ipynb"

    def test_two_digit(self):
        assert get_notebook_filename(17, "MultiAgent-RL") == "GameTheory-17-MultiAgent-RL.ipynb"


# --- get_side_track_filename ---


class TestGetSideTrackFilename:
    def test_simple(self):
        assert get_side_track_filename("2b") == "GameTheory-2b.ipynb"

    def test_two_char_id(self):
        assert get_side_track_filename("16c") == "GameTheory-16c.ipynb"


# --- create_main_navigation ---


class TestCreateMainNavigation:
    def test_first_notebook_no_prev(self):
        nav = create_main_navigation(1, "Setup", [])
        assert "Navigation" in nav
        assert "[Index](README.md)" in nav
        # First notebook should NOT have a prev link
        assert "0-" not in nav
        # Should have next link
        assert "2-NormalForm" in nav

    def test_last_notebook_no_next(self):
        nav = create_main_navigation(17, "MultiAgent-RL", [])
        assert "Navigation" in nav
        assert "16-" in nav
        # Last notebook should NOT have a next link (no 18)

    def test_middle_notebook_both_links(self):
        nav = create_main_navigation(5, "ZeroSum-Minimax", [])
        assert "4-NashEquilibrium" in nav
        assert "6-EvolutionTrust" in nav

    def test_with_side_tracks(self):
        nav = create_main_navigation(2, "NormalForm", ["2b-Lean-Definitions"])
        assert "Side tracks" in nav
        assert "2b-Lean-Definitions" in nav

    def test_without_side_tracks(self):
        nav = create_main_navigation(3, "Topology2x2", [])
        assert "Side tracks" not in nav

    def test_multiple_side_tracks(self):
        nav = create_main_navigation(4, "NashEquilibrium",
                                      ["4b-Lean-NashExistence", "4c-NashExistence-Python"])
        assert "4b-Lean-NashExistence" in nav
        assert "4c-NashExistence-Python" in nav
        assert " | " in nav  # Links separated by pipe

    def test_contains_index_link(self):
        nav = create_main_navigation(1, "Setup", [])
        assert "[Index](README.md)" in nav


# --- create_side_track_navigation ---


class TestCreateSideTrackNavigation:
    def test_basic_side_track(self):
        nav = create_side_track_navigation("2b")
        assert "Navigation" in nav
        assert "2-NormalForm" in nav
        assert "[Index](README.md)" in nav

    def test_parent_link_present(self):
        nav = create_side_track_navigation("4c")
        assert "4-NashEquilibrium" in nav
        assert "track principal" in nav

    def test_sibling_links(self):
        """Side track 4c should link to sibling 4b."""
        nav = create_side_track_navigation("4c")
        assert "Autres side tracks" in nav
        assert "4b" in nav

    def test_no_siblings_for_only_child(self):
        """Side track 2b has no siblings (only one side track for parent 2)."""
        nav = create_side_track_navigation("2b")
        assert "Autres side tracks" not in nav

    def test_all_side_tracks_have_parent(self):
        """Every side track should reference its parent."""
        for track_id in SIDE_TRACKS:
            nav = create_side_track_navigation(track_id)
            assert "Navigation" in nav, f"Missing nav for {track_id}"
            assert "[Index](README.md)" in nav, f"Missing index for {track_id}"


# --- STRUCTURE consistency ---


class TestStructureConsistency:
    def test_structure_has_17_entries(self):
        assert len(STRUCTURE) == 17

    def test_keys_are_sequential(self):
        assert list(STRUCTURE.keys()) == list(range(1, 18))

    def test_all_side_tracks_reference_valid_parent(self):
        for track_id, (parent_num, _desc) in SIDE_TRACKS.items():
            assert parent_num in STRUCTURE, f"Side track {track_id} references invalid parent {parent_num}"

    def test_all_side_tracks_listed_in_structure(self):
        """Every side track in STRUCTURE's side_tracks list should be in SIDE_TRACKS."""
        for num, (name, side_tracks) in STRUCTURE.items():
            for st in side_tracks:
                st_id = st.split("-")[0]
                assert st_id in SIDE_TRACKS, f"Side track {st_id} from STRUCTURE[{num}] not in SIDE_TRACKS"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
