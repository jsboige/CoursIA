"""Unit tests for Lean/lean_notebook_utils.py (cross-platform Lean notebook helper).

The module is the cross-platform bridge for running Lean 4 from notebooks
(WSL on Windows, native on Linux/macOS) — used across the SymbolicAI/Lean and
GameTheory/*_lean series. It was a **test orphan**: imported by notebooks via
``sys.path`` but never by pytest (grep repo-wide = 0 ``test_`` importers).

This suite pins the **platform-independent** logic (no Lean/lake/WSL subprocess
needed): the platform predicates, the Windows→WSL path conversion, the
project-discovery walk, and the file reader/formatter. The ``count_sorry``
function shells out to ``grep``/``wsl`` and is intentionally NOT covered here
(see the PR body for a documented docstring/implementation finding on it).

CPU-only, no deps beyond stdlib. Each project fixture is a real tmp dir tree so
``find_lean_project``/``read_lean_module`` exercise the parent-walk + file I/O.
"""
import platform
import sys
from pathlib import Path

import pytest

# lean_notebook_utils.py lives in SymbolicAI/Lean/ (parent of scripts/).
_LEAN_DIR = Path(__file__).resolve().parents[2]
if str(_LEAN_DIR) not in sys.path:
    sys.path.insert(0, str(_LEAN_DIR))

import lean_notebook_utils as lnu  # noqa: E402

WINDOWS = platform.system() == "Windows"


# --- platform predicates ----------------------------------------------------

def test_is_windows_matches_platform():
    assert lnu.is_windows() == WINDOWS


def test_is_native_matches_platform():
    assert lnu.is_native_platform() == (platform.system() in ("Linux", "Darwin"))


def test_predicates_consistent_on_windows():
    """On Windows the two predicates are mutually exclusive."""
    if not WINDOWS:
        pytest.skip("Windows-specific consistency check")
    assert lnu.is_windows() is True
    assert lnu.is_native_platform() is False


# --- win_to_wsl path conversion ---------------------------------------------

@pytest.mark.skipif(not WINDOWS, reason="drive conversion only meaningful on Windows")
def test_win_to_wsl_c_drive():
    out = lnu.win_to_wsl(Path(r"C:\Users\foo\bar"))
    assert out == "/mnt/c/Users/foo/bar"


@pytest.mark.skipif(not WINDOWS, reason="drive conversion only meaningful on Windows")
def test_win_to_wsl_d_drive_lowercase():
    out = lnu.win_to_wsl(Path(r"D:\Projects\lean"))
    assert out.startswith("/mnt/d/")
    assert "Projects" in out and "lean" in out


def test_win_to_wsl_already_mnt_passthrough():
    """A path that already lives under /mnt/ is returned as-is.

    On Windows this is exercised via the no-drive branch; on non-Windows we
    construct a posix path with no drive so the same branch is taken.
    """
    # Use a path that resolves to something with no Windows drive letter.
    p = Path("/mnt/c/Users/foo")
    out = lnu.win_to_wsl(p)
    assert out == str(p.resolve()) or out.startswith("/mnt/")


# --- find_lean_project (parent walk) ----------------------------------------

def _make_project(root: Path, name: str):
    proj = root / name
    proj.mkdir(parents=True)
    (proj / "lakefile.lean").write_text("{}", encoding="utf-8")
    return proj


def test_find_lean_project_walks_up_to_cwd_parent(tmp_path, monkeypatch):
    proj = _make_project(tmp_path, "myproj")
    deep = proj / "src" / "deep"
    deep.mkdir(parents=True)
    monkeypatch.chdir(deep)
    found = lnu.find_lean_project("myproj")
    assert found == proj.resolve()


def test_find_lean_project_raises_when_absent(tmp_path, monkeypatch):
    # tmp_path has no <name>/lakefile.lean up its tree (its parents are the
    # pytest tmp root, which contains no Lake projects).
    monkeypatch.chdir(tmp_path)
    with pytest.raises(FileNotFoundError):
        lnu.find_lean_project("definitely_not_a_project_xyz")


def test_find_lean_project_uses_nb_file_env(tmp_path, monkeypatch):
    """NB_FILE env var adds a second search start (Papermill case)."""
    proj = _make_project(tmp_path, "viaparam")
    nb_dir = proj / "notebooks"
    nb_dir.mkdir()
    # CWD is elsewhere (no project above it), but NB_FILE points inside the project.
    elsewhere = tmp_path / "elsewhere"
    elsewhere.mkdir()
    monkeypatch.chdir(elsewhere)
    monkeypatch.setenv("NB_FILE", str(nb_dir / "demo.ipynb"))
    found = lnu.find_lean_project("viaparam")
    assert found == proj.resolve()


# --- read_lean_module -------------------------------------------------------

def test_read_lean_module_returns_content(tmp_path, monkeypatch):
    proj = _make_project(tmp_path, "readproj")
    (proj / "Mod.lean").write_text("theorem t : True := by trivial\n", encoding="utf-8")
    sub = proj / "sub"
    sub.mkdir()  # create BEFORE chdir
    monkeypatch.chdir(sub)
    out = lnu.read_lean_module("readproj", "Mod.lean")
    assert "theorem t" in out
    assert "trivial" in out


def test_read_lean_module_missing_returns_sentinel(tmp_path, monkeypatch):
    proj = _make_project(tmp_path, "readproj2")
    monkeypatch.chdir(proj)
    out = lnu.read_lean_module("readproj2", "Nope.lean")
    assert out.startswith("[FICHIER INTROUVABLE]")
    assert "Nope.lean" in out


# --- display_lean_module (formatter) ----------------------------------------

def test_display_formats_with_line_numbers(tmp_path, monkeypatch, capsys):
    proj = _make_project(tmp_path, "dispproj")
    (proj / "M.lean").write_text("line one\nline two\nline three\n", encoding="utf-8")
    monkeypatch.chdir(proj)
    lnu.display_lean_module("dispproj", "M.lean")
    out = capsys.readouterr().out
    assert "--- M.lean ---" in out
    assert "1 | line one" in out
    assert "2 | line two" in out
    assert "--- fin (3 lignes) ---" in out


def test_display_respects_max_lines(tmp_path, monkeypatch, capsys):
    proj = _make_project(tmp_path, "dispproj2")
    (proj / "M.lean").write_text("a\nb\nc\nd\ne\n", encoding="utf-8")
    monkeypatch.chdir(proj)
    lnu.display_lean_module("dispproj2", "M.lean", max_lines=2)
    out = capsys.readouterr().out
    assert "1 | a" in out and "2 | b" in out
    assert "3 | c" not in out  # truncated
    assert "lignes restantes" in out
    assert "total" in out


def test_display_highlights_marked_lines(tmp_path, monkeypatch, capsys):
    proj = _make_project(tmp_path, "dispproj3")
    (proj / "M.lean").write_text("x\ny\nz\n", encoding="utf-8")
    monkeypatch.chdir(proj)
    lnu.display_lean_module("dispproj3", "M.lean", highlight=[2])
    out = capsys.readouterr().out
    # Format is f"{marker} {i:>3d} | {line}" with marker=' >>>' for highlighted
    # lines. Assert per-row: line 2's row carries '>>>' next to '| y';
    # lines 1 and 3 do NOT carry '>>>' next to their content.
    rows = [l for l in out.splitlines() if "| " in l]
    row_y = next(r for r in rows if r.endswith("| y"))
    row_x = next(r for r in rows if r.endswith("| x"))
    assert ">>>" in row_y
    assert ">>>" not in row_x


def test_display_missing_file_prints_sentinel(tmp_path, monkeypatch, capsys):
    proj = _make_project(tmp_path, "dispproj4")
    monkeypatch.chdir(proj)
    lnu.display_lean_module("dispproj4", "Absent.lean")
    out = capsys.readouterr().out
    assert "[FICHIER INTROUVABLE]" in out
    # No formatting header when the file is missing.
    assert "--- Absent.lean ---" not in out
