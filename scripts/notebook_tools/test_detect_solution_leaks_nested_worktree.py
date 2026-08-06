"""Tests unitaires pour detect_solution_leaks.discover_notebooks.

Couvre le FP class "nested-git-worktree" : un répertoire de travail contient un
worktree git (`.git` *fichier* pointant vers `.git/worktrees/<name>`) ; sans
filtre, `os.walk` descend dedans et double-compte tous les notebooks.

Run: python scripts/notebook_tools/test_detect_solution_leaks_nested_worktree.py
"""
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from detect_solution_leaks import discover_notebooks  # noqa: E02


def _make_notebook(path: Path) -> None:
    """Build a minimal but valid .ipynb at `path`."""
    nb = {
        "cells": [
            {
                "cell_type": "markdown",
                "metadata": {},
                "source": ["# Exercice 1"],
            },
            {
                "cell_type": "code",
                "execution_count": 1,
                "metadata": {},
                "outputs": [],
                "source": ["x = 1\ny = 2\nprint(x + y)"],
            },
        ],
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "name": "python3", "language": "python"}
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f)


def _make_git_worktree_file(path: Path, parent_repo: str = "/tmp/parent") -> None:
    """Create a `.git` *file* (not directory) simulating a git worktree pointer."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(f"gitdir: {parent_repo}/.git/worktrees/test-orphan\n")


class TestNestedWorktreeSkip(unittest.TestCase):
    """FP class: nested git worktree must be skipped to avoid double-count."""

    def test_orphan_worktree_is_skipped(self):
        """A `.git` file inside a subdirectory must NOT cause descent."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "tree"
            # Main tree notebook (kept)
            _make_notebook(root / "MyIA.AI.Notebooks" / "MainTest.ipynb")
            # Orphan worktree: `.git` FILE pointing elsewhere
            orphan_dir = root / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "orphan"
            _make_git_worktree_file(orphan_dir / ".git")
            # Notebook inside the orphan (would be double-counted without the fix)
            _make_notebook(orphan_dir / "MyIA.AI.Notebooks" / "Search" / "OrphanTest.ipynb")

            found = discover_notebooks(str(root))
            rel = [os.path.relpath(p, str(root)) for p in found]

            self.assertIn(os.path.join("MyIA.AI.Notebooks", "MainTest.ipynb"), rel)
            self.assertNotIn(
                os.path.join(
                    "MyIA.AI.Notebooks",
                    "SymbolicAI",
                    "Lean",
                    "orphan",
                    "MyIA.AI.Notebooks",
                    "Search",
                    "OrphanTest.ipynb",
                ),
                rel,
                msg=f"Orphan was not skipped — found: {rel}",
            )
            self.assertEqual(len(found), 1, msg=f"Expected exactly 1, got {len(found)}: {rel}")

    def test_plain_git_directory_is_still_skipped(self):
        """`.git` as a *directory* (not a file) is still excluded (regression guard)."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            git_dir = root / ".git"
            git_dir.mkdir(exist_ok=True)
            (git_dir / "HEAD").write_text("ref: refs/heads/main\n")
            # Notebook anywhere inside is fine, but the .git/* contents are NOT notebooks
            _make_notebook(root / "MyIA.AI.Notebooks" / "MainTest.ipynb")
            found = discover_notebooks(str(root))
            rel = [os.path.relpath(p, str(root)) for p in found]
            self.assertEqual(rel, [os.path.join("MyIA.AI.Notebooks", "MainTest.ipynb")])

    def test_no_git_marker_at_all(self):
        """No `.git` anywhere → behave as before, scan everything (sanity)."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "tree"
            _make_notebook(root / "A.ipynb")
            _make_notebook(root / "sub" / "B.ipynb")
            found = discover_notebooks(str(root))
            self.assertEqual(len(found), 2)

    def test_dotfile_dotgit_file_alongside_real_notebooks(self):
        """`.git` file with sibling notebooks in same dir: only notebooks are picked up."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "tree"
            worktree = root / "wt"
            worktree.mkdir(parents=True)
            _make_git_worktree_file(worktree / ".git")
            _make_notebook(worktree / "Search.ipynb")  # must be skipped (descend-bait)
            _make_notebook(root / "Top.ipynb")  # must be picked up
            found = discover_notebooks(str(root))
            rel = sorted(os.path.relpath(p, str(root)) for p in found)
            self.assertEqual(rel, ["Top.ipynb"])


if __name__ == "__main__":
    unittest.main(verbosity=2)