"""Tests for scripts/check_docs_index.py — docs index reachability (#13748).

Covers the acceptance of issue #13748 (item « Index docs/ reference 100 % des
live ») and the positive control that keeps the organ honest:

- a doc linked from the index is reachable; an unlinked one is reported;
- reachability is transitive through a sub-directory index (the metric the
  index itself documents: *directement ou via un index de sous-repertoire*);
- ``docs/archive/`` is frozen by design and out of the live set;
- the closure never escapes ``docs/`` (fail-closed: it may under-credit
  reachability, never over-credit it);
- the real tree is green — this is the acceptance, read from the repository;
- ``--expect-unreachable`` renders rc=2 when the control is unmet, so a dead
  detection path cannot be mistaken for a clean tree.
"""

import sys
import textwrap
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_docs_index
from check_docs_index import find_unreachable


def _write(path: Path, content: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(textwrap.dedent(content), encoding="utf-8")
    return path


def _tree(root: Path) -> None:
    """Synthetic docs/ tree: one indexed doc, one orphan, one nested doc."""
    _write(root / "docs" / "README.md", """\
        # Index

        | Fichier | Description |
        |---------|-------------|
        | [linked.md](linked.md) | Lie depuis l'index |
    """)
    _write(root / "docs" / "linked.md", "# Lie\n")
    _write(root / "docs" / "unlinked.md", "# Jamais cite\n")


def test_linked_doc_is_reachable_and_unlinked_doc_is_reported(tmp_path):
    _tree(tmp_path)
    unreachable, live = find_unreachable(tmp_path)
    assert live == 3  # README + linked + unlinked
    assert unreachable == ["docs/unlinked.md"]


def test_reachability_goes_through_a_subdirectory_index(tmp_path):
    _tree(tmp_path)
    _write(tmp_path / "docs" / "sub" / "README.md", """\
        # Index du sous-repertoire

        | Fichier | Description |
        |---------|-------------|
        | [nested.md](nested.md) | Doc imbriquee |
    """)
    _write(tmp_path / "docs" / "sub" / "nested.md", "# Doc imbriquee\n")
    _write(tmp_path / "docs" / "README.md", """\
        # Index

        | Fichier | Description |
        |---------|-------------|
        | [linked.md](linked.md) | Lie depuis l'index |
        | [sub/README.md](sub/README.md) | Index du sous-repertoire |
    """)
    unreachable, _ = find_unreachable(tmp_path)
    assert "docs/sub/nested.md" not in unreachable  # atteint via sub/README.md
    assert unreachable == ["docs/unlinked.md"]


def test_archive_is_frozen_and_out_of_the_live_set(tmp_path):
    _tree(tmp_path)
    _write(tmp_path / "docs" / "archive" / "vieux.md", "# Archive\n")
    _write(tmp_path / "docs" / "archive" / "README.md", "# Archive\n")
    unreachable, live = find_unreachable(tmp_path)
    assert live == 3  # l'archive ne compte pas dans le vivant
    assert not [p for p in unreachable if "archive" in p]


def test_closure_does_not_escape_docs(tmp_path):
    """A link out of docs/ is not followed, even if it links back inside."""
    _tree(tmp_path)
    _write(tmp_path / "outside.md", "[retour](docs/unlinked.md)\n")
    _write(tmp_path / "docs" / "README.md", """\
        # Index

        | Fichier | Description |
        |---------|-------------|
        | [linked.md](linked.md) | Lie depuis l'index |
        | [hors docs](../outside.md) | Ne doit pas etre suivi |
    """)
    unreachable, live = find_unreachable(tmp_path)
    # `outside.md` n'est pas un doc de docs/ : hors set vivant, donc ni compte
    # ni credite. Le doc qu'il cite reste inatteignable (fail-closed).
    assert live == 3
    assert unreachable == ["docs/unlinked.md"]


def test_missing_index_is_an_error(tmp_path):
    with pytest.raises(FileNotFoundError):
        find_unreachable(tmp_path)


def test_real_repository_has_no_unreachable_live_doc():
    """L'acceptance de #13748, lue sur l'arbre reel : 100 % atteignables."""
    unreachable, live = find_unreachable()
    assert live > 150, f"trop peu de docs vivants detectes ({live}) — detection morte ?"
    assert unreachable == [], f"docs vivants inatteignables : {unreachable}"


def test_positive_control_fails_when_unmet(tmp_path, monkeypatch):
    _tree(tmp_path)  # 1 inatteignable seulement
    monkeypatch.setattr(check_docs_index, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(sys, "argv",
                        ["check_docs_index.py", "--expect-unreachable", "5"])
    with pytest.raises(SystemExit) as exc:
        check_docs_index.main()
    assert exc.value.code == 2


def test_exit_code_is_1_when_a_doc_is_unreachable(tmp_path, monkeypatch):
    _tree(tmp_path)
    monkeypatch.setattr(check_docs_index, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(sys, "argv", ["check_docs_index.py", "--json"])
    with pytest.raises(SystemExit) as exc:
        check_docs_index.main()
    assert exc.value.code == 1
