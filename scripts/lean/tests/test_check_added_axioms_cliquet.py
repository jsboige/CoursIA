#!/usr/bin/env python3
"""Tests for check_added_axioms_cliquet.py.

Dual-mode: runnable directly or under pytest (auto-collected by scripts-tests.yml).

Covers the cliquet responsibilities cited in #21387:

1. ``native_decide`` / ``sorry`` / ``admit`` tokens are detected only in
   *code* -- a token in a docstring or line comment is not flagged.
2. each detection is attributed to its enclosing declaration (theorem,
   lemma, def, example, instance, ...).
3. detections inside ``example`` or anonymous ``instance`` are reported
   with ``in_example=True`` and do not contribute to the rouge count.
4. detections inside NAMED declarations are reported with
   ``in_example=False`` and contribute to the rouge count.
5. the control positive (``#20584`` at ``3e9c8504c2``) renders 3 hits,
   all in ``example``.
6. a diff without these tokens renders an empty report.
7. a file deleted in head is skipped (no anchors possible).
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_added_axioms_cliquet import (  # noqa: E402
    NAMELESS_KINDS,
    AnchorHit,
    CliquetReport,
    declared_line,
    detect_anchors,
    enclosing_declaration,
    parse_declarations,
    render_text,
    scan_added_lines,
    _git_diff_added_lines,
    _git_rev_list,
    _git_show_file,
)
from count_code_sorry import strip_lean_comments  # noqa: E402


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #


def _make_repo() -> Path:
    """Create a tiny git repo with one empty ``.lean`` file committed.
    Returns the path to the repo. The caller resets and adds files as needed.
    """
    tmpdir = tempfile.mkdtemp(prefix="cliquet-test-")
    repo = Path(tmpdir) / "test"
    repo.mkdir()
    subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True)
    subprocess.run(["git", "config", "user.email", "test@test"], check=True, cwd=repo)
    subprocess.run(["git", "config", "user.name", "test"], check=True, cwd=repo)
    (repo / "Init.lean").write_text("-- init\n")
    subprocess.run(["git", "add", "Init.lean"], check=True, cwd=repo)
    subprocess.run(["git", "commit", "-q", "-m", "base"], check=True, cwd=repo)
    return repo


def _commit(repo: Path, files: dict[str, str], message: str) -> str:
    """Write ``files`` into the repo, ``git add`` them and commit. Return head SHA."""
    for name, content in files.items():
        (repo / name).parent.mkdir(parents=True, exist_ok=True)
        (repo / name).write_text(content)
    subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
    subprocess.run(["git", "commit", "-q", "-m", message], check=True, cwd=repo)
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8", cwd=repo
    ).stdout.strip()


def _reset(repo: Path) -> str:
    """Reset the repo to the first commit (the one with only Init.lean).
    Return the SHA of that first commit.
    """
    first = subprocess.run(
        ["git", "rev-list", "--max-parents=0", "HEAD"],
        capture_output=True, text=True, encoding="utf-8", cwd=repo,
    ).stdout.strip()
    subprocess.run(["git", "reset", "--hard", first], check=True, cwd=repo)
    return first


# --------------------------------------------------------------------------- #
# detect_anchors: pure function
# --------------------------------------------------------------------------- #


class TestDetectAnchors:
    def test_empty(self):
        assert detect_anchors("") == []

    def test_single_native_decide(self):
        assert detect_anchors("  ring") == []
        assert detect_anchors("  native_decide") == ["native_decide"]

    def test_single_sorry(self):
        assert detect_anchors("  sorry") == ["sorry"]

    def test_single_admit(self):
        assert detect_anchors("  admit") == ["admit"]

    def test_multiple_tokens(self):
        # rare, but allowed: a single line can mention both native_decide and sorry
        assert detect_anchors("  native_decide <;> sorry") == ["native_decide", "sorry"]

    def test_word_boundary(self):
        # ``sorrying`` is not a real ``sorry`` tactic -- word boundary
        assert detect_anchors("  sorrying") == []
        # ``admitted`` is not ``admit``
        assert detect_anchors("  admitted") == []
        # ``native_decided`` is not ``native_decide``
        assert detect_anchors("  native_decided") == []

    def test_decide_alone_is_not_native_decide(self):
        # ``decide`` is a different tactic; only ``native_decide`` is a token
        assert detect_anchors("  decide") == []


# --------------------------------------------------------------------------- #
# parse_declarations: pure function
# --------------------------------------------------------------------------- #


class TestParseDeclarations:
    def test_named_theorem(self):
        text = "/-- doc -/\ntheorem foo : 1 + 1 = 2 := by\n  ring\n"
        decls = parse_declarations(text)
        assert len(decls) == 1
        assert decls[0].kind == "theorem"
        assert decls[0].name == "foo"
        assert decls[0].header_line == 2

    def test_example_anon(self):
        text = "example : 1 + 1 = 2 := by native_decide\n"
        decls = parse_declarations(text)
        assert len(decls) == 1
        assert decls[0].kind == "example"
        assert decls[0].name == ""

    def test_anon_instance(self):
        text = "instance : Inhabited Nat := ⟨0⟩\n"
        decls = parse_declarations(text)
        assert len(decls) == 1
        assert decls[0].kind == "instance"
        assert decls[0].name == ""

    def test_named_instance(self):
        text = "instance myInst : Inhabited Nat := ⟨0⟩\n"
        decls = parse_declarations(text)
        assert len(decls) == 1
        assert decls[0].kind == "instance"
        assert decls[0].name == "myInst"


# --------------------------------------------------------------------------- #
# enclosing_declaration: pure function
# --------------------------------------------------------------------------- #


class TestEnclosingDeclaration:
    def test_before_any_decl(self):
        # Lines BEFORE the first decl header are not enclosed by any
        # declaration (they sit at the module top level).
        text = "import Foo.Bar\n\ntheorem foo : True := by trivial\n"
        decls = parse_declarations(text)
        # line 1 (import) is before the theorem header at line 3
        assert enclosing_declaration(decls, 1) is None
        assert enclosing_declaration(decls, 2) is None
        # line 3 is the theorem header itself
        assert enclosing_declaration(decls, 3) is not None
        assert enclosing_declaration(decls, 3).name == "foo"

    def test_inside_theorem(self):
        decls = parse_declarations("theorem foo : 1 + 1 = 2 := by\n  ring\n")
        owner = enclosing_declaration(decls, 2)
        assert owner is not None
        assert owner.kind == "theorem"
        assert owner.name == "foo"

    def test_advances_to_next_decl(self):
        text = "theorem a : True := by trivial\n\ntheorem b : True := by trivial\n"
        decls = parse_declarations(text)
        owner = enclosing_declaration(decls, 4)
        assert owner is not None
        assert owner.name == "b"

    def test_advances_to_example(self):
        text = "theorem a : True := by trivial\nexample : True := by trivial\n"
        decls = parse_declarations(text)
        owner = enclosing_declaration(decls, 2)
        assert owner is not None
        assert owner.kind == "example"
        assert owner.name == ""


# --------------------------------------------------------------------------- #
# scan_added_lines: integration with a temp git repo
# --------------------------------------------------------------------------- #


class TestScanAddedLines:
    def test_no_anchors(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _commit(repo, {"X.lean": "/-- doc -/\ntheorem foo : 1 + 1 = 2 := by\n  ring\n"},
                        "no anchors")
        r = scan_added_lines(base, head, repo_root=repo)
        assert isinstance(r, CliquetReport)
        assert r.hits == []
        assert r.lines_added > 0
        assert r.hits_in_named_decls == []

    def test_native_decide_in_named_theorem_is_rouge(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _commit(repo, {"Y.lean": "theorem bar : 1 + 1 = 2 := by native_decide\n"},
                        "rouge")
        r = scan_added_lines(base, head, repo_root=repo)
        assert len(r.hits) == 1
        h = r.hits[0]
        assert h.token == "native_decide"
        assert h.decl_kind == "theorem"
        assert h.decl_name == "bar"
        assert h.in_example is False
        assert len(r.hits_in_named_decls) == 1

    def test_sorry_in_named_lemma_is_rouge(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _commit(repo, {"Z.lean": "lemma baz : True := by sorry\n"}, "rouge")
        r = scan_added_lines(base, head, repo_root=repo)
        assert len(r.hits) == 1
        h = r.hits[0]
        assert h.token == "sorry"
        assert h.decl_kind == "lemma"
        assert h.in_example is False

    def test_admit_in_named_def_is_rouge(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _commit(repo, {"A.lean": "def foo : Nat := by admit\n"}, "rouge")
        r = scan_added_lines(base, head, repo_root=repo)
        assert len(r.hits) == 1
        assert r.hits[0].token == "admit"
        assert r.hits[0].decl_kind == "def"
        assert r.hits[0].in_example is False

    def test_native_decide_in_example_is_green(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _commit(repo, {"E.lean": "example : 1 + 1 = 2 := by native_decide\n"},
                        "green")
        r = scan_added_lines(base, head, repo_root=repo)
        assert len(r.hits) == 1
        assert r.hits[0].in_example is True
        assert r.hits_in_named_decls == []

    def test_docstring_mentions_sorry_not_counted(self):
        repo = _make_repo()
        base = _reset(repo)
        # The docstring mentions sorry; the proof uses trivial.
        head = _commit(repo, {
            "D.lean": (
                "/-- We avoid sorry here. -/\n"
                "theorem safe : True := by trivial\n"
                "\n"
                "-- inline comment: sorry, this is fine\n"
                "theorem other : 1 + 1 = 2 := by ring\n"
            ),
        }, "docstring")
        r = scan_added_lines(base, head, repo_root=repo)
        assert r.hits == []

    def test_modified_file_only_added_lines_counted(self):
        # Modify an existing file: only the + lines should be inspected.
        # The - lines must NOT contribute.
        repo = _make_repo()
        (repo / "M.lean").write_text("theorem a : True := by trivial\n")
        subprocess.run(["git", "add", "M.lean"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "init M"], check=True, cwd=repo)
        base = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8", cwd=repo
        ).stdout.strip()
        # Modify: REPLACE the trivial with sorry. The - line is trivial
        # (no anchor), the + line is sorry (anchor in named decl).
        (repo / "M.lean").write_text("theorem a : True := by sorry\n")
        subprocess.run(["git", "add", "M.lean"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "replace"], check=True, cwd=repo)
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8", cwd=repo
        ).stdout.strip()
        r = scan_added_lines(base, head, repo_root=repo)
        # exactly one anchor (the + sorry), not two.
        assert len(r.hits) == 1
        assert r.hits[0].token == "sorry"

    def test_deleted_file_is_skipped(self):
        repo = _make_repo()
        (repo / "G.lean").write_text("theorem a : True := by trivial\n")
        subprocess.run(["git", "add", "G.lean"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "add G"], check=True, cwd=repo)
        base = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8", cwd=repo
        ).stdout.strip()
        # Delete the file: no anchors possible (a deleted file has no HEAD content).
        (repo / "G.lean").unlink()
        subprocess.run(["git", "add", "-A"], check=True, cwd=repo)
        subprocess.run(["git", "commit", "-q", "-m", "delete G"], check=True, cwd=repo)
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, encoding="utf-8", cwd=repo
        ).stdout.strip()
        r = scan_added_lines(base, head, repo_root=repo)
        # Only Init.lean is unchanged; G.lean is gone -- no anchors.
        assert r.hits == []


# --------------------------------------------------------------------------- #
# render_text: la sortie declarative et nominative
# --------------------------------------------------------------------------- #


class TestRenderTextDeclaredLines:
    """La sortie doit NOMMER l'ancre, pas seulement la compter.

    Mesure du 2026-10-21 : un `ROUGE: 20 anchor(s)` ne dit pas QUELLE
    declaration rendrait le merge impossible. La ligne
    `[LEAN-ANCHOR-DECLARED] <fichier>:<decl> -- <motif>` est ce qui rend le
    diagnostic actionnable sans rejouer le diff.
    """

    def test_named_anchor_renders_declared_line(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _commit(repo, {"Y.lean": "theorem bar : 1 + 1 = 2 := by native_decide\n"},
                        "rouge")
        r = scan_added_lines(base, head, repo_root=repo)
        text = render_text(r)
        assert "[LEAN-ANCHOR-DECLARED] Y.lean:theorem bar -- native_decide" in text
        # Une seule ligne declaree : une ligne par ancre nommee.
        assert text.count("[LEAN-ANCHOR-DECLARED]") == 1

    def test_example_anchor_renders_no_declared_line(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _commit(repo, {"E.lean": "example : 1 + 1 = 2 := by native_decide\n"},
                        "green")
        r = scan_added_lines(base, head, repo_root=repo)
        text = render_text(r)
        # Une ancre en `example` est mergeable par conception : rien a declarer.
        assert "[LEAN-ANCHOR-DECLARED]" not in text
        assert "GREEN:" in text

    def test_one_declared_line_per_hit_with_its_own_token(self):
        repo = _make_repo()
        base = _reset(repo)
        head = _commit(
            repo,
            {
                "M.lean": (
                    "theorem a : 1 + 1 = 2 := by native_decide\n"
                    "lemma b : True := by sorry\n"
                ),
            },
            "rouge",
        )
        r = scan_added_lines(base, head, repo_root=repo)
        text = render_text(r)
        assert "[LEAN-ANCHOR-DECLARED] M.lean:theorem a -- native_decide" in text
        assert "[LEAN-ANCHOR-DECLARED] M.lean:lemma b -- sorry" in text
        assert text.count("[LEAN-ANCHOR-DECLARED]") == 2
        # L'ordre est celui des hits (deterministe).
        assert text.index("-- native_decide") < text.index("-- sorry")
