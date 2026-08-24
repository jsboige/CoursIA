"""Tests for scripts/lean/setup_native_lean4_import.py (#12168).

Positive controls required by the issue: a pattern set validates by its
FALSE NEGATIVES, not its hits. The founding defect: the tag filter dropped
``-rcN`` suffixes outright while the script's own docstring advertised
``build-repl v4.30.0-rc2`` -- the resolver then reported the misleading
NO-SOURCE-TAG (the tag exists upstream; the local filter had dropped it).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lean"))

import setup_native_lean4_import as setup  # noqa: E402
from setup_native_lean4_import import _repl_tag_sort_key as key  # noqa: E402


def test_rc_precedes_release():
    """#12168 controle positif 1 : key('v4.30.0-rc2') < key('v4.30.0')."""
    assert key("v4.30.0-rc2") < key("v4.30.0")


def test_rc_numeric_order():
    """rc10 > rc9 numeriquement -- lexicographique donnerait 'rc10' < 'rc9'."""
    assert key("v4.30.0-rc9") < key("v4.30.0-rc10")
    assert key("v4.30.0-rc1") < key("v4.30.0-rc2")


def test_release_below_next_rc():
    """Une release reste sous le rc de la release suivante."""
    assert key("v4.30.0") < key("v4.31.0-rc1")
    assert key("v4.29.0") < key("v4.30.0-rc2")


def test_malformed_sorts_below_everything_without_raising():
    """L'ancien int() levait ValueError -> resilience None trompeuse. Un tag
    malforme doit trier sous tout sans lever (fail-safe, jamais NO-SOURCE-TAG
    mensonger sur un ensemble pourtant valide)."""
    assert key("garbage")[0] == -1
    assert key("garbage") < key("v0.0.0")


class _FakeResult:
    def __init__(self, stdout):
        self.stdout = stdout


def test_resolve_rc_tag_from_ls_remote(monkeypatch):
    """#12168 controle positif 2 : build-repl v4.30.0-rc2 resout une source.

    Replay du ls-remote sans reseau : le tag rc est present upstream et doit
    etre resolu. Pre-fix, le filtre jetait 'v4.30.0-rc2' et la fonction rendait
    None (NO-SOURCE-TAG mensonger).
    """
    ls_remote = "\n".join(
        f"6c3a41e9d2f1b0a7c8d9e0f1a2b3c4d5e6f7a8b9\trefs/tags/{t}"
        for t in ("v4.29.0", "v4.30.0-rc1", "v4.30.0-rc2", "v4.30.0", "v4.31.0")
    )
    monkeypatch.setattr(setup, "_wsl", lambda *a, **kw: _FakeResult(ls_remote))
    assert setup._resolve_repl_source_tag("v4.30.0-rc2") == "v4.30.0-rc2"


def test_resolve_nearest_below(monkeypatch):
    """Le cas historique du docstring tient toujours : nearest <= v4.32.1."""
    ls_remote = "\n".join(
        f"6c3a41e9d2f1b0a7c8d9e0f1a2b3c4d5e6f7a8b9\trefs/tags/{t}"
        for t in ("v4.31.0", "v4.32.0", "v4.33.0")
    )
    monkeypatch.setattr(setup, "_wsl", lambda *a, **kw: _FakeResult(ls_remote))
    assert setup._resolve_repl_source_tag("v4.32.1") == "v4.32.0"


def test_resolve_release_can_fall_on_its_own_rc(monkeypatch):
    """v4.32.1 n'a pas de tag repl : nearest <= v4.32.1. Si upstream n'avait
    que v4.32.1-rc1 et v4.31.0, le rc doit etre retenu (il est <= )."""
    ls_remote = "\n".join(
        f"6c3a41e9d2f1b0a7c8d9e0f1a2b3c4d5e6f7a8b9\trefs/tags/{t}"
        for t in ("v4.31.0", "v4.32.1-rc1")
    )
    monkeypatch.setattr(setup, "_wsl", lambda *a, **kw: _FakeResult(ls_remote))
    assert setup._resolve_repl_source_tag("v4.32.1") == "v4.32.1-rc1"


def test_resolve_rejects_malformed_request(monkeypatch):
    """Une demande mal formee rend None proprement (fail-safe d'origine)."""
    monkeypatch.setattr(setup, "_wsl",
                        lambda *a, **kw: _FakeResult("x\trefs/tags/v4.30.0\n"))
    assert setup._resolve_repl_source_tag("not-a-tag") is None
