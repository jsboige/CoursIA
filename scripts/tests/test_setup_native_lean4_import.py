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


# --- #18120 : table _repl_for_toolchain installee vs REPL_TOOLCHAIN_TAGS ----
# Mesure po-2026 28/09 : la copie installee (fork fige v0.0.1-native-import,
# reformatee par endroit) portait 6 tags quand la constante du depot en avait 7
# -- un lake v4.34.0-rc1 serait silencieusement route sur le repl stable
# (Unknown identifier, aucune erreur de version).

_REPO_LAYOUT = (
    "    def _repl_for_toolchain(lake_root):\n"
    "        mapping = {'v4.30.0-rc2': 'repl-4.30.0-rc2',\n"
    "                   'v4.32.1': 'repl-4.32.1'}\n"
)
_FORK_LAYOUT = (
    "    def _repl_for_toolchain(lake_root):\n"
    "        mapping = {'v4.30.0-rc2': 'repl-4.30.0-rc2', 'v4.32.1': 'repl-4.32.1'}\n"
)
_UPSTREAM = "class Lean4ReplWrapper:\n    pass\n"


def test_extract_repl_table_layout_independent():
    """L'extraction ne depend pas du formatage (payload depot vs fork fige)."""
    expected = {"v4.30.0-rc2": "repl-4.30.0-rc2", "v4.32.1": "repl-4.32.1"}
    assert setup._extract_repl_table(_REPO_LAYOUT) == expected
    assert setup._extract_repl_table(_FORK_LAYOUT) == expected


def test_extract_repl_table_upstream_is_none():
    """Controle negatif : repl.py amont (sans _repl_for_toolchain) -> None.

    None est le signal fail-closed du sync : la commande doit refuser d'ecrire
    sur un fichier qu'elle ne comprend pas, jamais ecrire a l'aveugle."""
    assert setup._extract_repl_table(_UPSTREAM) is None


def test_repl_table_drift_classes():
    """missing / extra / changed -- seuls missing+changed sont nocifs."""
    drift = setup._repl_table_drift(
        {"v4.32.1": "repl-4.32.1", "v4.33.0": "repl-WRONG", "v4.29.0": "repl-4.29.0"},
        {"v4.32.1": "repl-4.32.1", "v4.33.0": "repl-4.33.0",
         "v4.34.0-rc1": "repl-4.34.0-rc1"})
    assert drift["missing"] == ["v4.34.0-rc1"]
    assert drift["extra"] == ["v4.29.0"]
    assert drift["changed"] == {"v4.33.0": ("repl-WRONG", "repl-4.33.0")}


def test_render_repl_table_roundtrip():
    """Le literal rendu re-extrait a la table identique (tri par tag)."""
    src = ("def _repl_for_toolchain(x):\n    mapping = "
           + setup._render_repl_table({"v4.32.1": "repl-4.32.1",
                                       "v4.30.0-rc2": "repl-4.30.0-rc2"}) + "\n")
    assert setup._extract_repl_table(src) == {
        "v4.30.0-rc2": "repl-4.30.0-rc2", "v4.32.1": "repl-4.32.1"}


def test_apply_repl_table_sync_replaces_only_literal():
    """Le sync remplace le literal, ajoute le tag manquant, ne touche au reste."""
    stale = (_FORK_LAYOUT + "        return mapping.get(lake_root, 'repl')\n")
    ref = {"v4.32.1": "repl-4.32.1", "v4.34.0-rc1": "repl-4.34.0-rc1"}
    new_src, drift = setup._apply_repl_table_sync(stale, ref)
    assert drift["missing"] == ["v4.34.0-rc1"]
    assert setup._extract_repl_table(new_src) == ref
    assert "return mapping.get(lake_root, 'repl')" in new_src


def test_apply_repl_table_sync_idempotent():
    """Table deja alignee -> source inchangee (no-op)."""
    src = ("def _repl_for_toolchain(x):\n    mapping = "
           + setup._render_repl_table({"v4.32.1": "repl-4.32.1"}) + "\n")
    out, drift = setup._apply_repl_table_sync(src, {"v4.32.1": "repl-4.32.1"})
    assert out == src
    assert not (drift["missing"] or drift["extra"] or drift["changed"])


def test_apply_repl_table_sync_fail_closed_on_upstream():
    """Controle negatif : sans literal detectable -> None, aucune ecriture."""
    out, drift = setup._apply_repl_table_sync(_UPSTREAM, {"v4.32.1": "repl-4.32.1"})
    assert out is None
    assert drift["missing"] == ["v4.32.1"]


def test_status_fails_on_stale_table(monkeypatch):
    """status rend rc=1 quand la table installee derive (detectable, pas muet).

    Replay sans WSL : repl.py fictif servi en base64 par le fake _wsl (le
    transport reel du #18120), grep PATCHED et test -f dispatches par commande.
    Cas : la table installee manque v4.34.0-rc1 -- la classe nocive (le lake
    serait silencieusement route sur le repl stable)."""
    import base64
    b64 = base64.b64encode(_FORK_LAYOUT.encode()).decode()

    def fake_wsl(cmd, *a, **kw):
        if "base64" in cmd:
            return _FakeResult(b64)
        if "grep -q" in cmd:
            return _FakeResult("PATCHED")
        if "test -f" in cmd:
            return _FakeResult("  present")
        return _FakeResult("")

    monkeypatch.setattr(setup, "_find_repl_py", lambda: "/home/u/.lean4-venv/repl.py")
    monkeypatch.setattr(setup, "_wsl", fake_wsl)
    monkeypatch.setattr(setup, "REPL_TOOLCHAIN_TAGS",
                        {"v4.32.1": "repl-4.32.1", "v4.34.0-rc1": "repl-4.34.0-rc1"})
    assert setup.cmd_status() == 1


def test_status_clean_table_passes(monkeypatch):
    """Controle oppose : tables alignees -> rc=0 (le rouge du test precedent
    vient bien de la derive, pas d'un defaut de wiring du fake)."""
    import base64
    src = ("def _repl_for_toolchain(x):\n    mapping = "
           + setup._render_repl_table({"v4.32.1": "repl-4.32.1"}) + "\n")
    b64 = base64.b64encode(src.encode()).decode()

    def fake_wsl(cmd, *a, **kw):
        if "base64" in cmd:
            return _FakeResult(b64)
        if "grep -q" in cmd:
            return _FakeResult("PATCHED")
        if "test -f" in cmd:
            return _FakeResult("  present")
        return _FakeResult("")

    monkeypatch.setattr(setup, "_find_repl_py", lambda: "/home/u/.lean4-venv/repl.py")
    monkeypatch.setattr(setup, "_wsl", fake_wsl)
    monkeypatch.setattr(setup, "REPL_TOOLCHAIN_TAGS", {"v4.32.1": "repl-4.32.1"})
    assert setup.cmd_status() == 0

