"""Tests du moteur de voie rapide (#11835).

Trois proprietes sont sous test, et deux d'entre elles existent parce que le
depot a deja paye leur violation ailleurs :

1. **La selection par chemin ne doit pas SOUS-selectionner.** Un motif qui
   rate ne leve pas d'erreur : il rend moins de gardes, donc un CI plus vert
   et plus rapide. C'est la forme de defaut la plus difficile a voir, et
   `**/*.ipynb` contre un fichier a la racine en est le cas exact.
2. **Un garde advisory ne doit JAMAIS rougir**, et ne doit pas non plus etre
   blanchi en `success` : son verdict est `neutral`, sinon on perd le signal
   dans un sens ou dans l'autre.
3. **La restauration de l'arbre apres la bascule de base est verifiee**, et
   son echec interrompt tout plutot que de publier des verdicts calcules sur
   un arbre inconnu.

Les cas positifs (un garde qui echoue doit produire `failure`) sont aussi
couverts : une suite ou tout passe serait indiscernable d'un moteur debranche.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import fast_lane  # noqa: E402
from fast_lane_registry import PILOT, Guard  # noqa: E402


# ---------------------------------------------------------------------------
# 1. Selection par chemin
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("path,pattern,expected", [
    # le cas qui motive la fonction : `**/` couvre AUSSI la racine chez GitHub
    ("a.ipynb", "**/*.ipynb", True),
    ("MyIA.AI.Notebooks/x/y.ipynb", "**/*.ipynb", True),
    ("docs/z.md", "**/*.md", True),
    ("README.md", "**/*.md", True),
    # negatifs : le filtre doit rester un filtre
    ("scripts/foo.py", "**/*.ipynb", False),
    ("a.ipynbx", "**/*.ipynb", False),
    # chemin exact
    ("scripts/notebook_tools/strip_probe_banner.py",
     "scripts/notebook_tools/strip_probe_banner.py", True),
    ("scripts/notebook_tools/other.py",
     "scripts/notebook_tools/strip_probe_banner.py", False),
])
def test_path_matches(path, pattern, expected):
    assert fast_lane.path_matches(path, pattern) is expected


def test_path_matches_accepts_windows_separators():
    """Le diff peut arriver avec des separateurs natifs selon l'appelant."""
    assert fast_lane.path_matches("MyIA.AI.Notebooks\\x\\y.ipynb", "**/*.ipynb")


def test_guard_without_paths_always_applies():
    guard = Guard(name="g", argv=["true"], source="s", paths=[])
    assert fast_lane.guard_applies(guard, []) is True
    assert fast_lane.guard_applies(guard, ["n/importe/quoi.txt"]) is True


def test_guard_with_paths_is_skipped_when_nothing_matches():
    guard = Guard(name="g", argv=["true"], source="s", paths=["**/*.ipynb"])
    assert fast_lane.guard_applies(guard, ["docs/a.md"]) is False
    assert fast_lane.guard_applies(guard, ["docs/a.md", "x/b.ipynb"]) is True


def test_notebook_guards_select_a_root_level_notebook():
    """Controle de bout en bout du piege `**/` sur le registre reel."""
    changed = ["Notebook-A-La-Racine.ipynb"]
    selected = [g.name for g in PILOT if fast_lane.guard_applies(g, changed)]
    for expected in ("banner-guard", "pip-leak-guard", "solution-leak-guard",
                     "prose-counts-guard"):
        assert expected in selected, (
            f"{expected} devrait couvrir un notebook a la racine "
            "(motif `**/*.ipynb`)"
        )


# ---------------------------------------------------------------------------
# 2. Conclusions -- controle positif ET negatif
# ---------------------------------------------------------------------------

def test_blocking_guard_failure_is_a_failure():
    guard = Guard(name="g", argv=["true"], source="s", blocking=True)
    assert fast_lane.conclusion_for(guard, 1) == "failure"


def test_advisory_guard_failure_is_neutral_not_failure_nor_success():
    guard = Guard(name="g", argv=["true"], source="s", blocking=False)
    concl = fast_lane.conclusion_for(guard, 1)
    assert concl == "neutral"
    assert concl != "failure", "un advisory ne doit jamais rougir la PR"
    assert concl != "success", "un advisory en echec ne doit pas etre blanchi"


def test_success_is_success_for_both_kinds():
    for blocking in (True, False):
        guard = Guard(name="g", argv=["true"], source="s", blocking=blocking)
        assert fast_lane.conclusion_for(guard, 0) == "success"


# ---------------------------------------------------------------------------
# 3. Coherence du registre avec les workflows d'origine
# ---------------------------------------------------------------------------

WORKFLOWS = Path(__file__).resolve().parents[2] / ".github" / "workflows"


def test_every_pilot_guard_names_an_existing_workflow():
    for guard in PILOT:
        assert (WORKFLOWS / guard.source).is_file(), (
            f"{guard.name} declare provenir de {guard.source}, absent du depot"
        )


def test_delta_guards_declare_what_they_swap():
    """Sans `swap_paths`, la phase 2 basculerait un ensemble vide et le delta
    comparerait HEAD a lui-meme -- un vert silencieux."""
    for guard in PILOT:
        if guard.delta_argv:
            assert guard.swap_paths, (
                f"{guard.name} est un delta sans swap_paths : sa phase base "
                "scannerait HEAD et le delta serait toujours vide"
            )


def test_delta_placeholders_are_resolvable():
    ctx = {"base_ref": "origin/main", "base_sha": "abc", "head_sha": "def",
           "pr_number": "1", "base_json": "/tmp/b.json",
           "head_json": "/tmp/h.json"}
    for guard in PILOT:
        fast_lane.substitute(guard.argv, ctx)
        if guard.delta_argv:
            resolved = fast_lane.substitute(guard.delta_argv, ctx)
            assert "/tmp/b.json" in resolved and "/tmp/h.json" in resolved


def test_advisory_flags_match_the_source_workflows():
    """Le caractere advisory est une propriete du garde, pas du moteur.

    `solution-leak-guard` et `prose-counts-guard` sont annonces advisory dans
    l'en-tete de leur workflow ; les inverser ici ferait rougir la flotte sur
    un stock que le depot a explicitement decide de ne pas bloquer.
    """
    by_name = {g.name: g for g in PILOT}
    assert by_name["solution-leak-guard"].blocking is False
    assert by_name["prose-counts-guard"].blocking is False
    assert by_name["banner-guard"].blocking is True
    assert by_name["pip-leak-guard"].blocking is True
    assert by_name["perimeter-review-guard"].blocking is True


# ---------------------------------------------------------------------------
# 4. Execution et capture
# ---------------------------------------------------------------------------

def test_run_argv_captures_exit_code_and_output():
    rc, log = fast_lane.run_argv(
        [sys.executable, "-c", "import sys; print('bonjour'); sys.exit(3)"], {})
    assert rc == 3
    assert "bonjour" in log
    assert "exit 3" in log


def test_payload_of_strips_the_header_added_by_run_argv():
    rc, log = fast_lane.run_argv(
        [sys.executable, "-c", "print('{\"k\": 1}')"], {})
    assert rc == 0
    assert fast_lane.payload_of(log).strip() == '{"k": 1}'


def test_substitute_leaves_unknown_braces_alone():
    """Regression : `str.format` aurait leve KeyError sur ces trois formes.

    Aucune n'est dans le registre pilote ; toutes apparaitront quand il
    grossira (filtre jq, quantificateur regex, litteral JSON). L'echec serait
    une panne d'infrastructure que le log rendrait indiscernable d'un verdict.
    """
    ctx = {"pr_number": "42", "base_ref": "origin/main"}
    argv = ['.workflow_runs[] | {n: .name}', 'a{2,3}b', '{"k": 1}',
            '--pr', '{pr_number}']
    assert fast_lane.substitute(argv, ctx) == [
        '.workflow_runs[] | {n: .name}', 'a{2,3}b', '{"k": 1}', '--pr', '42']


def test_run_argv_reports_timeout_as_a_verdict_not_an_exception(monkeypatch):
    monkeypatch.setattr(fast_lane, "GUARD_TIMEOUT_S", 1)
    rc, log = fast_lane.run_argv(
        [sys.executable, "-c", "import time; time.sleep(30)"], {})
    assert rc == 124
    assert "delai depasse" in log


# ---------------------------------------------------------------------------
# 5. Verification de restauration d'arbre
# ---------------------------------------------------------------------------

def test_tree_is_clean_detects_a_dirty_path(tmp_path, monkeypatch):
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    (tmp_path / "f.txt").write_text("un", encoding="utf-8")
    subprocess.run(["git", "-C", str(tmp_path), "add", "f.txt"], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "-c", "user.email=t@t",
                    "-c", "user.name=t", "commit", "-qm", "init"], check=True)
    monkeypatch.setattr(fast_lane, "REPO_ROOT", tmp_path)

    clean, dirt = fast_lane.tree_is_clean(["f.txt"])
    assert clean is True and dirt == ""

    (tmp_path / "f.txt").write_text("deux", encoding="utf-8")
    clean, dirt = fast_lane.tree_is_clean(["f.txt"])
    assert clean is False
    assert "f.txt" in dirt


# ---------------------------------------------------------------------------
# 6. Emission
# ---------------------------------------------------------------------------

def test_dry_run_publishes_nothing(capsys, monkeypatch):
    def explode(*a, **k):  # pragma: no cover - doit rester non appele
        raise AssertionError("aucun appel reseau ne doit avoir lieu a blanc")
    monkeypatch.setattr(subprocess, "run", explode)
    fast_lane.emit_check_run("o/r", "sha", "n", "success", "t", "s",
                             dry_run=True)
    assert "a-blanc" in capsys.readouterr().out


def test_summary_is_truncated_below_the_api_limit(monkeypatch):
    captured = {}

    class Fake:
        returncode = 0
        stdout = ""
        stderr = ""

    def fake_run(cmd, **kwargs):
        captured["payload"] = kwargs.get("input", "")
        return Fake()

    monkeypatch.setattr(subprocess, "run", fake_run)
    fast_lane.emit_check_run("o/r", "sha", "n", "success", "t", "x" * 200000,
                             dry_run=False)
    assert len(captured["payload"]) < 70000
