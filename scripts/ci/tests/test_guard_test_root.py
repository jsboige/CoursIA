"""Tests du parseur `guard_test_root.py` (CONCERNS coordinateur c.86, #18896).

Trois cas exiges par l'arbitrage du 03/10 :

  1. bloc pytest valide AVEC `-n` (xdist) : le pattern matche, la liste
     des chemins collectes est non-vide.
  2. bloc pytest valide SANS `-n` (juste `-q`) : le pattern matche
     (avant le fix c.86, il rendait une liste vide et le garde disait
     `ok=True` sans rien verifier -- un faux positif silencieux).
  3. workflow mentionnant `pytest` sans bloc multi-lignes reconnu :
     `parse_collected_paths` leve `PytestBlockNotFound` ; le `main`
     rend `rc=2` et un message explicite.

Ces tests sont network-free : le module est importe en local, les
fichiers YAML de test sont crees dans un `tmp_path` pytest.
"""
import importlib.util
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[3]
_GUARD = _REPO_ROOT / "scripts" / "ci" / "guard_test_root.py"
_SPEC = importlib.util.spec_from_file_location("guard_test_root", _GUARD)
assert _SPEC is not None and _SPEC.loader is not None
guard = importlib.util.module_from_spec(_SPEC)
sys.modules["guard_test_root"] = guard
_SPEC.loader.exec_module(guard)


# ---------------------------------------------------------------------------
# 1. Bloc pytest valide AVEC `-n` (le cas historique)
# ---------------------------------------------------------------------------

def test_parse_with_xdist_returns_all_paths(tmp_path):
    """Bloc pytest avec `-n 4 --dist loadscope` : 17 chemins collectes
    sur le workflow reel. Le test isole un sous-ensemble a 4 chemins
    pour eviter une re-execution des autres jobs."""
    wf = tmp_path / "with_xdist.yml"
    wf.write_text(
        "name: with-xdist\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    runs-on: ubuntu-latest\n"
        "    steps:\n"
        "      - run: |\n"
        "          pytest \\\n"
        "            scripts/tests \\\n"
        "            scripts/notebook_tools/tests \\\n"
        "            scripts/lean/tests \\\n"
        "            MyIA.AI.Notebooks/GameTheory/tests \\\n"
        "            -n 4 --dist loadscope --tb=short -q\n"
    )
    paths = guard.parse_collected_paths(wf)
    assert paths == [
        "scripts/tests",
        "scripts/notebook_tools/tests",
        "scripts/lean/tests",
        "MyIA.AI.Notebooks/GameTheory/tests",
    ]


# ---------------------------------------------------------------------------
# 2. Bloc pytest valide SANS `-n` (le cas du CONCERNS c.86)
# ---------------------------------------------------------------------------

def test_parse_without_xdist_returns_paths(tmp_path):
    """Bloc pytest avec juste `-q` en queue : avant le fix c.86, le
    pattern exigeait `-n\\s` en queue, donc cette fixture rendait une
    liste vide et le garde disait `ok=True` sans rien verifier. Le
    fix accepte tout argument pytest en queue (le bloc se termine a
    la derniere ligne se terminant par `\\`).
    """
    wf = tmp_path / "no_xdist.yml"
    wf.write_text(
        "name: no-xdist\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    runs-on: ubuntu-latest\n"
        "    steps:\n"
        "      - run: |\n"
        "          python -m pytest \\\n"
        "            scripts/notebook_tools/tests/ \\\n"
        "            -q\n"
    )
    paths = guard.parse_collected_paths(wf)
    assert paths == ["scripts/notebook_tools/tests/"]


def test_parse_without_any_pytest_options(tmp_path):
    """Bloc pytest sans aucune option en queue (juste les chemins).
    Le pattern matche car le bloc se termine a la derniere ligne `\\`."""
    wf = tmp_path / "bare.yml"
    wf.write_text(
        "name: bare\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    steps:\n"
        "      - run: |\n"
        "          pytest \\\n"
        "            scripts/tests \\\n"
        "            scripts/notebook_tools/tests\n"
    )
    paths = guard.parse_collected_paths(wf)
    # Le dernier chemin n'a pas de \\ final -- il est ignore par le pattern.
    # Le pattern exige au moins une ligne se terminant par \\.
    assert paths == ["scripts/tests"]


# ---------------------------------------------------------------------------
# 3. Workflow mentionnant `pytest` sans bloc multi-lignes (defaut)
# ---------------------------------------------------------------------------

def test_parse_pytest_no_multiline_block_raises(tmp_path):
    """Si le workflow contient `pytest \\` (signe d'un appel multi-lignes
    intentionnel) mais que PYTEST_BLOCK_RE ne matche pas le bloc
    (par exemple parce que la ligne `pytest \\` est seule sans
    chemins -- bug de l'auteur), on leve `PytestBlockNotFound`.
    Le main rend rc=2 et un message qui nomme la cause -- c'est
    l'arbitrage explicite du coordinateur ('s'il ne le prend pas en
    charge, elle doit rendre une erreur de lecture, jamais OK')."""
    wf = tmp_path / "orphan_block.yml"
    wf.write_text(
        "name: orphan-block\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    steps:\n"
        "      - run: |\n"
        "          pytest \\\n"  # ligne finale sans chemin -- bug YAML
        "          -q\n"
    )
    import pytest
    with pytest.raises(guard.PytestBlockNotFound):
        guard.parse_collected_paths(wf)


def test_parse_inline_pytest_returns_empty(tmp_path):
    """Un workflow avec pytest INLINE (pas de convention multi-lignes
    avec `\\`) rend une liste vide : le garde n'a pas de convention
    a appliquer. C'est distinct du cas pytest-sans-bloc-matche
    (test_parse_pytest_no_multiline_block_raises), ou on leve."""
    wf = tmp_path / "inline.yml"
    wf.write_text(
        "name: inline\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    steps:\n"
        "      - run: pytest scripts/tests/ -q\n"  # inline, pas multi-lignes
    )
    paths = guard.parse_collected_paths(wf)
    assert paths == []


def test_parse_no_pytest_at_all_returns_empty(tmp_path):
    """Un workflow sans pytest du tout rend une liste vide -- le
    workflow n'est pas dans le scope de cette garde. La distinction
    avec le cas 3 (pytest sans bloc) est que pytest est absent."""
    wf = tmp_path / "no_pytest.yml"
    wf.write_text(
        "name: no-pytest\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    steps:\n"
        "      - run: echo 'no tests here'\n"
    )
    paths = guard.parse_collected_paths(wf)
    assert paths == []


# ---------------------------------------------------------------------------
# 4. main() : rc=2 sur pytest sans bloc, rc=0 sur workflow OK
# ---------------------------------------------------------------------------

def test_main_returns_2_on_pytest_block_not_found(tmp_path, capsys):
    """Le main intercepte `PytestBlockNotFound` et rend rc=2 avec un
    message explicite sur stderr. Avant le fix c.86, ce cas rendait
    rc=0 -- le garde ne verifiait rien et disait 'OK'."""
    wf = tmp_path / "orphan.yml"
    wf.write_text(
        "name: orphan\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    steps:\n"
        "      - run: |\n"
        "          pytest \\\n"  # bloc YAML bugge : pytest \ sans chemins
        "          -q\n"
    )
    rc = guard.main(["--workflow", str(wf), "--json"])
    captured = capsys.readouterr()
    assert rc == 2
    assert "PYTEST_BLOCK_RE ne matche pas" in captured.err


def test_main_returns_0_on_clean_workflow(tmp_path, capsys, monkeypatch):
    """Workflow propre : main rend rc=0 et liste les chemins collectes.
    On monkeypatche REPO_ROOT pour qu'il accepte le chemin tmp_path
    dans la sortie JSON (relative_to), ce que la garde reecrite en
    c.86 fait deja via `args.workflow.resolve().relative_to(REPO_ROOT)`.
    Si le tmp_path est sous REPO_ROOT, pas besoin de patch ; sinon
    on elargit REPO_ROOT pour ce test."""
    # Placer le workflow sous REPO_ROOT pour eviter le monkeypatch
    rel_wf = _REPO_ROOT / "scripts" / "ci" / "tests" / "_tmp_clean.yml"
    rel_wf.write_text(
        "name: clean\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    steps:\n"
        "      - run: |\n"
        "          pytest \\\n"
        "            scripts/tests \\\n"
        "            -q\n"
    )
    try:
        rc = guard.main(["--workflow", str(rel_wf), "--json"])
        captured = capsys.readouterr()
        assert rc == 0
        import json
        out = json.loads(captured.out)
        assert out["ok"] is True
        assert "scripts/tests" in out["collected_paths"]
    finally:
        rel_wf.unlink()


# ---------------------------------------------------------------------------
# 5. Controles positifs (temoins du CONCERNS)
# ---------------------------------------------------------------------------

def test_no_xdist_with_root_test_detects_violation(tmp_path, monkeypatch):
    """Temoignage du CONCERNS c.86 : un workflow pytest SANS `-n` qui
    pointe vers scripts/notebook_tools/tests/ (un dossier collecte)
    doit rendre ok=True si tous les test_*.py de scripts/notebook_tools/
    sont dans scripts/notebook_tools/tests/ (ou dans un sous-dossier
    collecte). Si un test_uncollected.py est a la racine de
    scripts/notebook_tools/, le garde DOIT le voir -- avant le fix,
    il rendait ok=True silencieusement (parse_collected_paths -> [],
    find_violations([]) -> [])."""
    # Repertoire de test
    nb_dir = tmp_path / "scripts" / "notebook_tools"
    nb_dir.mkdir(parents=True)
    (nb_dir / "tests").mkdir()
    (nb_dir / "tests" / "test_alpha.py").write_text("# test\n")
    (nb_dir / "test_uncollected.py").write_text("# orphan\n")  # racine, hors tests/

    # Workflow qui pointe vers scripts/notebook_tools/tests/ sans -n
    wf = tmp_path / "no_xdist.yml"
    wf.write_text(
        "name: no-xdist\n"
        "on: [push]\n"
        "jobs:\n"
        "  t:\n"
        "    steps:\n"
        "      - run: |\n"
        "          python -m pytest \\\n"
        "            scripts/notebook_tools/tests/ \\\n"
        "            -q\n"
    )

    # Repertoire racine du garde : on patche REPO_ROOT pour pointer
    # vers notre tmp_path, et on enqueue _in_scope pour accepter
    # n'importe quel scripts/notebook_tools/.
    monkeypatch.setattr(guard, "REPO_ROOT", tmp_path)
    from scripts.ci import guard_test_root  # noqa: F401  (already loaded)
    monkeypatch.setattr(guard, "_in_scope", lambda p: True)

    paths = guard.parse_collected_paths(wf)
    assert paths == ["scripts/notebook_tools/tests/"], (
        f"Sans -n, le pattern doit quand meme extraire scripts/notebook_tools/tests/ ; "
        f"avant le fix c.86, il rendait [] et find_violations([]) -> [] masquait "
        f"test_uncollected.py. paths={paths!r}"
    )

    violations = guard.find_violations(paths)
    assert any("test_uncollected.py" in str(v) for v in violations), (
        f"find_violations doit detecter test_uncollected.py a la racine de "
        f"scripts/notebook_tools/ ; avant le fix c.86, paths etait [] et "
        f"violations etait [] aussi. violations={violations!r}"
    )
