"""Tests pour scripts/audit/scan_duplicate_test_pairs.py — issue #14730 point 4.

Le recensement #14615 croisait les basenames : la 3e paire (legacy
scripts/tests/test_extract_titles.py couvrant DEUX extracteurs dont les suites
canoniques ont des basenames differents) lui etait structurellement invisible.
Ces tests pinnent le predicat de remplacement — appariement sur le module
teste (docstring + imports) — sur les quatre axes qui fondent l'issue :

  - detection de la paire en forme « extract » (legacy multi-modules + deux
    canoniques), avec preuve explicite de l'invisibilite a la cle basename ;
  - detection par imports seuls (sans mention de docstring) ;
  - arbre propre -> 0 paire, --check exit 0 ; paire presente -> exit 1 ;
  - bruit exclu : helpers de tests/, __init__.py, conftest ne creent pas de paire ;

et deux temoins sur le reel :
  - controle positif RETROACTIF : le scanner applique a l'etat PRE-a6720c7286
    (consolidation de la 3e paire) doit la voir — skip si l'historique git est
    absent (clone shallow en CI) ou si ses blobs ne sont pas materialisables
    (fetch promisor en echec sur un clone partiel blob:none) ;
  - non-regression a l'etat courant : les modules extract ne sont PLUS en paire.

Tous les tests de fixture sont hermetiques (tmp_path, aucun dependance reseau
ou historique). Le scanner EXTRAIT, il ne decide pas : les ~12 candidats que
l'etat courant porte reellement (sur-comptage #14615) ne sont PAS asserts ici —
ils vivent dans le rapport de l'issue et la revue humaine.
"""

import importlib.util
import os
import subprocess
import sys
from pathlib import Path

import pytest

# Module lives in scripts/audit/ (flat, not a package) -> spec_from_file_location.
_MOD_PATH = Path(__file__).resolve().parent.parent / "scan_duplicate_test_pairs.py"
_spec = importlib.util.spec_from_file_location("scan_duplicate_test_pairs", _MOD_PATH)
scanner = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(scanner)

REPO_ROOT = Path(__file__).resolve().parents[3]
PRE_CONSOLIDATION = "a6720c7286~1"


# ---------------------------------------------------------------------------
# fixtures : arbres synthetiques
# ---------------------------------------------------------------------------

def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8", newline="\n")


def _make_extract_shaped_tree(root: Path) -> None:
    """Reproduit la forme exacte de la 3e paire (pre-a6720c7286).

    legacy : UN fichier de test couvrant DEUX modules, dont le basename n'est
    le basename d'aucune des deux suites canoniques.
    """
    _write(root / "scripts/notebook_tools/extract_pptx_titles.py", "TITLE = 1\n")
    _write(root / "scripts/notebook_tools/extract_slidev_titles.py", "TITLE = 2\n")
    _write(
        root / "scripts/tests/test_extract_titles.py",
        '"""Tests for scripts/notebook_tools/extract_pptx_titles.py and '
        'scripts/notebook_tools/extract_slidev_titles.py."""\n'
        "import scripts.notebook_tools.extract_pptx_titles\n"
        "import scripts.notebook_tools.extract_slidev_titles\n"
        "def test_a():\n    assert True\n",
    )
    _write(
        root / "scripts/notebook_tools/tests/test_extract_pptx_titles.py",
        '"""Tests for scripts/notebook_tools/extract_pptx_titles.py."""\n'
        "import scripts.notebook_tools.extract_pptx_titles\n"
        "def test_b():\n    assert True\n",
    )
    _write(
        root / "scripts/notebook_tools/tests/test_extract_slidev_titles.py",
        '"""Tests for scripts/notebook_tools/extract_slidev_titles.py."""\n'
        "import scripts.notebook_tools.extract_slidev_titles\n"
        "def test_c():\n    assert True\n",
    )


def _make_import_only_tree(root: Path) -> None:
    _write(root / "scripts/zoo/animal.py", "KIND = 'zoo'\n")
    _write(
        root / "scripts/tests/test_animal.py",
        "import scripts.zoo.animal\n" "def test_x():\n    assert True\n",
    )
    _write(
        root / "scripts/zoo/tests/test_animal_deep.py",
        "import scripts.zoo.animal\n" "def test_y():\n    assert True\n",
    )


def _make_noise_tree(root: Path) -> None:
    """Un helper de tests importe par deux suites ne fait PAS une paire."""
    _write(root / "scripts/zoo/animal.py", "KIND = 'zoo'\n")
    _write(
        root / "scripts/tests/helpers.py",
        "CONST = 1\n",
    )
    _write(
        root / "scripts/tests/__init__.py",
        "",
    )
    _write(
        root / "scripts/tests/test_one.py",
        "from scripts.tests.helpers import CONST\n" "def test_1():\n    assert CONST\n",
    )
    _write(
        root / "scripts/zoo/tests/test_two.py",
        "from scripts.tests.helpers import CONST\n" "def test_2():\n    assert CONST\n",
    )


def _pairs_by_module(result: dict) -> dict:
    return {pair["module"]: pair for pair in result["pairs"]}


# ---------------------------------------------------------------------------
# predicat : la forme « extract », invisible au basename
# ---------------------------------------------------------------------------

def test_detects_extract_shaped_pair_and_basename_blindness(tmp_path):
    _make_extract_shaped_tree(tmp_path)
    result = scanner.scan(tmp_path)
    pairs = _pairs_by_module(result)

    pptx = "scripts/notebook_tools/extract_pptx_titles.py"
    slidev = "scripts/notebook_tools/extract_slidev_titles.py"
    assert pptx in pairs, "paire pptx invisible au scanner"
    assert slidev in pairs, "paire slidev invisible au scanner"

    for module in (pptx, slidev):
        files = {entry["test_file"] for entry in pairs[module]["test_files"]}
        assert "scripts/tests/test_extract_titles.py" in files
        assert any("notebook_tools/tests" in f for f in files)
        # Aucun basename partage entre les membres de la paire : une cle de
        # regroupement par basename ne peut PAS produire ce groupement.
        basenames = {Path(f).name for f in files}
        assert len(files) == 2
        assert len(basenames) == 2, "paire visible par basename : temoin affaibli"


def test_detects_pair_by_imports_only(tmp_path):
    _make_import_only_tree(tmp_path)
    result = scanner.scan(tmp_path)
    pairs = _pairs_by_module(result)
    assert "scripts/zoo/animal.py" in pairs
    files = {e["test_file"] for e in pairs["scripts/zoo/animal.py"]["test_files"]}
    assert files == {"scripts/tests/test_animal.py", "scripts/zoo/tests/test_animal_deep.py"}


def test_tests_dir_helpers_do_not_create_pairs(tmp_path):
    _make_noise_tree(tmp_path)
    result = scanner.scan(tmp_path)
    assert result["pairs"] == []


def test_clean_tree_reports_zero(tmp_path):
    _write(tmp_path / "scripts/zoo/animal.py", "KIND = 'zoo'\n")
    _write(
        tmp_path / "scripts/zoo/tests/test_animal.py",
        '"""Tests for scripts/zoo/animal.py."""\n',
    )
    result = scanner.scan(tmp_path)
    assert result["pairs"] == []
    assert result["test_files_scanned"] == 1


# ---------------------------------------------------------------------------
# CLI : --check exit codes
# ---------------------------------------------------------------------------

def _run_cli(repo_root: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(_MOD_PATH), "--repo-root", str(repo_root), "--check"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=str(REPO_ROOT),
    )


def test_check_exit_zero_on_clean_tree(tmp_path):
    _write(tmp_path / "scripts/zoo/animal.py", "KIND = 'zoo'\n")
    _write(
        tmp_path / "scripts/zoo/tests/test_animal.py",
        '"""Tests for scripts/zoo/animal.py."""\n',
    )
    proc = _run_cli(tmp_path)
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_check_exit_nonzero_with_pair(tmp_path):
    _make_extract_shaped_tree(tmp_path)
    proc = _run_cli(tmp_path)
    assert proc.returncode == 1
    assert "extract_pptx_titles.py" in proc.stdout


# ---------------------------------------------------------------------------
# temoins sur le reel
# ---------------------------------------------------------------------------

def _commit_exists(rev: str) -> bool:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "cat-file", "-e", f"{rev}^{{commit}}"],
        capture_output=True,
    )
    return proc.returncode == 0


class PromisorObjectUnavailable(RuntimeError):
    """Blob absent d'un clone partiel, que le fetch promisor n'a pas pu ramener.

    Ce n'est pas un verdict sur le scanner : c'est l'infrastructure de checkout
    qui ne peut pas materialiser l'arbre historique (remote injoignable, quota
    d'installation sature). Le test doit alors se declarer non jouable, pas
    rougir -- un rouge d'infra sur un check REQUIS gele la merge de toute la
    flotte.
    """


def _run_git(args: list, env: dict) -> str:
    """Lance git et, en cas d'echec, remonte la cause dans l'erreur.

    `check=True, capture_output=True` ne laissait dans le log CI que
    « returned non-zero exit status 128 » : la cause reelle (un fetch promisor
    en echec) etait invisible, et le rouge se lisait comme une regression du
    scanner. Mesure du 2026-09-21 : c'est exactement ce qui a fait passer ce
    rouge pour un defaut herite de la base pendant plusieurs heures.
    """
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        check=False, env=env, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or "").strip()
        if "promisor remote" in detail:
            raise PromisorObjectUnavailable(detail)
        raise RuntimeError(f"git {' '.join(args)} -> exit {proc.returncode}\n{detail}")
    return proc.stdout


def _extract_scripts_tree(ref: str, dest: Path) -> None:
    """Extrait scripts/ au ref donne dans dest/scripts/, sans toucher l'index du clone.

    Sur un clone partiel `blob:none` (celui des workflows du depot :
    `fetch-depth: 0` + `filter: blob:none`), `read-tree` suffit -- les arbres
    sont presents -- mais les **blobs** de l'etat historique ne le sont pas.
    `checkout-index` est bien fetch-aware (mesure : 2364 fichiers extraits d'un
    clone blob:none dont le remote repond), mais quand ce fetch promisor
    **echoue** il sort en 128 :

        fatal: could not fetch <sha> from promisor remote

    D'ou `PromisorObjectUnavailable`, que l'appelant traduit en test non
    jouable. Les autres echecs git restent des echecs durs.
    """
    index = dest / "_extract_idx"
    env = {**os.environ, "GIT_INDEX_FILE": str(index)}
    _run_git(["read-tree", ref + ":scripts"], env)
    prefix = (dest / "scripts").as_posix() + "/"
    _run_git(["checkout-index", "-a", "--prefix=" + prefix], env)
    index.unlink(missing_ok=True)


@pytest.mark.skipif(
    not _commit_exists(PRE_CONSOLIDATION),
    reason="historique indisponible (clone shallow) : controle retroactif non jouable",
)
def test_retroactive_control_sees_third_pair_pre_consolidation(tmp_path):
    """Le scanner, applique a l'etat PRE-consolidation, doit voir la 3e paire.

    C'est le controle positif retroactif exige par #14730 point 4 : l'etat
    a6720c7286~1 porte le legacy test_extract_titles.py (38 tests, deux
    extracteurs) a cote des deux suites canoniques — invisible a toute cle de
    basename.
    """
    try:
        _extract_scripts_tree(PRE_CONSOLIDATION, tmp_path)
    except PromisorObjectUnavailable as exc:
        pytest.skip(
            "blobs historiques non materialisables (fetch promisor en echec) : "
            f"controle retroactif non jouable -- {exc}"
        )

    result = scanner.scan(tmp_path)
    pairs = _pairs_by_module(result)
    for module in (
        "scripts/extract_pptx_titles.py",
        "scripts/extract_slidev_titles.py",
    ):
        assert module in pairs, f"controle retroactif : {module} devait etre en paire"
        files = {e["test_file"] for e in pairs[module]["test_files"]}
        assert "scripts/tests/test_extract_titles.py" in files
        assert any("notebook_tools/tests" in f for f in files)
        basenames = {Path(f).name for f in files}
        assert len(basenames) == len(files), "la paire etait visible par basename"


def test_current_tree_extract_pair_stays_consolidated():
    """Non-regression : la consolidation a6720c7286 tient — les modules extract
    ne sont plus en paire a l'etat courant.

    NOTE : l'etat courant porte par ailleurs d'autres candidats de paire (le
    sur-comptage du recensement #14615, signale sur l'issue) — ce test ne les
    assert PAS : le scanner extrait, la revue decide.
    """
    result = scanner.scan(REPO_ROOT)
    modules_in_pairs = {pair["module"] for pair in result["pairs"]}
    assert "scripts/extract_pptx_titles.py" not in modules_in_pairs
    assert "scripts/extract_slidev_titles.py" not in modules_in_pairs
