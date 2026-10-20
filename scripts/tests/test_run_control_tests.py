"""Tests de `scripts/ci/run_control_tests.py` (#20200).

Le contrat teste est un contrat de DIAGNOSTIC, pas de verdicte : les trois
situations sortent en non-zero (fail-closed), mais elles ne doivent pas
s'accuser l'une l'autre. Un arbre de checkout ampute doit etre nomme comme tel
et **jamais** comme une derive de version ; un vrai echec de test doit garder
son code de sortie sans etre requalifie.
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "ci" / "run_control_tests.py"

# Le module est importe pour couvrir les branches internes de `_pytest_boundary`
# que le contrat de bout en bout n'atteint pas (revue NanoClaw, #21566).
CI_DIR = ROOT / "scripts" / "ci"
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))
import run_control_tests as rct  # noqa: E402


def _run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


def _write(tmp_path: Path, name: str, body: str) -> str:
    path = tmp_path / name
    path.write_text(body, encoding="utf-8")
    return str(path)


def test_missing_file_names_the_checkout_and_never_a_drift(tmp_path):
    """Le cas mesure le 2026-10-10 : un fichier commite absent du disque."""
    missing = str(tmp_path / "test_gitleaks_qwen_rule.py")

    proc = _run(missing, "--label", "Gitleaks positive controls")

    assert proc.returncode == 1, proc.stdout
    assert "Arbre de checkout incomplet" in proc.stdout
    assert missing in proc.stdout
    # La faute a ne pas commettre : accuser une derive de version/pin.
    lowered = proc.stdout.lower()
    assert "drift" not in lowered
    assert "derive" not in lowered
    assert "Update both to the same value" not in proc.stdout
    # Le nom du controle est repris tel quel, pour que le log soit attribuable.
    assert "Gitleaks positive controls" in proc.stdout


def test_the_checkout_check_precedes_pytest(tmp_path):
    """Un chemin valide et un absent : l'absent est nomme, pytest n'est pas lance."""
    ok = _write(tmp_path, "test_ok.py", "def test_pass():\n    assert True\n")
    missing = str(tmp_path / "absent.py")

    proc = _run(ok, missing)

    assert proc.returncode == 1
    assert "Arbre de checkout incomplet" in proc.stdout
    assert missing in proc.stdout


def test_present_passing_file_is_green(tmp_path):
    """Controle negatif : un arbre sain ne doit RIEN dire."""
    ok = _write(tmp_path, "test_ok.py", "def test_pass():\n    assert True\n")

    proc = _run(ok)

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "::error" not in proc.stdout


def test_real_failure_keeps_its_exit_code_and_is_not_relabelled(tmp_path):
    """Un vrai echec de test reste un vrai echec : rc propage, aucun message ajoute."""
    bad = _write(tmp_path, "test_bad.py", "def test_fail():\n    assert False\n")

    proc = _run(bad)

    assert proc.returncode == 1
    assert "Controle vide" not in proc.stdout
    assert "Arbre de checkout incomplet" not in proc.stdout
    assert "::error" not in proc.stdout


def test_file_without_tests_is_named_vacuous(tmp_path):
    """Le controle rougit sur sa PROPRE vacuite -- l'objet meme de #20200."""
    empty = _write(tmp_path, "test_empty.py", "# aucun test ici\n")

    proc = _run(empty)

    assert proc.returncode == 1, proc.stdout
    assert "Controle vide" in proc.stdout
    assert "aucune assertion" in proc.stdout
    # Un controle vide n'est pas une faute du depot : ne pas le confondre.
    assert "Arbre de checkout incomplet" not in proc.stdout


def test_collection_error_is_named_as_collection_and_not_as_a_test_failure(tmp_path):
    """rc=2 (INTERRUPTED) : la collecte echoue avant execution, ce n'est pas un test rouge.

    Cas mesure #21539 : sur Windows la collecte remontait jusqu'a un point
    d'analyse protege et rendait rc=2 ; l'appelant lisait 2, puis la suite
    accusait la PR d'un echec de test qu'aucun test n'avait produit.
    """
    broken = _write(tmp_path, "test_import_casse.py", "import module_qui_n_existe_pas_du_tout\n")

    proc = _run(broken)

    assert proc.returncode == 1, proc.stdout
    assert "Erreur de collecte" in proc.stdout
    # Ni un test rouge, ni un controle vide : les trois causes restent distinctes.
    assert "Controle vide" not in proc.stdout
    assert "Arbre de checkout incomplet" not in proc.stdout


def test_pytest_config_is_pinned_so_the_rootdir_never_walks_up(tmp_path):
    """Le rootdir vient du configfile nomme, pas d'une remontee vers la racine du volume."""
    ok = _write(tmp_path, "test_ok.py", "def test_pass():\n    assert True\n")

    proc = _run(ok)

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert f"rootdir: {ROOT}" in proc.stdout, proc.stdout[:2000]


# --- branches de repli de _pytest_boundary (revue NanoClaw, #21566) ---------
# La branche `-c` est couverte par le test ci-dessus (le depot a toujours un
# configfile sous le cwd). Les deux branches de repli ne l'etaient pas :
# un configfile absent au-dessus du cwd, et des chemins sur des volumes
# differents. Elles sontdeterminees ici, sans dependre de l'arborescence
# de la machine (le cwd est un tmp_path, les noms de configfile sont
# neutralises).

def test_repli_rootdir_commun_quand_aucun_configfile_nest_au_dessus(
    monkeypatch, tmp_path
):
    """Aucun configfile dans les ancetres du cwd -> le rootdir est le chemin commun."""
    monkeypatch.setattr(rct, "CONFIG_NAMES", ("config-qui-nexiste-pas.ini",))
    monkeypatch.chdir(tmp_path)
    cible = tmp_path / "test_ok.py"
    cible.write_text("def test_pass():\n    assert True\n", encoding="utf-8")

    attendu = os.path.dirname(os.path.abspath(str(cible)))
    assert rct._pytest_boundary([str(cible)]) == ["--rootdir", attendu]


def test_repli_sans_rootdir_quand_les_volumes_different(monkeypatch, tmp_path):
    """Des chemins sur des volumes differents : aucun rootdir n'est force."""
    monkeypatch.setattr(rct, "CONFIG_NAMES", ("config-qui-nexiste-pas.ini",))
    monkeypatch.chdir(tmp_path)

    def _volumes_differents(*args, **kwargs):
        raise ValueError("Paths don't have the same drive")

    monkeypatch.setattr(rct.os.path, "commonpath", _volumes_differents)

    assert rct._pytest_boundary(["C:/a/test_x.py", "D:/b/test_y.py"]) == []
