"""#23342 : install-coursia-units.sh -- dry-run non privilegie + garde d'ecriture.

CI-wired : ce fichier vit dans `scripts/ci/tests/`, collecte par le run pytest de
`scripts-tests.yml`. Il couvre les quatre criteres d'acceptance de #23342 :

  1. `--machine M --dry-run` en utilisateur ordinaire rend l'inventaire, rc=0 ;
  2. le meme appel SANS `--dry-run` abandonne toujours sur "root requis" ;
  3. les deux sont couverts par un test qui tourne sur une machine de CI sans
     privilege ;
  4. le compte de sites d'ecriture gardes est verifie par
     `check_coursia_units_write_guards.py`, que ce test execute aussi sur un
     script synthetique non garde (controle positif : l'organe a des dents).

Le harnais des deux modes (1, 2, 3) est le test bash sœur
`test_install_coursia_units_nonprivileged.sh` (stubbe `id`=1000, execute le
dry-run et le mode reel, et porte son propre controle positif). Ce fichier pytest
est le point d'entree CI : il invoque ce harnais, puis exerce l'organe de garde.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve()
CI_DIR = HERE.parent.parent                      # scripts/ci
RUNNER_DIR = CI_DIR / "docker/linux-runner"
BASH_TEST = RUNNER_DIR / "test_install_coursia_units_nonprivileged.sh"
ORGAN = CI_DIR / "check_coursia_units_write_guards.py"
TARGET = RUNNER_DIR / "install-coursia-units.sh"


def _run(cmd: list[str], timeout: int) -> subprocess.CompletedProcess:
    # encoding= explicite : text=True seul decode en cp1252 sur un hote Windows
    # et crashe sur la sortie UTF-8 (accentes) du harnais (#12811).
    return subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=timeout
    )


def test_two_nonprivileged_modes() -> None:
    """Criteria 1, 2, 3 : le harnais bash (id=1000) passe de bout en bout."""
    proc = _run(["bash", str(BASH_TEST)], timeout=120)
    assert proc.returncode == 0, (
        f"harness rc={proc.returncode}\n{proc.stdout}\n{proc.stderr}"
    )
    # Le harnais affiche son propre compte de contrôles réussis.
    assert "6 PASS / 0 FAIL" in proc.stdout, proc.stdout


def test_write_guard_organ_green_on_shipped_script() -> None:
    """Criterion 4 : l'organe passe sur le script livre (toutes les ecrites gardes)."""
    proc = _run([sys.executable, str(ORGAN), str(TARGET)], timeout=60)
    assert proc.returncode == 0, (
        f"organe rouge sur le script livre:\n{proc.stdout}\n{proc.stderr}"
    )


def test_write_guard_organ_red_on_unguarded_script(tmp_path: Path) -> None:
    """Controle positif : l'organe rougit sur une ecriture HORS garde, epargne la gardee.

    Un script synthetique minimal, independant du contenu exact du script livre :
    une `systemctl restart` sans garde (doit etre signalee) et une
    `systemctl daemon-reload` sous garde (doit etre epargnee).
    """
    sample = tmp_path / "unguarded.sh"
    sample.write_text(
        "#!/usr/bin/env bash\n"
        'systemctl restart docker.service\n'
        '[ "$icc_DRY_RUN" -eq 1 ] || systemctl daemon-reload\n',
        encoding="utf-8",
    )
    proc = _run([sys.executable, str(ORGAN), str(sample)], timeout=60)
    assert proc.returncode == 1, (
        f"organe aveugle a l'ecriture non gardee:\n{proc.stdout}\n{proc.stderr}"
    )
    assert "systemctl restart docker.service" in proc.stderr, proc.stderr
    assert "daemon-reload" not in proc.stderr, (
        "l'organe a signale la ligne GARDEE -- faux positif"
    )


def test_write_guard_organ_fails_closed_on_unmatched_backtick(tmp_path: Path) -> None:
    """Une coquille de formatage ne doit pas blanchir les écritures suivantes."""
    sample = tmp_path / "unparseable.sh"
    sample.write_text(
        "# unmatched ` backtick\n"
        "systemctl restart docker.service\n",
        encoding="utf-8",
    )
    proc = _run([sys.executable, str(ORGAN), str(sample)], timeout=60)
    assert proc.returncode == 1, (
        f"organe vert malgré une source non parsable:\n{proc.stdout}\n{proc.stderr}"
    )
    assert "source non parsable" in proc.stderr, proc.stderr
