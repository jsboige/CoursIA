"""Non-regression #15201: l'organe de pin des runners Linux.

Le compromis #15182 (`--disableupdate`) fige la version du runner a celle
de l'image ; le rebuild etant manuel, l'ecart avec l'exigence GitHub courante
grandit SANS RIEN QUI LE VOIE : les slots restent `online`, c'est GitHub qui
refuse de leur confier un job. L'organe `check_runner_version_pin.py` doit :
- comparer la pin (4 sites) a l'exigence GitHub courante et rouge quand
  l'ecart est bloquant (mode de panne nomme : "online mais non eligible") ;
- verifier que les sites de la pin sont en phase (verification
  cross-fichiers) ;
- ne JAMAIS rendre "a jour" sur un defaut de lecture de l'exigence (rc 2).

Levolet 1 est hermétique (faux depot injecte via --repo-root et
--required-version, API fakee par injection de commande). Le volet 2 est le
controle positif du repo reel : les 4 sites du depôt doivent s'accorder.

Run:
    python -m pytest scripts/tests/test_check_runner_version_pin.py
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

SCRIPT = (
    Path(__file__).resolve().parents[2]
    / "scripts"
    / "ci"
    / "check_runner_version_pin.py"
)
sys.path.insert(0, str(SCRIPT.parent))

import check_runner_version_pin as organ  # noqa: E402


def _fake_repo(tmp_path: Path, versions: dict[str, str] | None = None) -> Path:
    """Faux depot : le runner dir avec les 4 fichiers machine-assertables."""
    runner_dir = tmp_path / "scripts" / "ci" / "docker" / "linux-runner"
    runner_dir.mkdir(parents=True)
    v = versions or {}
    (runner_dir / "Dockerfile").write_text(
        "FROM ubuntu:24.04\n"
        f"ARG RUNNER_VERSION={v.get('Dockerfile', '2.337.0')}\n",
        encoding="utf-8",
    )
    (runner_dir / "Dockerfile.lean").write_text(
        f"FROM coursia-linux-runner:{v.get('Dockerfile.lean', '2.337.0')}\n",
        encoding="utf-8",
    )
    (runner_dir / "supervise.sh").write_text(
        'IMAGE="${COURSIA_RUNNER_IMAGE:-coursia-linux-runner:'
        f"{v.get('supervise.sh:IMAGE', '2.337.0')}}}\"\n"
        'LEAN_IMAGE="${COURSIA_LEAN_RUNNER_IMAGE:-coursia-lean-runner:'
        f"{v.get('supervise.sh:LEAN_IMAGE', '2.337.0')}}}\"\n",
        encoding="utf-8",
    )
    return tmp_path


# --- volet 1 : verdicts, depot fake ------------------------------------------

def test_pin_a_jour_et_en_phase_rend_rc0(tmp_path: Path):
    repo = _fake_repo(tmp_path)
    pins = organ.parse_pins(repo)
    verdict = organ.report(pins, required="2.337.0")
    assert verdict["status"] == "PIN_OK"
    assert verdict["exit_code"] == 0
    assert verdict["pinned_version"] == "2.337.0"


def test_exigence_superieure_rouge_pin_stale(tmp_path: Path):
    """GitHub exige 2.338.0, la pin est a 2.337.0 : le slot est en ligne mais
    ne recevra plus de job -- le rapport doit nommer le mode de panne."""
    repo = _fake_repo(tmp_path)
    verdict = organ.report(organ.parse_pins(repo), required="2.338.0")
    assert verdict["status"] == "PIN_STALE"
    assert verdict["exit_code"] == 1
    assert "online mais non eligible" in verdict["detail"]
    assert "2.338.0" in verdict["detail"]


def test_sites_desaccordes_rend_in_phase_failure(tmp_path: Path):
    """Un seul site en retard (supervise.sh IMAGE 2.336.0) : les autres sites
    ne peuvent pas etre la verite -- l'image rebuild est une seule."""
    repo = _fake_repo(tmp_path, {"supervise.sh:IMAGE": "2.336.0"})
    verdict = organ.report(organ.parse_pins(repo), required="2.337.0")
    assert verdict["status"] == "IN_PHASE_FAILURE"
    assert verdict["exit_code"] == 1


def test_site_manquant_est_une_erreur_de_mesure_pas_une_pin(tmp_path: Path):
    """Dockerfile.lean absent : IN_PHASE_FAILURE qui nomme le site -- jamais
    un vert sur une pin incompletement lue."""
    repo = _fake_repo(tmp_path)
    (repo / "scripts" / "ci" / "docker" / "linux-runner" / "Dockerfile.lean").unlink()
    verdict = organ.report(organ.parse_pins(repo), required="2.337.0")
    assert verdict["status"] == "IN_PHASE_FAILURE"
    assert "Dockerfile.lean" in verdict["detail"]
    assert verdict["exit_code"] == 1


def test_exigence_illisible_rend_rc2_pas_un_vert(tmp_path: Path):
    """API injoignable (None) : aucun verdict possible -- rc 2, le rapport le
    dit explicitement au lieu de pretender que la pin est a jour."""
    repo = _fake_repo(tmp_path)
    verdict = organ.report(organ.parse_pins(repo), required=None)
    assert verdict["status"] == "UNCHECKED_REQUIREMENT"
    assert verdict["exit_code"] == 2
    assert verdict["guard_pass"] is None


def test_fetch_required_version_parse_et_echoue(tmp_path: Path):
    """Injection de commande : `gh api` attendu rend v2.337.0 ; une commande
    qui echoue (403/timeout) rend None, jamais une valeur par defaut."""
    ok = organ.fetch_required_version(
        gh=[sys.executable, "-c", 'print("v2.337.0")']
    )
    assert ok == "2.337.0"
    fail = organ.fetch_required_version(
        gh=[sys.executable, "-c", "import sys; sys.exit(1)"]
    )
    assert fail is None


# --- volet 2 : controle positif du depot reel ---------------------------------

def test_repo_reel_sites_en_phase():
    """Les 4 sites du depôt s'accordent (le controle positif de l'organe
    dans sa forme la plus simple) -- si ce test rouge, l'image n'est PAS une
    seule version et les slots portent des binaires differents."""
    pins = organ.parse_pins(organ.REPO_ROOT)
    assert len(set(pins.values())) == 1, f"sites desaccordes : {pins}"