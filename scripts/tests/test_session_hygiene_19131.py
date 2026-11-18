"""Regression #19131 : un journal FRAIS peut porter un echec de demarrage.

Du 2026-10-01 12:09Z au 2026-10-04 18:15Z, l'organe planifie ``merge_ready``
n'a rien merge : a chaque tir il sortait en exit 2 sur
« merge_ready : impossible de demarrer -- ... » (une ligne de commentaire de
``hold.txt`` lue comme une retenue malformee). Pendant ces trois jours,
``session_hygiene`` affichait ``[ok] journal ecrit il y a 16 min`` : le
controle de #17748 mesure la FRAICHEUR du journal, pas son CONTENU -- et un
journal qui repete un echec de demarrage est frais.

Remede : lire la DERNIERE LIGNE du journal en plus de son age.
- ROUGE sur signature d'echec de demarrage (``impossible de demarrer``) ou
  code de sortie non nul que l'organe ecrit lui-meme (``=== run end rc=N ===``).
- AMBRE quand plusieurs tirs consecutifs rendent la MEME ligne d'echec sans
  signature reconnue (un echec isole non signe reste vert : l'organe vit).
- La ligne lue est rendue dans le detail, pour que le coordinateur voie la
  cause sans ouvrir le fichier.
"""

from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

_SCRIPT = Path(__file__).resolve().parent.parent / "coordination" / "session_hygiene.py"
_spec = importlib.util.spec_from_file_location("session_hygiene_19131", _SCRIPT)
sh = importlib.util.module_from_spec(_spec)
sys.modules["session_hygiene_19131"] = sh
_spec.loader.exec_module(sh)

NOW = 1_800_000_000.0

STARTUP_FAIL = "merge_ready : impossible de demarrer -- retenue malformee dans hold.txt"


def _install(appdata: Path, repo: Path, journal: str, age_min: float = 5.0) -> Path:
    """Faux organe merge_ready : lanceur VBS + journal FRAIS au contenu donne."""
    state = appdata / "CoursIA" / "merge_ready"
    (state / "logs").mkdir(parents=True)
    (state / "run_hidden.vbs").write_text(
        'WScript.Quit WshShell.Run("C:\\Python314\\python.exe '
        f"{repo}\\scripts\\coordination\\install_merge_ready_task.py --run --repo {repo}\", 0, True)\n",
        encoding="utf-8",
    )
    log = state / "logs" / "merge_ready_20261001.log"
    log.write_text(journal, encoding="utf-8")
    t = NOW - age_min * 60
    os.utime(log, (t, t))
    return state


def _only(checks):
    assert len(checks) == 1
    return checks[0]


def test_echec_de_demarrage_sur_journal_frais_est_rouge(tmp_path):
    """Le cas mesure : journal frais, derniere ligne = echec de demarrage -> RED."""
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, f"=== run start ===\n{STARTUP_FAIL}\n", age_min=16)
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.RED
    assert "impossible de demarrer" in c.detail


def test_code_de_sortie_non_nul_est_rouge(tmp_path):
    """L'organe ecrit lui-meme son rc : rc=2 sur un journal frais -> RED."""
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, "=== run start ===\n=== run end rc=2 ===\n")
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.RED
    assert "rc=2" in c.detail


def test_tir_nominal_sur_journal_frais_est_vert(tmp_path):
    """Controle negatif : journal frais, derniere ligne = tir nominal -> GREEN."""
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, "=== run start ===\n=== run end rc=0 ===\n")
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.GREEN
    assert "rc=0" in c.detail


def test_echec_non_signe_repetie_est_ambre(tmp_path):
    """Sans signature reconnue, une MEME ligne d'echec repetee alerte -> AMBER."""
    seat = tmp_path / "seat"
    seat.mkdir()
    ligne = "merge_ready : echec de lecture de hold.txt (retenue malformee)"
    _install(tmp_path, seat, "\n".join([ligne] * 3) + "\n")
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.AMBER
    assert "3" in c.detail


def test_ligne_benigne_repetee_reste_verte(tmp_path):
    """Controle : une ligne NOMINALE repetee n'est pas un echec -- pas d'AMBRE.

    Un organe sain ecrit la meme ligne a chaque tir ; seule la repetition d'une
    ligne d'ECHEC doit alerter, sinon l'AMBRE punirait la regularite.
    """
    seat = tmp_path / "seat"
    seat.mkdir()
    ligne = "merge_ready : 3 PRs examinees, rien a merger ce tour"
    _install(tmp_path, seat, "\n".join([ligne] * 3) + "\n")
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.GREEN


def test_echec_non_signe_isole_reste_vert(tmp_path):
    """Un echec isole non signe ne rougit pas : la ligne est rendue, verdict GREEN."""
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, "merge_ready : retenu par hold.txt (rien a merger ce tour)\n")
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.GREEN
    assert "hold.txt" in c.detail


def test_journal_muet_garde_le_rouge_et_nomme_la_ligne(tmp_path):
    """Le predicat d'age de #17748 reste entier : muet -> RED, avec la ligne lue."""
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, f"{STARTUP_FAIL}\n", age_min=140)
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.RED
    assert c.data["age_min"] == 140
    assert "impossible de demarrer" in c.detail
