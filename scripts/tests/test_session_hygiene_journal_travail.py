"""Le journal de TRAVAIL comme source de vivacite d'un organe planifie.

Mesure du 22/11 (merge_ready sur ai-01) : la tache planifiee declenche bien
l'organe, et l'organe travaille -- mais le log de lancement du jour se FIGE
pendant le tir. Le lanceur (`install_merge_ready_task.py --run`) ouvre le log du
jour et y redirige la sortie de l'organe ; cette sortie est BUFFERISEE cote
enfant, donc le mtime du log ne bouge plus une fois le tir lance.

Etat mesure a 11:33Z :
- `logs/merge_ready_20261122.log` : mtime **07:03** (tir lance a 06:56) ;
- `journal.jsonl` (un verdict par PR evaluee) : mtime **11:32:28** ;
- `session_hygiene` rendait : « journal muet depuis 269 min » -- **ROUGE FAUX**.

La regle : l'organe n'est muet que si **TOUTES** ses sources sont muettes. La
vivacite se mesure sur la source la plus recente (log de lancement ET journal de
travail), jamais sur une seule.

Ces tests sont SYNTHETIQUES : ils fabiquent les deux sources avec des ages
controles. Le cas reel est verifie par la mesure ci-dessus (rapportee dans le
body de la PR).
"""

from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

_SCRIPT = Path(__file__).resolve().parent.parent / "coordination" / "session_hygiene.py"
_spec = importlib.util.spec_from_file_location("session_hygiene_journal_travail", _SCRIPT)
sh = importlib.util.module_from_spec(_spec)
sys.modules["session_hygiene_journal_travail"] = sh
_spec.loader.exec_module(sh)

NOW = 1_800_000_000.0

#: Age du log de lancement mesure : 07:03 pour un tir lance a 06:56, relu a 11:33.
AGE_LOG_FIGE_MIN = 269
#: Age du journal de travail mesure : ecrit 41 s avant la lecture.
AGE_JOURNAL_FRAIS_MIN = 0


def _install(appdata: Path, repo: Path, log: str, age_log_min: float = 5.0,
             journal: str | None = None, age_journal_min: float = 1.0) -> Path:
    """Faux organe merge_ready : lanceur VBS + log de lancement + journal de travail.

    ``journal=None`` = l'organe n'ecrit pas de journal de travail (machine ou
    organe qui n'en a pas) : le repli sur le log seul doit rester entier.
    """
    state = appdata / "CoursIA" / "merge_ready"
    (state / "logs").mkdir(parents=True)
    (state / "run_hidden.vbs").write_text(
        'WScript.Quit WshShell.Run("C:\\Python314\\python.exe '
        f"{repo}\\scripts\\coordination\\install_merge_ready_task.py --run --repo {repo}\", 0, True)\n",
        encoding="utf-8",
    )
    fichier_log = state / "logs" / "merge_ready_20261122.log"
    fichier_log.write_text(log, encoding="utf-8")
    t = NOW - age_log_min * 60
    os.utime(fichier_log, (t, t))
    if journal is not None:
        fichier_journal = state / "journal.jsonl"
        fichier_journal.write_text(journal, encoding="utf-8")
        t = NOW - age_journal_min * 60
        os.utime(fichier_journal, (t, t))
    return state


def _only(checks):
    assert len(checks) == 1
    return checks[0]


def test_le_journal_de_travail_frais_annule_le_rouge_du_log_fige(tmp_path):
    """LE CAS MESURE : log fige depuis 269 min, journal ecrit a l'instant -> GREEN.

    L'organe travaille (il evalue des PR) ; le log, lui, ne bouge plus parce que
    la sortie de l'enfant est bufferisee. Rendre ROUGE ici, c'est publier une
    alarme fausse qui immobilise la session.
    """
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(
        tmp_path,
        seat,
        "=== 2026-11-22T06:56:34 run start ===\ndepot synchronise sur origin/main\n",
        age_log_min=AGE_LOG_FIGE_MIN,
        journal='{"ts": "2026-11-22T11:32:28Z", "pr": 27900, "verdict": "skipped"}\n',
        age_journal_min=AGE_JOURNAL_FRAIS_MIN,
    )
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.GREEN
    assert c.data["age_min"] == AGE_JOURNAL_FRAIS_MIN
    assert "journal de travail" in c.data["source"]
    assert "journal de travail" in c.detail


def test_le_log_frais_reste_la_source_quand_il_n_y_a_pas_de_journal(tmp_path):
    """Repli : sans journal de travail, la vivacite se lit sur le log (comportement d'origine)."""
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(tmp_path, seat, "=== run start ===\n=== run end rc=0 ===\n", age_log_min=5)
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.GREEN
    assert c.data["source"] == "log de lancement"
    assert c.data["age_min"] == 5


def test_les_deux_sources_muettes_rougissent(tmp_path):
    """L'organe n'est muet que si TOUTES ses sources sont muettes -> RED.

    Controle negatif : la correction ne doit pas rendre l'organe muet
    infranchissable (c'etait le role du predicat d'age de #17748).
    """
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(
        tmp_path,
        seat,
        "=== run start ===\ndepot synchronise sur origin/main\n",
        age_log_min=269,
        journal='{"ts": "2026-11-22T11:32:28Z", "pr": 27900, "verdict": "skipped"}\n',
        age_journal_min=269,
    )
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.RED
    assert c.data["age_min"] == 269
    assert "TOUTES ses sources" in c.detail


def test_un_log_frais_prime_sur_un_journal_fige(tmp_path):
    """Le symetrique : un tir qui vient de finir ecrit le log, meme sans verdict.

    Un organe qui n'evalue aucune PR n'ecrit rien dans le journal de travail :
    son log reste alors la seule preuve qu'il a tire. La vivacite prend donc la
    source la plus recente, pas une source privilegiee.
    """
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(
        tmp_path,
        seat,
        "=== run start ===\n=== run end rc=0 ===\n",
        age_log_min=2,
        journal='{"ts": "2026-11-20T08:00:00Z", "pr": 27890, "verdict": "skipped"}\n',
        age_journal_min=600,
    )
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.GREEN
    assert c.data["source"] == "log de lancement"
    assert c.data["age_min"] == 2


def test_un_echec_de_demarrage_reste_rouge_meme_si_le_journal_avance(tmp_path):
    """Le contenu garde sa priorite : #19131 n'est pas abroge par la source de vivacite.

    Un journal de travail qui avance ne pardonne pas un echec de demarrage : le
    predicat de CONTENU (#19131) reste entier, il ne s'ajoute qu'une source.
    """
    seat = tmp_path / "seat"
    seat.mkdir()
    _install(
        tmp_path,
        seat,
        "=== run start ===\nmerge_ready : impossible de demarrer -- retenue malformee\n",
        age_log_min=16,
        journal='{"ts": "2026-11-22T11:32:28Z", "pr": 27900, "verdict": "skipped"}\n',
        age_journal_min=1,
    )
    c = _only(sh.check_scheduled_organs(local_appdata=tmp_path, now=NOW))
    assert c.level == sh.RED
    assert "impossible de demarrer" in c.detail
