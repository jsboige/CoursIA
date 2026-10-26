"""Tests du lanceur plafonne ``scripts/ci/run_guarded.py`` (issue #21661).

Ce que ces tests doivent prouver, mecanisme par mecanisme :

* le **plafond dur de memoire** du Job Object arrete bien l'entrainement quand
  l'allocation depasse le plafond, et l'arret vient du **noyau** (MemoryError
  chez l'enfant) -- pas d'une heurique du lanceur ;
* le **controle negatif** : sans Job Object (``--no-job``), la meme allocation
  passe. Sans ce contre-tour, le test positif ne prouve rien (il pourrait
  passer pour une raison étrangère au plafond) ;
* la **garde de charge de commit** refuse un demarrage au-dessus du seuil, et
  refuse **aussi** quand la mesure est illisible (fail-CLOSED) ;
* le **verrou N=1** refuse un second lancement concurrent ;
* le **fichier de PID** est ecrit ;
* la **garde GPU** (#22456) : sans ``--gpu-entity`` AUCUN appel au ledger ;
  avec ``--gpu-entity`` vers un device tenu (HOLD) le lancement est refuse ;
  reservation impossible a ecrire = lancement refuse ; source du gate
  indisponible = lancement refuse ; et la sequence codee held -> travail ->
  released, y compris le signal d'un released manquant (rc 7).

Ces tests ne s'executent que sur Windows : le Job Object est une API
Windows. Hors Windows, ils sont ignores (le lanceur y mesure et tue, mais ne
plafonne pas l'allocation).

Les tests GPU sont HERMETIQUES : l'appel a l'organe ``debt_ledger.py`` est
remplace par un faux injecte par monkeypatch (aucun sous-processus de
l'organe, aucun reseau, aucun depot du parc touche, aucun git invoque).
"""
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
GUARDED = REPO_ROOT / "scripts" / "ci" / "run_guarded.py"
LAUNCHER = (REPO_ROOT / "MyIA.AI.Notebooks" / "QuantConnect" / "ML-Training-Pipeline"
            / "scripts" / "launchers" / "launch_capped.ps1")

pytestmark = pytest.mark.skipif(os.name != "nt", reason="Job Object : API Windows")

# Enfant qui alloue plus que le plafond. Il alloue par blocs pour que
# l'echec d'allocation soit net (MemoryError) et non un crash du process.
ALLOC_CHILD = (
    "import sys\n"
    "blocks = []\n"
    "try:\n"
    "    for _ in range(64):\n"
    "        blocks.append(bytearray(16 * 1024 * 1024))\n"
    "except MemoryError:\n"
    "    print('MEMORYERROR', flush=True)\n"
    "    sys.exit(1)\n"
    "print('ALLOC_OK', flush=True)\n"
)

TRIVIAL_CHILD = "print('TRIVIAL_OK', flush=True)\n"


def _load_guarded():
    spec = importlib.util.spec_from_file_location("run_guarded_mod", GUARDED)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def guarded():
    return _load_guarded()


def _run(guarded, argv, tmp_path, extra=()):
    """Lance le lanceur et rend ``(rc, stdout_console, journal)``."""
    log = tmp_path / "run.log"
    cmd = [sys.executable, str(GUARDED), "--log", str(log), *extra, "--", *argv]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=300,
                          encoding="utf-8", errors="replace")
    journal = log.read_text(encoding="utf-8") if log.exists() else ""
    return proc.returncode, proc.stdout, journal


def test_plafond_job_arrete_l_allocation(guarded, tmp_path):
    """Le plafond du Job Object fait ECHOUE l'allocation chez l'enfant.

    Le plafond RSS du lanceur (``--limit-gib``) est volontairement laisse
    haut : l'arret observe doit venir du noyau (rc de l'enfant), pas de la
    garde de RSS (rc 3).
    """
    rc, out, journal = _run(
        guarded,
        [sys.executable, "-c", ALLOC_CHILD],
        tmp_path,
        extra=["--limit-gib", "8", "--reserve-gib", "1",
               "--job-memory-limit-gib", "0.25"],
    )
    # La sortie de l'enfant est redirigee vers le journal (--log), pas vers la
    # console du lanceur : c'est la que se lit la preuve de l'echec.
    assert "MEMORYERROR" in journal, f"l'enfant aurait du echouer d'allocation :\n{out}\n{journal}"
    assert rc == 1, f"rc {rc} attendu (MemoryError de l'enfant), journal :\n{journal}"
    assert "plafond job" in journal, journal


def test_controle_negatif_sans_job_object_l_allocation_passe(guarded, tmp_path):
    """CONTROLE NEGATIF : sans Job Object, la meme allocation reussit.

    C'est ce test qui prouve que l'arret du test precedent vient bien du
    plafond et pas d'une coincidence de l'environnement.
    """
    rc, out, journal = _run(
        guarded,
        [sys.executable, "-c", ALLOC_CHILD],
        tmp_path,
        extra=["--limit-gib", "8", "--reserve-gib", "1", "--no-job"],
    )
    assert "ALLOC_OK" in journal, f"l'allocation aurait du reussir sans plafond :\n{out}\n{journal}"
    assert rc == 0, f"rc {rc} attendu (0) sans plafond, journal :\n{journal}"


def test_garde_de_charge_de_commit_refuse_au_dessus_du_seuil(guarded, tmp_path):
    """Un seuil de 1 % est franchi par toute machine vivante : refus garanti."""
    rc, out, journal = _run(
        guarded,
        [sys.executable, "-c", TRIVIAL_CHILD],
        tmp_path,
        extra=["--limit-gib", "8", "--reserve-gib", "1", "--max-commit-charge-pct", "1"],
    )
    assert rc == 5, f"rc {rc} attendu (5 = refus), journal :\n{journal}"
    assert "charge de commit" in journal, journal
    assert "TRIVIAL_OK" not in journal, "rien ne doit avoir ete lance"


def test_garde_de_charge_de_commit_illisible_refuse(guarded, tmp_path, monkeypatch):
    """Fail-CLOSED : une mesure ILLISIBLE refuse aussi le demarrage."""
    monkeypatch.setattr(guarded, "_commit_charge_pct", lambda: None)
    log = tmp_path / "illisible.log"
    rc = guarded.main([
        "--limit-gib", "8", "--reserve-gib", "1",
        "--max-commit-charge-pct", "50",
        "--log", str(log),
        "--", sys.executable, "-c", TRIVIAL_CHILD,
    ])
    assert rc == 5, f"rc {rc} attendu (5 = refus fail-CLOSED)"
    journal = log.read_text(encoding="utf-8")
    assert "ILLISIBLE" in journal, journal


def test_verrou_n1_refuse_un_second_lancement(guarded, tmp_path):
    """Un verrou deja pris refuse le second lancement (N = 1)."""
    lock = tmp_path / "train.lock"
    holder = guarded._acquire_exclusive_lock(str(lock))
    assert holder is not None, "verrou impossible a prendre sur un fichier libre"
    try:
        rc, out, journal = _run(
            guarded,
            [sys.executable, "-c", TRIVIAL_CHILD],
            tmp_path,
            extra=["--limit-gib", "8", "--reserve-gib", "1",
                   "--exclusive-lock", str(lock)],
        )
        assert rc == 5, f"rc {rc} attendu (5 = refus), journal :\n{journal}"
        assert "verrou exclusif" in journal, journal
        assert "TRIVIAL_OK" not in out, "rien ne doit avoir ete lance"
    finally:
        holder.close()


def test_fichier_de_pid_ecrit(guarded, tmp_path):
    """Le PID du processus lance est ecrit dans le fichier demande."""
    pidfile = tmp_path / "pid.txt"
    rc, out, journal = _run(
        guarded,
        [sys.executable, "-c", TRIVIAL_CHILD],
        tmp_path,
        extra=["--limit-gib", "8", "--reserve-gib", "1", "--pid-file", str(pidfile)],
    )
    assert rc == 0, journal
    assert pidfile.exists(), "fichier de PID absent"
    pid = int(pidfile.read_text(encoding="utf-8").strip())
    assert pid > 0


def test_defaut_de_production_48_go():
    """Le lanceur de production porte 48 Go et 85 % (engagement Maintenance)."""
    texte = LAUNCHER.read_text(encoding="utf-8")
    assert "[double]$MemoryCapGiB = 48" in texte, "defaut de memoire absent du lanceur"
    assert "[int]$MaxCommitChargePct = 85" in texte, "defaut de charge de commit absent"
    assert "--job-memory-limit-gib" in texte, "le lanceur ne pose pas de plafond de job"
    assert "--exclusive-lock" in texte, "le lanceur ne pose pas de verrou N=1"
    assert "--max-commit-charge-pct" in texte, "le lanceur ne pose pas de garde d'admission"


# --- Garde GPU (#22456) : gate + reservation ledger --------------------------
#
# Hermeticite : l'appel a l'organe scripts/coordination/debt_ledger.py est
# remplace par un faux injecte par monkeypatch -- aucun sous-processus de
# l'organe, aucun reseau, aucun depot du parc touche, aucun git invoque.
# Seul l'enfant trivial (python -c local) tourne reellement.

def _faux_organ_factory(calls, gate_verdict="NO_OBS", gate_rc=0,
                        gate_unavailable=False, fail_states=()):
    """Construit un faux ``_run_ledger_organ`` pilotant les verdicts du gate.

    Chaque appel est enregistre dans ``calls`` (spy). ``gate_unavailable``
    simule une panne de l'organe (rc=None) ; ``fail_states`` fait echouer
    l'append pour les etats listes.
    """
    def faux_organ(args, timeout=120):
        calls.append(list(args))
        if args[0] == "check_pending":
            if gate_unavailable:
                return None, "", "organe introuvable (faux hermetique)"
            payload = {"verdict": gate_verdict, "reason": "faux organ",
                       "entity": "myia-ai-01#gpu2"}
            return gate_rc, json.dumps(payload), ""
        if args[0] == "append":
            fields = json.loads(args[args.index("--fields-json") + 1])
            if fields.get("state") in fail_states:
                return 2, "", f"ERROR FAUX: append refuse pour state={fields.get('state')}"
            return 0, "[OBS] " + json.dumps({"observation_id": "obs-faux"}), ""
        return 0, "", ""
    return faux_organ


def _gpu_argv(log, expected_end=None):
    """Argv type d'un lancement garde avec device declare."""
    argv = ["--limit-gib", "8", "--reserve-gib", "1", "--poll", "0.2",
            "--gpu-entity", "myia-ai-01#gpu2",
            "--gpu-holder", "myia-ai-01:CoursIA-2",
            "--gpu-workload", "smoke-test",
            "--log", str(log)]
    if expected_end:
        argv += ["--gpu-expected-end", expected_end]
    return argv


def test_sans_gpu_entity_aucun_appel_au_ledger(guarded, tmp_path, monkeypatch):
    """Non-regression : sans device declare, le ledger n'est JAMAIS sollicite."""
    calls = []
    monkeypatch.setattr(guarded, "_run_ledger_organ", _faux_organ_factory(calls))
    log = tmp_path / "no_gpu.log"
    rc = guarded.main([
        "--limit-gib", "8", "--reserve-gib", "1", "--poll", "0.2",
        "--log", str(log), "--", sys.executable, "-c", TRIVIAL_CHILD])
    journal = log.read_text(encoding="utf-8")
    assert rc == 0, f"rc {rc} attendu (0), journal :\n{journal}"
    assert "TRIVIAL_OK" in journal, journal
    assert calls == [], "le ledger ne doit etre appele en aucun point sans --gpu-entity"


def test_gpu_gate_hold_refuse_le_lancement(guarded, tmp_path, monkeypatch):
    """Un device tenu (verdict HOLD) refuse le lancement, sans poser de held."""
    calls = []
    monkeypatch.setattr(
        guarded, "_run_ledger_organ",
        _faux_organ_factory(calls, gate_verdict="HOLD", gate_rc=1))
    log = tmp_path / "gpu_hold.log"
    rc = guarded.main(_gpu_argv(log) + ["--", sys.executable, "-c", TRIVIAL_CHILD])
    journal = log.read_text(encoding="utf-8")
    assert rc == 5, f"rc {rc} attendu (5 = refus), journal :\n{journal}"
    assert "HOLD" in journal, journal
    assert "TRIVIAL_OK" not in journal, "rien ne doit avoir ete lance sur un device tenu"
    assert [c[0] for c in calls] == ["check_pending"], (
        "le gate doit etre consulte une seule fois, et AUCUN append ne doit "
        f"suivre sur un device refuse ; appels : {calls}")


def test_gpu_gate_indisponible_refuse_le_lancement(guarded, tmp_path, monkeypatch):
    """Fail-CLOSED : une source de gate illisible refuse aussi le lancement."""
    calls = []
    monkeypatch.setattr(
        guarded, "_run_ledger_organ",
        _faux_organ_factory(calls, gate_unavailable=True))
    log = tmp_path / "gpu_unreachable.log"
    rc = guarded.main(_gpu_argv(log) + ["--", sys.executable, "-c", TRIVIAL_CHILD])
    journal = log.read_text(encoding="utf-8")
    assert rc == 5, f"rc {rc} attendu (5 = refus), journal :\n{journal}"
    assert "INDISPONIBLE" in journal, journal
    assert "TRIVIAL_OK" not in journal
    assert [c[0] for c in calls] == ["check_pending"], calls


def test_gpu_reservation_illisible_refuse_le_lancement(guarded, tmp_path, monkeypatch):
    """Fail-CLOSED : un held qui ne peut pas etre ecrit refuse le lancement."""
    calls = []
    monkeypatch.setattr(
        guarded, "_run_ledger_organ",
        _faux_organ_factory(calls, fail_states=("held",)))
    log = tmp_path / "gpu_nowrite.log"
    rc = guarded.main(_gpu_argv(log) + ["--", sys.executable, "-c", TRIVIAL_CHILD])
    journal = log.read_text(encoding="utf-8")
    assert rc == 5, f"rc {rc} attendu (5 = refus), journal :\n{journal}"
    assert "n'a pas pu etre ecrite" in journal, journal
    assert "TRIVIAL_OK" not in journal, "rien ne doit etre lance sans reservation portee"
    # le gate a ete consulte PUIS l'ecriture tentee : c'est l'ordre code
    assert [c[0] for c in calls] == ["check_pending", "append"], calls


def test_gpu_sequence_hold_puis_released(guarded, tmp_path, monkeypatch):
    """La sequence codee : gate -> held AVANT l'enfant -> released au teardown.

    C'est le test de la sequence mesuree par le regisseur : la reservation
    existe avant le premier appel CUDA (le held precede le lancement), et le
    released ferme le hold avec started_at = instant du held et expected_end =
    heure reelle de fin.
    """
    calls = []
    monkeypatch.setattr(guarded, "_run_ledger_organ", _faux_organ_factory(calls))
    log = tmp_path / "gpu_seq.log"
    rc = guarded.main(
        _gpu_argv(log, expected_end="2026-10-26T18:00:00Z")
        + ["--", sys.executable, "-c", TRIVIAL_CHILD])
    journal = log.read_text(encoding="utf-8")
    assert rc == 0, f"rc {rc} attendu (0), journal :\n{journal}"
    assert "TRIVIAL_OK" in journal, "l'enfant doit avoir tourne"
    appends = []
    for call in calls:
        if call[0] == "append":
            appends.append(json.loads(call[call.index("--fields-json") + 1]))
    assert len(appends) == 2, f"held + released attendus, appels : {calls}"
    held, released = appends
    assert held["state"] == "held"
    assert held["holder"] == "myia-ai-01:CoursIA-2"
    assert held["workload"] == "smoke-test"
    assert held["expected_end"] == "2026-10-26T18:00:00Z"
    assert held["started_at"].endswith("Z"), "le stamp doit etre UTC explicite"
    assert released["state"] == "released"
    assert released["started_at"] == held["started_at"], (
        "le released doit citer l'instant du held qu'il ferme")
    assert released["expected_end"] >= held["started_at"], (
        "l'expected_end du released est l'heure reelle de fin")
    assert "held ecrit" in journal and "released ecrit" in journal, journal


def test_gpu_released_manquant_est_signale(guarded, tmp_path, monkeypatch):
    """Un held dont le released echoue laisse le rc non nul (7) + un message.

    Le defaut a eviter est un held vivant sur un device libre : le travail a
    reussi, mais l'appelant ne doit pas croire que tout va bien.
    """
    calls = []
    monkeypatch.setattr(
        guarded, "_run_ledger_organ",
        _faux_organ_factory(calls, fail_states=("released",)))
    log = tmp_path / "gpu_stuck.log"
    rc = guarded.main(_gpu_argv(log) + ["--", sys.executable, "-c", TRIVIAL_CHILD])
    journal = log.read_text(encoding="utf-8")
    assert rc == 7, f"rc {rc} attendu (7 = released non ecrit), journal :\n{journal}"
    assert "TRIVIAL_OK" in journal, "le travail lui-meme doit avoir tourne"
    assert "VIVANTE" in journal, journal


def test_gpu_entity_sans_holder_est_une_erreur_usage(guarded, tmp_path):
    """--gpu-entity incomplet (pas de holder/workload) = erreur d'usage argparse."""
    with pytest.raises(SystemExit) as excinfo:
        guarded.main([
            "--limit-gib", "8", "--gpu-entity", "myia-ai-01#gpu2",
            "--log", str(tmp_path / "usage.log"),
            "--", sys.executable, "-c", TRIVIAL_CHILD])
    assert excinfo.value.code == 2, "ap.error doit sortir avec le code d'usage argparse"


# --- publication de la reservation (#22456) ---------------------------------
#
# Le gate lit l'etat PUBLIE (branche `ops/gpu-ledger`). Une observation restee
# dans le spool local rend `UNPOSTED`, qui BLOQUE le lancement suivant -- y
# compris celui de la machine qui vient de reserver. Ces tests mesurent le
# maillon de publication : present, il bloque sur echec de publication.


def _faux_organ_publish(calls, *, gate_verdict="NO_OBS", fail_publish=False):
    """Faux organe qui repond a `publish` (succes par defaut, refus simule)."""
    def faux_organ(args, timeout=120):
        calls.append(list(args))
        if args[0] == "check_pending":
            payload = {"verdict": gate_verdict, "reason": "faux organ",
                       "entity": "myia-ai-01#gpu2"}
            return 0, json.dumps(payload), ""
        if args[0] == "append":
            fields = json.loads(args[args.index("--fields-json") + 1])
            return 0, "[OBS] " + json.dumps(
                {"observation_id": f"obs-faux-{fields.get('state')}"}), ""
        if args[0] == "publish":
            if fail_publish:
                return 3, "", "ERROR FAUX: push refuse (concurrence)"
            return 0, "PUBLISHED 1 observation(s) -> origin/ops/gpu-ledger", ""
        return 0, "", ""
    return faux_organ


def test_gpu_reservation_est_publiee_avant_le_lancement(guarded, tmp_path, monkeypatch):
    """Le held est PUBLIE sur la branche avant que l'enfant ne tourne : la
    flotte voit la reservation pendant le job, pas apres."""
    calls = []
    monkeypatch.setattr(guarded, "_run_ledger_organ", _faux_organ_publish(calls))
    log = tmp_path / "gpu_publish.log"
    rc = guarded.main(
        _gpu_argv(log) + ["--", sys.executable, "-c", TRIVIAL_CHILD])
    journal = log.read_text(encoding="utf-8")
    assert rc == 0, f"rc {rc} attendu (0), journal :\n{journal}"
    assert "TRIVIAL_OK" in journal
    publishes = [c for c in calls if c[0] == "publish"]
    assert len(publishes) == 2, f"un publish par observation (held, released) : {calls}"
    assert "--emit" in publishes[0]
    assert "--machine" in publishes[0]
    assert "myia-ai-01" in publishes[0]
    assert "PUBLIE" in journal, journal


def test_gpu_publication_refusee_empêche_le_lancement(guarded, tmp_path, monkeypatch):
    """Une reservation non PUBLIEE = invisible de la flotte : fail-CLOSED, le
    travail ne demarre pas (le held reste ecrit localement, et le journal dit
    comment publier)."""
    calls = []
    monkeypatch.setattr(
        guarded, "_run_ledger_organ", _faux_organ_publish(calls, fail_publish=True))
    log = tmp_path / "gpu_publish_fail.log"
    rc = guarded.main(_gpu_argv(log) + ["--", sys.executable, "-c", TRIVIAL_CHILD])
    journal = log.read_text(encoding="utf-8")
    assert rc == 5, f"rc {rc} attendu (5 = refus), journal :\n{journal}"
    assert "TRIVIAL_OK" not in journal, "l'enfant ne doit pas avoir demarre"
    assert "PUBLIEE" in journal or "PUBLIE" in journal, journal
    assert "publish --git" in journal, journal
