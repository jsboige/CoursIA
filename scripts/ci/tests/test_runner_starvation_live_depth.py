"""Profondeur VIVANTE de la file annoncee par la sonde de starvation (#26719).

Deux instruments lisent la MEME file et rendaient deux mesures : la sonde
compte les runs `queued` de SA fenetre d'examen, `scripts/ci/gh_queue_health.py
--live-depth` rend la population queued MOINS les classes de fantomes mesurees
(pre-cutoff, pr-closed, scheduled-orphan, no-job). Le coordinateur a tranche :
le second chiffre est celui de reference, et le premier ne doit plus etre lu
seul.

Ce fichier verrouille les quatre proprietes qui en decoulent :

  - la note annonce la profondeur VIVANTE, et quand elle diverge du nombre de
    runs vus par la sonde, les DEUX chiffres sont nommes avec l'ecart ;
  - une profondeur NON MESUREE est une WARNING, jamais une erreur : le
    predicat STARVATION reste une affirmation de niveau JOB ;
  - le cutoff de la mesure reste egal au defaut du CLI de l'organe voisin --
    deux cutoffs feraient porter les deux chiffres sur deux populations ;
  - le predicat STARVATION est INCHANGE par la profondeur vivante, y compris
    quand elle vaut 0 (une file vide ne requalifie pas des jobs affames).

Aucun test n'atteint l'API : le voisin est remplace dans `sys.modules`, et la
sonde est pilotee par des `Starvation` construites a la main.
"""

from __future__ import annotations

import builtins
import importlib.util
import json
import re
import sys
import types
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_runner_starvation.py"
_spec = importlib.util.spec_from_file_location("check_runner_starvation", SCRIPT)
mod = importlib.util.module_from_spec(_spec)
# `@dataclass` resout ses annotations via sys.modules[cls.__module__] : le
# module doit etre enregistre AVANT exec_module.
sys.modules[_spec.name] = mod
_spec.loader.exec_module(mod)

NEIGHBOUR = Path(__file__).resolve().parents[1] / "gh_queue_health.py"


def _inventory() -> mod.RunnerInventory:
    """Deux slots online : l'inventaire ne doit pas bruiter le verdict."""
    return mod.RunnerInventory(online=["r1", "r2"])


def _job(age_min: float = 35.0, number: int = 1) -> mod.JobRow:
    return mod.JobRow(workflow="Guard A", run_number=number, run_id=1000 + number,
                      job_name="guard", status="queued", age_min=age_min)


# --- 1. La note annonce la profondeur VIVANTE et nomme l'ecart --------------

def test_la_note_annonce_la_profondeur_vivante_et_nomme_l_ecart():
    st = mod.Starvation(queued_runs_seen=12)
    v = mod.evaluate(_inventory(), st, warn_floor=2, live_depth=5)

    note = next(n for n in v.notes if n.startswith("profondeur VIVANTE"))
    assert "5 run(s)" in note
    assert "scripts/ci/gh_queue_health.py --live-depth" in note

    ecart = next(n for n in v.notes
                 if n.startswith("profondeur de file divergente"))
    assert "12 run(s)" in ecart and "5 run(s)" in ecart
    assert "+7" in ecart, "l'ecart doit etre chiffre, pas seulement raconte"
    assert "fantomes" in ecart, "la classe qui explique l'ecart est nommee"
    assert v.errors == [], v.errors
    assert v.status == "OK"


def test_sans_divergence_aucune_note_d_ecart():
    st = mod.Starvation(queued_runs_seen=5)
    v = mod.evaluate(_inventory(), st, warn_floor=2, live_depth=5)
    assert any(n.startswith("profondeur VIVANTE") for n in v.notes)
    assert not any(n.startswith("profondeur de file divergente")
                   for n in v.notes), v.notes


# --- 2. Une mesure impossible est une WARNING, jamais une erreur ------------

def test_profondeur_non_mesuree_est_une_warning_sans_erreur():
    v = mod.evaluate(_inventory(), mod.Starvation(), warn_floor=2,
                     live_depth=None, live_depth_error="RuntimeError: API muette")
    assert v.errors == [], v.errors
    assert v.status == "OK"
    assert any(w.startswith("PROFONDEUR VIVANTE non mesuree")
               for w in v.warnings), v.warnings
    assert any("RuntimeError: API muette" in w for w in v.warnings), v.warnings


def test_un_appelant_historique_sans_mesure_ne_recoit_pas_de_bruit():
    """Pas de tentative = pas d'affirmation sur la profondeur.

    Les appelants existants (tests, controleur) n'ont jamais mesure cette
    profondeur : leur ajouter une WARNING a chaque passage ferait du bruit
    permanent et casserait leurs verdicts attendus. Seule une mesure TENTEE
    qui echoue se dit.
    """
    v = mod.evaluate(_inventory(), mod.Starvation(), warn_floor=2)
    assert not any("PROFONDEUR VIVANTE" in w for w in v.warnings), v.warnings


# --- 3. Non-regression du cutoff face au CLI de l'organe voisin -------------

def test_le_cutoff_reste_egal_au_defaut_du_cli_de_l_organe_voisin():
    """`LIVE_DEPTH_CUTOFF` et le defaut `--cutoff` du voisin sont UNE valeur.

    La note annonce la meme mesure que `--live-depth` : deux cutoffs
    differents feraient porter les deux chiffres sur deux populations
    differentes, et la comparaison serait fausse sans que rien ne le dise.
    """
    source = NEIGHBOUR.read_text(encoding="utf-8")
    found = re.search(
        r'add_argument\(\s*"--cutoff"\s*,\s*default\s*='
        r'\s*"([0-9]{4}-[0-9]{2}-[0-9]{2})"',
        source)
    assert found, ("le defaut du CLI --cutoff n'a pas ete trouve dans "
                   f"{NEIGHBOUR} -- la garde de non-regression est aveugle")
    assert found.group(1) == mod.LIVE_DEPTH_CUTOFF, (
        f"LIVE_DEPTH_CUTOFF={mod.LIVE_DEPTH_CUTOFF!r} diverge du defaut du "
        f"CLI ({found.group(1)!r}) : les deux chiffres ne porteraient plus "
        f"sur la meme population")


# --- 4. Le predicat STARVATION est inchange --------------------------------

def test_le_predicat_starvation_est_inchange_a_une_profondeur_vivante_nulle():
    """Une file VIVANTE vide ne requalifie pas des jobs affames.

    La starvation est une affirmation de niveau JOB : un job libelle queued
    depuis plus du seuil sans aucun job in_progress reste un ROUGE, que la
    profondeur vivante soit 0 ou 400. Ce test est le temoin que la nouvelle
    note n'a pas glisse dans le predicat.
    """
    st = mod.Starvation(starved=[_job(35.0)], in_progress=[],
                        queued_runs_seen=1)
    v = mod.evaluate(_inventory(), st, warn_floor=2, live_depth=0)
    assert any(e.startswith("STARVATION") for e in v.errors), v.errors
    assert v.status == "ERROR"
    assert any(n.startswith("profondeur VIVANTE de la file: 0 run(s)")
               for n in v.notes), v.notes


# --- 5. Le contrat de `_live_queue_depth` (voisin simule, zero reseau) -----

def _fake_neighbour(monkeypatch, report=None, error=None) -> dict:
    """Installe un `gh_queue_health` simule et retient ses arguments."""
    calls: dict = {}
    fake = types.SimpleNamespace()
    fake.NO_JOB_EVENTS = frozenset({"issue_comment"})
    fake.DEFAULT_NO_JOB_MIN_AGE_HOURS = 24.0

    def parse_date(value: str):
        calls["cutoff_raw"] = value
        return f"parsed:{value}"

    def live_depth_report(**kwargs):
        calls.update(kwargs)
        if error is not None:
            raise error
        return report

    def measure_queue_depth(**kwargs):
        calls.update(kwargs)
        if error is not None:
            raise error
        return report

    def api_call_count() -> int:
        return 7

    fake.parse_date = parse_date
    fake.live_depth_report = live_depth_report
    fake.measure_queue_depth = measure_queue_depth
    fake.api_call_count = api_call_count
    monkeypatch.setitem(sys.modules, "gh_queue_health", fake)
    return calls


def test_live_queue_depth_transmet_les_parametres_de_la_commande_unique(
        monkeypatch):
    calls = _fake_neighbour(monkeypatch,
                            report={"live_depth": 7, "parse_failures": 0,
                                    "depth_kind": "live", "depth": 7})
    depth, bound, reason, api_calls = mod._live_queue_depth("jsboige/CoursIA")
    assert (depth, bound, reason) == (7, None, "")
    assert api_calls == 7
    assert calls["repo"] == "jsboige/CoursIA"
    assert calls["cutoff_date"] == mod.LIVE_DEPTH_CUTOFF
    assert calls["cutoff"] == f"parsed:{mod.LIVE_DEPTH_CUTOFF}"
    assert calls["no_job_events"] == frozenset({"issue_comment"})
    assert calls["no_job_min_age_hours"] == 24.0
    assert calls["max_workers"] == 8
    # #26739 -- la mesure porte le seuil de saturation : c'est lui qui
    # permet a l'organe voisin de NE PAS payer la mesure complete quand le
    # brut est sous le seuil.
    assert calls["saturation_threshold"] == mod.LIVE_DEPTH_SATURATION_THRESHOLD
    assert calls["now"].utcoffset().total_seconds() == 0, \
        "l'instant de mesure doit etre UTC"


def test_live_queue_depth_rend_un_majorant_quand_la_mesure_n_est_pas_payee(
        monkeypatch):
    """#26739 -- quand l'organe voisin epargne la mesure, il rend un
    MAJORANT de la profondeur vivante, pas une profondeur."""
    calls = _fake_neighbour(
        monkeypatch,
        report={"live_depth": None, "depth": 470, "depth_kind": "raw-upper-bound",
                "parse_failures": 0})
    depth, bound, reason, api_calls = mod._live_queue_depth("jsboige/CoursIA")
    assert depth is None
    assert bound == 470
    assert reason == ""
    assert api_calls == 7
    assert calls["saturation_threshold"] == mod.LIVE_DEPTH_SATURATION_THRESHOLD


def test_live_queue_depth_est_fail_closed_sur_un_instrument_incomplet(
        monkeypatch):
    _fake_neighbour(monkeypatch,
                    report={"live_depth": 3, "parse_failures": 2})
    depth, bound, reason, _calls = mod._live_queue_depth("jsboige/CoursIA")
    assert depth is None, "une profondeur sur une population trouee ne se publie pas"
    assert bound is None
    assert reason.startswith("instrument incomplet:")
    assert "2" in reason


def test_live_queue_depth_absorbe_une_exception_de_l_api(monkeypatch):
    _fake_neighbour(monkeypatch, error=RuntimeError("API muette"))
    depth, bound, reason, _calls = mod._live_queue_depth("jsboige/CoursIA")
    assert depth is None
    assert bound is None
    assert reason == "RuntimeError: API muette"


def test_live_queue_depth_survit_a_un_organe_voisin_absent(monkeypatch):
    """L'organe ne doit JAMAIS planter parce que son voisin manque."""
    real_import = builtins.__import__

    def import_sans_voisin(name, *args, **kwargs):
        if name == "gh_queue_health":
            raise ImportError("organe voisin absent (test)")
        return real_import(name, *args, **kwargs)

    monkeypatch.delitem(sys.modules, "gh_queue_health", raising=False)
    monkeypatch.setattr(builtins, "__import__", import_sans_voisin)
    depth, bound, reason, _calls = mod._live_queue_depth("jsboige/CoursIA")
    assert depth is None
    assert bound is None
    assert reason == "ImportError: organe voisin absent (test)"


# --- 6. Le cablage de `main()` ---------------------------------------------

def _starved_and_running(seen: int = 9) -> mod.Starvation:
    """Une file ou un job AFFAME est detecte ET un job tourne : le verdict
    reste OK, mais la note de profondeur a lieu d'etre lue (#26739 : la
    mesure n'est payee que dans ce cas)."""
    return mod.Starvation(
        queued_runs_seen=seen,
        stats=mod.CallStats(calls=1),
        starved=[_job(35.0)],
        in_progress=[mod.JobRow(workflow="Guard A", run_number=2, run_id=1002,
                                job_name="guard", status="in_progress",
                                age_min=1.0)])


def test_main_passe_la_profondeur_vivante_et_nomme_l_ecart(monkeypatch,
                                                           capsys):
    """Le câblage bout en bout : `main()` calcule, `evaluate()` annonce."""
    st = _starved_and_running(9)
    monkeypatch.setattr(mod, "fetch_scheduled_runs", lambda *a, **k: [])
    monkeypatch.setattr(mod, "fetch_inventory",
                        lambda *a, **k: mod.RunnerInventory(online=["r1", "r2"]))
    monkeypatch.setattr(mod, "fetch_starvation", lambda *a, **k: st)
    monkeypatch.setattr(mod, "_live_queue_depth",
                        lambda repo: (4, None, "", 3))
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--json", "--mirror-off",
        "--declared-hosts", "",
    ])

    assert mod.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["live_depth"] == 4
    assert payload["live_depth_upper_bound"] is None
    assert payload["live_depth_api_calls"] == 3
    assert payload["queued_runs_seen"] == 9
    notes = payload["notes"]
    assert any(n.startswith("profondeur VIVANTE de la file: 4 run(s)")
               for n in notes), notes
    ecart = next(n for n in notes
                 if n.startswith("profondeur de file divergente"))
    assert "9 run(s)" in ecart and "4 run(s)" in ecart and "+5" in ecart
    # #26739 -- le cout du passage est nomme (quota horaire partage).
    assert any(n.startswith("api-quota:") for n in notes), notes


def test_main_ne_paie_pas_la_mesure_sans_job_affame(monkeypatch, capsys):
    """#26739 -- sans job affame, la note de profondeur n'apporte rien au
    verdict : la mesure n'est PAS payee (114 appels par passage)."""
    st = mod.Starvation(queued_runs_seen=9, stats=mod.CallStats(calls=1))
    monkeypatch.setattr(mod, "fetch_scheduled_runs", lambda *a, **k: [])
    monkeypatch.setattr(mod, "fetch_inventory",
                        lambda *a, **k: mod.RunnerInventory(online=["r1", "r2"]))
    monkeypatch.setattr(mod, "fetch_starvation", lambda *a, **k: st)

    def interdit(repo):
        raise AssertionError(
            "aucune mesure de profondeur sans job affame detecte")

    monkeypatch.setattr(mod, "_live_queue_depth", interdit)
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--json", "--mirror-off",
        "--declared-hosts", "",
    ])

    assert mod.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["live_depth"] is None
    assert payload["live_depth_upper_bound"] is None
    assert not any("PROFONDEUR VIVANTE" in w for w in payload["warnings"])


def test_main_annonce_le_majorant_quand_la_mesure_n_est_pas_payee(
        monkeypatch, capsys):
    """#26739 -- quand l'organe voisin epargne la mesure, la note annonce un
    MAJORANT et n'affirme AUCUN ecart (la profondeur n'est pas mesuree)."""
    st = _starved_and_running(9)
    monkeypatch.setattr(mod, "fetch_scheduled_runs", lambda *a, **k: [])
    monkeypatch.setattr(mod, "fetch_inventory",
                        lambda *a, **k: mod.RunnerInventory(online=["r1", "r2"]))
    monkeypatch.setattr(mod, "fetch_starvation", lambda *a, **k: st)
    monkeypatch.setattr(mod, "_live_queue_depth",
                        lambda repo: (None, 470, "", 1))
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--json", "--mirror-off",
        "--declared-hosts", "",
    ])

    assert mod.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["live_depth"] is None
    assert payload["live_depth_upper_bound"] == 470
    notes = payload["notes"]
    assert any("profondeur VIVANTE NON MESUREE: au plus 470" in n
               for n in notes), notes
    assert not any(n.startswith("profondeur de file divergente")
                   for n in notes), notes


def test_main_ne_paie_pas_la_mesure_quand_la_sonde_n_a_rien_lu(monkeypatch,
                                                                capsys):
    """Une sonde qui n'a fait AUCUN appel n'a rien mesure.

    C'est ce qui garde la suite existante hermetique : plusieurs tests
    injectent un `Starvation()` et ne patchent pas le voisin. Payer une
    seconde lecture de la file sur une mesure injectee n'aurait aucun sens
    (le chiffre n'aurait pas de provenance) et appellerait l'API depuis un
    test.
    """
    monkeypatch.setattr(mod, "fetch_scheduled_runs", lambda *a, **k: [])
    monkeypatch.setattr(mod, "fetch_inventory",
                        lambda *a, **k: mod.RunnerInventory(online=["r1", "r2"]))
    monkeypatch.setattr(mod, "fetch_starvation",
                        lambda *a, **k: mod.Starvation())

    def interdit(repo):
        raise AssertionError(
            "aucune lecture de profondeur sans lecture effective de la file")

    monkeypatch.setattr(mod, "_live_queue_depth", interdit)
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--json", "--mirror-off",
        "--declared-hosts", "",
    ])

    assert mod.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["live_depth"] is None
    assert not any("PROFONDEUR VIVANTE" in w for w in payload["warnings"])