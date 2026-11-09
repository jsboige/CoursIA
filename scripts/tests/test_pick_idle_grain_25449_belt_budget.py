"""Tests du correctif #25449 : le mur de temps de la BOUCLE, arme a son entree.

Le defaut (issue #25449) : le budget du `--belt` etait arme AVANT le
chargement du pool, et mesure depuis le debut du RUN. Le chargement du
pool (258-648 s mesures sur ai-01, #22500) le consumait entierement, et la
boucle entrait avec 0 s : le fail-CLOSED ecartait alors TOUS les candidats
comme si un filtre l'avait decide. Run B de l'issue : budget 600 s, boucle
entree a 511 s restantes -- meme issue. Le mur n'etait donc pas la cause
des retraits, il etait la cause de la famine.

Ce que ces tests epinglent :

1. un pool LENT ne vide plus la boucle -- le budget de boucle s'arme a
   l'entree de la boucle, il n'est plus deduit du temps d'amont ;
2. un pool qui depasse son PROPRE plafond echoue vite, en nommant la
   phase qui a consomme le budget (fail-CLOSED) ;
3. l'attribution du depassement est MESUREE : la phase qui a consomme le
   budget est designee, pas devinee.

Fichier separe de `test_pick_idle_grain_belt.py` et
`test_pick_idle_grain.py` deliberement (convention du depot : les helpers
sont dupliques plutot que partages, pour qu'une PR avance sans rebase
croise).
"""

import json
import re
import sys
import time as _real_time
import types
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402

LANE = "myia-ai-01:CoursIA-2"


class _RealGhReached(BaseException):
    """Un test a atteint un `gh` reel.

    Derive de `BaseException` : le picker attrape large (`except Exception`)
    sur ses chemins de fetch, un garde qui deriverait d'`Exception` serait
    avale -- exactement le silence qu'il doit casser.
    """


@pytest.fixture(autouse=True)
def _no_real_gh(monkeypatch, request):
    """#19913 : aucun test de ce fichier n'emet un appel `gh` reel.

    Le garde coupe au SEUL point de passage commun (`subprocess.run` avec
    `gh` dans l'argv) : il leve en millisecondes, bruyamment, avec la
    ligne fautive.
    """
    if request.node.get_closest_marker("real_gh"):
        return
    real_run = pig.subprocess.run

    def guarded_run(argv, *args, **kwargs):
        cmd = argv if isinstance(argv, (list, tuple)) else [argv]
        joined = " ".join(str(part) for part in cmd)
        if re.search(r"(^|[\\/ ])gh(\.exe)?($|\s)", joined):
            raise _RealGhReached(
                "appel gh reel depuis un test : " + joined[:160])
        return real_run(argv, *args, **kwargs)

    monkeypatch.setattr(pig.subprocess, "run", guarded_run)


@pytest.fixture(autouse=True)
def _reset_belt_state(monkeypatch):
    """Le state du mur est GLOBAL au module : chaque test repart de zero.

    Sans ce reset, l'etat d'un test (echeance armee, phase horodatee) fuite
    dans le suivant -- et un test qui passe pour une mauvaise raison (une
    echeance restee armee) est un test qui ne prouve rien.
    """
    monkeypatch.setattr(pig, "_BELT_DEADLINE", [None])
    monkeypatch.setattr(pig, "_BELT_LOOP_BUDGET", [None])
    monkeypatch.setattr(pig, "_BELT_PHASE_LABEL",
                        ["preparation du tapis (export, reparation, pool)"])
    monkeypatch.setattr(pig, "_BELT_PHASE_SPAN_START", [None])
    monkeypatch.setattr(pig, "_BELT_PHASE_SPAN_TOTAL", [0.0])
    monkeypatch.setattr(pig, "_BELT_POOL_SPAN", [None])


def _fake_clock(monkeypatch, start=0.0):
    """Horloge injectee a la place du module `time` de `pig`.

    L'ATTRIBUT de module est remplace (pas `time.monotonic` globalement) :
    le patch reste local, et `time.time()` continue de fonctionner pour le
    code qui l'utilise (caches a TTL, stamps de livraison).
    """
    clock = [start]
    fake = types.SimpleNamespace(
        monotonic=lambda: clock[0],
        time=_real_time.time,
        perf_counter=_real_time.perf_counter,
        sleep=_real_time.sleep,
    )
    monkeypatch.setattr(pig, "time", fake)
    return clock


def _patch_network(monkeypatch):
    """Neutralise les surfaces reseau de `main --belt` (cf. #19913).

    Copie locale du helper de `test_pick_idle_grain_belt.py` : le depot
    duplique les helpers plutot que de les partager, pour qu'une PR avance
    sans rebase croise.
    """
    monkeypatch.setattr(pig, "fetch_open_prs", list)
    monkeypatch.setattr(pig, "fetch_pool", lambda **k: ([], None))
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {})
    monkeypatch.setattr(pig, "unaddressed_review_points_detail",
                        lambda nums: {})
    monkeypatch.setattr(pig, "fetch_lane_record_prs", lambda **k: ([], None))
    monkeypatch.setattr(pig, "_complete_open_prs", list)
    monkeypatch.setattr(pig, "fetch_main_head_probe", lambda *a, **k: None)
    monkeypatch.setattr(pig, "check_claims",
                        lambda nums, lane, **kwargs: {
                            n: (pig.CLAIM_CODE_FREE, "libre") for n in nums})
    monkeypatch.setattr(pig, "latest_claim_stamp", lambda n: None)
    monkeypatch.setattr(pig, "fetch_visits", lambda *a, **k: ({}, None))
    monkeypatch.setattr(pig, "fetch_series_visits",
                        lambda **k: ({}, {}, None))
    monkeypatch.setattr(pig, "fetch_merged", lambda *a, **k: ([], None))
    monkeypatch.setattr(pig, "fetch_closed_issues", lambda *a, **k: ([], None))
    monkeypatch.setattr(pig.gh_identity, "pin_gh_token", lambda *a, **k: None)
    monkeypatch.setattr(pig, "_belt_snapshot_prime",
                        lambda repo, numbers: None)


class _Args:
    """Args minimaux pour `_belt_loop_entry`."""

    def __init__(self, belt_time_budget):
        self.belt_time_budget = belt_time_budget
        self.lane = LANE
        self.json = False


# ==================================================================
# 1. Un pool lent ne vide plus la boucle
# ==================================================================


def test_slow_pool_does_not_empty_the_loop_budget(monkeypatch, capsys):
    """Un pool lent ne vide plus la boucle : le mur s'arme a son entree.

    Le pool met 300 s a etre charge (mesure : 258-648 s sur ai-01, #22500)
    et le budget de boucle est de 240 s. AVANT le correctif, la boucle
    entrait avec 0 s et le fail-CLOSED ecartait tous ses candidats comme
    si un filtre l'avait decide. APRES, la boucle entre avec son budget
    entier, et le plafond PROPRE du pool reste la seule borne de l'amont.
    """
    clock = _fake_clock(monkeypatch)
    _patch_network(monkeypatch)

    def slow_pool(**kwargs):
        clock[0] += 300.0
        return [], None

    monkeypatch.setattr(pig, "fetch_pool", slow_pool)

    rc = pig.main(["--lane", LANE, "--belt", "--json",
                   "--belt-time-budget", "240"])

    assert rc == 0, "un pool lent ne doit pas faire echouer le run"
    captured = capsys.readouterr()
    # Le mur de boucle est arme a l'entree de la boucle : le temps d'amont
    # ne l'a pas consomme.
    assert "240s pour la boucle, arme a son entree" in captured.err
    assert "restants a son entree" not in captured.err
    # Et le plafond du pool reste une borne distincte, nommee.
    assert "plafond (pool : 900s" in captured.err
    payload = json.loads(captured.out)
    assert payload["mode"] == "belt"
    assert payload["belt_loop_budget_s"] == 240.0
    assert "error" not in payload


def test_loop_budget_is_the_requested_budget_not_the_remainder(monkeypatch):
    """Le budget de boucle est celui demande, meme apres une phase d'amont.

    Controle du calcul, sans passer par `main` : c'est le coeur du
    correctif -- avant, la valeur rendue etait `budget - temps_ecoule`,
    donc 0 s des que le pool avait pris plus que le budget.
    """
    clock = _fake_clock(monkeypatch)
    t0 = pig._arm_belt_run_clock(240.0)
    clock[0] += 300.0  # le pool a pris 300 s

    budget, overrun = pig._belt_loop_entry(_Args(240.0), t0, clock[0])

    assert budget == 240.0
    assert overrun is None, "300 s < plafond du pool : aucun echec"


def test_no_budget_means_no_wall(monkeypatch):
    """Controle positif : sans budget (`0`), aucun mur n'est arme.

    `0 desactive le mur` : boucle ET plafond d'amont. Le comportement
    d'avant est preserve.

    #25449 correctif 2 -- le test doit faire AVANCER l'horloge au-dela du
    plafond. Sans cela, le predicat rendait `None` parce que le temps
    n'avait pas bouge, pas parce que le mur etait desarme : le controle
    positif donnait l'assurance sans la preuve (relit par Hermes sur la tete
    `659641f`, qui mesure la regression : base rc 0, tete rc 3).
    """
    clock = _fake_clock(monkeypatch)
    t0 = pig._arm_belt_run_clock(0.0)
    assert pig._BELT_DEADLINE[0] is None

    # Au-dela du plafond de l'amont (900 s par defaut) : si le mur restait
    # arme, le depassement serait nomme ici.
    clock[0] += pig._belt_pool_ceiling() + 1

    budget, overrun = pig._belt_loop_entry(_Args(0.0), t0, clock[0])
    assert budget is None
    assert overrun is None, "sans budget, le plafond d'amont est desarme"


def test_no_budget_disarms_the_upstream_ceiling_on_the_real_path(
        monkeypatch, capsys):
    """Meme contrat, par le chemin reel (`main`) : un run sans budget ne
    doit pas s'arreter en 3 apres le chargement du pool.

    C'est la regression mesuree par Hermes contre la base (`main --belt
    --json --belt-time-budget 0`, pool injecte a 1000 s : base rc 0, tete
    rc 3). Le test passe par `main`, donc il mesure le chemin de
    production, pas une fonction isolee.
    """
    clock = _fake_clock(monkeypatch)
    _patch_network(monkeypatch)

    def very_slow_pool(**kwargs):
        clock[0] += 1000.0
        return [], None

    monkeypatch.setattr(pig, "fetch_pool", very_slow_pool)

    rc = pig.main(["--lane", LANE, "--belt", "--json",
                   "--belt-time-budget", "0"])

    assert rc != 3, "sans budget, l'echec rapide du plafond ne doit pas fires"
    payload = json.loads(capsys.readouterr().out)
    assert "error" not in payload, "aucun echec rapide sans budget"


def test_the_measured_repair_span_does_not_survive_a_run(monkeypatch):
    """La duree horodatee de la reparation est un etat DU RUN.

    Dans un meme process, le cumul du run precedent etait retranche du run
    suivant : l'attribution « mesuree, pas devinee » pouvait designer une
    phase qui n'avait pas tourne (relit par Hermes sur la tete `659641f`).
    """
    clock = _fake_clock(monkeypatch)
    t0 = pig._arm_belt_run_clock(240.0)
    token = pig._publish_phase_deadline(300.0)
    clock[0] += 1000.0
    pig._restore_phase_deadline(token)
    assert pig._BELT_PHASE_SPAN_TOTAL[0] == 1000.0

    # Run suivant dans le meme process : l'etat du run precedent ne suit pas.
    pig._arm_belt_run_clock(240.0)
    assert pig._BELT_PHASE_SPAN_TOTAL[0] == 0.0

    clock[0] += 1000.0
    overrun = pig._belt_pool_overrun(pig.time.monotonic() - 1000.0, clock[0])
    assert overrun is not None
    assert overrun["repair_s"] == 0.0, "la reparation du run precedent ne compte pas"


# ==================================================================
# 2. Un pool qui depasse son plafond echoue vite, en nommant la phase
# ==================================================================


def test_pool_over_its_ceiling_fails_fast_naming_the_phase(monkeypatch,
                                                            capsys):
    """Un pool qui depasse son plafond echoue vite, en nommant la phase.

    Fail-CLOSED : le run s'arrete, la boucle n'entre pas. Les candidats
    ne sont pas « ecartes par un filtre » : ils ne sont pas servis, et le
    dit. Le message nomme la phase qui a consomme le budget.
    """
    clock = _fake_clock(monkeypatch)
    _patch_network(monkeypatch)

    def very_slow_pool(**kwargs):
        clock[0] += 1000.0
        return [], None

    monkeypatch.setattr(pig, "fetch_pool", very_slow_pool)

    rc = pig.main(["--lane", LANE, "--belt", "--json",
                   "--belt-time-budget", "240"])

    assert rc == 3, "le depassement du plafond doit etre un echec nomme"
    captured = capsys.readouterr()
    assert "chargement du pool" in captured.err
    assert "plafond" in captured.err
    payload = json.loads(captured.out)
    assert payload["mode"] == "belt"
    assert payload["error"]["phase"] == "chargement du pool"
    assert payload["error"]["ceiling_s"] == 900.0
    # La boucle n'est pas entree : rien n'a ete servi, rien n'a ete ecarte.
    assert payload["picks"] == []
    assert payload["withheld"] == []


def test_overrun_reports_the_measured_phase_and_ceiling(monkeypatch):
    """La preuve du depassement porte la phase, les secondes et le plafond.

    Sans ces trois nombres, l'echec serait un « le run a echoue » opaque :
    on ne saurait pas quelle phase ralentir, ni a quel point.
    """
    clock = _fake_clock(monkeypatch)
    t0 = pig._arm_belt_run_clock(240.0)
    clock[0] += 1000.0

    overrun = pig._belt_pool_overrun(t0, clock[0])

    assert overrun is not None
    assert overrun["phase"] == "chargement du pool"
    assert overrun["elapsed_s"] == 1000.0
    assert overrun["ceiling_s"] == 900.0
    assert "chargement du pool" in overrun["message"]


def test_overrun_attributes_the_repair_phase_when_it_is_the_consumer(
        monkeypatch):
    """L'attribution est MESUREE : si c'est la reparation qui a consomme,
    c'est elle qui est nommee -- pas le pool par defaut.
    """
    clock = _fake_clock(monkeypatch)
    t0 = pig._arm_belt_run_clock(240.0)
    token = pig._publish_phase_deadline(300.0)
    clock[0] += 1000.0
    pig._restore_phase_deadline(token)

    overrun = pig._belt_pool_overrun(t0, clock[0])

    assert overrun is not None
    assert overrun["phase"] == "reparation (file red_backlog)"
    assert overrun["repair_s"] == 1000.0


def test_the_named_phase_is_the_measured_consumer_not_the_pool_by_default(
        monkeypatch):
    """La phase nommee est le consommateur MESURE, pas « le pool » par defaut.

    #25449 correctif 4 -- le reliquat du budget (apres reparation) couvre
    l'export du tableau, l'ardoise de lane ET le pool. Nommer « chargement
    du pool » par defaut pouvait envoyer une lane optimiser le pool alors que
    le temps etait parti ailleurs (relit par Hermes sur la tete `659641f`).

    Ici : 1000 s ecoulees, dont 100 s de pool mesurees -> le consommateur
    mesure est l'export + l'ardoise (900 s), pas le pool.
    """
    clock = _fake_clock(monkeypatch)
    t0 = pig._arm_belt_run_clock(240.0)
    pig._BELT_POOL_SPAN[0] = 100.0
    clock[0] += 1000.0

    overrun = pig._belt_pool_overrun(t0, clock[0])

    assert overrun is not None
    assert overrun["phase"] == "preparation du tapis (export, ardoise)"
    assert overrun["phase_s"] == 900.0


def test_the_pool_is_named_when_it_is_the_measured_consumer(monkeypatch):
    """Controle inverse : quand le pool est le plus gros consommateur mesure,
    c'est lui qui est nomme -- et avec SES secondes, pas avec le reliquat.
    """
    clock = _fake_clock(monkeypatch)
    t0 = pig._arm_belt_run_clock(240.0)
    pig._BELT_POOL_SPAN[0] = 800.0
    clock[0] += 1000.0

    overrun = pig._belt_pool_overrun(t0, clock[0])

    assert overrun is not None
    assert overrun["phase"] == "chargement du pool"
    assert overrun["phase_s"] == 800.0


def test_pool_ceiling_is_read_at_call_time(monkeypatch):
    """Le plafond est lu a chaque appel : un siege lent l'elargit sans patch.

    `PICK_BELT_POOL_CEILING_S` prime sur la constante ; une valeur invalide
    retombe sur la constante (jamais sur « pas de plafond »).
    """
    monkeypatch.setenv("PICK_BELT_POOL_CEILING_S", "1200")
    assert pig._belt_pool_ceiling() == 1200.0
    monkeypatch.setenv("PICK_BELT_POOL_CEILING_S", "pas-un-nombre")
    assert pig._belt_pool_ceiling() == pig.BELT_POOL_CEILING_S
    monkeypatch.delenv("PICK_BELT_POOL_CEILING_S")
    assert pig._belt_pool_ceiling() == pig.BELT_POOL_CEILING_S
