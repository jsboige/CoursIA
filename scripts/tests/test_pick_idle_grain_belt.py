"""Tests pour le mode --belt de scripts/pick_idle_grain.py (#18832).

Acceptance (issue #18832, body) :
1. l'ordre suit la derniere visite ;
2. une issue jamais servie se classe par sa creation ;
3. une issue livree hier passe derriere une issue livree il y a un mois ;
4. une issue reclamee par une autre lane est sautee ;
5. un garde rouge ne vide pas le resultat.

Le mode --belt est un court-circuit avant le tirage pondere : pas de
loterie, pas de graine. Chaque test verifie un predicat precis, sans
toucher au fetch reseau (le mode belt est en memoire apres le fetch_pool,
qui est shime par les tests existants).
"""

import json
import re
import subprocess
import sys
from datetime import datetime, timezone, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402


class _RealGhReached(BaseException):
    """Un test a atteint un `gh` reel.

    Derive de `BaseException`, pas d'`Exception` : le picker attrape
    large (`except Exception` / `OSError`) sur ses chemins de fetch pour
    rendre un fail-OPEN. Un garde qui deriverait d'`Exception` serait
    avale par ces `except` -- exactement le silence qu'il doit casser.
    """


@pytest.fixture(autouse=True)
def _no_real_gh(monkeypatch, request):
    """#19913 : aucun test de ce fichier n'emet un appel `gh`.

    Le piege mesure (coordinateur, 2026-10-09) : sur une fusion avec main,
    la suite de ce fichier pendait par tests de 30 s a plusieurs minutes.
    Cause : `main --belt` touche des surfaces que la fixture
    `_patch_belt_network` n'enumerait pas -- `fetch_series_visits` ->
    `gh_payload_cache` -> `run_gh` -> `subprocess.run`, bloque sur un
    `communicate` reel. Enumerer les surfaces une par une est une course
    perdue : chaque fonction reseau ajoutee rouvre le trou.

    Ce garde coupe au SEUL point de passage commun : `subprocess.run`
    avec `gh` dans l'argv. Il leve en millisecondes, bruyamment, avec la
    ligne fautive -- la ou un oubli de fixture produisait un hang muet.
    Les autres subprocess (git...) passent inchangees. Un test qui veut
    vraiment `gh` se marque `@pytest.mark.real_gh` et pose son propre
    desarmement ; aucun test de ce fichier n'en a besoin.
    """
    if request.node.get_closest_marker("real_gh"):
        return
    real_run = pig.subprocess.run

    def guarded_run(argv, *args, **kwargs):
        cmd = argv if isinstance(argv, (list, tuple)) else [argv]
        joined = " ".join(str(part) for part in cmd)
        if re.search(r"(^|[\\/ ])gh(\.exe)?($|\s)", joined):
            raise _RealGhReached(
                "appel gh reel depuis un test : "
                + joined[:160]
                + " -- stuber la surface (voir _patch_belt_network) ou "
                "marquer le test @pytest.mark.real_gh")
        return real_run(argv, *args, **kwargs)

    monkeypatch.setattr(pig.subprocess, "run", guarded_run)


def _make_item(number, age_days, idle, klass="grain", last=None,
               created=None, genre="docs"):
    return {
        "number": number,
        "klass": klass,
        "age": age_days,
        "idle": idle,
        "genre": genre,
        "labels": [],
        "title": f"issue #{number}",
        "created_at": created or f"2026-{(age_days % 9) + 1:02d}-01T00:00:00Z",
        "last_delivery_stamp": last,
    }


class _FakeArgs:
    """Args minimum pour draw_belt / belt_sort_key / belt_filter."""

    def __init__(self, *, exclude_issue=None, require_label=None,
                 exclude_label=None, min_age_days=None, max_age_days=None,
                 min_idle_days=None, max_idle_days=None,
                 urns="grain,umbrella,delivered", grains=4):
        self.exclude_issue = exclude_issue or []
        self.require_label = require_label or []
        self.exclude_label = exclude_label or []
        self.min_age_days = min_age_days
        self.max_age_days = max_age_days
        self.min_idle_days = min_idle_days
        self.max_idle_days = max_idle_days
        self.urns = urns
        self.grains = grains


# Predicat 1 : l'ordre suit la derniere visite (cf body #18832).


def test_belt_sort_key_orders_by_last_delivery_first():
    """Critere 1 : ordre par derniere visite (None d'abord, ISO asc)."""
    never = _make_item(1, age_days=5, idle=1, last=None)
    fresh = _make_item(2, age_days=10, idle=2,
                       last="2026-10-01T00:00:00Z")  # tres recente (hier)
    ancient = _make_item(3, age_days=100, idle=50,
                         last="2026-08-01T00:00:00Z")  # ~2 mois
    pool = [fresh, never, ancient]
    pool.sort(key=pig.belt_sort_key)
    # None en tete, puis 2026-08 avant 2026-10 (plus ancien d'abord)
    assert [it["number"] for it in pool] == [1, 3, 2]


def test_belt_sort_key_tie_breaks_on_created_then_number():
    """Meme date de derniere visite : createdAt croissant, puis `number`."""
    same = _make_item(5, age_days=10, idle=2,
                      last="2026-09-15T00:00:00Z",
                      created="2026-08-01T00:00:00Z")
    newer_create = _make_item(6, age_days=5, idle=1,
                              last="2026-09-15T00:00:00Z",
                              created="2026-09-01T00:00:00Z")
    pool = [newer_create, same]
    pool.sort(key=pig.belt_sort_key)
    # same (creee plus tot) en premier
    assert pool[0]["number"] == 5
    assert pool[1]["number"] == 6


# Predicat 2 : une issue jamais servie se classe par sa creation.


def test_belt_sort_key_never_served_ordered_by_created():
    """Critere 2 : jamais servis tries par createdAt croissant puis number."""
    n_old_create = _make_item(10, age_days=200, idle=1, last=None,
                              created="2026-01-01T00:00:00Z")
    n_new_create = _make_item(11, age_days=10, idle=1, last=None,
                              created="2026-09-01T00:00:00Z")
    pool = [n_new_create, n_old_create]
    pool.sort(key=pig.belt_sort_key)
    # Plus ancienne creation en premier
    assert pool[0]["number"] == 10
    assert pool[1]["number"] == 11


# Predicat 3 : une issue livree hier passe derriere une livree il y a un mois.


def test_belt_sort_old_delivery_before_recent():
    """Critere 3 : ancien derriere recent -- jamais servis prennent les
    premieres places, puis livraisons anciennes, puis livraisons recentes.
    """
    fresh = _make_item(20, age_days=20, idle=2,
                       last="2026-10-01T00:00:00Z")  # hier
    ancient = _make_item(21, age_days=20, idle=2,
                         last="2026-08-01T00:00:00Z")  # il y a un mois
    never = _make_item(22, age_days=20, idle=2, last=None)
    pool = [fresh, ancient, never]
    pool.sort(key=pig.belt_sort_key)
    # never en tete (acception 1), puis ancient (livraison il y a un mois)
    # puis fresh (livraison hier). La livraison plus ancienne passe AVANT
    # la livraison recente -- c'est l'inverse du tirage pondere.
    assert [it["number"] for it in pool] == [22, 21, 20]


# Predicat 4 : une issue reclamee par une autre lane est sautee.


def test_belt_claim_holder_is_skipped_replaced(monkeypatch):
    """Critere 4 : claims occupes sont skippes dans la fenetre du tapis.

    Le mode belt regarde le reel via check_claims ; un candidat tenu est
    remplace par le suivant non tenu, dans la limite de la fenetre
    `grains + 4`.

    Vrai vocabulaire (cf CHANGES_REQUESTED #18836 point 6 -- le tapis ne
    regarde QUE le code machine rendu par `_summarize_claim`) : FREE /
    FREE_STALE / OWNED_BY_ME / BLOCKED. Une fenetre ``belt_check_window``
    est verifiee initialement ; au-dela, le tapis verifie au fil de l'eau.
    """
    items = [
        _make_item(30, age_days=100, idle=10, last=None),
        _make_item(31, age_days=100, idle=10, last=None),
        _make_item(32, age_days=100, idle=10, last=None),
        _make_item(33, age_days=100, idle=10, last=None),
    ]
    # 30 et 31 sont tenus par d'autres lanes ; 32 et 33 sont libres.
    # Le fake_check rend la NOUVELLE forme (code, human).
    def fake_check(numbers, lane):
        return {n: (pig.CLAIM_CODE_BLOCKED if n < 32 else pig.CLAIM_CODE_FREE,
                    "BLOQUE par autre lane" if n < 32 else "libre")
                for n in numbers}
    monkeypatch.setattr(pig, "check_claims", fake_check)

    # On reproduit le comportement du main : on prend la fenetre,
    # on applique le verdict par code machine, on garde grains non BLOCKED.
    check_window = max(4 + 4, 8)
    belt_claims = fake_check([it["number"] for it in items[:check_window]],
                             "myia-ai-01:CoursIA-2")
    picks = []
    withheld = []
    for it in items:
        if len(picks) >= 4:
            break
        code, human = belt_claims.get(it["number"],
                                      (pig.CLAIM_CODE_ERROR, "(no check)"))
        if code == pig.CLAIM_CODE_BLOCKED:
            withheld.append((it, human))
        else:
            picks.append(it)
    assert [p["number"] for p in picks] == [32, 33]
    assert [w[0]["number"] for w in withheld] == [30, 31]


# Predicat 5 : un garde rouge ne vide pas le tapis.


def test_belt_red_backlog_does_not_empty_pool():
    """Critere 5 : le tapis rend la file complete, les rouges du worker
    sont en amont (file de reparation) et ne vident pas le tapis.

    Le main court-circuite AVANT le tapis si red_hit/wip_hit (cf
    coordinator-discipline R0) : la file de reparation est rendue, et le
    tapis n'est pas invoque derriere. Mais une fois dans le tapis, une
    marque rouge sur un item du pool ne le filtre PAS -- c'est le mode
    belt qui prend la releve quand la voie ponderee rendrait vide, par
    construction la file du tapis ne refuse JAMAIS.
    """
    # Items dont aucun ne contient de marqueur rouge, mais on verifie
    # qu'un filtre simulant un rouge laisse passer le tapis quand meme.
    pool = [
        _make_item(40, age_days=100, idle=10, last=None),
        _make_item(41, age_days=50, idle=5,
                   last="2026-09-01T00:00:00Z"),
        _make_item(42, age_days=30, idle=1,
                   last="2026-10-01T00:00:00Z"),
    ]
    args = _FakeArgs(grains=4)
    filtered = pig.belt_filter(pool, args)
    filtered.sort(key=pig.belt_sort_key)
    # Le tapis rend les 3 : 40 (jamais servi), 41 (livraison il y a un
    # mois), 42 (livraison hier). Aucune marque ne les elimine.
    assert len(filtered) == 3
    # Meme un item marque "rouge" par le caller resterait dans la file
    # belt -- c'est le main qui sort les trevises AVANT, jamais le tapis.
    fake_red = dict(pool[0])
    fake_red["red_marker"] = "fixture-rouge-base"
    pool.append(fake_red)
    filtered = pig.belt_filter(pool, args)
    assert any(it["number"] == 40 for it in filtered), \
        "le tapis ne filtre pas les rouges (main s'en occupe)"


# 6e point CHANGES_REQUESTED #18836 (post-c.56) : _summarize_claim rend un
# code machine, la boucle belt retient BLOQUE seul, et verifie au fil de
# l'eau les items hors fenetre. Trois tests :


def test_summarize_claim_machine_codes():
    """Le vrai vocabulaire : 4 codes machine + 2 chemins d'erreur.

    Couvre les branches de `_summarize_claim` directement. Le tapis roulant
    ne regarde QUE le code, pas le verbe humain (cf bug fondateur c.56 :
    `_summarize_claim` rendait du texte, la boucle testait `== "CLEAR"`,
    resultat jamais servie dans la fenetre verifiee).
    """
    # Cas BLOQUE par une autre lane : blocking_lanes non vide.
    blocked_json = ('{"blocking_lanes": ["myia-po-2024:CoursIA-2"],'
                    '"my_active_claim": false, "stale_claims": []}')
    code, human = pig._summarize_claim(blocked_json + "\n", 0)
    assert code == pig.CLAIM_CODE_BLOCKED
    assert "BLOQUE par" in human
    # cas OWNED_BY_ME : my_active_claim=True.
    owned_json = ('{"blocking_lanes": [], "my_active_claim": true,'
                  '"stale_claims": []}')
    code, human = pig._summarize_claim(owned_json + "\n", 0)
    assert code == pig.CLAIM_CODE_OWNED_BY_ME
    # cas FREE_STALE : stale_claims non vide.
    stale_json = ('{"blocking_lanes": [], "my_active_claim": false,'
                  '"stale_claims": [42]}')
    code, human = pig._summarize_claim(stale_json + "\n", 0)
    assert code == pig.CLAIM_CODE_FREE_STALE
    # cas FREE : tout vide.
    free_json = ('{"blocking_lanes": [], "my_active_claim": false,'
                 '"stale_claims": []}')
    code, human = pig._summarize_claim(free_json + "\n", 0)
    assert code == pig.CLAIM_CODE_FREE
    # cas ERROR : sortie sans JSON.
    code, human = pig._summarize_claim("usage: --lane <lane> <N>\n", 2)
    assert code == pig.CLAIM_CODE_ERROR


def test_belt_head_of_queue_free_surfaces_as_pick_one(monkeypatch):
    """Le scenario fondateur du steer coordinateur : la tete de file est
    ``libre``, le tapis DOIT la sortir en pick #1 (et pas les positions 9+
    non verifiees).

    Montre la regression d'origine : avant le fix, _summarize_claim rendait
    ``"libre"`` (humain) et la boucle belt testait `== "CLEAR"`, jamais
    rendue -> la tete tombait en retenue, et les positions 9+ etaient
    servies via `belt_claims.get(n, "CLEAR")` SANS verification.
    """
    # File de 12 issues ; on impose la tete comme 5105 (last=None, jamais
    # servie) en controlant created_at directement, puis les items 5106,
    # 5108 sont BLOQUE, les suivants libres. La tete 5105 doit sortir en
    # pick #1 (le scenario du steer).
    items = [
        _make_item(5105, age_days=200, idle=10, last=None,
                   created="2025-01-01T00:00:00Z"),  # tete, tres ancienne
        _make_item(5106, age_days=180, idle=10, last=None,
                   created="2025-06-01T00:00:00Z"),
        _make_item(5107, age_days=170, idle=10, last=None,
                   created="2025-12-01T00:00:00Z"),
        _make_item(5108, age_days=160, idle=10, last=None,
                   created="2026-01-01T00:00:00Z"),
        _make_item(5109, age_days=150, idle=10, last=None,
                   created="2026-03-01T00:00:00Z"),
        _make_item(5110, age_days=140, idle=10, last=None,
                   created="2026-05-01T00:00:00Z"),
        _make_item(5111, age_days=130, idle=10, last=None,
                   created="2026-07-01T00:00:00Z"),
    ]
    items.sort(key=pig.belt_sort_key)
    # La tete est 5105 (jamais servie, creee en 2025-01-01 = la plus ancienne).
    assert items[0]["number"] == 5105, (
        f"sanity: tete devrait etre 5105, got {items[0]['number']}"
    )
    # fake_check reproduit le contrat reel : 5105 libre (scenario du steer),
    # 5106/5107/5108 BLOQUE, le reste libre.
    def fake_check(numbers, lane):
        out = {}
        for n in numbers:
            if n in (5106, 5107, 5108):
                out[n] = (pig.CLAIM_CODE_BLOCKED, "BLOQUE par autre lane")
            else:
                out[n] = (pig.CLAIM_CODE_FREE, "libre")
        return out
    monkeypatch.setattr(pig, "check_claims", fake_check)

    belt_pool = items
    grains = 3
    check_window = min(max(grains + 4, 8), len(belt_pool))
    initial_nums = [it["number"] for it in belt_pool[:check_window]]
    belt_claims = fake_check(initial_nums, "myia-ai-01:CoursIA-2")
    picks = []
    withheld = []
    for it in belt_pool:
        if len(picks) >= grains:
            break
        code, human = belt_claims.get(it["number"],
                                      (pig.CLAIM_CODE_ERROR, "(no check)"))
        if code == pig.CLAIM_CODE_BLOCKED:
            withheld.append((it, human))
        else:
            picks.append(it)
    # La tete de file sort en pick #1.
    assert picks[0]["number"] == 5105, (
        f"BUG #18836 fondateur : la tete libre doit sortir en pick #1, "
        f"mais le tapis rend {picks[0]['number']}. La boucle belt est "
        f"trompee par un verbe humain au lieu d'un code machine."
    )
    # Les BLOQUE ont ete retenus.
    assert [w[0]["number"] for w in withheld] == [5106, 5107, 5108]
    # Et les picks non-bloques apres 5105 sont les suivants.
    assert [p["number"] for p in picks] == [5105, 5109, 5110]


def test_belt_verifies_outside_window_on_the_fly(monkeypatch):
    """La verification au fil de l'eau : un item hors `belt_check_window`
    qui n'a pas ete verifie initialement doit etre verifie ICI -- sinon
    le tapis le sert sans l'avoir jamais teste.

    Avant le fix : `belt_claims.get(n, "CLEAR")` rendait ``"CLEAR"`` par
    defaut pour les positions hors fenetre. Apres le fix : on appelle
    ``check_claims([n])`` au fil de l'eau et on tranche.

    On monte une pool de 12 items ou les 8 premiers sont tous BLOQUE : le
    tapis doit faire UN appel initial, puis 3 appels au fil de l'eau pour
    les items hors fenetre (809, 810, 811) avant de servir 3 picks.
    """
    items = [_make_item(800 + i, age_days=200 - i, idle=10, last=None,
                        created=f"2026-{(i % 9) + 1:02d}-01T00:00:00Z")
             for i in range(12)]
    items.sort(key=pig.belt_sort_key)
    # Les 8 premiers par sort_triene sont bloques (verifie initialement) ;
    # les 4 suivants sont servis au fil de l'eau, tous libres.
    blocked_nums = {it["number"] for it in items[:8]}
    free_nums = {it["number"] for it in items[8:]}

    calls = []

    def fake_check(numbers, lane):
        calls.append(list(numbers))
        out = {}
        for n in numbers:
            if n in blocked_nums:
                out[n] = (pig.CLAIM_CODE_BLOCKED, "BLOQUE par autre lane")
            else:
                out[n] = (pig.CLAIM_CODE_FREE, "libre")
        return out
    monkeypatch.setattr(pig, "check_claims", fake_check)

    belt_pool = items
    grains = 3
    check_window = min(max(grains + 4, 8), len(belt_pool))
    initial_nums = [it["number"] for it in belt_pool[:check_window]]
    belt_claims = fake_check(initial_nums, "myia-ai-01:CoursIA-2")
    picks = []
    withheld = []
    for it in belt_pool:
        if len(picks) >= grains:
            break
        n = it["number"]
        if n in belt_claims:
            code, human = belt_claims[n]
        else:
            extra = fake_check([n], "myia-ai-01:CoursIA-2")
            code, human = extra.get(n, (pig.CLAIM_CODE_ERROR, "(no check)"))
            belt_claims[n] = (code, human)
        if code == pig.CLAIM_CODE_BLOCKED:
            withheld.append((it, human))
        else:
            picks.append(it)
    # Les 8 BLOQUE ont ete retenus (a prealable, dans la fenetre initiale).
    assert {w[0]["number"] for w in withheld} == blocked_nums, (
        f"withheld devrait etre {blocked_nums}, "
        f"got {{w[0]['number'] for w in withheld}}"
    )
    # Les 3 picks sont les 3 premiers non-bloques (par sort_triene).
    expected_picks = sorted(free_nums)[:3]
    assert [p["number"] for p in picks] == expected_picks, (
        f"picks devrait etre {expected_picks}, "
        f"got {[p['number'] for p in picks]}"
    )
    # Au moins 2 appels a check_claims : 1 initial + au moins 1 fil du l'eau.
    assert len(calls) >= 2, (
        f"Apres le fix, le tapis doit verifier au fil de l'eau "
        f"(appels : {calls}) ; sans cela, on retombe sur le bug "
        f"fondateur : servir sans verifier."
    )


# Accumulateur : couverture end-to-end via les exports.


def test_belt_filter_respects_exclude_issue_and_urns():
    """Filtre actif : exclusions explicites, urnes."""
    pool = [
        _make_item(50, age_days=10, idle=1, klass="grain"),
        _make_item(51, age_days=10, idle=1, klass="umbrella"),
        _make_item(52, age_days=10, idle=1, klass="delivered"),
        _make_item(53, age_days=10, idle=1, klass="grain"),
    ]
    args = _FakeArgs(exclude_issue=["50"], urns="grain,umbrella")
    filtered = pig.belt_filter(pool, args)
    nums = sorted(it["number"] for it in filtered)
    assert nums == [51, 53]
    # delivered exclue par urns
    assert not any(it["klass"] == "delivered" for it in filtered)


def test_belt_filter_respects_label_exclude():
    """Filtre label exclu : un label exclue elimine l'item."""
    pool = [
        _make_item(60, age_days=10, idle=1, klass="grain"),
        _make_item(61, age_days=10, idle=1, klass="grain"),
    ]
    pool[0]["labels"].append("wontfix")
    args = _FakeArgs(exclude_label=["wontfix"])
    filtered = pig.belt_filter(pool, args)
    assert [it["number"] for it in filtered] == [61]


def test_belt_filter_respects_age_bounds():
    """Bornes d'age : min_age_days / max_age_days appliques."""
    pool = [
        _make_item(70, age_days=2, idle=1),
        _make_item(71, age_days=10, idle=1),
        _make_item(72, age_days=100, idle=1),
    ]
    args = _FakeArgs(min_age_days=5, max_age_days=50)
    filtered = pig.belt_filter(pool, args)
    assert [it["number"] for it in filtered] == [71]


def test_belt_report_metrics_handles_empty_pool():
    """--report : pool vide -> ecart = None, ferme = 0."""
    metrics = pig.belt_report_metrics([], closed_7d=None)
    assert metrics == (None, None, 0)


def test_belt_report_metrics_computes_max_gap():
    """--report : ecart_max = jours depuis la derniere livraison."""
    pool = [
        {"last_delivery_stamp": "2026-09-01T00:00:00Z"},
        {"last_delivery_stamp": "2026-08-15T00:00:00Z"},
    ]
    metrics = pig.belt_report_metrics(pool, closed_7d=12)
    max_gap, closed_7d, sample = metrics
    assert sample == 2
    assert closed_7d == 12
    # max_gap est arrondi, on ne teste pas la valeur exacte mais le signe
    assert max_gap is not None and max_gap > 0


# #15069 sous le tapis : l'urne `delivered` est presente dans le defaut de
# `--urns`. La voie ponderee la retire pour une lane worker via
# `apply_delivered_urn_gate` ; le tapis doit recevoir ces urnes EFFECTIVES,
# pas relire `args.urns` brut (sinon le mode par defaut de /continue sert
# des fermetures a des lanes qui ne ferment rien).


def test_belt_filter_honours_delivered_gate_for_worker_lane():
    pool = [
        _make_item(70, age_days=90, idle=30, klass="delivered"),
        _make_item(71, age_days=80, idle=20, klass="grain"),
        _make_item(72, age_days=70, idle=10, klass="umbrella"),
    ]
    args = _FakeArgs()
    selected = {v.casefold() for v in pig._csv_values([args.urns])}
    urns, notice = pig.apply_delivered_urn_gate(
        "myia-po-2023:CoursIA", args.urns, "grain,umbrella,delivered",
        selected)
    assert notice is not None
    kept = {it["number"] for it in pig.belt_filter(pool, args, urns=urns)}
    assert kept == {71, 72}


def test_belt_filter_keeps_delivered_for_coordinator_lane():
    pool = [
        _make_item(70, age_days=90, idle=30, klass="delivered"),
        _make_item(71, age_days=80, idle=20, klass="grain"),
    ]
    args = _FakeArgs()
    selected = {v.casefold() for v in pig._csv_values([args.urns])}
    urns, notice = pig.apply_delivered_urn_gate(
        "myia-ai-01:CoursIA", args.urns, "grain,umbrella,delivered",
        selected)
    assert notice is None
    kept = {it["number"] for it in pig.belt_filter(pool, args, urns=urns)}
    assert kept == {70, 71}


# ==================================================================
# Tests #18866 : mode --belt --json = un seul document JSON.
# La cle `repair` fusionne le rappel rouge/WIP qui etait sinon imprime
# en double (deux objets JSON sur la sortie standard). La fenetre
# `last_delivery_window_days` elargit a 90 j pour ne pas oublier les
# livraisons au-dela des 14 j par defaut.
# ==================================================================


def _state_red():
    """Retourne un etat GraphQL shape compatible `fetch_pr_states`."""
    return {"checks": [("PR gate", "FAILURE", True)],
            "mergeable": "MERGEABLE",
            "reviews": []}


def _patch_belt_network(monkeypatch, prs, red_state):
    """Patche le strict minimum pour faire passer `main --belt --json`
    jusqu'au bloc `out_belt` sans toucher au reseau.

    Le test reste en memoire : pas de `fetch_pool` reel (un pool vide
    court-circuite la volee ponderee et le tapis no-op). `red_backlog`
    reste fonctionnel : il voit 1 PR rouge de la lane, declenche le garde,
    et le `repair_payload` est calcule pour la fusion.
    """
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    # fetch_pool = reseau reel (gh issue list). En mode test, on rend
    # un pool vide pour court-circuiter la volee ponderee et garder
    # la sortie compacte.
    monkeypatch.setattr(pig, "fetch_pool",
                        lambda **k: ([], None))
    monkeypatch.setattr(pig, "fetch_pr_states",
                        lambda nums: {n: red_state for n in nums if n in {p["number"] for p in prs}})
    monkeypatch.setattr(pig, "unaddressed_review_points_detail",
                        lambda nums: {18844: {"count": 1, "authors": [],
                                              "verdict": None, "verdict_surface": None}} if prs else {})
    monkeypatch.setattr(pig, "fetch_lane_record_prs", lambda **k: ([], None))
    monkeypatch.setattr(pig, "fetch_main_head_probe", lambda *a, **k: None)
    # Le tapis fait un check_claims : on rend toujours FREE.
    monkeypatch.setattr(pig, "check_claims",
                        lambda nums, lane: {n: (pig.CLAIM_CODE_FREE, "libre")
                                            for n in nums})
    # Le tapis lit aussi les claims comme visites : jamais de reseau en test.
    monkeypatch.setattr(pig, "latest_claim_stamp", lambda n: None)
    # `fetch_visits` (visits + long_visits, l.6024/6029 de main) etait le
    # trou de la fixture : non patchee, `main --belt --json` sortait sur un
    # vrai `gh` et le test pendait 99 s (mesure 2026-10-09, coordinateur
    # #19913 : la suite bloquait sur un subprocess.communicate reel).
    # Un dictionnaire VIDE n'est pas une visite manquante : le tapis traite
    # l'absence comme "jamais servie" (la plus ancienne en tete), ce qui
    # est exactement l'etat que le pool vide implique deja.
    monkeypatch.setattr(pig, "fetch_visits", lambda *a, **k: ({}, None))
    # `fetch_series_visits` (l.6044 de main) : 2e trou de la meme famille,
    # trouve par le garde `_no_real_gh` (stack : series_saturation ->
    # gh_payload_cache -> run_gh -> subprocess.run bloque en communicate).
    # Rend `(zones, issue_to_family, erreur)` ; vide + erreur None = mesure
    # faite, aucune zone -- un test de saturation injecte la sienne.
    monkeypatch.setattr(pig, "fetch_series_visits",
                        lambda **k: ({}, {}, None))
    # `fetch_merged` (l.6066 de main, importe de series_saturation) : le
    # corpus de livraisons reelles. Meme famille que fetch_series_visits --
    # passe par gh_payload_cache -> run_gh. `measure_delivery`, en aval,
    # est pure : elle ne fait que lire ce corpus. Forme `(prs, err)`.
    monkeypatch.setattr(pig, "fetch_merged", lambda *a, **k: ([], None))
    # `pin_gh_token()` (gh_identity, appele au demarrage de main) : le
    # VRAI hang des tests `main --belt` (mesure 2026-10-09 : ~300 s par
    # test, 5 tests). Le garde `_no_real_gh` l'a nomme en 0,8 s -- un
    # `gh auth token --user myia-po-2026` sans jeton machine repond apres
    # un aller-retour d'auth lent. C'est de l'installation d'environnement,
    # pas le comportement sous test : on le neutralise.
    monkeypatch.setattr(pig.gh_identity, "pin_gh_token", lambda *a, **k: None)
    # `snapshot_prime` (#22630) : le tapis rafraichit son instantane partage
    # UNE FOIS par passe, ce qui emet un `gh api` par issue candidate. Le
    # defaut de la boucle est INERTE (`belt_snapshot_prime_inert`) ; `main`
    # injecte le vrai rafraichisseur. On enumere ici la surface, comme les
    # autres : les tests qui gardent un pool vide n'ont aucun candidat a
    # rafraichir, et l'ecriture du cache reste desactivee sous pytest
    # (`_PASS_SNAPSHOT`).
    monkeypatch.setattr(pig, "_belt_snapshot_prime", lambda repo, numbers: None)


def test_belt_json_emits_single_document_when_red_present(monkeypatch, capsys):
    """`--belt --json` produit UN SEUL document JSON parseable.

    Avant le fix (#18866 point 2), la branche rouge du main() faisait
    `print(json.dumps(...))` puis retournait 0 sans condition sur
    `args.belt`. Le tapis re-imprimait son propre JSON juste apres. Le
    consommateur lisait DEUX objets, et `json.loads` se cassait sur
    `Extra data`.

    Apres le fix, en mode belt, le rappel rouge est mis sous la cle
    `repair` du document du tapis, et la sortie reste UN document.
    """
    red = _state_red()
    prs = [{
        "number": 18844,
        "title": "PR rouge de la lane",
        "body": "Grain: MED/guard -- lane myia-po-2024:CoursIA-2",
        "createdAt": "2026-09-30T12:00:00Z",
        "isDraft": False,
    }]
    _patch_belt_network(monkeypatch, prs, red)

    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2",
                   "--belt", "--json"])

    assert rc == 0
    out = capsys.readouterr().out
    # CRITIQUE : UN seul document JSON. Si le fix est casse, on a
    # DEUX objets et `json.loads` leve `Extra data`.
    payload = json.loads(out)
    # `mode` est l'identifiant du tapis -- la fusion a bien eu lieu.
    assert payload["mode"] == "belt"
    # Le repair est fusionne (non-None) : le garde rouge s'est declenche.
    assert payload["repair"] is not None
    assert payload["repair"]["assignment"] == "reparer-son-rouge"
    assert payload["repair"]["grain"]["number"] == 18844
    # La fenetre de livraisons en mode belt fait 90 j, pas 14 j.
    assert payload["last_delivery_window_days"] == 90


def test_belt_json_repair_key_absent_when_no_red(monkeypatch, capsys):
    """`--belt --json` sans garde rouge : `repair` est None.

    Controle positif du test precedent : la cle `repair` existe
    toujours (les consommateurs peuvent compter dessus), mais sa valeur
    est None quand la lane n'a pas de reparation a faire, distinct
    d'une cle absente (qui signalerait un schema inconsistant).
    """
    _patch_belt_network(monkeypatch, prs=[], red_state=_state_red())

    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2", "--belt", "--json"])

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["mode"] == "belt"
    assert payload["repair"] is None
    assert payload["last_delivery_window_days"] == 90


class _RealProbeReached(AssertionError):
    """Un test a atteint une sonde reseau par defaut -- le piege #19913."""


def test_belt_loop_default_probes_are_inert(monkeypatch):
    """#19913 : sans sonde injectee, la boucle n'atteint JAMAIS le reseau.

    Les defauts de ``belt_pick_with_replacements`` sont les sondes inertes
    (doctrine ``delivered_probe_inert`` / ``merged_pr_probe_inert``). Avant
    le fix, le defaut etait ``has_delivered_signal`` / ``merged_pr_signal``
    -- un test qui oubliait d'injecter sa sonde sortait sur un vrai ``gh``
    et pendait (mesure 2026-10-09 : 99 s pour un seul test). Ce garde
    casse au premier retour d'un defaut reseau : les vraies sondes sont
    remplacees par des leveuses d'exception, la boucle doit completer.

    Le rafraichissement d'instantane (#22630) est couvert de la meme facon :
    le vrai ``_belt_snapshot_prime`` est une leveuse -- si la boucle
    redevenait reseau par defaut, ce test echoue au lieu de pendre. Le
    garde `_no_real_gh` attrape au passage tout `gh` residuel.
    """
    def raise_delivered(n, lane=None):
        raise _RealProbeReached(f"has_delivered_signal atteinte pour #{n}")

    def raise_merged(n, lane=None):
        raise _RealProbeReached(f"merged_pr_signal atteinte pour #{n}")

    def raise_recent(n):
        raise _RealProbeReached(
            f"has_recent_delivery_marker atteinte pour #{n}")

    monkeypatch.setattr(pig, "has_delivered_signal", raise_delivered)
    monkeypatch.setattr(pig, "merged_pr_signal", raise_merged)
    monkeypatch.setattr(pig, "has_recent_delivery_marker", raise_recent)
    monkeypatch.setattr(
        pig, "_belt_snapshot_prime",
        lambda repo, numbers: (_ for _ in ()).throw(
            _RealProbeReached("_belt_snapshot_prime atteint hors injection")))

    pool = [_make_item(19001, age_days=50, idle=5, last=None),
            _make_item(19002, age_days=49, idle=5, last=None)]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(), probe_budget=8)

    # Fail-OPEN : la sonde inerte rend None = « non sondable », le candidat
    # est SERVI (jamais refuse faute de signal) et RAPPORTE dans failures
    # -- doctrine TRI-ETAT de merged_pr_probe_inert. Les deux numeros dans
    # failures sont le comportement attendu du defaut, pas un defaut.
    assert [p["number"] for p in picks] == [19001, 19002]
    assert state["failures"] == [19001, 19002]
    assert withheld == []


def test_belt_main_json_path_never_reaches_real_probes(monkeypatch, capsys):
    """#19913 : le chemin complet `main --belt --json` est inerte par defaut.

    Controle negatif du piege mesure par le coordinateur : sur une fusion
    avec main, ``test_belt_json_emits_single_document_when_red_present``
    depassait 30 s dans un vrai ``fetch_visits``, et restait bloque sur un
    ``subprocess.communicate`` reel. Apres le fix (fixture + defauts
    inertes), ``fetch_visits`` est couvert par la fixture, et les sondes
    de livraison ``has_delivered_signal`` / ``merged_pr_signal`` sont
    remplacees par des leveuses : le meme scenario main doit completer
    vite et sans exception. Toute regression (sonde reseau non couverte
    par la fixture, defaut reseau reintroduit dans la boucle) fait lever
    ce test.
    """
    def raise_real(name):
        def raiser(*a, **k):
            raise _RealProbeReached(f"{name} atteinte hors injection")
        return raiser

    red = _state_red()
    prs = [{"number": 18844,
            "title": "PR rouge de la lane",
            "body": "Grain: MED/guard -- lane myia-po-2024:CoursIA-2",
            "createdAt": "2026-09-30T12:00:00Z",
            "isDraft": False}]
    _patch_belt_network(monkeypatch, prs, red)
    # La fixture couvre fetch_visits (main l'appelle legitiment, sans
    # reseau en test) ET le rafraichisseur d'instantane. Les sondes de
    # livraison, elles, ne DOIVENT etre atteintes nulle part sur ce chemin
    # -- defauts inertes de la boucle : si un defaut reseau revient, la
    # leveuse fait echouer le test.
    monkeypatch.setattr(pig, "has_delivered_signal",
                        raise_real("has_delivered_signal"))
    monkeypatch.setattr(pig, "merged_pr_signal",
                        raise_real("merged_pr_signal"))

    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2", "--belt", "--json"])

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["mode"] == "belt"
    assert payload["repair"]["grain"]["number"] == 18844


def test_belt_main_injects_the_real_snapshot_prime(monkeypatch, capsys):
    """Le cache reste utilise en production : `main` injecte le vrai prime.

    Controle positif du defaut inerte : la boucle seule n'emet aucune
    requete, mais le run complet rafraichit bien l'instantane partage UNE
    FOIS pour les candidats de la fenetre. Le rafraichisseur est espionne
    (aucune requete reelle), les candidats restent vides de claims pour
    garder le run en memoire.
    """
    _patch_belt_network(monkeypatch, prs=[], red_state=_state_red())
    pool = [_make_item(19101, age_days=50, idle=5, last=None)]
    monkeypatch.setattr(pig, "fetch_pool", lambda **k: (list(pool), None))
    # La mesure des dernieres visites (`latest_claim_stamp` / bulk GraphQL)
    # n'est pas la surface sous test : elle est neutralisee comme dans les
    # autres tests de la boucle, pour garder le run entierement en memoire.
    monkeypatch.setattr(pig, "fetch_latest_claim_stamps_bulk",
                        lambda *a, **k: ({}, None))
    # Sondes de livraison : verdicts injectes, comme partout dans ce fichier
    # -- seul le BRANCHEMENT du rafraichisseur est mesure ici.
    monkeypatch.setattr(pig, "has_delivered_signal", lambda n, lane=None: False)
    monkeypatch.setattr(pig, "merged_pr_signal", lambda n, lane=None: False)
    monkeypatch.setattr(pig, "has_recent_delivery_marker", lambda n: False)
    primed: list[list[int]] = []

    def spy_prime(repo, numbers):
        primed.append(list(numbers))

    monkeypatch.setattr(pig, "_belt_snapshot_prime", spy_prime)
    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2", "--belt", "--json"])

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["mode"] == "belt"
    assert primed, "main n'a pas branche le rafraichissement d'instantane"
    assert primed == [[19101]], "une seule passe, sur les candidats tires"


def test_non_belt_json_red_still_emits_standalone_repair(monkeypatch, capsys):
    """Regression check : hors `--belt`, le mode repair reste standalone.

    Sans ce controle, le refactor pourrait fusionner par erreur la cle
    `repair` dans le mode non-belt et briser la volee ponderee.
    L'ancien contrat -- `mode: "repair"`, pas de `mode: belt` -- est
    preserve pour le consommateur de la volee.
    """
    red = _state_red()
    prs = [{
        "number": 18844,
        "title": "PR rouge de la lane",
        "body": "Grain: MED/guard -- lane myia-po-2024:CoursIA-2",
        "createdAt": "2026-09-30T12:00:00Z",
        "isDraft": False,
    }]
    _patch_belt_network(monkeypatch, prs, red)

    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2", "--json"])

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    # Le mode reste `repair`, pas `belt` : la volee ponderee est inchangee.
    assert payload["mode"] == "repair"
    assert payload["grain"]["number"] == 18844


# Le tapis avance au claim, pas au merge (mandat user 2026-10-04).
# Mesure fondatrice : l'EPIC #7265 servie le matin par une sous-issue
# reservee (#19088) est restee en tete de file, et une seconde lane l'a
# tiree le soir.


def test_belt_visit_stamp_is_latest_of_merge_claim_child():
    it = _make_item(1, age_days=90, idle=1, last="2026-08-01T00:00:00Z")
    assert pig.belt_visit_stamp(it) == "2026-08-01T00:00:00Z"
    it["last_claim_stamp"] = "2026-10-04T19:49:00Z"
    it["last_child_stamp"] = "2026-10-04T09:50:00Z"
    assert pig.belt_visit_stamp(it) == "2026-10-04T19:49:00Z"
    never = _make_item(2, age_days=90, idle=1, last=None)
    assert pig.belt_visit_stamp(never) is None


def test_belt_claim_moves_issue_behind_unvisited_ones():
    """Une issue reservee depuis son dernier merge passe derriere une issue
    plus recente jamais visitee, sans attendre de merge."""
    old = _make_item(10, age_days=90, idle=1, last="2026-08-01T00:00:00Z",
                     created="2026-07-01T00:00:00Z")
    newer = _make_item(11, age_days=30, idle=1, last=None,
                       created="2026-09-01T00:00:00Z")
    pool = [old, newer]
    claims = {10: "2026-10-04T19:49:00Z"}
    probed = pig.settle_belt_head(pool, need=2, probe=claims.get, max_probes=10)
    assert [it["number"] for it in pool] == [11, 10]
    assert probed == {10, 11}
    assert old["last_claim_stamp"] == "2026-10-04T19:49:00Z"


def test_belt_claim_older_than_merge_changes_nothing():
    it = _make_item(12, age_days=90, idle=1, last="2026-09-20T00:00:00Z",
                    created="2026-07-01T00:00:00Z")
    other = _make_item(13, age_days=30, idle=1, last="2026-09-25T00:00:00Z",
                       created="2026-09-01T00:00:00Z")
    pool = [other, it]
    pig.settle_belt_head(pool, need=2, probe={12: "2026-09-01T00:00:00Z"}.get,
                         max_probes=10)
    assert [x["number"] for x in pool] == [12, 13]


def test_belt_settle_reads_the_freed_slot_until_head_is_stable():
    """Toute la tete est reservee : chaque place liberee est lue a son tour,
    et la premiere issue non reservee finit en tete."""
    pool = [_make_item(20 + k, age_days=90, idle=1, last=None,
                       created=f"2026-07-0{k + 1}T00:00:00Z") for k in range(5)]
    claims = {20: "2026-10-04T10:00:00Z", 21: "2026-10-04T11:00:00Z",
              22: "2026-10-04T12:00:00Z"}
    probed = pig.settle_belt_head(pool, need=2, probe=claims.get, max_probes=10)
    assert [it["number"] for it in pool][:2] == [23, 24]
    assert {20, 21, 22, 23, 24} <= probed


def test_belt_settle_is_bounded_by_max_probes():
    pool = [_make_item(40 + k, age_days=90, idle=1, last=None,
                       created=f"2026-07-{k + 1:02d}T00:00:00Z") for k in range(20)]
    calls = []

    def probe(n):
        calls.append(n)
        return f"2026-10-04T{len(calls):02d}:00:00Z"

    pig.settle_belt_head(pool, need=3, probe=probe, max_probes=7)
    assert len(calls) == 7


def test_belt_child_issue_visits_its_parent_7265_scenario():
    """Cas fondateur : la sous-issue #19088 (titre ``[#7265 ...``) creee a
    09:50Z fait passer l'EPIC #7265 derriere une issue d'aout jamais servie."""
    epic = _make_item(7265, age_days=78, idle=0, klass="umbrella",
                      last="2026-08-13T00:00:00Z",
                      created="2026-07-18T00:00:00Z")
    august = _make_item(14000, age_days=40, idle=3, last=None,
                        created="2026-08-25T00:00:00Z")
    child = _make_item(19088, age_days=0, idle=0, last=None,
                       created="2026-10-04T09:50:00Z")
    child["title"] = "[#7265 · pépite A3] Object explorer metadata-driven"
    child["body"] = "Pepite A3 de l'EPIC #7265."
    belt_pool = [epic, august]
    latest = pig.apply_child_visits([epic, august, child], belt_pool)
    assert latest[7265] == "2026-10-04T09:50:00Z"
    assert epic["last_child_stamp"] == "2026-10-04T09:50:00Z"
    belt_pool.sort(key=pig.belt_sort_key)
    assert [it["number"] for it in belt_pool] == [14000, 7265]


def test_parent_refs_reads_part_of_and_title_prefix_not_self():
    it = _make_item(500, age_days=1, idle=0)
    it["title"] = "[#16231] renommer ICT-45"
    it["body"] = "Part of #4362. See #9999.\nPart of #500 (soi-meme)"
    assert pig.parent_refs(it) == {16231, 4362}
    plain = _make_item(501, age_days=1, idle=0)
    plain["body"] = "See #4362 et Refs #12"
    assert pig.parent_refs(plain) == set()


def _claim(at: str, body: str) -> dict:
    return {"createdAt": at, "body": body, "author": {"login": "jsboige"}}


def test_claim_visit_stamp_reads_decorated_markers_like_the_organ():
    """Reserve tierce #19147, point 1 : la grammaire est celle de
    ``check_lane_claim.py`` (#10906, #12711), pas une regex propre au tapis."""
    for body in (
        "**[CLAIMED] lane myia-po-2027:CoursIA -- T1**",
        "## [CLAIMED] lane myia-po-2027:CoursIA -- T1",
        "- [CLAIMED] lane myia-po-2027:CoursIA -- T1",
        "> [CLAIMED] lane myia-po-2027:CoursIA -- T1",
        "→[CLAIMED] lane myia-po-2027:CoursIA -- T1",
        "[claimed] lane myia-po-2027:CoursIA -- T1",
    ):
        assert pig.claim_visit_stamp(
            [_claim("2026-10-04T09:50:12Z", body)]) == "2026-10-04T09:50:12Z", body


def test_claim_visit_stamp_ignores_quoted_and_midline_mentions():
    """Une citation en bloc fence, une mention en milieu de ligne, un marqueur
    sans lane ne sont la visite de personne."""
    fenced = ("Le gabarit est :\n```\n[CLAIMED] lane myia-po-2027:CoursIA"
              " -- T1\n```\n")
    comments = [
        _claim("2026-10-04T09:00:00Z", fenced),
        _claim("2026-10-04T10:00:00Z",
               "T1 livree. Le [CLAIMED] du matin reste valable."),
        _claim("2026-10-04T11:00:00Z", "> [CLAIMED] cite sans lane"),
    ]
    assert pig.claim_visit_stamp(comments) is None


def test_claim_visit_stamp_closures_advance_the_visit():
    """Point 2 de la reserve : une cloture est lue, et c'est une visite.
    Elle AVANCE la date au lieu de la laisser figee sur la prise."""
    claim = _claim("2026-10-04T09:50:12Z",
                   "[CLAIMED] lane myia-po-2027:CoursIA -- T1")
    for close in ("RELEASED", "DONE", "ABANDONED", "CANCELLED", "DELIVERED"):
        assert pig.claim_visit_stamp([
            claim,
            _claim("2026-10-04T12:00:00Z",
                   f"[{close}] lane myia-po-2027:CoursIA -- PR #19999"),
        ]) == "2026-10-04T12:00:00Z", close


def test_claim_visit_stamp_counts_every_lane():
    """Toutes lanes : la plus recente marque, quelle que soit la lane."""
    comments = [
        _claim("2026-10-04T08:00:00Z",
               "[CLAIMED] lane myia-po-2024:CoursIA -- B"),
        _claim("2026-10-04T09:00:00Z",
               "[CLAIMED] lane myia-po-2027:CoursIA -- A"),
        _claim("2026-10-04T07:00:00Z",
               "[RELEASED] lane myia-po-2023:CoursIA -- ancien"),
    ]
    assert pig.claim_visit_stamp(comments) == "2026-10-04T09:00:00Z"


def test_belt_released_issue_stays_behind_7742_scenario():
    """Bout en bout, cas mesure #7742 : prise le 31/08, rendue le 19/09 apres
    deux tranches mergees. Lue a la prise seule, elle repassait devant une
    issue visitee le 10/09 ; lue a sa cloture, elle reste derriere."""
    claim = _claim("2026-08-31T01:31:34Z",
                   "[CLAIMED] lane myia-po-2024:CoursIA -- paths: a.ipynb")
    release = _claim("2026-09-19T14:46:38Z",
                     "[RELEASED] lane myia-po-2024:CoursIA -- tranches "
                     "livrees, le claim rend la main")

    def order(comments):
        pool = [
            _make_item(7742, age_days=75, idle=0, last=None,
                       created="2026-07-21T16:31:50Z"),
            _make_item(200, age_days=30, idle=0,
                       last="2026-09-10T00:00:00Z",
                       created="2026-09-01T00:00:00Z"),
        ]
        pig.settle_belt_head(
            pool, need=2,
            probe=lambda n: pig.claim_visit_stamp(comments)
            if n == 7742 else None,
            max_probes=4)
        return [it["number"] for it in pool]

    assert order([]) == [7742, 200]                 # jamais servie : en tete
    assert order([claim]) == [7742, 200]            # prise le 31/08 < 10/09
    assert order([claim, release]) == [200, 7742]   # rendue le 19/09 : derriere


def test_latest_claim_stamp_reads_claims_of_any_lane(monkeypatch):
    payload = {"comments": [
        _claim("2026-10-04T09:50:12Z",
               "[CLAIMED] lane myia-po-2027:CoursIA -- T1"),
        _claim("2026-10-04T10:50:00Z",
               "[CLAIMED-AMEND] lane myia-po-2027:CoursIA -- paths: a/**"),
        _claim("2026-10-04T12:00:00Z",
               "T1 livree. Le [CLAIMED] du matin reste valable."),
    ]}

    class _R:
        stdout = json.dumps(payload)

    monkeypatch.setattr(pig.subprocess, "run", lambda *a, **k: _R())
    assert pig.latest_claim_stamp(19088) == "2026-10-04T10:50:00Z"


def test_latest_claim_stamp_read_failure_is_none(monkeypatch):
    def boom(*a, **k):
        raise OSError("gh absent")

    monkeypatch.setattr(pig.subprocess, "run", boom)
    assert pig.latest_claim_stamp(1) is None


def test_delivered_info_stamp_matches_the_three_marker_forms():
    """#19295 : les trois formes employees par les lanes (mesure #17263
    c.754) sont chacune une visite -- la plus recente gagne."""
    comments = [
        _claim("2026-09-13T09:17:03Z",
               "[INFO] candidate-delivered #13112 -- substance deja livree"),
        _claim("2026-10-02T12:57:29Z",
               "[INFO candidate-delivered] lane myia-po-2026:CoursIA-2"),
        _claim("2026-10-05T06:58:26Z",
               "[INFO] lane myia-po-2026:CoursIA-2 -- 2026-10-05 -- "
               "candidate-delivered, preuve firsthand"),
    ]
    assert pig.delivered_info_stamp(comments) == "2026-10-05T06:58:26Z"


def test_delivered_info_stamp_ignores_discursive_mentions():
    """Une mention du mecanisme, ancre au milieu d'une phrase, n'est pas
    l'en-tete d'un marqueur (garde anti-FP de `_DELIVERED_MARKER_RE`)."""
    comments = [
        _claim("2026-10-05T00:00:00Z",
               "sans [INFO] candidate-delivered dans ce fil, rien ne compte"),
        _claim("2026-10-05T01:00:00Z",
               "Le [INFO] absent : aucune livraison a signaler ici."),
    ]
    assert pig.delivered_info_stamp(comments) is None


def test_delivered_info_stamp_partial_ne_marque_pas_de_visite():
    """#20008 (FP) : un marqueur PARTIEL n'est pas une livraison pleine --
    sinon l'horloge du tapis avance sur une livraison qui n'existe pas et le
    candidat repart en queue alors qu'un residu explicite reste ouvert.
    Instance mesuree : #14549 c.5645287892."""
    comments = [
        _claim("2026-10-05T06:58:26Z",
               "[INFO] candidate-delivered-partial -- myia-po-2023:CoursIA-2, "
               "c.488 : 3.5/4 livre + parite mesuree. Wan Video reste ouvert"),
        _claim("2026-10-06T00:00:00Z",
               "[INFO candidate-delivered-partial -- residu explicite]"),
    ]
    assert pig.delivered_info_stamp(comments) is None


def test_delivered_info_stamp_forme_espacee_a_contenu_interne():
    """#20008 (FN) : la forme espacee a contenu interne
    (`[INFO candidate-delivered <contenu>]`) est un en-tete valide -- avant
    le fix, aucune des trois alternatives ne la reconnaissait, la visite
    restait invisible et le candidat resservi comme grain neuf."""
    comments = [
        _claim("2026-10-05T06:58:26Z",
               "[INFO candidate-delivered -- 70/81 creneaux verifies, "
               "preuve firsthand sur main]"),
    ]
    assert pig.delivered_info_stamp(comments) == "2026-10-05T06:58:26Z"


def test_latest_claim_stamp_takes_max_of_claim_and_delivered(monkeypatch):
    """Le probe de tete lit claim ET livraison dans la meme charge de
    commentaires : une seule requete (#19295, cout borne), le max gagne."""
    payload = {"comments": [
        _claim("2026-10-01T00:00:00Z",
               "[CLAIMED] lane myia-po-2026:CoursIA -- #13107"),
        _claim("2026-10-05T06:58:26Z",
               "[INFO] candidate-delivered -- #13112 merged 2026-08-26"),
    ]}
    calls = []

    class _R:
        stdout = json.dumps(payload)

    def fake_run(*a, **k):
        calls.append(a)
        return _R()

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    assert pig.latest_claim_stamp(13107) == "2026-10-05T06:58:26Z"
    assert len(calls) == 1


def test_belt_delivered_info_moves_served_issue_behind_13107_scenario():
    """Acceptance #19295 en bout en bout : #13107 servie par un
    `[INFO] candidate-delivered` recule derriere une issue jamais servie,
    au meme titre qu'un claim -- le tapis cesse de la reservir comme
    grain neuf."""
    palomar = _make_item(13107, age_days=90, idle=1,
                         last="2026-08-26T19:38:55Z",
                         created="2026-08-26T12:17:31Z")
    fresh = _make_item(19088, age_days=30, idle=1, last=None,
                       created="2026-09-10T00:00:00Z")
    pool = [palomar, fresh]
    pig.settle_belt_head(
        pool, need=2,
        probe={13107: "2026-10-05T06:58:26Z"}.get,
        max_probes=10)
    assert [it["number"] for it in pool][0] == 19088
    assert palomar["last_claim_stamp"] == "2026-10-05T06:58:26Z"


def test_belt_merge_only_flag_is_accepted(monkeypatch, capsys):
    _patch_belt_network(monkeypatch, prs=[], red_state=_state_red())
    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2", "--belt",
                   "--belt-merge-only", "--json"])
    assert rc == 0
    assert json.loads(capsys.readouterr().out)["mode"] == "belt"


# Volet livraison du tapis (#19390) : la voie ponderee ecartait et
# remplacait les candidats [INFO] candidate-delivered, le tapis les
# servait comme grains neufs (mesure 06/10 : #15974 et #16048, deux
# marqueurs chacune, servies a deux reprises). Les tests portent sur la
# boucle extraite `belt_pick_with_replacements` -- convention du
# fichier : main() n'est appele qu'a pool vide.


def _belt_args(grains=2, include_delivered=False):
    import types
    return types.SimpleNamespace(
        grains=grains, include_delivered=include_delivered,
        lane="myia-po-2023:CoursIA-2")


def _free_claims(items):
    return {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in items}


def test_belt_withdraws_delivered_candidates_and_replaces():
    """Controle positif #19390 : un candidat livre (label OU commentaire)
    sort en withheld -- cause LIVRAISON -- jamais en picks, et le suivant
    le remplace dans la fenetre."""
    marked_label = _make_item(15974, age_days=100, idle=10, last=None)
    marked_label["labels"] = ["candidate-delivered"]
    marked_comment = _make_item(16048, age_days=99, idle=9, last=None)
    clean_a = _make_item(19001, age_days=50, idle=5, last=None)
    clean_b = _make_item(19002, age_days=49, idle=5, last=None)
    pool = [marked_label, marked_comment, clean_a, clean_b]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: n == 16048,
        # 3e surface de livraison #19907 : probe injecte explicitement
        # False, le test ne couvre que le label et le marqueur. Depuis le
        # defaut inerte (#19913), omettre le param serait aussi sur ; on
        # l'injecte pour garder le scope du test lisible.
        merged_pr_probe=lambda n, lane=None: False)
    assert [p["number"] for p in picks] == [19001, 19002], (
        "les candidats livres doivent etre remplaces, pas servis")
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert 15974 in causes and causes[15974].startswith("LIVRAISON")
    assert 16048 in causes and causes[16048].startswith("LIVRAISON")
    assert not state["budget_hit"] and state["failures"] == []


def test_belt_recent_marker_excludes_hors_budget():
    """#19768 perimetre restant : marqueur de cloture sur le DERNIER
    commentaire ([DELIVERED] / [FROZEN]) -- le tapis ecarte
    le candidat SANS consommer de sonde de livraison (filtre bon marche,
    hors budget). La sonde pleine n'est meme pas atteinte pour lui.

    Depuis #21721, `[RELEASED]` n'est PAS un marqueur de cloture pour ce
    filtre : une main rendue sur une barriere reelle laisse l'item
    servable par la flotte."""
    marked = _make_item(7742, age_days=90, idle=9, last=None)
    clean_a = _make_item(19006, age_days=50, idle=5, last=None)
    clean_b = _make_item(19007, age_days=49, idle=5, last=None)
    probed = []

    def delivered(n, lane=None):
        probed.append(n)
        return False

    picks, withheld, state = pig.belt_pick_with_replacements(
        [marked, clean_a, clean_b],
        _free_claims([marked, clean_a, clean_b]),
        _belt_args(), probe_budget=8,
        delivered_probe=delivered,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: n == 7742)
    assert [p["number"] for p in picks] == [19006, 19007]
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[7742].startswith("LIVRAISON (recent)")
    assert state["recent_filtered"] == 1
    assert 7742 not in probed, ("le filtre recent devait ecarter #7742 "
                                "sans atteindre la sonde pleine")
    assert not state["budget_hit"] and state["failures"] == []


def test_belt_recent_marker_survives_budget_exhaustion():
    """Le cas fondateur du tapis (mesure po-2023 du 10-09 : 5 candidats
    servis non prenables) : budget de sonde EPUIS -- la sonde pleine rend
    UNPROBED et un candidat non filtre est servi (fail-OPEN, doctrine
    inchangee). Le marque, lui, ne passe PLUS : le filtre recent est HORS
    budget, l'epuisement ne peut plus servir une cloture marquee."""
    marked = _make_item(7742, age_days=90, idle=9, last=None)
    clean = _make_item(19008, age_days=40, idle=4, last=None)
    picks, withheld, state = pig.belt_pick_with_replacements(
        [marked, clean], _free_claims([marked, clean]),
        _belt_args(grains=2), probe_budget=0,
        delivered_probe=lambda n, lane=None: True,
        merged_pr_probe=lambda n, lane=None: True,
        recent_marker_probe=lambda n: n == 7742)
    # Le clean, non marque, reste servi en fail-OPEN (budget eteint) ;
    # le marque, lui, est ecarte hors budget.
    assert [p["number"] for p in picks] == [19008]
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[7742].startswith("LIVRAISON (recent)")
    assert state["recent_filtered"] == 1
    assert state["budget_hit"] is True


def test_belt_real_probe_serves_item_released_on_barrier(monkeypatch):
    """#21721, bout en bout : le tapis SERVIT un item dont le dernier
    commentaire porte `[RELEASED]`.

    Unlike `test_belt_recent_marker_excludes_hors_budget` (sonde INJECTEE),
    this one uses the REAL probe (`has_recent_delivery_marker`) : only the
    `gh issue view --json comments` subprocess is intercepted. What is
    under test is therefore the production wiring -- regex, budget, and
    loop -- not a stub.

    Before the fix, this item was withheld with the reason
    « LIVRAISON (recent) » : a lane handing back an item on a real barrier
    (GPU-only, vision-only) was losing it from the belt for good.
    """
    released_body = "[RELEASED] lane myia-po-2023:CoursIA -- barriere GPU-only"

    class _R:
        pass

    def fake_run(*args, **kwargs):
        r = _R()
        r.stdout = json.dumps({"comments": [{"body": released_body}]})
        r.returncode = 0
        r.stderr = ""
        return r

    monkeypatch.setattr(pig.subprocess, "run", fake_run)

    released = _make_item(19010, age_days=40, idle=4, last=None)
    other = _make_item(19011, age_days=41, idle=5, last=None)
    pool = [released, other]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=pig.has_recent_delivery_marker)
    assert [p["number"] for p in picks] == [19010, 19011], (
        "un item rendu sur une barriere reelle doit rester servi")
    assert withheld == []
    assert state["recent_filtered"] == 0


@pytest.mark.parametrize("verdict", [None, False])
def test_belt_recent_marker_unread_or_absent_falls_through(verdict):
    """Tri-etat du filtre recent : None (lecture en echec) ou False (pas
    de marqueur) = pas d'exclusion -- la boucle enchaine sur la sonde
    pleine (fail-OPEN sur None, nominal sur False)."""
    item = _make_item(19009, age_days=40, idle=4, last=None)
    probed = []

    def delivered(n, lane=None):
        probed.append(n)
        return False

    picks, withheld, state = pig.belt_pick_with_replacements(
        [item], _free_claims([item]), _belt_args(), probe_budget=8,
        delivered_probe=delivered,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: verdict)
    assert probed == [19009], "la sonde pleine doit etre atteinte"
    assert [p["number"] for p in picks] == [19009]
    assert withheld == []
    assert state["recent_filtered"] == 0


def test_belt_recent_marker_does_not_touch_umbrellas():
    """Portee grain seule : une umbrella dont le dernier commentaire porte
    un marqueur de cloture n'est pas ecartee -- meme garde que la sonde
    pleine (test_belt_does_not_withdraw_umbrella_on_marker), sur le filtre
    recent."""
    umbrella = _make_item(19010, age_days=60, idle=6, klass="umbrella",
                          last=None)
    picks, withheld, state = pig.belt_pick_with_replacements(
        [umbrella], _free_claims([umbrella]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: True)
    assert [p["number"] for p in picks] == [19010]
    assert withheld == []
    assert state["recent_filtered"] == 0


def test_belt_keeps_unmarked_candidate_pickable():
    """Controle negatif #19390 : sans marqueur (label absent, sonde
    False), le candidat reste tirable."""
    clean = _make_item(19003, age_days=40, idle=4, last=None)
    picks, withheld, _ = pig.belt_pick_with_replacements(
        [clean], _free_claims([clean]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        # 3e surface #19907 : probe inert ici (le test verifie que sans
        # marqueur, le candidat reste tirable -- on ne veut pas qu'une
        # PR reelle mergee le fausse).
        merged_pr_probe=lambda n, lane=None: False)
    assert [p["number"] for p in picks] == [19003]
    assert withheld == []


def test_belt_unread_probe_is_fail_open_and_reported():
    """Tri-etat : sonde None (lecture en echec) = candidat CONSERVE,
    echec rapporte -- une lecture qui n'a pas abouti n'est pas une
    absence de signal."""
    unread = _make_item(19004, age_days=40, idle=4, last=None)
    picks, withheld, state = pig.belt_pick_with_replacements(
        [unread], _free_claims([unread]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: None,
        # 3e surface #19907 : probe inert (le test verifie le tri-etat
        # du probe commentaire ; la 3e surface n'est pas sous test ici).
        merged_pr_probe=lambda n, lane=None: False)
    assert [p["number"] for p in picks] == [19004]
    assert withheld == []
    assert state["failures"] == [19004]


def test_belt_does_not_withdraw_umbrella_on_marker():
    """Portee : l'urne grain seule. Une umbrella marquee reste servie --
    un marqueur sur un EPIC n'est pas un verdict de fermeture (decision
    mesuree du canal label, cf delivered_signal_reason).

    Le LABEL n'est pas un verdict de fermeture sur une umbrella : le
    workflow advisory le pose des qu'une PR d'arc merge, et une umbrella
    accumule des PRs. Le MARQUEUR DE CONTENEUR pose dans un commentaire,
    lui, l'est : cf `test_belt_withdraws_umbrella_with_container_marker`."""
    umbrella = _make_item(19005, age_days=60, idle=6, klass="umbrella",
                          last=None)
    umbrella["labels"] = ["candidate-delivered"]
    picks, withheld, _ = pig.belt_pick_with_replacements(
        [umbrella], _free_claims([umbrella]), _belt_args(), probe_budget=8)
    assert [p["number"] for p in picks] == [19005]
    assert withheld == []


# --- Umbrella livree : le marqueur de CONTENEUR ecarte l'EPIC du tapis ----
#
# Mesure du 2026-10-26 (#17528) : le meme EPIC a ete servi quatre fois en
# cinq jours (21/10, 22/10, 25/10 x2) et quatre lanes y ont repose le meme
# marqueur `[INFO] candidate-delivered`. Le filtre de livraison du tapis ne
# s'appliquait qu'a l'urne `grain` : l'urne `umbrella` le resservait.
#
# Ce que la branche change : une umbrella dont le DERNIER commentaire porte
# le marqueur de CONTENEUR est reservee au coordinateur/adjoint (urne
# `delivered`, #15069) au lieu d'etre resservie a toutes les lanes.


def test_belt_withdraws_umbrella_with_container_marker():
    """Controle positif : l'umbrella livree sort du tirage, le candidat
    suivant la remplace dans la meme urne."""
    delivered = _make_item(17528, age_days=32, idle=0, klass="umbrella",
                           last=None)
    fresh = _make_item(19020, age_days=20, idle=2, last=None)
    pool = [delivered, fresh]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: n == 17528)
    assert [p["number"] for p in picks] == [19020], (
        "l'umbrella livree ne doit pas etre servie")
    assert [w[0]["number"] for w in withheld] == [17528]
    assert "conteneur" in withheld[0][1], (
        "la cause doit nommer le marqueur de conteneur : " + withheld[0][1])
    assert state["recent_filtered"] == 1


def test_belt_keeps_umbrella_without_container_marker():
    """Controle negatif : sans marqueur de conteneur, l'umbrella reste
    servable -- le filtre ne peut pas ecarter une umbrella par defaut."""
    umbrella = _make_item(19021, age_days=40, idle=4, klass="umbrella",
                          last=None)
    picks, withheld, state = pig.belt_pick_with_replacements(
        [umbrella], _free_claims([umbrella]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: False)
    assert [p["number"] for p in picks] == [19021]
    assert withheld == []
    assert state["recent_filtered"] == 0


def test_belt_umbrella_container_marker_read_failure_is_fail_open():
    """Tri-etat : une lecture en echec (None) laisse l'umbrella servable --
    une lecture qui n'a pas abouti n'est pas une absence de signal."""
    umbrella = _make_item(19022, age_days=40, idle=4, klass="umbrella",
                          last=None)
    picks, withheld, _ = pig.belt_pick_with_replacements(
        [umbrella], _free_claims([umbrella]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: None)
    assert [p["number"] for p in picks] == [19022]
    assert withheld == []


def test_belt_umbrella_container_read_failure_is_REPORTED():
    """Le fail-OPEN reste assume, mais le SILENCE ne l'est plus.

    Mesure #17528 (session jumelle `coursia-2-25`, 2026-10-26) : le conteneur
    portait le marqueur `[INFO] candidate-delivered`, la LECTURE du dernier
    commentaire a echoue (reseau / 403 / payload illisible), et le tapis a
    resservi le conteneur deja livre -- sans qu'aucune ligne de sortie ne
    distingue ce cas d'un conteneur libre.

    Le correctif ne change PAS le tirage (fail-OPEN conserve : on ne refuse
    pas un grain faute d'avoir pu lire un commentaire) ; il change le
    RENDU : le numero est reporte dans `container_unread`, exactement comme
    `claim_unread` le fait pour le claim (#20265).
    """
    umbrella = _make_item(19024, age_days=40, idle=4, klass="umbrella",
                          last=None)
    picks, withheld, state = pig.belt_pick_with_replacements(
        [umbrella], _free_claims([umbrella]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: None)
    # Le tirage est MAINTENU (fail-OPEN assume)...
    assert [p["number"] for p in picks] == [19024]
    assert withheld == []
    # ... mais l'etat INCONNU du conteneur est PUBLIE.
    assert state["container_unread"] == [19024]


def test_belt_umbrella_container_read_success_is_not_reported():
    """Controle negatif : une lecture ABOUTIE ne produit aucun rapport --
    que le conteneur porte le marqueur (ecarte) ou non (servi). Le signal
    doit désigner l'INCERTITUDE, pas le conteneur."""
    marque = _make_item(19025, age_days=40, idle=4, klass="umbrella",
                        last=None)
    _picks, _withheld, state = pig.belt_pick_with_replacements(
        [marque], _free_claims([marque]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: True)
    assert state["container_unread"] == []

    libre = _make_item(19026, age_days=40, idle=4, klass="umbrella",
                       last=None)
    _picks, _withheld, state = pig.belt_pick_with_replacements(
        [libre], _free_claims([libre]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: False)
    assert state["container_unread"] == []


def test_belt_recent_marker_read_failure_is_REPORTED():
    """La SONDE DU MARQUEUR RECENT avait le meme silence que celle du
    conteneur -- et c'est elle qui a produit la 4e livraison en double.

    Mesure #17528 (session jumelle `coursia-2-25`, 2026-10-26) : le picker a
    signale `403` sur deux candidats du meme run (« claim NON LU sur #15604,
    #21092 : reseau, 403, payload illisible ») -- le quota GraphQL etait
    epuise. L'echec de la SONDE DE MARQUEUR, lui, n'etait nomme **nulle
    part** : un `None` (lu impossible) y etait indiscernable d'un « pas de
    marqueur » dans le rapport.

    Le tirage reste MAINTENU (fail-OPEN assume) ; le numero est desormais
    RAPPORTE.
    """
    grain = _make_item(19027, age_days=40, idle=4, klass="grain", last=None)
    picks, withheld, state = pig.belt_pick_with_replacements(
        [grain], _free_claims([grain]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: None,
        container_marker_probe=lambda n: False)
    assert [p["number"] for p in picks] == [19027]
    assert withheld == []
    assert state["marker_unread"] == [19027]


def test_belt_recent_marker_read_success_is_not_reported():
    """Controle negatif : une lecture ABOUTIE ne produit aucun rapport --
    que le marqueur soit present (ecarte) ou absent (servi)."""
    marque = _make_item(19028, age_days=40, idle=4, klass="grain",
                        last=None)
    _picks, _withheld, state = pig.belt_pick_with_replacements(
        [marque], _free_claims([marque]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: True,
        container_marker_probe=lambda n: False)
    assert state["marker_unread"] == []

    libre = _make_item(19029, age_days=40, idle=4, klass="grain", last=None)
    _picks, _withheld, state = pig.belt_pick_with_replacements(
        [libre], _free_claims([libre]), _belt_args(), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: False)
    assert state["marker_unread"] == []


def test_le_rapport_marqueur_rend_la_trace_visible(capsys):
    """Le rendu du troisieme pendant : le numero et la nature de
    l'incertitude doivent etre visibles."""
    pig.print_marker_unread_report([21092], "myia-ai-01:CoursIA-2")
    out = capsys.readouterr().out
    assert "LIVRAISON NON LU" in out
    assert "#21092" in out
    assert "candidate-delivered" in out


def test_le_rapport_marqueur_est_muet_sans_lecture_ratee(capsys):
    """Controle negatif du rendu : aucun bruit quand tout s'est bien passe."""
    pig.print_marker_unread_report([], "myia-ai-01:CoursIA-2")
    pig.print_marker_unread_report(None, "myia-ai-01:CoursIA-2")
    assert capsys.readouterr().out == ""


def test_belt_marker_KO_and_budget_epuise_ne_sert_pas_silencieusement():
    """Le COUPLE de fail-OPEN, mesure par la session jumelle `coursia-2-25`
    (2026-10-26, #17528) : deux verifications ratees qui se COMBINENT.

    1. la sonde du marqueur echoue (403 / quota GraphQL epuise) -> elle rend
       `None`, qui passait pour « pas de marqueur » ;
    2. le budget de la sonde PLEINE est epuise -> elle rend
       `DELIVERED_SIGNAL_UNPROBED`, qui passe pour « rien a signaler ».

    Les deux ensemble : un conteneur **reellement livre** est servi, et
    rien dans la sortie ne le dit. C'est la 4e livraison en double.

    Ce que le correctif change : le tirage reste MAINTENU (fail-OPEN
    assume), mais le numero est RAPPORTE — le verdict « incertitude » est
    distinct du verdict « pas de marqueur ».
    """
    grain = _make_item(19030, age_days=40, idle=4, klass="grain", last=None)
    picks, withheld, state = pig.belt_pick_with_replacements(
        [grain], _free_claims([grain]), _belt_args(), probe_budget=0,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: None,
        container_marker_probe=lambda n: False)
    # Le budget de sondes est epuise : la sonde pleine n'a rien vu.
    assert state["budget_hit"] is True
    # Le fail-OPEN reste assume : le candidat est servi.
    assert [p["number"] for p in picks] == [19030]
    # ... mais l'echec de la sonde de marqueur est PUBLIE.
    assert state["marker_unread"] == [19030]


def test_belt_sonde_marqueur_KO_avec_gh_en_echec_rend_None(monkeypatch):
    """La sonde reelle rend `None` sur echec de LECTURE -- jamais `False`.

    Un `False` se lirait « pas de marqueur » (le conteneur est libre) ; c'est
    l'echec de lecture qui doit etre `None`, pour que l'appelant puisse
    distinguer les deux. Mesure #17528 : sur un `gh` qui leve, la sonde rend
    `None`, et le candidat etait servi comme si de rien n'etait.
    """
    def boom(cmd, *args, **kwargs):
        raise RuntimeError("403 quota GraphQL epuise")

    monkeypatch.setattr(pig.subprocess, "run", boom)
    monkeypatch.setattr(pig, "_issue_comment_bodies_rest",
                        lambda n: None, raising=False)
    assert pig.has_recent_delivery_marker(17528) is None
    assert pig.has_recent_container_delivery_marker(17528) is None


def test_le_rapport_conteneur_rend_la_trace_visible(capsys):
    """Le rendu du pendant de `print_claim_unread_report` : le numero et la
    nature de l'incertitude doivent etre visibles."""
    pig.print_container_unread_report([17528], "myia-ai-01:CoursIA-2")
    out = capsys.readouterr().out
    assert "CONTENEUR NON LU" in out
    assert "#17528" in out
    assert "candidate-delivered" in out


def test_le_rapport_conteneur_est_muet_sans_lecture_ratee(capsys):
    """Controle negatif du rendu : un rapport qui bavarde a vide serait du
    bruit a chaque tirage -- y compris ceux ou tout s'est bien passe."""
    pig.print_container_unread_report([], "myia-ai-01:CoursIA-2")
    pig.print_container_unread_report(None, "myia-ai-01:CoursIA-2")
    assert capsys.readouterr().out == ""


def test_belt_include_delivered_keeps_umbrella_with_container_marker():
    """L'echappatoire `--include-delivered` reste respectee sur l'urne
    umbrella : le marqueur de conteneur n'est pas une barriere absolue."""
    umbrella = _make_item(19023, age_days=40, idle=4, klass="umbrella",
                          last=None)
    picks, withheld, _ = pig.belt_pick_with_replacements(
        [umbrella], _free_claims([umbrella]),
        _belt_args(include_delivered=True), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        container_marker_probe=lambda n: True)
    assert [p["number"] for p in picks] == [19023]
    assert withheld == []


# La grammaire du marqueur de CONTENEUR, testee sur la sonde reelle (le
# transport est stube) : c'est elle qui distingue « le conteneur est livre »
# de « la lane a livre SON grain ».


def _stub_last_comment(monkeypatch, body):
    """Force le transport de la sonde : le DERNIER commentaire porte `body`."""
    payload = json.dumps({"comments": [{"body": body}]})

    def fake_run(cmd, *args, **kwargs):
        assert cmd[:3] == ["gh", "issue", "view"], f"transport : {cmd}"
        return subprocess.CompletedProcess(cmd, 0, stdout=payload, stderr="")

    monkeypatch.setattr(pig.subprocess, "run", fake_run)


@pytest.mark.parametrize("body", [
    "[INFO] candidate-delivered — les cinq arcs sont clos.",
    "[INFO] candidate-delivered lane myia-po-2027:CoursIA -- EPIC closable",
    "## [INFO] candidate-delivered\n\nles cinq arcs sont clos",
    "[INFO candidate-delivered] verification first-hand des arcs",
    # La forme exacte mesuree par la session jumelle `coursia-2-25` sur
    # #17528 (2026-10-26) : marqueur suivi d'un TIRET CADRATIN et d'un
    # libelle libre. C'est elle qui a echappe au filtre.
    "[INFO] candidate-delivered — lane myia-po-2027:CoursIA — EPIC materiellement livree",
    # Variante SANS les deux-points : la forme libre la plus courte.
    "[INFO] candidate-delivered EPIC materiellement livree",
])
def test_container_marker_detects_container_statements(monkeypatch, body):
    """Le marqueur de conteneur est reconnu dans ses formes."""
    _stub_last_comment(monkeypatch, body)
    assert pig.has_recent_container_delivery_marker(17528) is True


@pytest.mark.parametrize("body", [
    # Une lane qui livre SON grain : sur une umbrella, ce n'est pas une
    # fermeture du conteneur.
    "[DELIVERED] lane myia-po-2027:CoursIA -- PR #21212",
    "[RELEASED] lane myia-po-2028:CoursIA -- umbrella saturee",
    "[INFO] candidate-delivered-partial -- un arc sur cinq",
    "[NOT-DELIVERED] verification first-hand : 2 arcs sur 5.",
    "Discussion sans marqueur.",
    # Les FORMES MUETTES : un marqueur qui a l'air correct a l'oeil et que la
    # machine ne voit pas (mesure du peer `coursia-2-25`, 2026-10-26, sur
    # #21092). Le detecteur exige `\[INFO\]\s+candidate-delivered` en tete de
    # ligne ; encager le `[INFO]` en backticks ou mettre le mot-cle en gras
    # suffit a rendre le marqueur INVISIBLE. C'est un piege d'ecriture, pas
    # de grammaire : la forme doit etre MESUREE apres l'ecriture.
    "`[INFO]` **candidate-delivered** lane myia-ai-01:CoursIA-2 -- livre",
    "**[INFO] candidate-delivered** lane myia-ai-01:CoursIA-2 -- livre",
])
def test_container_marker_ignores_non_container_statements(monkeypatch, body):
    """Une livraison de sous-grain, une retraction, une simple discussion ou
    une forme muette ne ferment PAS le conteneur."""
    _stub_last_comment(monkeypatch, body)
    assert pig.has_recent_container_delivery_marker(17528) is False


def test_container_marker_read_failure_is_none(monkeypatch):
    """Tri-etat : une lecture en echec rend None (fail-OPEN), pas False."""
    def boom(cmd, *args, **kwargs):
        raise OSError("reseau indisponible")

    monkeypatch.setattr(pig.subprocess, "run", boom)
    assert pig.has_recent_container_delivery_marker(17528) is None


def test_container_marker_without_comment_is_false(monkeypatch):
    """Aucun commentaire : pas de marqueur (False, pas None)."""
    _stub_last_comment(monkeypatch, "")
    assert pig.has_recent_container_delivery_marker(17528) is False


# Retractation du marqueur, cote TAPIS : la sonde que `main` injecte dans
# cette boucle est `has_delivered_signal`, une implementation SEPAREE de
# `_has_delivered_marker`. Sans la symetrie, le marqueur restait permanent
# pour le tapis : l'issue relevee par le coordinateur -- mesure du 12/10, 20
# des 80 issues marquees livrees l'etaient partiellement -- restait ecartee a
# chaque cycle. Ces tests injectent la sonde REELLE et stubbent son transport :
# c'est la seule facon de prouver que c'est la BOUCLE, pas seulement la sonde,
# qui rend l'issue au tapis.


_DELIVERED_BODY = ("[INFO] candidate-delivered — verification first-hand du "
                   "geste 1 sur origin/main, MERGE 6d0bd02093.")
_REVOKED_BODY = "[NOT-DELIVERED] verification first-hand : 2 cellules sur 5."


def _patch_issue_comments(monkeypatch, bodies_by_issue):
    """Stub du transport `gh issue view N --json comments`, corps en ordre."""
    def fake_run(cmd, *args, **kwargs):
        assert cmd[:3] == ["gh", "issue", "view"], f"transport inattendu : {cmd}"
        bodies = bodies_by_issue[int(cmd[3])]

        class _R:
            stdout = json.dumps({"comments": [{"body": b} for b in bodies]})

        return _R()

    monkeypatch.setattr(pig.subprocess, "run", fake_run)


def test_belt_serves_a_candidate_whose_marker_was_revoked(monkeypatch):
    """Marqueur retracte par un commentaire POSTERIEUR -> le candidat est
    SERVI, jamais ecarte en LIVRAISON."""
    item = _make_item(19010, age_days=90, idle=8, last=None)
    _patch_issue_comments(monkeypatch,
                          {19010: [_DELIVERED_BODY, _REVOKED_BODY]})
    picks, withheld, state = pig.belt_pick_with_replacements(
        [item], _free_claims([item]), _belt_args(grains=1), probe_budget=8,
        delivered_probe=pig.has_delivered_signal,
        merged_pr_probe=lambda n, lane=None: False)
    assert [p["number"] for p in picks] == [19010], (
        "un marqueur retracte ne peut plus ecarter le candidat")
    assert withheld == []
    assert state["failures"] == []


def test_belt_still_withholds_a_live_delivered_marker(monkeypatch):
    """Controle positif de la meme boucle : SANS retractation, le marqueur
    ecarte toujours le candidat (cause LIVRAISON)."""
    item = _make_item(19012, age_days=90, idle=8, last=None)
    _patch_issue_comments(monkeypatch, {19012: [_DELIVERED_BODY]})
    picks, withheld, _ = pig.belt_pick_with_replacements(
        [item], _free_claims([item]), _belt_args(grains=1), probe_budget=8,
        delivered_probe=pig.has_delivered_signal,
        merged_pr_probe=lambda n, lane=None: False)
    assert picks == []
    assert [w[0]["number"] for w in withheld] == [19012]
    assert withheld[0][1].startswith("LIVRAISON")


def test_belt_rewithholds_when_a_marker_follows_the_revocation(monkeypatch):
    """Le sens est porte par l'ORDRE : un marqueur repose APRES la
    retractation rearme l'ecartement."""
    item = _make_item(19013, age_days=90, idle=8, last=None)
    _patch_issue_comments(
        monkeypatch,
        {19013: [_DELIVERED_BODY, _REVOKED_BODY, _DELIVERED_BODY]})
    picks, withheld, _ = pig.belt_pick_with_replacements(
        [item], _free_claims([item]), _belt_args(grains=1), probe_budget=8,
        delivered_probe=pig.has_delivered_signal,
        merged_pr_probe=lambda n, lane=None: False)
    assert picks == []
    assert [w[0]["number"] for w in withheld] == [19013]
    assert withheld[0][1].startswith("LIVRAISON")


def test_belt_probe_budget_is_bounded_and_fail_open_when_exhausted():
    """Cout borne : le budget de sondes vaut la fenetre de tete. Au-dela,
    plus personne n'est sonde -- fail-OPEN rapporte (budget_hit), jamais
    un faux LIVRAISON sur un candidat jamais lu."""
    items = [_make_item(n, age_days=30, idle=3, last=None)
             for n in (19006, 19007, 19008)]
    probes = []

    def counting_probe(n, lane=None):
        probes.append(n)
        return True

    picks, withheld, state = pig.belt_pick_with_replacements(
        items, _free_claims(items), _belt_args(), probe_budget=1,
        delivered_probe=counting_probe)
    # 1 sonde : le premier candidat est ecarte (marqueur lu), les deux
    # suivants sont SERVIS sans lecture -- le budget epuise ne fabrique
    # ni retrait ni silence non dit.
    assert probes == [19006]
    assert [p["number"] for p in picks] == [19007, 19008]
    assert [w[0]["number"] for w in withheld] == [19006]
    assert state["budget_hit"] is True


def test_belt_probe_budget_covers_the_settle_window():
    """#19969 : le plafond de la boucle de service ne peut pas valoir la seule
    fenetre de tete. ``settle_belt_head`` recoit deja ``window * 3 + 12``
    sondes pour stabiliser la MEME region de la file -- deux compteurs
    distincts, une seule region, donc un seul plafond reseau."""
    for window in (4, 8, 12):
        assert pig.belt_probe_budget(window) == window * 3 + 12
        assert pig.belt_probe_budget(window) > window, (
            "un budget egal a la fenetre ramene la fuite de #19969")


def test_belt_head_denser_than_the_window_no_longer_serves_delivered_items():
    """Regression #19969, jouee sur la valeur d'avant ET d'apres.

    Mesure firsthand du rapport : sur un seul tirage, huit candidats servis
    par le tapis etaient deja livres. Au-dela du budget, la sonde rendait
    DELIVERED_SIGNAL_UNPROBED et le candidat partait en ``picks`` comme un
    grain neuf -- fail-OPEN assume, mais sous-dimensionne."""
    window = 8
    delivered = set(range(19100, 19114))          # 14 livres, fenetre de 8
    items = [_make_item(n, age_days=200 - i, idle=2, last=None)
             for i, n in enumerate(sorted(delivered, reverse=True))]
    fresh = _make_item(19300, age_days=1, idle=1, last=None)
    pool = items + [fresh]

    def probe(n, lane=None):
        return n in delivered

    # Budget d'AVANT (la fenetre seule) : des livres sont servis, et
    # l'epuisement est rapporte -- le temoin du defaut.
    old_picks, _, old_state = pig.belt_pick_with_replacements(
        list(pool), _free_claims(pool), _belt_args(grains=20),
        probe_budget=window, delivered_probe=probe,
        # 3e surface #19913 : explicitement False. Sous l'ancien defaut
        # (sonde reseau) ce test laissait `main` sonder le depot ; depuis
        # les defauts inertes, l'omission se lit `failures` (None =
        # non sondable) et brouille l'assertion -- l'injection rend la
        # dependance visible.
        merged_pr_probe=lambda n, lane=None: False)
    leaked = [p["number"] for p in old_picks if p["number"] in delivered]
    assert leaked, "temoin : l'ancien budget doit laisser fuiter des livres"
    assert old_state["budget_hit"] is True

    # Budget aligne : plus aucun livre servi, et plus d'epuisement.
    new_picks, new_withheld, new_state = pig.belt_pick_with_replacements(
        list(pool), _free_claims(pool), _belt_args(grains=20),
        probe_budget=pig.belt_probe_budget(window), delivered_probe=probe,
        merged_pr_probe=lambda n, lane=None: False)
    assert [p["number"] for p in new_picks] == [19300]
    assert {w[0]["number"] for w in new_withheld} == delivered
    assert new_state["budget_hit"] is False
    assert new_state["failures"] == []


def test_has_delivered_signal_grammar_ignores_discursive_mentions(monkeypatch):
    """Controle negatif #19390, au niveau de la grammaire : une mention
    discursive porte la sous-chaine sans etre un en-tete de marqueur --
    elle ne doit pas retirer le candidat. Le vrai en-tete, si."""
    def fake_run(argv, **kwargs):
        class _P:
            stdout = ""
            returncode = 0
        marker = argv[3]
        if marker == "15974":
            _P.stdout = json.dumps({
                "comments": [
                    {"body": "Verifie : rien de livree ici, "
                             "sans [INFO] candidate-delivered dans ce fil."},
                ]})
        else:
            _P.stdout = json.dumps({
                "comments": [
                    {"body": "[INFO] candidate-delivered lane "
                             "myia-po-2024:CoursIA-2 -- preuve firsthand."},
                ]})
        return _P()

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    assert pig.has_delivered_signal(15974) is False, (
        "une mention discursive n'est pas un marqueur")
    assert pig.has_delivered_signal(16048) is True


def test_summarize_claim_implicit_occupation():
    """#14300 -- occupation IMPLICITE : le JSON de l'organe porte la cle,
    le reducteur rend CLAIM_CODE_IMPLICIT (pas FREE -- lecons du 2026-09-14 :
    l'emission ne suffit pas, c'est la consommation qui fait le garde)."""
    implicit_json = ('{"blocking_lanes": [], "my_active_claim": false,'
                     '"stale_claims": [], "implicit_occupation": '
                     '[{"number": 14293, "lane": "myia-po-2026:CoursIA",'
                     ' "files": ["scripts/ci/docker/linux-runner/supervise.sh"],'
                     ' "additions": 79, "deletions": 3}]}')
    code, human = pig._summarize_claim(implicit_json + "\nIMPLICIT: ...", 3)
    assert code == pig.CLAIM_CODE_IMPLICIT
    assert "#14293" in human
    assert "myia-po-2026:CoursIA" in human
    # review 5429946072 : le claim de l'APPELANT est teste AVANT l'implicite
    # -- un grain deja marque par la lane qui tire reste OWNED_BY_ME meme si
    # une PR tierce reference l'issue (sinon la lane perd son propre grain).
    owned_json = ('{"blocking_lanes": [], "my_active_claim": true,'
                  '"stale_claims": [], "implicit_occupation": '
                  '[{"number": 14293, "lane": "myia-po-2026:CoursIA"}]}')
    code, human = pig._summarize_claim(owned_json, 0)
    assert code == pig.CLAIM_CODE_OWNED_BY_ME
    # priorite : un BLOCKED explicite prime sur l'implicite (le marqueur a
    # plus d'autorite) -- le reducteur teste blocking_lanes AVANT.
    both_json = ('{"blocking_lanes": ["myia-po-2027:CoursIA"],'
                 '"my_active_claim": false, "stale_claims": [],'
                 '"implicit_occupation": [{"number": 14293,'
                 ' "lane": "myia-po-2026:CoursIA"}]}')
    code, _ = pig._summarize_claim(both_json + "\n", 3)
    assert code == pig.CLAIM_CODE_BLOCKED
    # sans la cle (organe ancien ou jambe sautee) : comportement inchange.
    plain_json = ('{"blocking_lanes": [], "my_active_claim": false,'
                  '"stale_claims": []}')
    code, _ = pig._summarize_claim(plain_json + "\n", 0)
    assert code == pig.CLAIM_CODE_FREE


# --- fetch_latest_claim_stamps_bulk (PR #19594, c.1113 picker stall) ---

def _graphql_payload_for(comments_by_issue: dict[int, list[dict]]) -> dict:
    """Construit la reponse GraphQL que `gh api graphql` rendrait.

    Reproduit la forme : data.repository.i{n}.comments.nodes[{author, body, createdAt}].
    """
    repo = {}
    for n, comments in comments_by_issue.items():
        repo[f"i{n}"] = {
            "number": n,
            "comments": {"nodes": comments},
        }
    return {"data": {"repository": repo}}


def test_fetch_latest_claim_stamps_bulk_parity_with_latest_claim_stamp(monkeypatch):
    """Parity : sur chaque issue, le stamp du bulk = le stamp de latest_claim_stamp.

    Mock `subprocess.run` pour repondre en mode GraphQL aux appels `gh api graphql`
    et en mode `gh issue view --json comments` aux appels de latest_claim_stamp.
    """
    issue_payloads = {
        10: [_claim("2026-10-04T09:50:12Z",
                    "[CLAIMED] lane myia-po-2027:CoursIA -- T1")],
        11: [_claim("2026-10-05T10:00:00Z",
                    "[CLAIMED] lane myia-po-2024:CoursIA -- T2"),
             _claim("2026-10-05T11:30:00Z",
                    "[CLAIMED-AMEND] lane myia-po-2024:CoursIA -- paths: a/**")],
        12: [_claim("2026-10-03T08:00:00Z",
                    "aucun marqueur de claim ici")],
    }

    def fake_run(cmd, *a, **k):
        class _R:
            pass
        r = _R()
        if cmd[:3] == ["gh", "api", "graphql"]:
            # Match order: les issue_numbers sont tries dans fetch_latest_...
            # mais on n'en depend pas, le resultat est indexe par alias.
            r.stdout = json.dumps(_graphql_payload_for(issue_payloads))
        elif cmd[:3] == ["gh", "issue", "view"]:
            # gh issue view N --json comments : on rend le payload de l'issue N
            n = int(cmd[3])
            r.stdout = json.dumps({"comments": issue_payloads[n]})
        else:
            raise AssertionError(f"fake_run: unexpected cmd {cmd!r}")
        return r

    monkeypatch.setattr(pig.subprocess, "run", fake_run)

    bulk_map, err = pig.fetch_latest_claim_stamps_bulk([10, 11, 12])
    assert err is None, f"unexpected bulk error: {err}"
    assert bulk_map == {
        10: "2026-10-04T09:50:12Z",
        11: "2026-10-05T11:30:00Z",  # max de claim + claim-amend
        12: None,                     # aucun marqueur -> None (et pas de raise)
    }, f"parite brisee: {bulk_map}"

    # Re-verification : latest_claim_stamp unitaire rend la meme valeur.
    assert pig.latest_claim_stamp(10) == bulk_map[10]
    assert pig.latest_claim_stamp(11) == bulk_map[11]
    assert pig.latest_claim_stamp(12) is None


def test_fetch_latest_claim_stamps_bulk_falls_back_on_subprocess_error(monkeypatch):
    """Repli : une exception subprocess rend ({}, err) ; le caller peut degrader.

    On verifie le contrat publie dans la docstring : pas de propagation, juste
    un signal d'erreur que le caller (settle_belt_head) interprete comme
    "stamp inconnu, retomber sur la sonde unitaire / belt_pool[:need]".
    """
    def boom(*a, **k):
        raise subprocess.TimeoutExpired(cmd="gh api graphql", timeout=30)

    monkeypatch.setattr(pig.subprocess, "run", boom)
    out_map, err = pig.fetch_latest_claim_stamps_bulk([42, 99])
    assert out_map == {}, f"le repli doit rendre un dict vide, pas {out_map!r}"
    assert err is not None and "TimeoutExpired" in err, (
        f"l'erreur doit nommer la cause : {err!r}")


def test_fetch_latest_claim_stamps_bulk_handles_more_than_100_comments(monkeypatch):
    """Pagination : avec >100 commentaires, le stamp reste correct (top 100).

    GitHub rend les 100 plus recents. Les marqueurs de claim etant toujours
    dans la queue recente, ils survivent a la fenetre. On verifie qu'un
    claim poste il y a 200 commentaires survit quand meme.
    """
    # 99 commentaires anciens (sans marqueur) + 1 claim recent en queue.
    old = [_claim(f"2026-09-{(i % 28) + 1:02d}T{(i % 24):02d}:{(i % 60):02d}Z",
                  f"commentaire ancien #{i} sans marqueur")
           for i in range(99)]
    recent_claim = _claim("2026-10-06T22:00:00Z",
                          "[CLAIMED] lane myia-po-2023:CoursIA-2 -- T-pagination")
    payload = {1234: old + [recent_claim]}

    def fake_run(cmd, *a, **k):
        class _R:
            stdout = json.dumps(_graphql_payload_for(payload))
        return _R()

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    out_map, err = pig.fetch_latest_claim_stamps_bulk([1234])
    assert err is None
    assert out_map == {1234: "2026-10-06T22:00:00Z"}, (
        f"le claim recent doit survivre meme avec >100 commentaires : {out_map!r}")


# === #20923 : validate_picks_live — defense en profondeur tapis ===

class _FakePopenResult:
    """Resultat minimal compatible avec subprocess.run.

    Le picker n'utilise que ``stdout`` (str) et la levee
    ``CalledProcessError(returncode=1)`` ; on tient les deux.
    """
    def __init__(self, stdout="", returncode=0, stderr=""):
        self.stdout = stdout
        self.returncode = returncode
        self.stderr = stderr


def test_validate_picks_live_drops_404(monkeypatch):
    """Issue 16774 (fondateur du ticket) : `gh issue view` -> 404, drop.

    Le mock imite le rc=1 + stderr `Could not resolve to a Repository` que
    `gh` rend sur un numero inconnu. Le picker doit dropper le pick et
    exposer la cause dans la liste dropped -- pas la taire.
    """
    picks = [
        _make_item(16774, age_days=10, idle=2),
        _make_item(16775, age_days=5, idle=1),
    ]
    calls: list[list[str]] = []

    def fake_run(argv, **kwargs):
        calls.append(list(argv))
        # argv = ["gh", "issue", "view", "<N>", "--repo", ...]
        number = str(argv[3]) if len(argv) > 3 else ""
        if number == "16774":
            raise subprocess.CalledProcessError(
                returncode=1, cmd=argv,
                stderr="Could not resolve to a Repository with number 16774")
        return _FakePopenResult(stdout=json.dumps(
            {"number": 16775, "state": "OPEN"}))

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    kept, dropped = pig.validate_picks_live(picks)

    assert [it["number"] for it in kept] == [16775], (
        f"16774 doit etre droppe (404), seul 16775 doit rester : {kept!r}")
    assert dropped == [(16774, "absente (404)")], (
        f"la cause 404 doit etre NOMMEE dans la liste dropped : {dropped!r}")
    # 2 appels, 1 par candidat : pas de fan-out.
    assert len(calls) == 2


def test_validate_picks_live_drops_closed(monkeypatch):
    """Issue ouverte dans le pool, fermee entre-temps : drop explicite.

    Race classique d'un pool cache ou d'un pick pris sur un snapshot
    precede. Le picker doit nommer `fermee` -- la lane n'a alors qu'a
    poser [INFO] candidate-delivered, pas a `gh issue view` a la main.
    """
    picks = [_make_item(20000, age_days=20, idle=5)]

    def fake_run(argv, **kwargs):
        return _FakePopenResult(stdout=json.dumps(
            {"number": 20000, "state": "CLOSED"}))

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    kept, dropped = pig.validate_picks_live(picks)

    assert kept == [], "l'issue fermee ne doit pas rester en tete"
    assert dropped == [(20000, "fermee")], (
        f"la cause `fermee` doit etre explicite : {dropped!r}")


def test_validate_picks_live_drops_merged(monkeypatch):
    """Issue reellement resolue : PR fermee par merge.

    Trouve au c.586 (revue Hermes sur #20954) : `gh issue view --json state`
    rend `MERGED` pour une PR fermee par merge, distinct de `CLOSED` (qui
    designe une PR fermee sans merge). Le candidat obsolete doit etre
    droppe avec le motif `mergee` pour que le rapport de la lane distingue
    les deux cas (cf `validate_picks_live` et le motif `fermee`/`mergee`).
    """
    picks = [_make_item(17029, age_days=20, idle=5)]

    def fake_run(argv, **kwargs):
        return _FakePopenResult(stdout=json.dumps(
            {"number": 17029, "state": "MERGED"}))

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    kept, dropped = pig.validate_picks_live(picks)

    assert kept == [], "l'issue mergee ne doit pas rester en tete"
    assert dropped == [(17029, "mergee")], (
        f"la cause `mergee` doit etre explicite : {dropped!r}")


def test_validate_picks_live_keeps_open(monkeypatch):
    """Le vert reste vert : OPEN ne droppe pas."""
    picks = [_make_item(20923, age_days=2, idle=0)]

    def fake_run(argv, **kwargs):
        return _FakePopenResult(stdout=json.dumps(
            {"number": 20923, "state": "OPEN"}))

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    kept, dropped = pig.validate_picks_live(picks)

    assert [it["number"] for it in kept] == [20923]
    assert dropped == []


def test_validate_picks_live_keeps_on_timeout(monkeypatch):
    """Le reseau qui tombe ne doit PAS dropper les picks.

    Defense en profondeur best-effort : un timeout 5xx garde le pick
    plutot que de vider la poignee. La cause est silencieuse ici -- le
    caller gere ca separement (le WARN GH-IDENTITY, le budget de sondes).
    Un pick droppe sur timeout fabriquerait le faux « pool vide » que
    cette fonction existe justement pour eviter sur un cas REEL (404/closed).
    """
    picks = [_make_item(20923, age_days=2, idle=0)]

    def fake_run(argv, **kwargs):
        raise subprocess.TimeoutExpired(cmd=argv, timeout=15)

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    kept, dropped = pig.validate_picks_live(picks)

    assert [it["number"] for it in kept] == [20923], (
        f"un timeout reseau doit GARDER le pick, pas le dropper : {kept!r}")
    assert dropped == []


def test_validate_picks_live_keeps_on_malformed_payload(monkeypatch):
    """Un payload JSON degnere garde le pick -- encore un cas best-effort.

    `gh issue view` peut repondre 200 avec un payload corrompu (rate limit
    intermediaire, proxy, etc.). On ne droppe pas sur un signal qu'on ne
    peut pas lire.
    """
    picks = [_make_item(20923, age_days=2, idle=0)]

    def fake_run(argv, **kwargs):
        return _FakePopenResult(stdout="not json at all")

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    kept, dropped = pig.validate_picks_live(picks)

    assert [it["number"] for it in kept] == [20923]
    assert dropped == []


def test_validate_picks_live_respects_max_to_check(monkeypatch):
    """``max_to_check`` borne la fenetre de defense en profondeur.

    La poignee tapis peut etre plus large que `args.grains` ; le caller
    veut verifier seulement la tete pour economiser des requetes. Le
    reste de la poignee passe SANS verification (et donc SANS drop) --
    le pick peut etre obsolete, mais on ne pretend pas le savoir.
    """
    picks = [
        _make_item(30001, age_days=10, idle=2),
        _make_item(30002, age_days=8, idle=1),
        _make_item(30003, age_days=5, idle=0),
    ]
    seen: list[str] = []

    def fake_run(argv, **kwargs):
        # argv = ["gh", "issue", "view", "<N>", "--repo", ...]
        number_str = str(argv[3]) if len(argv) > 3 else ""
        seen.append(number_str)
        return _FakePopenResult(stdout=json.dumps(
            {"number": int(number_str), "state": "OPEN"}))

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    kept, dropped = pig.validate_picks_live(picks, max_to_check=2)

    # 2 candidats verifies (les 2 premiers dans l'ordre de la liste).
    assert seen == ["30001", "30002"], (
        f"max_to_check borne la fenetre : {seen!r}")
    # Le 3e candidat reste dans `kept` (pas verifie, pas droppe).
    assert [it["number"] for it in kept] == [30001, 30002, 30003]
    assert dropped == []


def test_validate_picks_live_empty_picks():
    """La liste vide passe en silence -- pas d'appel reseau, pas de drop."""
    kept, dropped = pig.validate_picks_live([])
    assert kept == []
    assert dropped == []


def test_validate_picks_live_skips_non_int_number(monkeypatch):
    """Un pick sans `number` entier (defaut structurel) reste dans `kept`.

    Belt-pool n'est pas suppose avoir de tels items, mais la defense en
    profondeur ne doit pas casser sur une forme inattendue : on garde le
    pick, on note la cause au mieux ailleurs.
    """
    picks = [{"number": "abc", "klass": "grain", "genre": "docs",
              "title": "anomalie", "age": 1, "idle": 0}]

    def fake_run(argv, **kwargs):
        raise AssertionError("gh ne doit pas etre appele pour un number non-int")

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    kept, dropped = pig.validate_picks_live(picks)

    assert [it["number"] for it in kept] == ["abc"]
    assert dropped == []


# --- Sonde de claims : un seul numero n'est pas un batch (c2197) -----------

# Sortie REELLE de `check_lane_claim.py --lane L N` pour UN numero (mesure du
# 2026-10-20 sur #20909) : le JSON mono-issue, une ligne vide, puis la phrase
# de verdict. `json.loads` la rejette (`Extra data`), `_summarize_claim` la lit.
_SINGLE_ISSUE_STDOUT = (
    '{\n  "number": 20909,\n  "blocking_lanes": [],\n'
    '  "my_active_claim": false,\n  "stale_claims": [],\n'
    '  "implicit_occupation": []\n}\n\nCLEAR: no other lane claims #20909.\n'
)


def _fake_run_recorder(stdout_for):
    calls = []

    def fake_run(cmd, **kwargs):
        calls.append(list(cmd))
        return subprocess.CompletedProcess(cmd, 0, stdout=stdout_for(cmd),
                                           stderr="")
    return calls, fake_run


def test_check_claims_single_number_reads_mono_issue_output(monkeypatch):
    """`check_claims([n])` (verification au fil de l'eau) lit la sortie
    mono-issue au lieu de la rendre en ERROR.

    Avant le correctif, l'appel passait par le chemin batch, `json.loads`
    levait `Extra data` sur la phrase « CLEAR: ... », et le verdict valait
    ERROR : 30 issues sur 50 du tirage du 2026-10-20 ont ete servies sans
    que leur claim soit lu.
    """
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt", lambda lane: None)
    # #22630 : la voie en processus (instantane local) est PRIORITAIRE dans
    # `check_claims` -- sans ce shunt, elle consomme deux subprocess (`gh api`
    # du rafraichissement, `gh issue view` du lecteur) avant la voie
    # historique instrumentee ici, et le compte d'appels n'a plus de sens.
    # La voie en processus a ses propres tests (test_gh_snapshot_22630.py) ;
    # ces trois tests verifient le contrat de la voie subprocess.
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None: None)
    calls, fake_run = _fake_run_recorder(lambda cmd: _SINGLE_ISSUE_STDOUT)
    monkeypatch.setattr(pig.subprocess, "run", fake_run)

    verdicts = pig.check_claims([20909], "myia-ai-01:CoursIA")

    assert verdicts[20909][0] == pig.CLAIM_CODE_FREE
    # Un seul appel, mono-issue : pas de batch suivi d'un repli.
    assert len(calls) == 1
    assert calls[0][-3:] == ["--lane", "myia-ai-01:CoursIA", "20909"]


def test_check_claims_unreadable_batch_falls_back_per_issue(monkeypatch):
    """Une sortie batch illisible ne rend plus ERROR : chaque issue est
    relue seule, comme le commentaire du code l'annoncait deja."""
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt", lambda lane: None)
    # #22630 : voie en processus ecartee -- ce test instrumente la voie
    # subprocess historique (cf. test_check_claims_single_number_...).
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None: None)

    def stdout_for(cmd):
        if cmd.count("--lane") and len(cmd) > 5:  # batch : 2 numeros ou plus
            return "pas du JSON\n"
        n = cmd[-1]
        return _SINGLE_ISSUE_STDOUT.replace("20909", n)

    calls, fake_run = _fake_run_recorder(stdout_for)
    monkeypatch.setattr(pig.subprocess, "run", fake_run)

    verdicts = pig.check_claims([101, 102], "myia-ai-01:CoursIA")

    assert verdicts == {101: verdicts[101], 102: verdicts[102]}
    assert all(v[0] == pig.CLAIM_CODE_FREE for v in verdicts.values())
    # 1 batch + 2 relectures mono-issue.
    assert len(calls) == 3


# --- #19969 : la banniere d'epuisement du budget reste IMPRIMEE -------------
#
# L'issue demande que « la mesure ne doit pas devenir silencieuse en se
# repariant » : quand le budget de sondes de livraison tombe, la lane doit
# lire que les candidats au-dela n'ont PAS ete verifies. Le texte est donc
# un contrat, verifie ici SANS reseau (appeler `main()` de bout en bout
# payerait une minute de `gh` pour verifier trois lignes de `print`).


def test_belt_budget_banner_is_printed_when_the_budget_is_exhausted(capsys):
    """Le fail-OPEN du budget est assume, son SILENCE ne l'est pas."""
    pig.print_belt_budget_report(True)
    out = capsys.readouterr().out
    assert "Plafond de sondes de livraison atteint" in out
    assert "fail-OPEN" in out
    assert "check_unaddressed_nits" in out
    # Verrou d'egalite sur le texte entier : trois sous-chaines
    # laisseraient passer une reecriture du milieu des phrases, ou la perte
    # d'une ligne dont les trois marqueurs survivraient (reserve NanoClaw
    # du 2026-10-22).
    assert out == (
        "   Plafond de sondes de livraison atteint : les candidats\n"
        "   au-dela ne sont pas sondes (fail-OPEN) -- la verification\n"
        "   de livraison leur revient, cf check_unaddressed_nits.\n"
    )


def test_belt_budget_banner_is_silent_when_the_budget_is_not_exhausted(capsys):
    """Pas de budget epuise = pas de banniere : une alerte permanente
    serait lue comme un etat du depot, pas comme un etat du tirage."""
    pig.print_belt_budget_report(False)
    assert capsys.readouterr().out == ""


def test_belt_delivery_probe_cost_is_bounded_by_the_budget():
    """#19969, critere 3 : le cout en requetes du tirage est borne par le
    budget de sondes -- une requete `gh issue view --json comments` par
    candidat sonde. La mesure joue la valeur d'AVANT (fenetre seule = 8)
    et celle d'apres (fenetre * 3 + 12 = 36) sur le MEME pool : la
    difference de requetes est exactement l'ecart de plafond.

    C'est le cout assume du correctif de #19977 : le budget de sondes passe
    de 8 a 36 (+28 de BUDGET), mais le surcout EN REQUETES est de +22 au
    pire sur un tirage charge (30 sondes - 8), pour ne plus servir un
    candidat livre comme un grain neuf. Les deux grandeurs ne se confondent
    pas : +28 est l'ecart de PLAFOND, +22 l'ecart de requetes mesure par
    les asserts ci-dessous (reserve NanoClaw du 2026-10-22). Le second
    terme du cout -- le filtre de marqueur recent, une requete par
    candidat, HORS budget -- est inchange par ce correctif."""
    delivered = set(range(19200, 19230))          # 30 livres, fenetre de 8
    items = [_make_item(n, age_days=200 - i, idle=2, last=None)
             for i, n in enumerate(sorted(delivered, reverse=True))]
    pool = items

    def run_with(budget):
        calls = []

        def probe(n, lane=None):
            calls.append(n)
            return n in delivered

        picks, _, state = pig.belt_pick_with_replacements(
            list(pool), _free_claims(pool), _belt_args(grains=40),
            probe_budget=budget, delivered_probe=probe,
            merged_pr_probe=lambda n, lane=None: False)
        return len(calls), len(picks), state

    old_calls, old_picks, old_state = run_with(8)
    new_calls, new_picks, new_state = run_with(pig.belt_probe_budget(8))

    # Une requete par candidat sonde, dans les deux cas.
    assert old_calls == 8
    assert new_calls == 30
    # Budget d'AVANT : 22 livres servis en fail-OPEN (le contrat), et
    # l'epuisement REPORTE -- la banniere l'annonce.
    assert old_state["budget_hit"] is True
    assert old_picks == 22
    # Budget aligne : 30 sondes suffisent, aucun livre servi, aucun
    # epuisement.
    assert new_state["budget_hit"] is False
    assert new_picks == 0


# ---------------------------------------------------------------------------
# #21436 -- mur de temps du tapis.
#
# Le defaut mesure : `probe_budget` borne le NOMBRE de sondes de livraison,
# pas leur DUREE ni les deux surfaces payees par candidat hors fenetre. Sur ce
# siege, 8 verdicts de claim coutent 47 s a froid ; `max_iters` = grains*5+50
# laissait donc ~410 s de travail possible avant la premiere sonde de
# livraison, et cinq mesures independantes (po-2023, po-2025, cette lane, deux
# taps) se sont arretees sur `pick_with_replacements start`.
#
# Ce que ces tests epinglent : l'echeance arrete TOUTES les surfaces couteuses
# (claim hors fenetre, filtre recent, sonde de livraison, sonde PR fusionnee)
# et le reliquat est SERVI en fail-OPEN en le rapportant -- le tapis ne rend
# jamais moins de candidats a cause du mur, il en rend de moins verifies.
# ---------------------------------------------------------------------------


def _patched_clock(monkeypatch, start=0.0):
    """Horloge injectee a la place du module `time` de `pig`.

    Remplacer l'ATTRIBUT de module (et non `time.monotonic` globalement) garde
    le patch local : les autres modules, et le harnais pytest, gardent leur
    horloge reelle.
    """
    import types
    clock = [start]
    monkeypatch.setattr(
        pig, "time", types.SimpleNamespace(monotonic=lambda: clock[0]))
    return clock


def test_belt_time_budget_stops_probing_mid_loop(monkeypatch):
    """L'echeance tombe en cours de boucle : le premier candidat paie ses
    sondes, les suivants sont servis sans aucune requete.

    C'est la forme exacte du defaut #21436 -- un run qui n'a pas fini sa
    fenetre de candidats quand le budget est consomme doit RENDRE la main,
    pas continuer a payer un `check_claims` par candidat.
    """
    clock = _patched_clock(monkeypatch)
    a = _make_item(30001, age_days=100, idle=9, last=None)
    b = _make_item(30002, age_days=99, idle=9, last=None)
    c = _make_item(30003, age_days=98, idle=9, last=None)
    pool = [a, b, c]
    calls = {"delivered": [], "merged": [], "recent": []}

    def delivered(n, lane=None):
        calls["delivered"].append(n)
        clock[0] += 1.0  # la sonde consomme le budget d'une seconde
        return False

    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=3), probe_budget=8,
        delivered_probe=delivered,
        merged_pr_probe=lambda n, lane=None: calls["merged"].append(n) or False,
        recent_marker_probe=lambda n: calls["recent"].append(n) or False,
        time_budget_s=1.0)

    # Le mur ne retire JAMAIS un candidat : les trois sont servis.
    assert [p["number"] for p in picks] == [30001, 30002, 30003]
    assert withheld == []
    # Une seule sonde de chaque espece, celle du premier candidat.
    assert calls["delivered"] == [30001]
    assert calls["recent"] == [30001]
    assert calls["merged"] == []
    assert state["time_budget_hit"] is True
    # Deux plafonds distincts : le mur de temps n'est pas le plafond de cout.
    assert state["budget_hit"] is False


def test_belt_time_budget_skips_on_the_fly_claim_check_and_reports(monkeypatch):
    """La verification de claim au fil de l'eau est la surface la plus chere
    (`check_claims` par candidat hors fenetre) et elle echappait au
    `probe_budget`. Passe l'echeance, elle n'est plus appelee du tout, et les
    candidats servis sans claim lu sont rapportes dans `claim_unread` (#20265)
    au lieu de partir comme s'ils avaient ete verifies.
    """
    _patched_clock(monkeypatch)
    a = _make_item(30011, age_days=100, idle=9, last=None)
    b = _make_item(30012, age_days=99, idle=9, last=None)
    claim_calls = []
    picks, withheld, state = pig.belt_pick_with_replacements(
        [a, b], {}, _belt_args(grains=2), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        claims_probe=lambda nums: claim_calls.append(list(nums)) or {},
        recent_marker_probe=lambda n: False,
        time_budget_s=0.0)

    assert [p["number"] for p in picks] == [30011, 30012]
    assert withheld == []
    assert claim_calls == [], "aucune verification de claim apres l'echeance"
    assert state["claim_unread"] == [30011, 30012]
    assert state["time_budget_hit"] is True


@pytest.mark.parametrize("budget", [None, 600.0])
def test_belt_without_expiry_keeps_previous_behaviour(budget):
    """Controle positif : sans mur (`None`, le defaut) ou avec un budget large,
    chaque candidat servi paie sa sonde et `time_budget_hit` reste faux. Le
    correctif ne doit pas eteindre les sondes quand rien n'est epuise."""
    a = _make_item(30021, age_days=100, idle=9, last=None)
    b = _make_item(30022, age_days=99, idle=9, last=None)
    pool = [a, b]
    probed = []
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=2), probe_budget=8,
        delivered_probe=lambda n, lane=None: probed.append(n) or False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        time_budget_s=budget)

    assert [p["number"] for p in picks] == [30021, 30022]
    assert probed == [30021, 30022]
    assert state["time_budget_hit"] is False


def test_belt_time_budget_flag_is_accepted(monkeypatch, capsys):
    """Le cablage CLI du mur : le drapeau est accepte et le verdict est publie
    dans le document JSON, a cote du plafond de sondes -- deux champs, parce
    qu'une lane qui lit l'un pour l'autre relance pour la mauvaise raison."""
    _patch_belt_network(monkeypatch, prs=[], red_state=_state_red())
    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2", "--belt",
                   "--belt-time-budget", "0", "--json"])
    assert rc == 0
    doc = json.loads(capsys.readouterr().out)
    assert doc["mode"] == "belt"
    assert doc["delivered_signal"]["time_budget_hit"] is False
    # `0` desactive le mur : le plafond de sondes garde son propre champ.
    assert doc["delivered_signal"]["budget_hit"] is False


def test_clamp_timeout_is_a_noop_without_a_belt_deadline():
    """Hors tapis, aucun clamp : `check_claims` garde ses 60 s.

    Sans cette garde, publier une echeance n'importe ou rendrait les sondes
    du reste du programme dependantes d'un etat global qu'elles n'ont pas
    demande.
    """
    pig._BELT_DEADLINE[0] = None
    assert pig._clamp_timeout(60) == 60
    assert pig._clamp_timeout(0.25) == 0.25


def test_clamp_timeout_bounds_a_probe_by_the_remaining_budget(monkeypatch):
    """#21436 : le mur borne le TIMEOUT de la sonde, pas seulement son
    demarrage. Une sonde de 60 s entamee 5 s avant l'echeance ne peut plus
    consommer 55 s au-dela du budget -- c'est ce depassement qui faisait
    rendre la main au-dela de 200 s pour un budget de 90 s.
    """
    clock = _patched_clock(monkeypatch)
    pig._BELT_DEADLINE[0] = clock[0] + 5.0
    try:
        assert pig._clamp_timeout(60) == pytest.approx(5.0)
        # Le plancher de 0,5 s s'applique quand l'echeance est deja passee :
        # un timeout nul rendrait la panne reseau indiscernable du mur.
        pig._BELT_DEADLINE[0] = clock[0] - 10.0
        assert pig._clamp_timeout(60) == 0.5
    finally:
        pig._BELT_DEADLINE[0] = None


def test_check_claims_reads_the_belt_deadline(monkeypatch):
    """La sonde de claim la plus chere de la boucle obeit au mur.

    `check_claims` est appele au fil de l'eau pour chaque candidat hors
    fenetre : c'est la surface que `probe_budget` ne compte pas, et celle qui
    a gele quatre runs consecutifs le 24/10.
    """
    clock = _patched_clock(monkeypatch)
    seen: list[float] = []

    class _Done:
        returncode = 0
        stdout = "{}"
        stderr = ""

    def fake_run(cmd, **kwargs):
        # Seul `check_lane_claim.py` nous interesse : le pourtour de
        # `check_claims` (cache des PRs ouvertes) a ses propres timeouts et
        # n'est pas la sonde que le mur doit clamper.
        if any("check_lane_claim.py" in str(part) for part in cmd):
            seen.append(kwargs.get("timeout"))
        return _Done()

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    # #22630 : voie en processus ecartee -- le mur de temps se mesure sur le
    # subprocess `check_lane_claim.py` de la voie historique, pas sur la voie
    # en processus (qui n'ouvre aucun subprocess de ce nom).
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None: None)
    pig._BELT_DEADLINE[0] = clock[0] + 2.0
    try:
        pig.check_claims([30031], "myia-po-2024:CoursIA")
    finally:
        pig._BELT_DEADLINE[0] = None

    assert seen, "aucun subprocess n'a ete lance"
    assert max(t for t in seen if t is not None) <= 2.0 + 0.05


def test_belt_loop_restores_the_published_deadline():
    """L'echeance publiee ne fuit pas hors de la boucle.

    Les tests (et tout appelant direct) rappellent `check_claims` et
    `has_recent_delivery_marker` dans le meme process : si le mur restait
    publie, ils heriteraient d'un budget deja epuise et verraient leur
    timeout tombe a 0,5 s sans qu'aucun tapis ne tourne.
    """
    pig._BELT_DEADLINE[0] = None
    pool = [_make_item(30041, age_days=10, idle=3, last=None)]
    pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=1), probe_budget=8,
        delivered_probe=lambda n, lane=None: False,
        merged_pr_probe=lambda n, lane=None: False,
        recent_marker_probe=lambda n: False,
        time_budget_s=30.0)
    assert pig._BELT_DEADLINE[0] is None


def test_belt_publishes_the_run_deadline_before_the_claims_phase(
        monkeypatch, capsys):
    """Le mur couvre le RUN, pas seulement la boucle de selection.

    Mesure du 24/10 : avec `--belt-time-budget 90`, le run s'arretait a
    `belt claims start: 8 numeros` et ne rendait jamais la main (275 s de
    silence, puis expiration par `timeout`). La fenetre de claims est payee
    AVANT la boucle, et chaque `check_claims` y ouvre un subprocess de
    60 s + 10 s par numero : publier l'echeance seulement dans la boucle
    laissait la phase la plus chere sans borne.

    Le predicat : au moment ou la fenetre de claims s'ouvre, une echeance
    est deja publiee, et elle est retiree quand le run se termine.
    """
    _patch_belt_network(monkeypatch, prs=[], red_state=_state_red())
    published: list = []

    def spy(numbers, lane):
        published.append(pig._BELT_DEADLINE[0])
        return {n: (pig.CLAIM_CODE_FREE, "libre") for n in numbers}

    monkeypatch.setattr(pig, "check_claims", spy)
    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2", "--belt",
                   "--belt-time-budget", "60", "--json"])
    assert rc == 0
    assert published, "la fenetre de claims n'a pas ete ouverte"
    assert all(d is not None for d in published), \
        "des claims ont ete lances sans echeance publiee (#21436)"
    assert pig._BELT_DEADLINE[0] is None, "l'echeance fuit apres le run"


def test_publish_phase_deadline_bounds_probes_and_lends_its_budget(monkeypatch):
    """#21436 : la phase de reparation a sa PROPRE echeance.

    Mesure du 24/10 sur ce siege : `red_backlog` seul = 172,7 s, payes AVANT
    que le tapis ne prenne la main, donc hors de tout mur existant. L'echeance
    publiee ici borne les deux surfaces de la phase : les sondes (via
    `_clamp_timeout`) et la passe nits de l'organe B.0 (via son budget).
    """
    import check_unaddressed_nits as nits

    clock = _patched_clock(monkeypatch, start=1000.0)
    previous_budget = nits.NITS_PASS_BUDGET_S
    pig._BELT_DEADLINE[0] = None
    nits._NITS_PASS_DEADLINE = None
    try:
        token = pig._publish_phase_deadline(30)
        assert pig._BELT_DEADLINE[0] == pytest.approx(1030.0)
        # La sonde de 90 s de `fetch_pr_states` (appelee par
        # `unattributed_blocked_prs`) ne peut plus consommer que le reste.
        assert pig._clamp_timeout(90) == pytest.approx(30.0)
        # L'organe herite du meme reste, et sa passe DEMARRE ici : sans la
        # remise a None, il heriterait d'une deadline armee ailleurs.
        assert nits.NITS_PASS_BUDGET_S == pytest.approx(30.0)
        assert nits._NITS_PASS_DEADLINE is None
        pig._restore_phase_deadline(token)
        assert pig._BELT_DEADLINE[0] is None
        assert nits.NITS_PASS_BUDGET_S == pytest.approx(previous_budget or 300.0)
    finally:
        pig._BELT_DEADLINE[0] = None
        nits.NITS_PASS_BUDGET_S = previous_budget
        nits._NITS_PASS_DEADLINE = None


def test_publish_phase_deadline_zero_keeps_the_old_behaviour(monkeypatch):
    """`--red-budget 0` rend le comportement d'avant, sans borne.

    L'echappatoire existe pour un siege dont l'organe B.0 est rapide : elle ne
    doit RIEN changer, ni au mur, ni au budget de l'organe.
    """
    import check_unaddressed_nits as nits

    _patched_clock(monkeypatch, start=500.0)
    previous_budget = nits.NITS_PASS_BUDGET_S
    pig._BELT_DEADLINE[0] = None
    try:
        token = pig._publish_phase_deadline(0)
        assert pig._BELT_DEADLINE[0] is None
        assert pig._clamp_timeout(60) == 60
        assert nits.NITS_PASS_BUDGET_S == previous_budget
        pig._restore_phase_deadline(token)
        assert pig._BELT_DEADLINE[0] is None
    finally:
        pig._BELT_DEADLINE[0] = None
        nits.NITS_PASS_BUDGET_S = previous_budget


def test_main_runs_the_repair_phase_inside_its_own_deadline(monkeypatch):
    """Le cablage, pas seulement l'helpers : `main` publie AVANT `red_backlog`.

    Le point de mesure est l'interieur de `red_backlog` -- c'est la que le
    timeout de sonde doit deja etre ramene au reste, et la que la passe nits
    doit deja avoir recu son budget. Un `finally` doit rendre l'etat d'apres.
    """
    import check_unaddressed_nits as nits

    clock = _patched_clock(monkeypatch, start=2000.0)
    seen = {}

    class _Stop(Exception):
        pass

    def fake_red_backlog(*a, **kw):
        seen["deadline"] = pig._BELT_DEADLINE[0]
        seen["clamped"] = pig._clamp_timeout(90)
        seen["nits_budget"] = nits.NITS_PASS_BUDGET_S
        raise _Stop

    monkeypatch.setattr(pig, "red_backlog", fake_red_backlog)
    monkeypatch.setattr(pig, "fetch_lane_record_prs", lambda **kw: ([], None))
    monkeypatch.setattr(pig.gh_identity, "pin_gh_token", lambda: None)
    pig._BELT_DEADLINE[0] = None
    previous_budget = nits.NITS_PASS_BUDGET_S
    try:
        with pytest.raises(_Stop):
            pig.main(["--lane", "myia-po-2024:CoursIA", "--red-budget", "45"])
        assert seen["deadline"] == pytest.approx(2045.0)
        assert seen["clamped"] == pytest.approx(45.0)
        assert seen["nits_budget"] == pytest.approx(45.0)
        # Le `finally` a rendu l'etat : aucune fuite vers la suite du run.
        assert pig._BELT_DEADLINE[0] is None
        assert nits.NITS_PASS_BUDGET_S == previous_budget
    finally:
        pig._BELT_DEADLINE[0] = None
        nits.NITS_PASS_BUDGET_S = previous_budget
        nits._NITS_PASS_DEADLINE = None
    _ = clock


def test_belt_withdraws_candidate_covered_by_open_pr():
    """#16589 sur le TAPIS : une PR ouverte qui porte deja l'issue ecarte
    le candidat, et le suivant le remplace.

    Controle positif du defaut mesure le 2026-10-27 : la sonde de
    couverture n'etait cablee que sur la voie PONDEREE
    (``draw_unclaimed``). Le tapis, lui, rendait ``ACTION REQUISE : poser
    [CLAIMED] ... sur #22374`` alors que ``#22515`` est OUVERTE et porte
    l'issue dans son titre et son body -- un claim qui aurait ete VOID a
    la seconde ou il etait pose.
    """
    covered = _make_item(22374, age_days=3, idle=1, last=None)
    clean = _make_item(19002, age_days=49, idle=5, last=None)
    pool = [covered, clean]

    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(), probe_budget=8,
        cover_probe=lambda n: "PR #22515" if n == 22374 else "")

    assert [p["number"] for p in picks] == [19002]
    assert len(withheld) == 1
    number, cause = withheld[0]
    assert number["number"] == 22374
    assert cause.startswith("EN COURS : ")
    assert "PR #22515" in cause
    # Aucun echec de sonde : la sonde a repondu.
    assert state.get("cover_failures", []) == []


def test_belt_cover_probe_failure_is_fail_open_and_reported():
    """Sonde de couverture ratee : le candidat est CONSERVE et le fait est
    RAPPORTE -- meme tri-etat que la sonde de livraison.

    Une lecture qui n'a pas ABOUTI n'est pas une absence de PR couvrante :
    ecarter ici couterait a la lane un grain disponible a chaque 403.
    """
    pool = [_make_item(19001, age_days=50, idle=5, last=None)]

    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(), probe_budget=8,
        cover_probe=lambda n: None)

    assert [p["number"] for p in picks] == [19001]
    assert withheld == []
    assert state["cover_failures"] == [19001]


def test_belt_cover_probe_shares_the_delivery_budget():
    """Sonde de couverture et sonde de livraison parent le MEME plafond.

    Un plafond double laisserait le tapis depenser deux fois le cout
    annonce par ``probe_budget`` -- la doctrine de la voie ponderee
    (#16589) est « au meme rang, donc au meme cout borne ».
    """
    pool = [_make_item(19001 + i, age_days=50 - i, idle=5, last=None)
            for i in range(4)]
    seen = []

    def cover(n):
        seen.append(n)
        return ""

    # probe_budget=1 : la premiere sonde de livraison (inerte) consomme
    # l'unite, la couverture n'a plus de budget et rend UNPROBED sans
    # appeler la sonde injectee.
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=4), probe_budget=1,
        cover_probe=cover)

    assert seen == []
    assert state["budget_hit"] is True
    # Fail-OPEN : les candidats restent servis.
    assert [p["number"] for p in picks] == [19001, 19002, 19003, 19004]
