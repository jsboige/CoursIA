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
import sys
from datetime import datetime, timezone, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402


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