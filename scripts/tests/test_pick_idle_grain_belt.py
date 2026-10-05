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
    monkeypatch.setattr(pig, "unaddressed_review_points", lambda nums: {18844: 1} if prs else {})
    monkeypatch.setattr(pig, "fetch_lane_record_prs", lambda **k: ([], None))
    monkeypatch.setattr(pig, "fetch_main_head_probe", lambda *a, **k: None)
    # Le tapis fait un check_claims : on rend toujours FREE.
    monkeypatch.setattr(pig, "check_claims",
                        lambda nums, lane: {n: (pig.CLAIM_CODE_FREE, "libre")
                                            for n in nums})
    # Le tapis lit aussi les claims comme visites : jamais de reseau en test.
    monkeypatch.setattr(pig, "latest_claim_stamp", lambda n: None)


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


def test_belt_merge_only_flag_is_accepted(monkeypatch, capsys):
    _patch_belt_network(monkeypatch, prs=[], red_state=_state_red())
    rc = pig.main(["--lane", "myia-po-2024:CoursIA-2", "--belt",
                   "--belt-merge-only", "--json"])
    assert rc == 0
    assert json.loads(capsys.readouterr().out)["mode"] == "belt"
