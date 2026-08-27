"""Tests for scripts/pick_idle_grain.py recent_delivery (#12174).

Un detecteur se valide par ses faux negatifs, pas par ses hits. Le cas
fondateur (2026-08-21) : #12014 tiree en urne grain a 16:47Z alors que
#12077, mergee a 16:19Z, avait deja livre 3 de ses 4 items -- le label
``candidate-delivered`` (workflow schedule: quotidien, dernier run 05:49Z)
n'en savait rien. Le replay ci-dessous rejoue cet etat exact.

Second angle mort, ferme le 2026-08-24 (#12504, rapporte par
myia-po-2023:CoursIA) : ne regarder que les PRs MERGEES laissait passer
les issues couvertes par une PR encore OUVERTE, qui ne portent aucune
trace -- ni label, ni body a jour, ni fusion a trouver. #12504 est
sortie en tete d'urne (p=2.0) alors que #12519 la couvrait ; la lane qui
l'a prise a pose un claim void. Une PR ouverte prime une fusion recente :
la fusion dit "c'est peut-etre fait", l'ouverte dit "quelqu'un y est".
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402


class _FakeCompleted:
    def __init__(self, stdout):
        self.stdout = stdout


def _patch_gh(monkeypatch, payloads, calls):
    """payloads : liste (dans l'ordre des candidats) de listes de PRs JSON."""
    def fake_run(cmd, **kwargs):
        calls.append(cmd)
        return _FakeCompleted(json.dumps(payloads[len(calls) - 1]))
    monkeypatch.setattr(pig.subprocess, "run", fake_run)


def _pick(n=12014, updated_at="2026-08-21T05:13:00Z"):
    return {"number": n, "klass": "grain", "updated_at": updated_at,
            "title": "founding case", "age": 30, "idle": 0,
            "genre": "slides", "weight": 1.0}


def test_founding_case_12014_surfaces_12077(monkeypatch):
    """#12174 controle positif : le tirage du 2026-08-21 doit nommer #12077.

    Issue non touchee depuis 05:13Z, PR mergee 16:19:17Z -- l'ecart que le
    label quotidien ne pouvait pas voir.
    """
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "state": "MERGED", "mergedAt": "2026-08-21T16:19:17Z"},
    ]], calls)
    notes = pig.recent_delivery([_pick()])
    assert 12014 in notes
    assert "#12077" in notes[12014]
    assert "16:19:17Z" in notes[12014]
    assert "05:13:00Z" in notes[12014]
    assert "confronter le body au reel" in notes[12014]


def test_query_shape_bounded_one_per_candidate(monkeypatch):
    """Cout borne : exactement une requete par candidat tire, jamais le pool.

    La commande doit chercher les PRs MERGEES referencant le numero
    (troisieme surface de grounding, cf #12174).
    """
    calls = []
    _patch_gh(monkeypatch, [[], []], calls)
    pig.recent_delivery([_pick(n=1), _pick(n=2)])
    assert len(calls) == 2
    for cmd, n in zip(calls, (1, 2)):
        # --state all depuis #12504 : ouvertes ET mergees dans la MEME
        # requete, donc l'invariant "une par candidat" tient toujours.
        assert "--state" in cmd and "all" in cmd
        assert "--limit" in cmd and "20" in cmd
        assert "--search" in cmd
        assert cmd[cmd.index("--search") + 1] == f"{n} in:title,body"


def test_merge_older_than_update_not_annotated(monkeypatch):
    """Une fusion ANTERIEURE a la derniere activite de l'issue est deja
    digeree par le body -- pas d'annotation, sinon le signal noie."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "state": "MERGED", "mergedAt": "2026-08-21T04:00:00Z"},
    ]], calls)
    notes = pig.recent_delivery([_pick(updated_at="2026-08-21T05:13:00Z")])
    assert notes == {}


def test_no_merged_pr_no_note(monkeypatch):
    calls = []
    _patch_gh(monkeypatch, [[]], calls)
    assert pig.recent_delivery([_pick()]) == {}


def test_candidate_stays_drawable(monkeypatch):
    """L'annotation informe, elle n'ecarte pas (parite candidate-delivered) :
    la fonction rend des notes, les picks passes ne sont ni filtres ni mutés."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "state": "MERGED", "mergedAt": "2026-08-21T16:19:17Z"},
    ]], calls)
    picks = [_pick()]
    snapshot = dict(picks[0])
    notes = pig.recent_delivery(picks)
    assert len(picks) == 1 and picks[0] == snapshot
    assert 12014 in notes  # annote ET toujours la, tirable


def test_multiple_prs_latest_named_with_count(monkeypatch):
    """Plusieurs PRs mergees referencent le numero : la plus recente porte la
    note, le compte evite de lire 'la livraison' comme l'unique."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "state": "MERGED", "mergedAt": "2026-08-21T16:19:17Z"},
        {"number": 12065, "state": "MERGED", "mergedAt": "2026-08-20T10:00:00Z"},
    ]], calls)
    notes = pig.recent_delivery([_pick()])
    assert "#12077" in notes[12014]
    assert "(+1 autres)" in notes[12014]
    assert "#12065" not in notes[12014]


def test_gh_failure_annotated_best_effort(monkeypatch):
    """Echec gh : l'absence d'annotation ne doit pas se lire comme 'aucune
    livraison verifiee'."""
    def boom(cmd, **kwargs):
        raise pig.subprocess.TimeoutExpired(cmd, 30)
    monkeypatch.setattr(pig.subprocess, "run", boom)
    notes = pig.recent_delivery([_pick()])
    assert "indisponible" in notes[12014]
    assert "TimeoutExpired" in notes[12014]


# --- PR OUVERTE couvrante (#12504, rapporte 2026-08-24) --------------------
#
# Le detecteur precedent se validait sur ses faux negatifs cote FUSION. Il en
# gardait un cote OUVERTURE, plus couteux : une fusion fait perdre du temps de
# lecture, une PR ouverte fait perdre un claim. Chaque test nomme le defaut
# qu'il empeche de revenir.


def test_founding_case_12504_open_pr_surfaces_12519(monkeypatch):
    """Controle positif : #12504 tiree en tete d'urne le 2026-08-24 alors que
    #12519 (OUVERTE, po-2026) la couvrait -- claim void de la lane suivante."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12519, "state": "OPEN", "isDraft": False, "mergedAt": None},
    ]], calls)
    notes = pig.recent_delivery([_pick(n=12504)])
    assert 12504 in notes
    assert notes[12504].startswith("TRAVAIL EN COURS")
    assert "#12519" in notes[12504]
    assert "VOID" in notes[12504]


def test_open_pr_annotated_even_when_issue_freshly_updated(monkeypatch):
    """Une PR ouverte est courante par construction : contrairement a une
    fusion, elle n'est PAS comparee a ``updated_at``. Une issue touchee il y a
    une minute peut tres bien etre en cours de traitement par une autre lane."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12519, "state": "OPEN", "isDraft": False, "mergedAt": None},
    ]], calls)
    notes = pig.recent_delivery([_pick(n=12504, updated_at="2099-01-01T00:00:00Z")])
    assert 12504 in notes and notes[12504].startswith("TRAVAIL EN COURS")


def test_open_pr_takes_priority_over_recent_merge(monkeypatch):
    """Les deux signaux coexistent souvent (une tranche livree, une en cours).
    L'ouverte gagne : elle dit ou est le risque de collision maintenant."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "state": "MERGED", "isDraft": False,
         "mergedAt": "2026-08-21T16:19:17Z"},
        {"number": 12519, "state": "OPEN", "isDraft": False, "mergedAt": None},
    ]], calls)
    notes = pig.recent_delivery([_pick()])
    assert notes[12014].startswith("TRAVAIL EN COURS")
    assert "#12519" in notes[12014]


def test_closed_unmerged_pr_is_not_a_signal(monkeypatch):
    """Sur-accusation a empecher : une PR fermee SANS fusion n'atteste de rien
    (abandon, doublon dispose). La compter en 'travail en cours' enverrait la
    lane chercher une collision inexistante."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12638, "state": "CLOSED", "isDraft": False, "mergedAt": None},
    ]], calls)
    assert pig.recent_delivery([_pick()]) == {}


def test_draft_open_pr_marked_as_such(monkeypatch):
    """Une draft compte (quelqu'un y est) mais se lit differemment d'une PR
    prete : le marqueur doit le dire plutot que de laisser deviner."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12519, "state": "OPEN", "isDraft": True, "mergedAt": None},
    ]], calls)
    notes = pig.recent_delivery([_pick()])
    assert "[draft]" in notes[12014]


def test_several_open_prs_named_with_count(monkeypatch):
    """Plusieurs lanes deja dessus : le compte evite de lire 'la PR' comme
    l'unique, et la plus basse est nommee (la premiere arrivee)."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12640, "state": "OPEN", "isDraft": False, "mergedAt": None},
        {"number": 12519, "state": "OPEN", "isDraft": False, "mergedAt": None},
    ]], calls)
    notes = pig.recent_delivery([_pick()])
    assert "#12519" in notes[12014]
    assert "#12640" in notes[12014]
    assert "+1 autre(s)" in notes[12014]


# --- garde "reparer son rouge d'abord" (mandat user 2026-08-22) ------------
#
# Un detecteur se valide par ses FAUX NEGATIFS et par ses SUR-ACCUSATIONS.
# La sur-accusation est ici le risque dominant : la definition naive
# "au moins un check rouge" rougissait 52 PRs sur 55 le 2026-08-22, dont 4
# uniquement sur des advisories. Chaque test ci-dessous nomme la population
# qu'il protege.


def _state(*, checks=(), mergeable="MERGEABLE", reviews=()):
    """Etat GraphQL d'une PR, forme rendue par fetch_pr_states."""
    return {
        "number": 1, "mergeable": mergeable,
        "reviews": {"nodes": [
            {"state": s, "submittedAt": "2026-08-20T00:00:00Z", "author": {"login": a}}
            for s, a in reviews
        ]},
        "commits": {"nodes": [{"commit": {"statusCheckRollup": {"contexts": {"nodes": [
            {"name": t[0], "conclusion": t[1], "isRequired": t[2],
             "completedAt": t[3] if len(t) > 3 else "2026-08-20T00:00:00Z"}
            for t in checks
        ]}}}}]},
    }


def test_failing_advisory_is_not_a_red():
    """Les 4 PRs que la definition naive sur-accusait le 2026-08-22.

    `Slidev composition advisory`, `fast-lane (ombre)`, `Degraded-mode
    confessions` echouent sans empecher aucun merge : renvoyer une lane les
    reparer serait lui faire perdre son cycle sur un faux rouge.
    """
    state = _state(checks=[
        ("Slidev composition advisory (#11923, non-blocking)", "FAILURE", False),
        ("fast-lane (ombre): perimeter-review-guard", "FAILURE", False),
        ("PR gate", "SUCCESS", True),
    ])
    assert pig.blocking_causes(state) == []


def test_failing_required_check_is_a_red_and_names_the_advisory_as_diagnostic():
    state = _state(checks=[
        ("PR gate", "FAILURE", True),
        ("Papermill ratchet (base vs PR)", "FAILURE", False),
    ])
    causes = pig.blocking_causes(state)
    assert "check requis en echec : PR gate" in causes
    # l'advisory est rendu comme DIAGNOSTIC (il dit quoi reparer), jamais
    # comme cause bloquante -- sinon il redeviendrait un motif de refus.
    assert any("non bloquant" in c and "Papermill ratchet" in c for c in causes)


def test_cancelled_is_not_a_failure():
    """Un run annule par `concurrency` n'est pas un echec.

    Les confondre est le faux positif qui rend un garde de cascade
    inutilisable : le 2026-08-21, un SHA de main portait 69 `cancelled`
    pour 0 echec reel.
    """
    assert pig.blocking_causes(_state(checks=[("PR gate", "CANCELLED", True)])) == []
    assert pig.blocking_causes(_state(checks=[("PR gate", "SKIPPED", True)])) == []
    assert pig.blocking_causes(_state(checks=[("PR gate", "NEUTRAL", True)])) == []


def test_conflicts_are_a_red():
    causes = pig.blocking_causes(_state(mergeable="CONFLICTING"))
    assert causes == ["conflits avec main -> rebaser"]


def test_standing_changes_requested_is_a_red():
    causes = pig.blocking_causes(_state(reviews=[("CHANGES_REQUESTED", "myia-ai-01")]))
    assert causes == ["CHANGES_REQUESTED non leve (myia-ai-01)"]


def test_changes_requested_superseded_by_approval_is_not_a_red():
    """Faux negatif a NE PAS produire dans l'autre sens : une review levee.

    L'ordre compte -- seule la DERNIERE review de chaque auteur vaut.
    """
    causes = pig.blocking_causes(_state(reviews=[
        ("CHANGES_REQUESTED", "myia-ai-01"), ("APPROVED", "myia-ai-01"),
    ]))
    assert causes == []


def test_blocked_awaiting_review_is_not_a_red():
    """Cas #12108, verifie firsthand le 2026-08-22 a 18:10Z.

    BLOCKED, MERGEABLE, zero check en echec : la PR attend un merge du
    coordinateur, pas une reparation de sa lane. Un garde qui lirait
    `mergeStateStatus` renverrait la lane reparer ce qui n'est pas casse.
    """
    assert pig.blocking_causes(_state(checks=[("PR gate", "SUCCESS", True)])) == []


def _patch_backlog(monkeypatch, prs, states, nits=None):
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {n: states[n] for n in nums if n in states})
    # Neutraliser l'organe B.0 par DEFAUT : sans cela chaque test partirait sur
    # le reseau interroger des numeros de PR fictifs (mesure : 2,9 s pour trois
    # numeros), et la suite deviendrait non deterministe sans jamais rougir.
    monkeypatch.setattr(pig, "unaddressed_review_points", lambda nums: dict(nits or {}))


def _pr(n, lane, age_hours, *, draft=False):
    created = (pig.NOW - pig.dt.timedelta(hours=age_hours)).strftime("%Y-%m-%dT%H:%M:%SZ")
    body = f"Grain: MED/guard -- lane {lane}\n" if lane else "pas de tag\n"
    return {"number": n, "title": f"pr {n}", "body": body,
            "createdAt": created, "isDraft": draft}


def test_red_backlog_scopes_to_the_lane_and_the_threshold(monkeypatch):
    """La lane et le brouillon filtrent ; l'age ne filtre PLUS le comptage.

    Une rouge fraiche reste dans `red` (elle nourrit le declencheur `count`)
    mais seule la vieille arme le declencheur `aged`.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [
        _pr(1, "myia-po-2026:CoursIA", 30),          # ma lane, vieille, rouge -> red + aged
        _pr(2, "myia-po-2026:CoursIA", 3),           # ma lane, fraiche        -> red seulement
        _pr(3, "myia-po-2023:CoursIA", 30),          # autre lane              -> non
        _pr(4, "myia-po-2026:CoursIA", 30, draft=True),  # brouillon           -> non
    ], {1: red, 2: red, 3: red, 4: red})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=3)
    assert [r["number"] for r in out["red"]] == [1, 2]
    assert [r["number"] for r in out["aged"]] == [1]
    assert out["triggers"] == ["aged"]


def test_a_pile_of_fresh_reds_refuses_the_draw(monkeypatch):
    """Le declencheur que l'age seul ne voyait pas (mandat user 2026-08-23).

    Mesure du jour : 51 des 58 PRs bloquees de la flotte avaient moins de
    24 h -- invisibles au garde. Une lane portant 3 rouges de 2 h doit
    reparer avant de produire, exactement comme celle qui en porte une de 30 h.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [
        _pr(n, "myia-po-2026:CoursIA", 2) for n in (1, 2, 3)
    ], {n: red for n in (1, 2, 3)})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=3)
    assert [r["number"] for r in out["red"]] == [1, 2, 3]
    assert out["aged"] == []
    assert out["triggers"] == ["count"]


def test_under_the_count_threshold_a_fresh_red_still_draws(monkeypatch):
    """Controle positif : le garde n'est pas bloque-a-l'allumage.

    Deux rouges fraiches sous le seuil ne refusent RIEN -- sinon toute lane
    normalement active serait immobilisee, et l'echappatoire `--ignore-red`
    deviendrait la voie ordinaire, ce qui viderait le garde de son sens.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [
        _pr(n, "myia-po-2026:CoursIA", 2) for n in (1, 2)
    ], {n: red for n in (1, 2)})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=3)
    assert len(out["red"]) == 2
    assert out["triggers"] == []


def test_a_fresh_pr_with_review_points_refuses_alone(monkeypatch):
    """Un point de review non leve refuse SEUL : ni vieux, ni nombreux.

    C'est la regression que le retrait du filtre d'age aurait introduite en
    silence. Avant, le filtre s'appliquait en amont : une PR a points non
    leves n'entrait dans `red` que si elle etait deja vieille. En le retirant
    pour le declencheur `count`, une PR recente a points non leves tomberait
    dans `red` sans rien declencher -- la lane tirerait un grain neuf avec une
    remarque en souffrance, ce que le mandat user du 2026-08-24 interdit.

    Une seule PR, 2 h d'age, sous les deux autres seuils : le refus doit
    quand meme tomber, et `nits` doit etre le premier motif nomme.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [_pr(1, "myia-po-2026:CoursIA", 2)],
                   {1: red}, nits={1: 2})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=3)
    assert out["triggers"] == ["nits"]        # ni "aged" ni "count"
    assert out["aged"] == []
    assert len(out["red"]) == 1
    # Le point de review est en TETE des causes : c'est la seule qu'un
    # `gh pr update-branch` ne levera jamais.
    assert "point(s) de review" in out["red"][0]["causes"][0]


def test_without_review_points_a_fresh_lone_red_still_draws(monkeypatch):
    """Controle positif du test precedent : sans nits, rien ne se declenche.

    Sans ce temoin, un `triggers == ["nits"]` obtenu parce que le garde refuse
    TOUT serait indiscernable d'un declencheur qui marche.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [_pr(1, "myia-po-2026:CoursIA", 2)], {1: red})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=3)
    assert out["triggers"] == []
    assert len(out["red"]) == 1


def test_untagged_blocked_prs_are_counted_but_never_attributed(monkeypatch):
    """Portee ecrite : ce que le garde NE couvre PAS.

    7 des 23 PRs bloquees de plus de 24 h n'avaient aucun tag lisible le
    2026-08-22. Deviner leur lane serait pire que les compter a part ; les
    taire donnerait a croire que le garde couvre tout l'ouvert.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [
        _pr(1, "myia-po-2026:CoursIA", 30),
        _pr(9, None, 30),
    ], {1: red, 9: red})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=99)
    assert [r["number"] for r in out["red"]] == [1]
    assert [u["number"] for u in out["unattributed_blocked"]] == [9]


def test_unattributed_blocked_is_printed_on_the_draw_path(monkeypatch, capsys):
    """#12738 : une lane a `red == []` mais `unattributed_blocked != []`
    doit voir les numeros dans la sortie humaine du TIRAGE, pas seulement
    quand elle est refassee. Sans ce cas, le test ne distingue pas le
    correctif de l'etat actuel (paragraphe confine a `print_red_refusal`).
    """
    red_state = _state(checks=[("PR gate", "FAILURE", True)])
    # age 2 h : sous le seuil red_hours=24, donc `red=[]` ; pas de tag -> `unattributed_blocked`.
    _patch_backlog(monkeypatch, [
        _pr(9, None, 2),
    ], {9: red_state})
    backlog = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=99)
    assert backlog["red"] == [], f"Lane doit avoir red vide (age 2h < 24h), got: {backlog['red']}"
    assert [u["number"] for u in backlog["unattributed_blocked"]] == [9]

    pig.print_unattributed_blocked(backlog)
    captured = capsys.readouterr().out
    assert "Portee :" in captured, f"Le paragraphe doit sortir sur le chemin du tirage, got: {captured!r}"
    assert "#9" in captured, f"Le numero #9 doit etre visible, got: {captured!r}"
    assert "`Grain:`" in captured, "Mention Grain: obligatoire"


def test_unattributed_blocked_stays_silent_when_empty(capsys):
    """Aucun output si `unattributed_blocked` est vide : ne pas polluer
    les tirages sans rouge sans tag."""
    pig.print_unattributed_blocked({"unattributed_blocked": []})
    pig.print_unattributed_blocked({})
    captured = capsys.readouterr().out
    assert captured == "", f"Aucun output attendu quand vide, got: {captured!r}"


def test_network_failure_does_not_block_the_draw(monkeypatch):
    """Un garde indisponible ne doit pas immobiliser une lane saine."""
    def boom():
        raise RuntimeError("gh down")
    monkeypatch.setattr(pig, "fetch_open_prs", boom)
    out = pig.red_backlog("myia-po-2026:CoursIA", 24)
    assert out["red"] == [] and out["unavailable"] == "RuntimeError"
    assert out["unattributed_blocked"] == []


# --- echecs perimes : le discriminant est temporel, jamais nominal -----------


def test_failure_older_than_a_green_of_the_same_name_is_history():
    """Mesure #11916 : FAILURE du 20/08 + SUCCESS du 22/08, meme nom, meme head.

    Le rouge est de l'histoire -- renvoyer la lane le reparer l'enverrait
    reparer un check deja vert.
    """
    state = _state(checks=[
        ("Require genre diversity vs prev:", "FAILURE", True, "2026-08-20T09:54:52Z"),
        ("Require genre diversity vs prev:", "SUCCESS", True, "2026-08-22T09:36:40Z"),
    ])
    assert pig.blocking_causes(state) == []


def test_failure_contemporaneous_with_a_green_twin_is_kept():
    """Symetrique (#11894) : deux workflows jumeaux emettent le meme nom au meme

    moment. Le rouge est vivant ; le filtrer par nom seul le masquerait.
    """
    state = _state(checks=[
        ("Fast lane (ombre)", "SUCCESS", True, "2026-08-22T10:00:00Z"),
        ("Fast lane (ombre)", "FAILURE", True, "2026-08-22T10:00:07Z"),
    ])
    assert pig.blocking_causes(state) == ["check requis en echec : Fast lane (ombre)"]


def test_repeated_identical_failures_are_named_once():
    """#12107 portait deux FAILURE du meme nom : la cause se lit une fois."""
    state = _state(checks=[
        ("PR gate", "FAILURE", True, "2026-08-22T13:32:17Z"),
        ("PR gate", "FAILURE", True, "2026-08-22T13:40:33Z"),
    ])
    assert pig.blocking_causes(state) == ["check requis en echec : PR gate"]


# --- affluence flotte : cited_issues / fetch_visits / amortissement --------
#
# Le defaut que ces tests auraient attrape (2026-08-23, avant merge) : la
# colonne `vus` rendait 0 sur TOUTES les issues, y compris celles que la ligne
# d'annotation juste en dessous disait fraichement livrees. Deux causes
# distinctes, toutes deux silencieuses :
#
#   1. attribution -- on reutilisait `extract_vein_key` (premier `#N` du corps),
#      qui rend la tranche SOEUR pour une PR d'ombrelle : #12591 s'intitule
#      `fix(notebooks,#11947)` et porte `See #11947`, mais son premier `#N` de
#      corps est #11949. Rappel mesure sur 10 issues : 59 % contre 76 %.
#   2. peche -- `gh pr list --state merged --limit N` trie par date de CREATION ;
#      filtrer ensuite sur `mergedAt` cote client perdait 44 % de la population
#      (101 PRs vues pour 181 reelles sur la meme fenetre de 24 h).
#
# Un zero d'absence de mesure se lit exactement comme un zero d'affluence : d'ou
# le controle positif, et d'ou `visits_measured` dans la sortie JSON.


def _visit_pr(number, title, body):
    """PR minimale pour l'attribution. Nom distinct du `_pr` du bloc rouge."""
    return {"number": number, "title": title, "body": body}


def test_umbrella_declared_by_title_and_see_is_attributed():
    """Cas fondateur #12591 : l'ombrelle est dans le titre et dans `See`."""
    pr = _visit_pr(12591,
                   "fix(notebooks,#11947): tranche CaseStudies heading_in_list",
                   "Grain: MED/notebook-python -- lane myia-po-2025:CoursIA -- "
                   "prev: MED/notebook-lean (#12491)\n\n"
                   "La tranche po-2023 d'origine (#11949) couvrait DecInfer.\n"
                   "See #11947 (contribution partielle)")
    cited = pig.cited_issues(pr)
    assert 11947 in cited, "l'ombrelle declaree doit compter"
    assert 12491 not in cited, "la clause prev: documente le grain PRECEDENT"


def test_prose_only_citation_is_not_a_visit():
    """Une citation de prose nue ne vaut pas declaration de sujet."""
    pr = _visit_pr(1000, "fix(x,#5000): quelque chose",
                   "Comparable au cas de #10143, pour memoire.\nSee #5000")
    assert pig.cited_issues(pr) == {5000}


def test_self_reference_never_counts():
    pr = _visit_pr(7777, "fix(x,#7777): auto", "Closes #7777")
    assert pig.cited_issues(pr) == set()


def test_fetch_visits_filters_dates_server_side(monkeypatch):
    """La requete DOIT porter `merged:>=` : le tri de gh est par creation."""
    seen = {}

    def fake_run(cmd, **kwargs):
        seen["cmd"] = cmd
        return _FakeCompleted(json.dumps([
            _visit_pr(1001, "fix(a,#1100): x", "See #1100"),
            _visit_pr(1002, "fix(b,#1100): y", "Closes #1100"),
            _visit_pr(1003, "fix(c,#1200): z", "See #1200"),
        ]))

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    visits, err = pig.fetch_visits()
    assert err is None
    assert visits == {1100: 2, 1200: 1}
    assert any(a.startswith("merged:>=") for a in seen["cmd"]), seen["cmd"]


def test_fetch_visits_failure_is_reported_not_silently_zero(monkeypatch):
    def boom(cmd, **kwargs):
        raise OSError("gh absent")

    monkeypatch.setattr(pig.subprocess, "run", boom)
    visits, err = pig.fetch_visits()
    assert visits == {}
    assert err and "OSError" in err


def test_crowding_damps_a_visited_issue():
    hot = {"number": 1, "age": 30, "idle": 1, "genre": "docs"}
    cold = {"number": 2, "age": 30, "idle": 1, "genre": "docs"}
    assert pig.weight(hot, None, {1: 12}) < pig.weight(cold, None, {2: 0})


def test_unmeasured_crowding_leaves_the_weight_intact():
    """Compteur vide = pas de mesure ; il ne doit PAS peser comme un zero."""
    item = {"number": 1, "age": 30, "idle": 1, "genre": "docs"}
    assert pig.weight(dict(item), None, {}) == pig.weight(dict(item), None, None)


def test_crowding_never_zeroes_a_candidate():
    """Amortir, jamais exclure : une issue tres visitee reste tirable."""
    item = {"number": 1, "age": 400, "idle": 90, "genre": "lean"}
    assert pig.weight(item, None, {1: 50}) > 0

# --- points de review non leves : la 4e cause (mandat user 2026-08-24) -------
#
# "Fais en sorte que les agents ne produisent plus tant qu'il leur reste des
# points a traiter dans leurs vieilles PRs, ca doit leur etre propose en
# premier lieu a chaque cycle."
#
# Les trois causes preexistantes (check requis, conflit, CHANGES_REQUESTED)
# sont structurellement aveugles aux trois surfaces de B.0 : nits du user en
# issue comments, reserves d'Hermes en prefixe de body sous `state: COMMENTED`,
# threads inline dans `reviewThreads`. Une PR peut etre VERTE, sans conflit,
# sans CHANGES_REQUESTED -- et rester non mergeable.


def test_unaddressed_review_point_is_a_red_on_an_otherwise_green_pr(monkeypatch):
    """Le cas que les trois causes preexistantes laissaient passer."""
    green = _state(checks=[("PR gate", "SUCCESS", True)])
    _patch_backlog(monkeypatch, [_pr(1, "myia-po-2026:CoursIA", 30)], {1: green},
                   nits={1: 2})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24)
    assert [r["number"] for r in out["red"]] == [1]
    cause = out["red"][0]["causes"][0]
    assert "2 point(s) de review non leve(s)" in cause


def test_review_points_come_first_among_the_causes(monkeypatch):
    """Proposes EN PREMIER : le mandat porte sur l'ordre, pas seulement le fait.

    Une PR qui cumule un rouge de CI et un nit doit montrer le nit d'abord --
    c'est le seul des deux qu'un `update-branch` ne reparera jamais.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [_pr(1, "myia-po-2026:CoursIA", 30)], {1: red},
                   nits={1: 1})
    causes = pig.red_backlog("myia-po-2026:CoursIA", 24)["red"][0]["causes"]
    assert "point(s) de review non leve(s)" in causes[0]
    assert any("check requis" in c for c in causes[1:])


def test_no_review_point_leaves_a_green_pr_drawable(monkeypatch):
    """Faux positif : une lane a l'ardoise propre doit pouvoir tirer."""
    green = _state(checks=[("PR gate", "SUCCESS", True)])
    _patch_backlog(monkeypatch, [_pr(1, "myia-po-2026:CoursIA", 30)], {1: green})
    assert pig.red_backlog("myia-po-2026:CoursIA", 24)["red"] == []


def test_only_the_lane_s_own_prs_are_examined(monkeypatch):
    """L'organe coute 2 appels API par PR : ne l'appeler que sur `mine`.

    Le filtre est la LANE, pas l'age. La PR 3 appartient a la lane et n'a que
    3 h : elle est examinee, parce que les declencheurs `count` et `nits`
    doivent la voir -- un tas de rouges recentes est precisement ce que le
    seul critere d'age manquait. La PR 2 (autre lane) reste exclue, et c'est
    l'invariant que ce test protege.

    Le cout monte avec le nombre de PR recentes de la lane. C'est inherent :
    on ne peut pas compter un tas sans regarder ce qui le compose.
    """
    seen = []
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: [
        _pr(1, "myia-po-2026:CoursIA", 30),
        _pr(2, "myia-po-2023:CoursIA", 30),
        _pr(3, "myia-po-2026:CoursIA", 3),
    ])
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {})
    monkeypatch.setattr(pig, "unaddressed_review_points",
                        lambda nums: seen.extend(nums) or {})
    pig.red_backlog("myia-po-2026:CoursIA", 24)
    assert seen == [1, 3]      # les deux PR de la lane
    assert 2 not in seen       # jamais celles d'une autre lane


def test_organ_failure_is_said_not_swallowed(monkeypatch):
    """Un zero de denominateur ne doit pas se lire comme un zero de numerateur.

    Si l'organe est injoignable, la lane peut tirer -- mais le tirage ne prouve
    plus que son ardoise est propre, et la sortie doit le DIRE.
    """
    green = _state(checks=[("PR gate", "SUCCESS", True)])
    def boom(nums):
        raise RuntimeError("gh down")
    monkeypatch.setattr(pig, "fetch_open_prs",
                        lambda: [_pr(1, "myia-po-2026:CoursIA", 30)])
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {1: green})
    monkeypatch.setattr(pig, "unaddressed_review_points", boom)
    out = pig.red_backlog("myia-po-2026:CoursIA", 24)
    assert out["red"] == []
    assert out["nits_unavailable"] == "RuntimeError"


def test_the_gap_warning_speaks_only_when_the_surface_was_unread(capsys):
    pig.print_nits_gap({"nits_unavailable": None})
    assert capsys.readouterr().out == ""
    pig.print_nits_gap({"nits_unavailable": "RuntimeError"})
    said = capsys.readouterr().out
    assert "n'ont PAS pu etre lus" in said
    assert "check_unaddressed_nits.py" in said
