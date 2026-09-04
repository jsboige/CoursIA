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


def _pr_with_author(n, lane, age_hours, author):
    pr = _pr(n, lane, age_hours)
    pr["author"] = {"login": author}
    return pr


def test_base_inherited_red_is_not_the_lanes(monkeypatch):
    """#13545 : 11 PRs / 4 lanes accusees pour un seul defaut de main.

    Le meme check requis en echec chez une LANE distincte = corroboration :
    le rouge est impute a la base, retire du refus de la lane, et rapporte
    comme tache coordinateur avec ses corroborations. Depuis #14537 la
    corroboration se fait sur la CAUSE : le nom pour un check direct, l'ORGANE
    (annotation du check-run) pour un agregateur -- les deux PRs echouent ici
    le meme organe sous le nom d'agregateur "PR gate".
    """
    red = _state(checks=[("Scripts Tests (CPU)", "FAILURE", True),
                         ("PR gate", "FAILURE", True)])
    st1, st2 = red, _state(checks=[("Scripts Tests (CPU)", "FAILURE", True),
                                   ("PR gate", "FAILURE", True)])
    for st, rid in ((st1, 111), (st2, 222)):
        st["commits"]["nodes"][0]["commit"]["statusCheckRollup"]["contexts"][
            "nodes"][1]["databaseId"] = rid
    monkeypatch.setattr(pig, "fetch_check_organs",
                        lambda rid: ["perimeter"])
    _patch_backlog(monkeypatch, [
        _pr_with_author(1, "myia-po-2023:CoursIA", 30, "myia-po-2023"),
        _pr_with_author(2, "myia-po-2026:CoursIA-2", 5, "myia-po-2026"),
    ], {1: st1, 2: st2})
    out = pig.red_backlog("myia-po-2023:CoursIA", 24, count_threshold=3)
    assert out["red"] == []            # rien d'imputable a la lane
    assert out["aged"] == []
    assert out["triggers"] == []       # pas de refus de tirage
    assert {i["check"] for i in out["base_inherited"]} == {
        "Scripts Tests (CPU)", "PR gate :: perimeter"}
    wits = next(i["corroborated_by"] for i in out["base_inherited"]
                if i["check"] == "Scripts Tests (CPU)")
    assert 1 in wits and 2 in wits    # la lane ET l'etrangere corroborent
    assert out["base_unresolved"] == []


def test_same_author_failures_are_not_imputed(monkeypatch):
    """Controle negatif : deux PRs de la MEME LANE ne se corroborent pas.

    Depuis #14537 l'unite de corroboration est le tag de lane, pas le login
    (identite de poussee partagee) : une lane qui casse le meme ratchet sur
    2 PRs porte 2 defauts a elle -- les imputer a la base transformerait un
    motif de refus legitime en silence complice. L'agregateur sans organe
    lisible est en outre DIT non tranche (#14567), pas passe sous silence.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [
        _pr_with_author(1, "myia-po-2023:CoursIA", 30, "jsboige"),
        _pr_with_author(2, "myia-po-2023:CoursIA", 30, "jsboige"),
    ], {1: red, 2: red})
    out = pig.red_backlog("myia-po-2023:CoursIA", 24, count_threshold=3)
    assert [r["number"] for r in out["red"]] == [1, 2]
    assert out["base_inherited"] == []
    assert "aged" in out["triggers"]
    assert {i["check"] for i in out["base_unresolved"]} == {"PR gate"}


def test_inheritance_does_not_swallow_other_causes(monkeypatch):
    """L'imputation retire le CHECK herite, pas les autres causes de la PR.

    Une PR dont le check herite de la base MAIS qui conflit avec main reste
    rouge : le conflit est bien le sien.
    """
    red = _state(checks=[("Scripts Tests (CPU)", "FAILURE", True)],
                 mergeable="CONFLICTING")
    _patch_backlog(monkeypatch, [
        _pr_with_author(1, "myia-po-2023:CoursIA", 30, "myia-po-2023"),
        _pr_with_author(2, "myia-po-2026:CoursIA-2", 5, "myia-po-2026"),
    ], {1: red, 2: red})
    out = pig.red_backlog("myia-po-2023:CoursIA", 24, count_threshold=3)
    assert [r["number"] for r in out["red"]] == [1]
    assert out["red"][0]["causes"] == ["conflits avec main -> rebaser"]


AGG = "Always-on guards -- 12 organes, 1 checkout"


def _agg_red(run_id, name=AGG, required=True):
    """Etat rouge d'un aggregateur RESOLVABLE : le ctx porte son check-run id."""
    st = _state(checks=[(name, "FAILURE", required)])
    st["commits"]["nodes"][0]["commit"]["statusCheckRollup"]["contexts"][
        "nodes"][0]["databaseId"] = run_id
    return st


def _patch_organs(monkeypatch, organs_by_run):
    monkeypatch.setattr(pig, "fetch_check_organs",
                        lambda rid: organs_by_run.get(rid, []))


def test_same_organ_two_lanes_same_push_login_is_imputed(monkeypatch):
    """Acceptance (a) #14537 : l'angle mort fondateur se ferme.

    Toutes les PRs sous le MEME login de poussee (jsboige = 52/59 de
    l'ouvert mesure le 2026-09-03), mais deux LANES distinctes echouant le
    MEME organe d'un agregateur : le cas nominal que l'ancien predicat
    (>=2 author.login) ne croisait JAMAIS. Il doit etre impute a la base.
    """
    _patch_organs(monkeypatch, {111: ["prev_guard"], 222: ["prev_guard"]})
    _patch_backlog(monkeypatch, [
        _pr_with_author(1, "myia-po-2023:CoursIA", 30, "jsboige"),
        _pr_with_author(2, "myia-po-2026:CoursIA", 30, "jsboige"),
    ], {1: _agg_red(111), 2: _agg_red(222)})
    out = pig.red_backlog("myia-po-2023:CoursIA", 24, count_threshold=3)
    assert out["red"] == []
    assert {i["check"] for i in out["base_inherited"]} == {f"{AGG} :: prev_guard"}
    wits = out["base_inherited"][0]["corroborated_by"]
    assert 1 in wits and 2 in wits


def test_distinct_organs_under_one_aggregate_are_not_imputed(monkeypatch):
    """Acceptance (b) #14537 : la table des six PRs, reduite a trois lanes.

    Trois organes DISTINCTS (lane_claim, prev_guard, perimeter) sous le meme
    nom d'agregateur : la corroboration par nom etait garantie par
    construction -- elle n'a jamais prouve une cause commune. Rien n'est
    impute, chaque lane garde son rouge, reparable chez elle.
    """
    _patch_organs(monkeypatch, {111: ["lane_claim"], 222: ["prev_guard"],
                                333: ["perimeter"]})
    _patch_backlog(monkeypatch, [
        _pr_with_author(1, "myia-po-2025:CoursIA", 30, "jsboige"),
        _pr_with_author(2, "myia-po-2023:CoursIA-2", 30, "jsboige"),
        _pr_with_author(3, "myia-po-2024:CoursIA", 30, "jsboige"),
    ], {1: _agg_red(111), 2: _agg_red(222), 3: _agg_red(333)})
    out = pig.red_backlog("myia-po-2025:CoursIA", 24, count_threshold=3)
    assert out["base_inherited"] == []
    assert [r["number"] for r in out["red"]] == [1]


def test_aggregate_with_unreadable_organ_stays_with_lane(monkeypatch):
    """Fail-closed #14567 : un agregateur non resolu ne corrobore RIEN.

    Deux lanes echouent l'agregateur mais aucune annotation n'est lisible :
    imputer a la base serait un verdict d'echec de mesure. Le rouge reste a
    la lane -- seul cote qui peut le reparer -- et l'echec de resolution
    est RAPPORTE au lieu d'un silence lu comme un acquittement.
    """
    _patch_organs(monkeypatch, {})
    _patch_backlog(monkeypatch, [
        _pr_with_author(1, "myia-po-2025:CoursIA", 30, "jsboige"),
        _pr_with_author(2, "myia-po-2026:CoursIA", 30, "jsboige"),
    ], {1: _agg_red(111), 2: _agg_red(222)})
    out = pig.red_backlog("myia-po-2025:CoursIA", 24, count_threshold=3)
    assert out["base_inherited"] == []
    assert [r["number"] for r in out["red"]] == [1]
    assert {i["check"] for i in out["base_unresolved"]} == {AGG}


def test_untagged_pr_never_corroborates(monkeypatch):
    """Fail-closed #14537 : sans tag de lane lisible, hors corroboration.

    Une PR sans Grain: lisible echouant le meme organe ne doit finir dans
    AUCUN seau -- deviner sa lane serait pire que de l'ignorer.
    """
    _patch_organs(monkeypatch, {111: ["prev_guard"], 222: ["prev_guard"]})
    _patch_backlog(monkeypatch, [
        _pr_with_author(1, "myia-po-2025:CoursIA", 30, "jsboige"),
        _pr_with_author(2, None, 30, "jsboige"),
    ], {1: _agg_red(111), 2: _agg_red(222)})
    out = pig.red_backlog("myia-po-2025:CoursIA", 24, count_threshold=3)
    assert out["base_inherited"] == []
    assert [r["number"] for r in out["red"]] == [1]


def test_rollup_stack_does_not_self_corroborate(monkeypatch):
    """Defaut 3 #14537 : une PR empilee n'est pas son propre temoin.

    Le rollup peut empiler plusieurs runs de meme nom sur une PR ; l'ancien
    `sorted(n for ...)` citait alors la meme PR trois fois comme sa propre
    corroboration. Le rendu deduplique : chaque PR est temoin UNIQUE.
    """
    stacked = _state(checks=[(AGG, "FAILURE", True), (AGG, "FAILURE", True)])
    nodes = stacked["commits"]["nodes"][0]["commit"]["statusCheckRollup"][
        "contexts"]["nodes"]
    nodes[0]["databaseId"] = 111
    nodes[1]["databaseId"] = 111
    _patch_organs(monkeypatch, {111: ["prev_guard"]})
    _patch_backlog(monkeypatch, [
        _pr_with_author(1, "myia-po-2025:CoursIA", 30, "jsboige"),
    ], {1: stacked})
    out = pig.red_backlog("myia-po-2025:CoursIA", 24, count_threshold=3)
    assert out["base_inherited"] == []


def test_partial_inheritance_keeps_the_lane_cause():
    """blocking_causes : heritage PAR ORGANE, pas par nom d'agregateur.

    Un agregateur tombe pour DEUX organes dont un seul est impute a la
    base : la lane doit encore voir une cause -- son organe a elle reste a
    reparer. Tous les organes herites : plus aucune cause a la lane.
    """
    state = _state(checks=[(AGG, "FAILURE", True)])
    both = {f"{AGG} :: perimeter", f"{AGG} :: prev_guard"}
    causes = pig.blocking_causes(state, inherited={f"{AGG} :: perimeter"},
                                 resolved_keys_by_name={AGG: both})
    assert causes == ["check requis en echec : " + AGG]
    assert pig.blocking_causes(state, inherited=both,
                               resolved_keys_by_name={AGG: both}) == []


def test_required_failure_links_advisory_as_its_probable_cause():
    """#13545 (presentation) : l'agregateur requis et sa cause advisory ne
    s'affichent plus comme deux lignes qui se contredisent.

    « check requis en echec : PR gate » puis « diagnostic, non bloquant :
    Scripts Tests (CPU) » sur le MEME rouge est illisible au moment ou le
    message compte : la deuxieme ligne doit dire qu'elle est la CAUSE
    probable de la premiere.
    """
    state = _state(checks=[("PR gate", "FAILURE", True),
                           ("Scripts Tests (CPU)", "FAILURE", False)])
    causes = pig.blocking_causes(state)
    assert "check requis en echec : PR gate" in causes
    linked = [c for c in causes if "Scripts Tests (CPU)" in c]
    assert len(linked) == 1
    assert "cause probable du requis" in linked[0]


# --- le rouge est une ASSIGNATION, jamais un vide (incident lanes 2, 30/08) --
#
# Le fond de ce chemin etait deja juste : il nomme les PRs, leurs causes et les
# gestes. C'est sa FORME qui a draine les lanes -- "REFUS DE TIRAGE" + sortie 2
# + aucun candidat se lit "l'outil n'a rien pour moi", et une lane a forte
# cadence le recevait a chaque cycle. Les deux tests suivants tiennent le
# contrat corrige ; le troisieme est leur controle positif.


def test_a_lane_with_reds_gets_a_grain_not_a_refusal(monkeypatch, capsys):
    """Sortie 0 et un travail NOMME : la reparation EST le grain du cycle.

    Le code 2 est la convention "rien a rendre". L'employer ici disait a la
    lane, dans le seul canal qu'elle lit, l'exact contraire de la regle HARD
    qu'il sert -- il y a toujours du travail.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [_pr(1, "myia-po-2026:CoursIA", 30)], {1: red})
    rc = pig.main(["--lane", "myia-po-2026:CoursIA"])
    out = capsys.readouterr().out
    assert rc == 0, f"le chemin reparation doit rendre 0, got {rc}"
    # C'est la PREMIERE ligne qui est lue comme le verdict de l'outil : la
    # phrase "ce n'est PAS un refus", plus bas, contient le mot a dessein.
    head = out.splitlines()[0]
    assert "REFUS" not in head.upper(), f"l'en-tete annonce encore un refus : {head!r}"
    assert "GRAIN DU CYCLE" in head
    assert "#1" in out, "la PR a reprendre doit etre nommee"
    # Le fond qui marchait deja ne doit pas disparaitre avec la forme.
    assert "check requis en echec" in out
    assert "update-branch" in out


def test_repair_json_carries_a_grain_field(monkeypatch, capsys):
    """Le consommateur machine lit un grain, pas un motif de refus.

    Sans ce cas, la sortie humaine pourrait etre corrigee pendant que `--json`
    continue d'annoncer un refus -- deux canaux, deux verites.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [_pr(7, "myia-po-2026:CoursIA", 30)], {7: red})
    rc = pig.main(["--lane", "myia-po-2026:CoursIA", "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["mode"] == "repair"
    assert payload["grain"]["number"] == 7
    assert "refus" not in payload


def test_adjacency_red_advice_replaces_three_generic_gestures(monkeypatch, capsys):
    """#13967 : quand la cause du rouge est `adjacency`, le picker doit
    remplacer les trois conseils generiques (`update-branch` / rebase /
    pousser) par le remede propre : « piocher un grain d'un AUTRE genre,
    ne PAS retaguer ». Mesure du 2026-09-01 : 13 PRs / 25 rouges
    mesurables = premiere cause de rouge de la flotte -- les trois
    gestes generiques sont invariants au predicat et la lane boucle.

    Le test pin le contrat par la sortie (pas de `update-branch`,
    mention explicite du remede). La fixture ajoute le champ
    optionnel `is_adjacency=True` au PR rouge -- c'est le point
    d'entree qu'un futur wrapper autour de
    `scripts/ci/variation_adjacency_guard.py` remplira pour passer
    du verdict de l'organe au conseil du picker (le picker n'appelle
    pas gh par PR rouge -- trop couteux, trop de surface).
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    pr = _pr(99, "myia-po-2026:CoursIA", 30)
    pr["is_adjacency"] = True
    _patch_backlog(monkeypatch, [pr], {99: red})
    rc = pig.main(["--lane", "myia-po-2026:CoursIA"])
    out = capsys.readouterr().out
    assert rc == 0
    # Le remede propre doit etre present.
    assert "Piocher un grain d'UN AUTRE genre" in out, (
        f"le conseil adjacency est absent : {out[-400:]!r}"
    )
    assert "Ne PAS retaguer la PR" in out, (
        "l'interdit de re-tag (protocole variation §2) doit etre rappele"
    )
    # Les trois gestes generiques doivent etre ABSENTS : aucun d'eux ne
    # modifie `genre` ou `prev_genre`, donc aucun ne leve le blocage.
    assert "gh pr update-branch" not in out, (
        "`gh pr update-branch` ne leve jamais adjacency (predicat "
        "invariant au SHA). Sa presence ici ferait perdre un cycle a "
        "la lane qui suit le conseil."
    )
    # L'en-tete Reparation doit toujours etre la (coherence avec le
    # test existant).
    assert "GRAIN DU CYCLE" in out
    assert "#99" in out


def test_non_adjacency_red_keeps_three_generic_gestures(monkeypatch, capsys):
    """#13967 : controle positif du test precedent.

    Un PR rouge pour une cause REPARABLE par push (check FAILURE
    substance) doit continuer d'afficher les trois gestes generiques.
    Sans ce controle, la correction pourrait supprimer le conseil pour
    tout le monde et le test precedent passerait quand meme.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    pr = _pr(11, "myia-po-2026:CoursIA", 30)
    # Pas de champ `is_adjacency` (defaut implicite = False / absent).
    assert "is_adjacency" not in pr
    _patch_backlog(monkeypatch, [pr], {11: red})
    rc = pig.main(["--lane", "myia-po-2026:CoursIA"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "Trois gestes, dans cet ordre" in out
    assert "gh pr update-branch" in out, (
        "un PR rouge substance doit conserver le premier geste "
        "(rejouer les checks sur tete fraiche peut le reparer)"
    )
    # Et l'absence du remede adjacency est l'autre moitie du contrat.
    assert "Piocher un grain d'UN AUTRE genre" not in out


def _pr_with_body(n: int, lane: str, age_hours: int, body: str) -> dict:
    """PR rouge avec un corps arbitraire (permet de pinner le tag `Grain:`
    du test : `_pr` le fige a `MED/guard` pour les tests existants).
    """
    created = (pig.NOW - pig.dt.timedelta(hours=age_hours)).strftime("%Y-%m-%dT%H:%M:%SZ")
    return {"number": n, "title": f"pr {n}", "body": body,
            "createdAt": created, "isDraft": False}


def test_adjacency_detected_from_body_when_caller_omits_flag(monkeypatch, capsys):
    """#13967 (cycle 158) : le picker doit DEDUIRE `is_adjacency` du corps
    de la PR via `variation_adjacency_guard.check`, pas attendre qu'un
    caller externe pose le flag. Le bug fondateur : la branche specialisee
    L1718 etait du code mort (flag jamais pose), donc les 13 PRs
    mesurees en adjacency recevaient les 3 conseils generiques invariants
    au predicat.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    body = ("Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- "
            "prev: LIGHT/guard #13940\n")
    pr = _pr_with_body(101, "myia-po-2026:CoursIA", 30, body)
    # Pas de champ `is_adjacency` : on verifie que le picker le deduit.
    assert "is_adjacency" not in pr
    _patch_backlog(monkeypatch, [pr], {101: red})
    rc = pig.main(["--lane", "myia-po-2026:CoursIA"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "Piocher un grain d'UN AUTRE genre" in out, (
        "le picker doit deduire l'adjacency du corps via l'organe "
        "variation_adjacency_guard ; le contrat du test existant etait "
        "que le caller pose le flag, mais aucun caller in-process ne le "
        "fait (cf #13967)"
    )
    assert "gh pr update-branch" not in out


def test_adjacency_not_triggered_when_genres_differ_in_body(monkeypatch, capsys):
    """#13967 controle negatif : un corps `MED/guard` apres `LIGHT/ledger`
    NE TRIPPE PAS l'organe d'adjacence, donc le picker conserve les
    trois conseils generiques (le push peut reparer le rouge).
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    body = ("Grain: MED/guard -- lane myia-po-2026:CoursIA -- "
            "prev: LIGHT/ledger #13941\n")
    pr = _pr_with_body(102, "myia-po-2026:CoursIA", 30, body)
    _patch_backlog(monkeypatch, [pr], {102: red})
    rc = pig.main(["--lane", "myia-po-2026:CoursIA"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "Trois gestes, dans cet ordre" in out
    assert "gh pr update-branch" in out, (
        "genres distincts = pas d'adjacence = conseil generic applicable"
    )
    assert "Piocher un grain d'UN AUTRE genre" not in out


def test_adjacency_caller_override_still_respected(monkeypatch, capsys):
    """#13967 preservation du contrat : un caller externe peut toujours
    poser `is_adjacency=False` pour court-circuiter la deduction par
    organe. Utile pour les tests pinnes qui ne veulent pas dependre du
    parseur de tag (cf le test existant L555 qui pose `True`).
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    # Corps qui TRIPPERAIT l'organe (LIGHT/guard apres LIGHT/guard)...
    body = ("Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- "
            "prev: LIGHT/guard #13942\n")
    pr = _pr_with_body(103, "myia-po-2026:CoursIA", 30, body)
    # ...mais le caller force l'override a False.
    pr["is_adjacency"] = False
    _patch_backlog(monkeypatch, [pr], {103: red})
    rc = pig.main(["--lane", "myia-po-2026:CoursIA"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "Trois gestes, dans cet ordre" in out, (
        "l'override du caller (`is_adjacency=False`) doit primer sur la "
        "deduction par organe -- le contrat de l'API externe est preserve"
    )
    assert "Piocher un grain d'UN AUTRE genre" not in out


def test_a_clean_lane_is_not_sent_to_repair(monkeypatch, capsys):
    """Controle positif des deux precedents.

    Un `rc == 0` obtenu parce que le garde ne se declenche JAMAIS serait
    indiscernable d'une assignation qui marche : ici la lane n'a aucun rouge,
    et la sortie ne doit contenir aucune assignation de reparation.
    """
    green = _state(checks=[("PR gate", "SUCCESS", True)])
    _patch_backlog(monkeypatch, [_pr(1, "myia-po-2026:CoursIA", 30)], {1: green})
    backlog = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=3)
    assert backlog["triggers"] == []
    pig.print_red_assignment("myia-po-2026:CoursIA", {"red": [], "triggers": []}, 24)
    assert "GRAIN DU CYCLE" in capsys.readouterr().out  # la fonction existe et rend


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
    correctif de l'etat actuel (paragraphe confine a `print_red_assignment`).
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


# --- orphelines du tag Grain : le constat doit porter sa route (#13086) -------


def _orphan_pr(n, age_hours, author, branch):
    pr = _pr(n, None, age_hours)
    pr["author"] = {"login": author}
    pr["headRefName"] = branch
    return pr


def test_unattributed_blocked_prs_carries_the_route(monkeypatch):
    """`--orphans-report` et `red_backlog` partagent la meme detection, et le
    resultat porte author+branch : un constat sans destinataire n'est pas un
    routage. Les untagged SANS rouge et les taggees ne comptent pas.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    green = _state(checks=[("PR gate", "SUCCESS", True)])
    tagged = _pr(1, "myia-po-2023:CoursIA", 50)
    tagged.update(author={"login": "myia-po-2023"}, headRefName="feature/ok")
    fresh_unblocked = _orphan_pr(2, 1, "myia-po-2024", "feature/fresh")
    prs = [
        tagged,
        fresh_unblocked,
        _orphan_pr(3, 30, "myia-po-2023", "feature/old"),
        _orphan_pr(4, 8, "myia-po-2023", "feature/mid"),
        _orphan_pr(5, 40, "jsboige", "feature/user"),
    ]
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    monkeypatch.setattr(
        pig, "fetch_pr_states",
        lambda nums: {n: (red if n in (3, 4, 5) else green) for n in nums})
    out = pig.unattributed_blocked_prs()
    assert [r["number"] for r in out] == [5, 3, 4]  # tri par age decroissant
    assert all(r["author"] and r["branch"] for r in out)
    assert out[0]["author"] == "jsboige" and out[0]["branch"] == "feature/user"


def test_red_backlog_unattributed_now_carries_the_route(monkeypatch):
    """Le champ historique `unattributed_blocked` est ENRICHI (auteur, branche),
    pas remplace : le skill coordinate lit ce champ, il gagne la route sans
    changer de canal.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    orphan = _orphan_pr(9, 12, "myia-po-2023", "feature/x")
    _patch_backlog(monkeypatch, [_pr(1, "myia-po-2026:CoursIA", 30), orphan],
                   {1: red, 9: red})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=99)
    assert out["unattributed_blocked"][0]["author"] == "myia-po-2023"
    assert out["unattributed_blocked"][0]["branch"] == "feature/x"


def test_build_orphans_comment_names_each_orphan_with_author_and_branch():
    """Le commentaire est le routage : chaque orpheline y est nommee avec son
    auteur et sa branche, groupees par auteur, entre marqueurs upsert.
    """
    orphans = [
        {"number": 5, "title": "fix thing", "author": "jsboige",
         "branch": "feature/user", "age_hours": 40},
        {"number": 3, "title": "other thing", "author": "myia-po-2023",
         "branch": "feature/old", "age_hours": 30},
    ]
    body = pig.build_orphans_comment(orphans)
    assert pig.ORPHANS_MARKER_START in body and pig.ORPHANS_MARKER_END in body
    assert "**jsboige** (1)" in body and "**myia-po-2023** (1)" in body
    assert "#5" in body and "#3" in body
    assert "`feature/user`" in body and "`feature/old`" in body
    assert "#13086" in body


def test_build_orphans_comment_empty_writes_zero_not_silence():
    """Un balayage muet est indiscernable d'un balayage mort : le cas vide
    s'ECRIT (zero date), il ne disparait pas.
    """
    body = pig.build_orphans_comment([])
    assert pig.ORPHANS_MARKER_START in body and pig.ORPHANS_MARKER_END in body
    assert ": 0." in body


def test_orphans_report_mode_dry_run_by_default(monkeypatch, capsys):
    """Sans --apply-comment : impression seule, AUCUN appel gh d'ecriture.
    Le mode ne demande pas --lane (la file est lane-independante).
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    monkeypatch.setattr(pig, "fetch_open_prs",
                        lambda: [_orphan_pr(9, 5, "myia-po-2023", "feature/x")])
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {9: red} if 9 in nums else {})
    def no_post(number, body):
        raise AssertionError(f"upsert appele en dry-run sur #{number}")
    monkeypatch.setattr(pig, "upsert_orphans_comment", no_post)
    rc = pig.main(["--orphans-report"])
    assert rc == 0
    out = capsys.readouterr().out
    assert pig.ORPHANS_MARKER_START in out and "#9" in out


def test_orphans_report_apply_upserts_the_comment(monkeypatch, capsys):
    """Avec --apply-comment N : l'upsert marker-guarde part exactement une fois
    sur l'issue demandee.
    """
    red = _state(checks=[("PR gate", "FAILURE", True)])
    monkeypatch.setattr(pig, "fetch_open_prs",
                        lambda: [_orphan_pr(9, 5, "myia-po-2023", "feature/x")])
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {9: red} if 9 in nums else {})
    calls = []
    monkeypatch.setattr(pig, "upsert_orphans_comment",
                        lambda number, body: calls.append((number, body)))
    rc = pig.main(["--orphans-report", "--apply-comment", "13086"])
    assert rc == 0
    assert calls and calls[0][0] == 13086
    assert pig.ORPHANS_MARKER_START in calls[0][1]
    assert "mis a jour sur #13086" in capsys.readouterr().out


def test_lane_still_required_outside_orphans_report(monkeypatch, capsys):
    """--lane reste OBLIGATOIRE sur le chemin de tirage : le passage de
    `required=True` a la validation manuelle ne doit pas ouvrir un tirage
    sans lane (la graine et le garde en dependent).
    """
    try:
        pig.main([])
    except SystemExit as exc:
        assert exc.code != 0
        assert "--lane" in capsys.readouterr().err
    else:
        raise AssertionError("main([]) sans --lane doit sortir en erreur")


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


# --- file_saturation : 4ᵉ declencheur (issue #12830, c.508-L2) -------------
#
# Le defaut fondateur : la lane po-2023 (puis po-2027) tirait dans un pool
# virtuellement vide parce que `mergeStateStatus: BLOCKED + MERGEABLE +
# checks tous PENDING depuis > N h` n'etait PAS un declencheur de refus.
# Le 3ᵉ etat etait mecaniquement non-different d'un `BLOCKED + MERGEABLE
# + checks SUCCESS` (attente coordinateur), qu'on veut deliberement laisser
# passer. La discrimination tient en 3 proprietes : AUCUN check n'a demarre
# (statut dans {PENDING, QUEUED}), la PR est MERGEABLE, et elle est ouverte
# depuis plus de `saturation_hours`. Mesure ai-01 du 2026-08-26T04:52Z :
# 1000 runs en file, 14 concurrents, attente observee 4 h 25.


def _state_with_started_at(*, checks=(), mergeable="MERGEABLE", reviews=()):
    """Comme `_state` mais chaque check porte `startedAt` ET `conclusion`/`state`.

    Le format GraphQL reel de `statusCheckRollup.contexts` inclut `startedAt`
    pour les `CheckRun` et `state` (PAS `conclusion`) pour les `StatusContext`
    encore en attente. Le discriminateur file_saturation lit `conclusion` puis
    `state` -- d'ou les helpers ci-dessous qui couvrent les deux formes.
    """
    return {
        "number": 1, "mergeable": mergeable,
        "reviews": {"nodes": [
            {"state": s, "submittedAt": "2026-08-20T00:00:00Z", "author": {"login": a}}
            for s, a in reviews
        ]},
        "commits": {"nodes": [{"commit": {"statusCheckRollup": {"contexts": {"nodes": [
            {"name": t[0], "conclusion": t[1], "state": t[1],
             "isRequired": t[2], "startedAt": "2026-08-25T00:00:00Z"}
            for t in checks
        ]}}}}]},
    }


def test_file_saturation_detected_when_all_checks_pending():
    """Cas fondateur (c.508-L2 sur #12640) : tous les checks en PENDING depuis
    > N h, MERGEABLE, pas de conflit, pas de CHANGES_REQUESTED -- c'est
    exactement la file qui n'a pas bouge, pas un rouge substance.

    Discrimination exigee : un seul FAIL vivant masquerait la file-saturation,
    parce que la lane peut le reparer et la file draine naturellement.
    """
    state = _state_with_started_at(checks=[
        ("PR gate", "PENDING", True),
        ("Scripts Tests (CPU)", "PENDING", True),
        ("Notebook Validation", "PENDING", False),
    ])
    causes = pig.blocking_causes(state, age_hours=28, saturation_hours=24)
    assert any("file_saturation" in c for c in causes)
    # La cause doit nommer le geste -- la lane peut commenter, pas rerun seule.
    assert any("commenter la PR" in c for c in causes)


# --- #13420 : la saturation date les CHECKS, pas la PR ---------------------
#
# Defaut mesure le 2026-08-29 : #12757 (ouverte 121 h) et #12850 (109 h)
# etaient annoncees "1 check requis en PENDING depuis >24h (cause infra)"
# alors que leurs checks avaient demarre a 11:39:44Z, soit 25 min plus tot.
# Le detecteur lisait `age_hours` (age de la PR) et jamais `startedAt`.
# Consequence : le geste prescrit (--ignore-red ou re-run) etait l'inverse du
# bon -- re-run RE-EMPILE dans la file dite saturee, --ignore-red pousse la
# lane devant un garde qui allait repondre. Le bon geste est d'attendre.


def _pending_started(when):
    """PR ancienne (120 h) dont l'unique check requis a demarre a `when`."""
    return {
        "number": 1, "mergeable": "MERGEABLE",
        "reviews": {"nodes": []},
        "commits": {"nodes": [{"commit": {"statusCheckRollup": {
            "state": "PENDING",
            "contexts": {"nodes": [
                {"name": "PR gate", "conclusion": None, "state": "PENDING",
                 "isRequired": True, "startedAt": when},
            ]}}}}]},
    }


def _iso_ago(hours):
    import datetime as _dt
    return (_dt.datetime.now(_dt.timezone.utc)
            - _dt.timedelta(hours=hours)).strftime("%Y-%m-%dT%H:%M:%SZ")


def test_13420_check_frais_sur_pr_ancienne_nest_pas_une_saturation():
    """Le cas mesure : PR ouverte depuis 120 h, check demarre il y a 25 min.

    La file AVANCE. Annoncer une saturation ici prescrit exactement le mauvais
    geste. CE TEST ECHOUE SI LE DETECTEUR REDEVIENT DATE SUR LA PR.
    """
    state = _pending_started(_iso_ago(0.42))  # ~25 min
    assert pig.file_saturation_cause(state, age_hours=120, threshold_hours=24) is None


def test_13420_controle_positif_file_reellement_figee_detectee():
    """Controle positif -- sans lui, un detecteur simplement ETEINT passerait
    le test precedent. Meme PR, meme forme, mais le check n'a pas bouge depuis
    50 h : c'est la vraie saturation, elle DOIT etre annoncee."""
    state = _pending_started(_iso_ago(50))
    cause = pig.file_saturation_cause(state, age_hours=120, threshold_hours=24)
    assert cause is not None
    assert "file-saturation" in cause


def test_13420_frontiere_juste_sous_le_seuil_ne_declenche_pas():
    """Temoin de frontiere : 23 h < 24 h -> pas de saturation."""
    state = _pending_started(_iso_ago(23))
    assert pig.file_saturation_cause(state, age_hours=120, threshold_hours=24) is None


def test_13420_sans_horodatage_lisible_on_retombe_sur_lage_de_la_pr():
    """Un champ absent prive le detecteur de precision, il ne l'eteint pas :
    sans `startedAt` ni `createdAt`, le comportement historique (age de la PR)
    reste en vigueur."""
    state = _pending_started(None)
    cause = pig.file_saturation_cause(state, age_hours=120, threshold_hours=24)
    assert cause is not None and "file-saturation" in cause


def test_13420_horodatage_illisible_ne_leve_pas_dexception():
    """Une chaine non-ISO ne doit pas casser un tour de picker."""
    state = _pending_started("pas-une-date")
    assert pig.file_saturation_cause(
        state, age_hours=120, threshold_hours=24) is not None


def test_13420_le_plus_recent_gagne_sur_les_anciens():
    """Dix checks vieux + un frais = la file a bouge. On date sur le PLUS
    RECENT, parce que la question est 'la file avance-t-elle ?'."""
    state = _pending_started(_iso_ago(50))
    nodes = state["commits"]["nodes"][0]["commit"]["statusCheckRollup"]["contexts"]["nodes"]
    nodes.append({"name": "Always-on guards", "conclusion": None,
                  "state": "PENDING", "isRequired": True,
                  "startedAt": _iso_ago(0.2)})
    assert pig.file_saturation_cause(state, age_hours=120, threshold_hours=24) is None


def test_file_saturation_not_detected_when_a_check_is_success():
    """Faux-positif a eviter : un SUCCESS + des PENDING n'est PAS de la
    file-saturation. La PR a au moins un verdict defini ; elle est en cours
    de merge, pas en attente de derainage de file.
    """
    state = _state_with_started_at(checks=[
        ("PR gate", "PENDING", True),
        ("Scripts Tests (CPU)", "SUCCESS", True),
    ])
    assert pig.blocking_causes(state, age_hours=28, saturation_hours=24) == []


def test_file_saturation_not_detected_when_a_check_fails():
    """Faux-positif a eviter : un FAIL substance prime sur la file-saturation.

    La lane peut reparer la substance ; la file draine naturellement apres
    re-push. Le discriminateur `not causes` dans `blocking_causes` protege
    exactement ce cas (les causes FAIL sont ajoutees avant la detection
    file_saturation).
    """
    state = _state_with_started_at(checks=[
        ("PR gate", "FAILURE", True),
        ("Scripts Tests (CPU)", "PENDING", True),
    ])
    causes = pig.blocking_causes(state, age_hours=28, saturation_hours=24)
    # Le FAIL gagne : file_saturation ne s'y ajoute pas, sinon la cause serait
    # `conflitante` et le geste suggere (commenter + ignore-red) perdrait
    # l'option reparation.
    assert any("check requis en echec" in c for c in causes)
    assert not any("file_saturation" in c for c in causes)


def test_file_saturation_not_detected_below_saturation_threshold():
    """L'age seul ne suffit pas : une PR jeune avec tous checks PENDING est
    dans la queue normale du depot, pas en saturation.

    Cf le mandat du 2026-08-24 sur le retrait du filtre d'age amont : c'est
    ici un garde-fou qui empeche la sur-accusation (mesure : 52/55 PRs le
    2026-08-22 pour la definition naive). Le seuil minimum est le meme que
    pour `aged` (`threshold_hours`), ce qui garde la coherence.
    """
    state = _state_with_started_at(checks=[
        ("PR gate", "PENDING", True),
        ("Scripts Tests (CPU)", "PENDING", True),
    ])
    # age < saturation : rien.
    assert pig.blocking_causes(state, age_hours=2, saturation_hours=24) == []
    # age == saturation : strictement au-dessus (>=) declenche.
    causes = pig.blocking_causes(state, age_hours=24, saturation_hours=24)
    assert any("file_saturation" in c for c in causes)


def test_file_saturation_not_detected_when_not_mergeable():
    """CONFLICTING prime sur la file-saturation : la lane peut rebaser, ce
    n'est plus un rouge de file.

    Le discriminateur exige `mergeable == MERGEABLE`. Une PR en conflit
    attend un rebase, pas un drainage CI.
    """
    state = _state_with_started_at(
        checks=[("PR gate", "PENDING", True)],
        mergeable="CONFLICTING",
    )
    causes = pig.blocking_causes(state, age_hours=28, saturation_hours=24)
    assert "conflits avec main -> rebaser" in causes
    assert not any("file_saturation" in c for c in causes)


def test_file_saturation_trigger_in_red_backlog(monkeypatch):
    """Le 4ᵉ declencheur remonte dans `triggers` quand au moins une PR de la
    lane est file-saturee et a l'age du seuil.

    Ce test est l'integration : `red_backlog` doit appeler `blocking_causes`
    avec `age_hours` et `saturation_hours` derives du seuil, et ajouter
    `"file_saturation"` aux triggers. C'est ce qui rend le narrow
    diagnostique enfin visible a la lane.
    """
    red = _state_with_started_at(checks=[
        ("PR gate", "PENDING", True),
        ("Scripts Tests (CPU)", "PENDING", True),
    ])
    _patch_backlog(monkeypatch, [
        _pr(1, "myia-po-2026:CoursIA", 28),
        _pr(2, "myia-po-2026:CoursIA", 2),
    ], {1: red, 2: red})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24, count_threshold=10)
    # La PR #1 est file-saturee (28 h > 24 h, tous PENDING, MERGEABLE).
    # La PR #2 ne l'est pas (2 h < 24 h).
    assert "file_saturation" in out["triggers"]
    assert any(any("file_saturation" in c for c in r["causes"])
               for r in out["red"] if r["number"] == 1)
    # Et l'ordre respecte la docstring : file_saturation precede `aged`
    # dans la liste des triggers (les deux sont vrais ici, file_saturation
    # doit apparaitre AVANT `aged`).
    assert out["triggers"].index("file_saturation") < out["triggers"].index("aged")


def test_file_saturation_signature_backward_compatible():
    """Le defaut `age_hours=None, saturation_hours=None` preserve les appels
    existants : un PR avec tous checks PENDING et sans ces parametres ne
    declenche PAS file_saturation. C'est ce qui permet aux 12 tests
    historiques de `blocking_causes` de rester verts sans modification.
    """
    state = _state_with_started_at(checks=[
        ("PR gate", "PENDING", True),
        ("Scripts Tests (CPU)", "PENDING", True),
    ])
    # Meme PR que test_file_saturation_detected_when_all_checks_pending,
    # mais sans age_hours : la cause ne doit PAS apparaitre.
    assert pig.blocking_causes(state) == []


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


# #12830 : tests pour le 3e etat file-saturation (BLOCKED + MERGEABLE + rollup
# PENDING > N h). Diagnostic fondateur po-2023 c.508 (PR #12640, 28h, MERGEABLE,
# 0 fail, rollup PENDING).


def _state_with_rollup(rollup_state, checks):
    """Variante de _state qui injecte statusCheckRollup.state.

    _state() historique ne pose pas rollup.state ; c'est exactement le champ
    que #12830 ajoute au fragment GraphQL. Les tests du file-saturation
    ne peuvent pas exister sans cette matiere premiere.
    """
    return {
        "mergeable": "MERGEABLE",
        "commits": {"nodes": [{"commit": {"statusCheckRollup": {
            "state": rollup_state,
            "contexts": {"nodes": [
                {"name": n, "conclusion": c, "state": c, "isRequired": req}
                for (n, c, req) in checks
            ]},
        }}}]},
        "reviews": {"nodes": []},
    }


def test_file_saturation_merges_pending_required_check_old_age():
    """#12830 acceptance #1+#3+#4 : file-saturation detecte si
    mergeable=MERGEABLE + rollup.state=PENDING + 1+ required check
    non-FAIL + age > seuil.
    """
    s = _state_with_rollup("PENDING", [
        ("PR gate", "IN_PROGRESS", True),
        ("Scripts Tests", "SUCCESS", False),
    ])
    assert pig.file_saturation_cause(s, 30.0, 24.0) is not None


def test_file_saturation_ignores_conflicting_pr():
    """#12830 acceptance #4 (negatif) : conflit git = blocking_causes classique,
    pas file-saturation. Cumuler les deux sur une meme PR serait double cause.
    """
    s = _state_with_rollup("PENDING", [
        ("PR gate", "IN_PROGRESS", True),
    ])
    s["mergeable"] = "CONFLICTING"
    assert pig.file_saturation_cause(s, 30.0, 24.0) is None


def test_file_saturation_ignores_successful_rollup():
    """#12830 acceptance #4 (negatif) : rollup SUCCESS = verdict final, pas
    une saturation. La PR est verte au niveau rollup, la lane n'a rien a
    faire cote CI.
    """
    s = _state_with_rollup("SUCCESS", [
        ("PR gate", "SUCCESS", True),
    ])
    assert pig.file_saturation_cause(s, 30.0, 24.0) is None


def test_file_saturation_does_not_double_substance_red():
    """#12830 acceptance #5 : si un check requis est FAIL, c'est un rouge
    substance que blocking_causes prend deja. file_saturation_cause doit
    rendre None pour eviter le double-comptage.
    """
    s = _state_with_rollup("FAILURE", [
        ("PR gate", "FAILURE", True),
    ])
    assert pig.file_saturation_cause(s, 30.0, 24.0) is None


def test_file_saturation_respects_threshold():
    """#12830 acceptance parametree : --saturation-hours distinct du seuil
    substance. Une PR de 5h ne doit pas matcher si seuil=24 ; doit matcher
    si seuil=4. La separation des deux causes (substance vs infra) tient.
    """
    s = _state_with_rollup("PENDING", [
        ("PR gate", "IN_PROGRESS", True),
    ])
    assert pig.file_saturation_cause(s, 5.0, 24.0) is None
    assert pig.file_saturation_cause(s, 5.0, 4.0) is not None


def test_file_saturation_requires_at_least_one_required_check():
    """#12830 acceptance #4 (negatif) : PR sans check requis = pas de CI
    structure, juste l'absence de CI. file-saturation ne s'applique pas.
    """
    s = _state_with_rollup("PENDING", [
        ("advisory opt", "NEUTRAL", False),
    ])
    assert pig.file_saturation_cause(s, 30.0, 24.0) is None

# ---------------------------------------------------------------------------
def test_13972_authoritative_genre_returns_docs_when_body_says_docs() -> None:
    """#13972 : body qui dit Grain: MED/docs -> auteur a declare META.

    Reproduction directe du cas fondateur documente par ai-01 sur #10475 :
    un titre qui suggere 'notebook' (infer_genre rendrait 'notebook-python',
    du CONTENU), un body qui dit 'Grain: MED/docs' (du META). Le tag du body
    est autoritatif : la sortie doit etre 'docs'.
    """
    title = "consolider les doublons de MyIA.AI.Notebooks/notebook_tools/"
    body = (
        "Grain: MED/docs -- lane myia-po-2026:CoursIA\n"
        "\n"
        "## Contexte\n"
        "Ce grain ne compte pas comme le plat principal (G-VAR-1)."
    )
    labels = []
    inferred = pig.infer_genre(title, labels)
    declared = pig.authoritative_genre(body)
    # L inference se trompe (titre contient Notebooks) :
    assert inferred == "notebook-python", (
        f"sanity: infer_genre sur le titre doit renvoyer notebook-python, "
        f"obtenu {inferred!r}"
    )
    # Mais le body est autoritatif :
    assert declared == "docs", (
        f"authoritative_genre doit renvoyer docs depuis le body, "
        f"obtenu {declared!r}"
    )


def test_13972_authoritative_genre_returns_none_when_body_has_no_tag() -> None:
    """#13972 : body sans tag -> None, infer_genre garde la main."""
    body = (
        "## Summary\n\n"
        "Issue ouverte, pas de tag Grain: dans le body.\n"
        "On laisse infer_genre decider depuis le titre."
    )
    assert pig.authoritative_genre(body) is None


def test_13972_authoritative_genre_canonicalizes_aliases() -> None:
    """#13972 : un alias (ex translation) est canonicalise.

    translation -> docs, notebook-genai-python -> notebook-python.
    """
    body_translation = "Grain: MED/translation -- lane myia-po-2026:CoursIA"
    assert pig.authoritative_genre(body_translation) == "docs"

    body_compound = "Grain: DEEP/notebook-genai-python -- lane myia-po-2026:CoursIA"
    assert pig.authoritative_genre(body_compound) == "notebook-python"


def test_13972_authoritative_genre_empty_body_returns_none() -> None:
    """#13972 : body vide -> None (pas de tag, pas d erreur)."""
    assert pig.authoritative_genre("") is None
    # None safe aussi (defense contre les chemins de bord ou le caller passe
    # directement le body=None sans normaliser en amont).
    assert pig.authoritative_genre(None) is None


def test_13972_pool_genre_prefers_body_over_title(monkeypatch) -> None:
    """#13972 integration : le pool attribue le genre du body, pas du titre.

    Cas fondateur #10475 : titre 'consolider MyIA.AI.Notebooks/notebook_tools/'
    ferait infer_genre -> notebook-python (CONTENU), body porte Grain: docs.
    Le dict du pool doit porter genre: docs pour que la restriction G-VAR-1
    (CONTENU only) elimine cet item.

    fetch_pool() appelle `gh issue list` en subprocess ; on mock pour
    injecter un payload shape-compatible.
    """
    payload = [
        {
            "number": 10475,
            "title": "consolider MyIA.AI.Notebooks/notebook_tools/ doublons",
            "labels": [],
            "createdAt": "2026-08-01T00:00:00Z",
            "updatedAt": "2026-09-01T00:00:00Z",
            "body": (
                "Grain: MED/docs -- lane myia-po-2026:CoursIA\n"
                "\n"
                "Ce grain est META, G-VAR-1 : pas le plat principal."
            ),
        },
        {
            "number": 99999,
            "title": "reel notebook python content",
            "labels": [],
            "createdAt": "2026-08-01T00:00:00Z",
            "updatedAt": "2026-09-01T00:00:00Z",
            "body": "Grain: DEEP/notebook-python -- lane myia-po-2026:CoursIA",
        },
    ]
    fake_proc = _FakeCompleted(json.dumps(payload))
    monkeypatch.setattr(pig.subprocess, "run", lambda *a, **kw: fake_proc)
    pool = pig.fetch_pool()
    by_number = {it["number"]: it for it in pool}
    # #10475 : titre dirait notebook-python, body dit docs -> genre = docs (META)
    assert by_number[10475]["genre"] == "docs", (
        f"sanity: titre contient 'notebook_tools', infer_genre rendrait "
        f"'notebook-python' (CONTENU) ; le body porte 'Grain: MED/docs' "
        f"qui doit primer. Obtenu: {by_number[10475]['genre']!r}"
    )
    # #99999 : titre et body disent notebook-python -> genre = notebook-python (CONTENU)
    assert by_number[99999]["genre"] == "notebook-python"


