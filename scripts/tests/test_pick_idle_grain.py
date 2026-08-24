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


def _patch_backlog(monkeypatch, prs, states):
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {n: states[n] for n in nums if n in states})


def _pr(n, lane, age_hours, *, draft=False):
    created = (pig.NOW - pig.dt.timedelta(hours=age_hours)).strftime("%Y-%m-%dT%H:%M:%SZ")
    body = f"Grain: MED/guard -- lane {lane}\n" if lane else "pas de tag\n"
    return {"number": n, "title": f"pr {n}", "body": body,
            "createdAt": created, "isDraft": draft}


def test_red_backlog_scopes_to_the_lane_and_the_threshold(monkeypatch):
    red = _state(checks=[("PR gate", "FAILURE", True)])
    _patch_backlog(monkeypatch, [
        _pr(1, "myia-po-2026:CoursIA", 30),          # ma lane, vieille, rouge -> compte
        _pr(2, "myia-po-2026:CoursIA", 3),           # ma lane, fraiche        -> non
        _pr(3, "myia-po-2023:CoursIA", 30),          # autre lane              -> non
        _pr(4, "myia-po-2026:CoursIA", 30, draft=True),  # brouillon           -> non
    ], {1: red, 2: red, 3: red, 4: red})
    out = pig.red_backlog("myia-po-2026:CoursIA", 24)
    assert [r["number"] for r in out["red"]] == [1]


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
    out = pig.red_backlog("myia-po-2026:CoursIA", 24)
    assert [r["number"] for r in out["red"]] == [1]
    assert [u["number"] for u in out["unattributed_blocked"]] == [9]


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
