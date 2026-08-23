"""Tests for scripts/pick_idle_grain.py recent_delivery (#12174).

Un detecteur se valide par ses faux negatifs, pas par ses hits. Le cas
fondateur (2026-08-21) : #12014 tiree en urne grain a 16:47Z alors que
#12077, mergee a 16:19Z, avait deja livre 3 de ses 4 items -- le label
``candidate-delivered`` (workflow schedule: quotidien, dernier run 05:49Z)
n'en savait rien. Le replay ci-dessous rejoue cet etat exact.
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
        {"number": 12077, "mergedAt": "2026-08-21T16:19:17Z"},
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
        assert "--state" in cmd and "merged" in cmd
        assert "--limit" in cmd and "20" in cmd
        assert "--search" in cmd
        assert cmd[cmd.index("--search") + 1] == f"{n} in:title,body"


def test_merge_older_than_update_not_annotated(monkeypatch):
    """Une fusion ANTERIEURE a la derniere activite de l'issue est deja
    digeree par le body -- pas d'annotation, sinon le signal noie."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "mergedAt": "2026-08-21T04:00:00Z"},
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
        {"number": 12077, "mergedAt": "2026-08-21T16:19:17Z"},
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
        {"number": 12077, "mergedAt": "2026-08-21T16:19:17Z"},
        {"number": 12065, "mergedAt": "2026-08-20T10:00:00Z"},
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
