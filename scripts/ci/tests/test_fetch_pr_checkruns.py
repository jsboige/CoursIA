"""Le collecteur des jambes de check (#26739).

Le collecteur remplace la boucle `gh api commits/<sha>/check-runs` PAR PR des
deux balayeurs (`pr-gate-stale-sweep`, `adjacency-stale-sweep`). Ce fichier
verrouille ce qui doit rester vrai, quel que soit le transport :

  - la **forme** du fichier produit est celle que le selecteur consomme
    (memes noms de champs) : un changement de nom cassereit le balayeur sans
    qu'aucun test de cet organe ne le voie ;
  - la **carte des runs** porte le `workflow_id` : c'est elle qui permet le
    pliage (workflow_id, name) -- le pliage par nom seul fusionnerait les
    verdicts de workflows homonymes (#11808) ;
  - les **pages** sont lues : l'endpoint rend les runs les plus **RECENTS**
    d'abord (identifiants decroissants), donc la page 1 seule donne une vue
    **INCOMPLETE** (les runs les plus anciens manquent) et une jambe peut
    disparaitre ; 51 PR sur 176 (mesure 2026-11-15, pool ouvert) portent
    plus de 100 check-runs, et pour 8 d'entre elles le verdict change ;
  - la conclusion d'un **run** de workflow n'est lue en REST que pour les PRs
    qui portent une jambe `PR gate` ROUGE -- la seule population dont le
    selecteur la consomme (#21300) ;
  - le resume **nomme le quota** : le cout du passage doit etre lisible.

Aucun test n'atteint le reseau : les transports sont remplaces par des
faux, et le lancement de `gh` est simule.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "fetch_pr_checkruns.py"
_spec = importlib.util.spec_from_file_location("fetch_pr_checkruns", SCRIPT)
mod = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = mod
_spec.loader.exec_module(mod)


# --- outils de construction -------------------------------------------------

def _rest_run(name="PR gate", conclusion="failure", run_id=900, title="",
              started="2026-11-15T10:00:00Z", status="completed"):
    return {
        "name": name,
        "status": status,
        "conclusion": conclusion,
        "started_at": started,
        "details_url": (f"https://github.com/jsboige/CoursIA/actions/runs/{run_id}"
                        "/job/4242"),
        "output": {"title": title},
    }


def _rest_page(runs, total_count=None):
    return {"total_count": total_count if total_count is not None else len(runs),
            "check_runs": runs}


def _gql_node(number, draft=False, suites=None, suite_total=None):
    suite_nodes = suites if suites is not None else [
        {"workflowRun": {"databaseId": 900,
                         "workflow": {"databaseId": 555, "name": "PR gate"}}}]
    return {
        "number": number,
        "isDraft": draft,
        "commits": {"nodes": [{"commit": {"checkSuites": {
            "totalCount": suite_total,
            "nodes": suite_nodes,
        }}}]},
    }


def _gql_page(nodes, has_next=False, cursor=None, cost=1):
    return {"data": {"rateLimit": {"cost": cost, "remaining": 4900},
                     "repository": {"pullRequests": {
                         "pageInfo": {"hasNextPage": has_next, "endCursor": cursor},
                         "nodes": nodes,
                     }}}}


def _prs(*numbers):
    return [{"number": n, "sha": f"sha{n}", "fork": False, "merge_state": ""}
            for n in numbers]


# --- 1. La forme du fichier produit ----------------------------------------

def test_la_forme_du_fichier_produit_est_celle_du_selecteur():
    legs, _pages, _total, _trunc = mod.read_legs("o/r", "sha1", rest=lambda _p: _rest_page(
        [_rest_run()]))
    assert legs
    for leg in legs:
        assert set(leg) == {"name", "status", "conclusion", "started_at",
                            "details_url", "title"}, leg


def test_le_titre_vide_est_une_chaine_et_non_une_absence():
    """`title` porte le signal du genou muet (#15825) : une cle ABSENTE
    change le classement du selecteur (l'absence de cle n'est jamais un
    muet)."""
    legs, _p, _t, _trunc = mod.read_legs("o/r", "sha1", rest=lambda _p: _rest_page(
        [_rest_run(title="")]))
    assert legs[0]["title"] == ""


def test_les_conclusions_restent_en_minuscules():
    """Le contrat du selecteur compare aux ensembles RED/GREEN du contrat
    REST (minuscules) : une normalisation absente ferait croire le pool
    vert."""
    run = _rest_run()
    run["conclusion"] = "FAILURE"
    run["status"] = "COMPLETED"
    legs, _p, _t, _trunc = mod.read_legs("o/r", "sha1", rest=lambda _p: _rest_page([run]))
    assert legs[0]["conclusion"] == "failure"
    assert legs[0]["status"] == "completed"


def test_parse_prs_lit_le_listing_du_balayeur(tmp_path):
    path = tmp_path / "openprs.txt"
    path.write_text("26745 abc123 false blocked\n"
                    "26746 def456 true \n"
                    "ligne vide\n"
                    "\n", encoding="utf-8")
    prs = mod.parse_prs(path)
    assert prs[0] == {"number": 26745, "sha": "abc123", "fork": False,
                      "merge_state": "blocked"}
    assert prs[1]["fork"] is True
    assert prs[1]["merge_state"] == ""
    assert len(prs) == 2


def test_parse_prs_lit_le_listing_court_de_l_adjacency(tmp_path):
    """Le balayeur d'adjacence n'ecrit que `numero sha`."""
    path = tmp_path / "adjacency_openprs.txt"
    path.write_text("26745 abc123\n26746 def456\n", encoding="utf-8")
    prs = mod.parse_prs(path)
    assert [pr["number"] for pr in prs] == [26745, 26746]
    assert prs[0]["fork"] is False


# --- 2. La pagination : le defaut de correction -----------------------------

def test_la_pagination_lit_la_page_suivante():
    """L'endpoint rend les runs les plus RECENTS d'abord : une tete qui porte
    plus de 100 runs exige les pages suivantes, sinon la lecture est
    INCOMPLETE (les runs les plus anciens manquent)."""
    pages = {
        1: _rest_page([_rest_run(name="PR gate", conclusion="failure")] * 100,
                      total_count=135),
        2: _rest_page([_rest_run(name="PR gate", conclusion="success")] * 35,
                      total_count=135),
    }
    calls = []

    def rest(path):
        page = int(path.rsplit("page=", 1)[1])
        calls.append(page)
        return pages[page]

    legs, pages_read, total, _trunc = mod.read_legs("o/r", "sha1", rest=rest)
    assert calls == [1, 2]
    assert pages_read == 2
    assert total == 135
    assert len(legs) == 135
    assert legs[-1]["conclusion"] == "success", "la page 2 doit etre lue"


def test_la_pagination_s_arrete_a_la_derniere_page():
    pages = {1: _rest_page([_rest_run()] * 100, total_count=100)}
    legs, pages_read, _total, _trunc = mod.read_legs(
        "o/r", "sha1", rest=lambda p: pages[1])
    assert pages_read == 1
    assert len(legs) == 100


# --- 3. La carte des runs : GraphQL, en bloc --------------------------------

def test_la_carte_porte_le_workflow_id_pour_le_pliage():
    """#11808 -- le pliage est par (workflow_id, name). La carte doit donc
    porter le workflow_id, et non le seul run id."""
    maps, stats = mod.read_run_maps(
        "o/r", transport=lambda q, v: _gql_page([_gql_node(1)]))
    assert maps[1]["900"] == 555
    assert stats["graphql_calls"] == 1


def test_la_pagination_graphql_couvre_le_pool():
    pages = {None: _gql_page([_gql_node(1)], has_next=True, cursor="c1"),
             "c1": _gql_page([_gql_node(2)])}
    maps, stats = mod.read_run_maps(
        "o/r", transport=lambda q, v: pages[v["after"]])
    assert set(maps) == {1, 2}
    assert stats["graphql_calls"] == 2


def test_une_carte_fenetree_est_comptee_et_non_silenciee():
    """Une PR qui porte plus de suites que la fenetre : son pliage retombe
    sur le run id (comportement historique) pour les runs NON lus. L'etat
    est REPORTE, jamais perdu -- une carte fenetree muette serait un repli
    invisible."""
    maps, stats = mod.read_run_maps(
        "o/r", transport=lambda q, v: _gql_page([_gql_node(1, suite_total=200)]))
    assert stats["map_truncated"] == [1]
    assert maps[1], "les suites lues restent dans la carte"


def test_les_drafts_sont_ignores():
    maps, _stats = mod.read_run_maps(
        "o/r", transport=lambda q, v: _gql_page([_gql_node(1, draft=True)]))
    assert maps == {}


# --- 4. La conclusion de run : REST, et pour qui ----------------------------

def test_la_carte_des_runs_est_lue_pour_une_pr_sans_jambe_de_gate():
    """#21463 : la population BLOCKED sans check-run `PR gate` doit pouvoir
    trouver le run `PR gate` de sa tete -- donc la carte des runs ne doit
    PAS etre conditionnee a la presence d'une jambe de gate."""
    def rest(path):
        return _rest_page([_rest_run(name="Other", conclusion="failure")])

    lines, _summary = mod.collect(
        repo="o/r", prs=_prs(1), rest=rest, workers=1,
        graphql=lambda q, v: _gql_page([_gql_node(1)]))
    assert lines[0]["workflows"], "la carte existe sans jambe de gate"


def test_red_gate_legs_reconnait_la_jambe_rouge():
    assert mod.red_gate_legs([{"name": "PR gate", "conclusion": "failure"}])
    assert mod.red_gate_legs([{"name": "PR gate", "conclusion": "cancelled"}])
    assert not mod.red_gate_legs([{"name": "PR gate", "conclusion": "success"}])
    assert not mod.red_gate_legs([{"name": "Other", "conclusion": "failure"}])


def test_la_conclusion_de_run_n_est_lue_en_rest_que_pour_une_jambe_rouge():
    red = _rest_run(name="PR gate", conclusion="failure", run_id=900)
    green = _rest_run(name="PR gate", conclusion="success", run_id=901)

    def rest(path):
        if "check-runs" in path:
            sha = path.split("/commits/")[1].split("/")[0]
            return _rest_page([red] if sha == "sha1" else [green])
        calls.append(path)
        return {"workflow_runs": [{"id": 900, "workflow_id": 555,
                                   "conclusion": "startup_failure"}]}

    calls = []
    lines, summary = mod.collect(
        repo="o/r", prs=_prs(1, 2), rest=rest, workers=1,
        graphql=lambda q, v: _gql_page([_gql_node(1), _gql_node(2)]))
    assert len(calls) == 1, "seule la PR rouge a droit a une lecture REST"
    assert summary["run_conclusion_calls"] == 1
    ligne = next(line for line in lines if line["number"] == 1)
    assert ligne["workflows"]["900"]["c"] == "startup_failure"


def test_une_lecture_rest_ratee_n_interrompt_pas_la_collecte():
    def rest(path):
        if "check-runs" in path:
            return _rest_page([_rest_run(conclusion="failure")])
        raise mod.CollectionError("HTTP 502")

    lines, summary = mod.collect(
        repo="o/r", prs=_prs(1), rest=rest, workers=1,
        graphql=lambda q, v: _gql_page([_gql_node(1)]))
    assert len(lines) == 1, "la PR reste lue, sa carte de runs est vide"
    assert summary["run_conclusion_failures"] == 1


# --- 5. La collecte ---------------------------------------------------------

def test_la_collecte_omet_une_pr_illisible():
    def rest(path):
        if "sha2" in path:
            raise mod.CollectionError("HTTP 500")
        return _rest_page([_rest_run()])

    lines, summary = mod.collect(
        repo="o/r", prs=_prs(1, 2), rest=rest, workers=1,
        graphql=lambda q, v: _gql_page([_gql_node(1), _gql_node(2)]))
    assert [line["number"] for line in lines] == [1]
    assert summary["prs_omitted"] == 1
    assert "2" in summary["unreadable"]


def test_la_ligne_produite_porte_toutes_les_cles_du_selecteur():
    def rest(path):
        return _rest_page([_rest_run()])

    lines, _summary = mod.collect(
        repo="o/r", prs=_prs(1), rest=rest, workers=1,
        graphql=lambda q, v: _gql_page([_gql_node(1)]))
    line = lines[0]
    assert set(line) == {"number", "sha", "fork", "merge_state", "checks",
                         "workflows"}, line


def test_le_resume_nomme_le_quota_api():
    """Le quota nomme TOUTES les lectures REST : les pages de jambes ET les
    conclusions de run. Un quota qui n'additionnerait qu'une partie des
    appels donnerait un cout sous-estime au lecteur du log."""
    def rest(path):
        if "check-runs" in path:
            return _rest_page([_rest_run()])
        return {"workflow_runs": [{"id": 900, "workflow_id": 555,
                                   "conclusion": "failure"}]}

    _lines, summary = mod.collect(
        repo="o/r", prs=_prs(1), rest=rest, workers=1,
        graphql=lambda q, v: _gql_page([_gql_node(1)], cost=3))
    assert summary["graphql_calls"] == 1
    assert summary["graphql_points"] == 3
    assert summary["rest_calls"] == 2, "1 page de jambes + 1 conclusion de run"
    assert summary["rest_pages"] == 1


def test_le_resume_compte_les_pages_lues():
    def rest(path):
        if "check-runs" in path:
            page = int(path.rsplit("page=", 1)[1])
            return _rest_page([_rest_run()] * 100, total_count=135) if page == 1 \
                else _rest_page([_rest_run()] * 35, total_count=135)
        return {"workflow_runs": [{"id": 900, "workflow_id": 555,
                                   "conclusion": "failure"}]}

    _lines, summary = mod.collect(
        repo="o/r", prs=_prs(1), rest=rest, workers=1,
        graphql=lambda q, v: _gql_page([_gql_node(1)]))
    assert summary["rest_pages"] == 2
    assert summary["rest_calls"] == 3, "2 pages + 1 conclusion de run"


def test_la_carte_des_runs_peut_etre_desactivee():
    """Le balayeur d'adjacence ne consomme NI la carte ni les conclusions de
    run : il ne doit payer aucune de ces lectures."""
    calls = []

    def rest(path):
        calls.append(path)
        return _rest_page([_rest_run()])

    _lines, summary = mod.collect(
        repo="o/r", prs=_prs(1), rest=rest, workers=1,
        use_run_map=False, use_run_conclusions=False)
    assert summary["graphql_calls"] == 0
    assert summary["run_conclusion_calls"] == 0
    assert not any("actions/runs" in path for path in calls)


# --- 6. La limite secondaire de l'API ---------------------------------------

def test_la_limite_secondaire_est_reconnue():
    assert mod._is_secondary_limit(
        "API rate limit already exceeded for user ID 3159389")
    assert mod._is_secondary_limit("You have exceeded a secondary rate limit")
    assert mod._is_secondary_limit("abuse detection mechanism triggered")
    assert not mod._is_secondary_limit("HTTP 502: Bad gateway")


def test_un_refus_de_limite_secondaire_est_rejoue_et_non_compte_comme_echec(monkeypatch):
    """Mesure 2026-11-15 : une rafale fait echouer l'appel avec "API rate
    limit already exceeded" alors que le budget horaire est intact. La
    collecte doit ATTENDRE et REJOUER, pas perdre la PR."""
    calls = {"n": 0}
    waits = []

    class _Proc:
        returncode = 0
        stdout = "{}"
        stderr = ""

    def fake_run(cmd, **kwargs):
        calls["n"] += 1
        if calls["n"] == 1:
            proc = _Proc()
            proc.returncode = 1
            proc.stderr = "API rate limit already exceeded for user ID 1"
            return proc
        proc = _Proc()
        proc.stdout = json.dumps({"total_count": 0, "check_runs": []})
        return proc

    monkeypatch.setattr(mod.subprocess, "run", fake_run)
    payload = mod.gh_api("repos/o/r/commits/sha/check-runs",
                         sleep=waits.append)
    assert payload == {"total_count": 0, "check_runs": []}
    assert calls["n"] == 2
    assert waits, "l'attente doit etre reelle"


def test_une_erreur_non_rejouable_propage(monkeypatch):
    class _Proc:
        returncode = 1
        stdout = ""
        stderr = "HTTP 502 Bad gateway"

    monkeypatch.setattr(mod.subprocess, "run", lambda cmd, **kw: _Proc())
    try:
        mod.gh_api("repos/o/r/commits/sha/check-runs", sleep=lambda _s: None)
    except mod.CollectionError as exc:
        assert "502" in str(exc)
    else:
        raise AssertionError("une erreur fatale doit etre propagee")


# --- 7. Le point d'entree ---------------------------------------------------

def _listing(tmp_path):
    path = tmp_path / "openprs.txt"
    path.write_text("1 sha1 false \n", encoding="utf-8")
    return path


def test_main_ecrit_le_fichier_et_le_resume(tmp_path, monkeypatch):
    def fake_collect(**kwargs):
        return ([{"number": 1, "sha": "sha1", "fork": False, "merge_state": "",
                  "checks": [], "workflows": {}}],
                {"prs_listed": 1, "prs_inspected": 1, "prs_omitted": 0,
                 "rest_calls": 1, "rest_pages": 1, "graphql_calls": 1,
                 "graphql_points": 1, "map_truncated": [],
                 "run_conclusion_calls": 0, "run_conclusion_failures": 0,
                 "unreadable": {}})
    monkeypatch.setattr(mod, "collect", fake_collect)
    out = tmp_path / "runs.jsonl"
    summary = tmp_path / "summary.json"
    rc = mod.main(["--repo", "o/r", "--prs", str(_listing(tmp_path)),
                   "--out", str(out), "--summary", str(summary)])
    assert rc == 0
    assert out.read_text(encoding="utf-8").strip()
    assert "api-quota:" in json.loads(summary.read_text(encoding="utf-8"))["api_quota"]


def test_main_echoue_sans_pr_inspectee(tmp_path, monkeypatch):
    def fake_collect(**kwargs):
        return ([], {"prs_listed": 3, "prs_inspected": 0, "prs_omitted": 3,
                     "rest_calls": 3, "rest_pages": 3, "graphql_calls": 0,
                     "graphql_points": 0, "map_truncated": [],
                     "run_conclusion_calls": 0, "run_conclusion_failures": 0,
                     "unreadable": {"1": "HTTP 500"}})
    monkeypatch.setattr(mod, "collect", fake_collect)
    rc = mod.main(["--repo", "o/r", "--prs", str(_listing(tmp_path)),
                   "--out", str(tmp_path / "runs.jsonl")])
    assert rc == 2, "une collecte a vide doit etre un echec, pas un vert"


def test_main_propage_un_echec_de_collecte(tmp_path, monkeypatch):
    def fake_collect(**kwargs):
        raise mod.CollectionError("HTTP 500")

    monkeypatch.setattr(mod, "collect", fake_collect)
    rc = mod.main(["--repo", "o/r", "--prs", str(_listing(tmp_path)),
                   "--out", str(tmp_path / "runs.jsonl")])
    assert rc == 1


# --- 8. Les muets du resume sont nommes (#26739) -----------------------------
#
# Quatre cas rendaient une lecture PARTIELLE sans le dire : le plafond de
# pages coupe en silence, les PRs illisibles ne sont jamais nommees, les
# erreurs GraphQL accompagnees de `data` sont ignorees, et une page
# `repository: null` rend une carte vide. Le repli du selecteur (run_id) est
# plus etroit dans les quatre cas -- mais muet.


def test_le_plafond_de_pages_tronque_en_signaleant():
    """Le plafond existe (5000 runs par tete) ; ce qui manquait, c'est sa
    DECLARATION : une lecture tronquee sans trace donne au selecteur une vue
    perimee, en silence."""
    def rest(_path):
        # pas de `total_count` : l'endpoint en rend un, mais une page pleine
        # SANS total laisse la pagination continuer (c'est le cas teste ici)
        return {"check_runs": [_rest_run(run_id=i) for i in range(100)]}

    _legs, pages, _total, truncated = mod.read_legs(
        "o/r", "sha1", rest=rest, max_pages=2)
    assert truncated is True, "la troncature doit etre rendue"
    assert pages == 2, f"le plafond doit arreter la lecture (pages={pages})"


def test_une_lecture_complete_n_est_pas_tronquee():
    """Controle negatif : une tete qui tient en deux pages n'est PAS
    declaree tronquee (un garde qui rouge toujours ne prouve rien)."""
    def rest(_path):
        return _rest_page([_rest_run()])

    _legs, _pages, _total, truncated = mod.read_legs("o/r", "sha1", rest=rest)
    assert truncated is False


def test_la_troncature_nomme_la_pr_dans_le_resume():
    def rest(_path):
        # pas de `total_count` : l'endpoint en rend un, mais une page pleine
        # SANS total laisse la pagination continuer (c'est le cas teste ici)
        return {"check_runs": [_rest_run(run_id=i) for i in range(100)]}

    _lines, summary = mod.collect(
        repo="o/r", prs=_prs(7), rest=rest, use_run_map=False,
        use_run_conclusions=False)
    assert summary["truncated_prs"] == [7], summary["truncated_prs"]
    assert summary["rest_page_cap"] == 5000


def test_les_prs_illisibles_sont_nommees_dans_le_resume():
    def rest(path):
        if "sha1" in path:
            raise mod.CollectionError(
                "GET repos/o/r/commits/sha1/check-runs : gh: Not Found (HTTP 404)")
        return _rest_page([_rest_run()])

    _lines, summary = mod.collect(
        repo="o/r", prs=_prs(1, 2), rest=rest, use_run_map=False,
        use_run_conclusions=False)
    assert summary["unreadable_prs"] == [1]
    assert summary["unreadable_detail"]["1"]["code"] == "HTTP 404"
    assert summary["unreadable_detail"]["1"]["endpoint"] == (
        "GET repos/o/r/commits/sha1/check-runs")


def test_les_erreurs_graphql_avec_data_sont_comptees():
    """Une reponse qui porte `data` ET `errors` ne fait pas echouer la
    lecture, mais elle rend une carte PARTIELLE : elle doit etre comptee."""
    def graphql(_query, _variables):
        payload = _gql_page([_gql_node(1)])
        payload["errors"] = [{"message": "Some paths are not exposed"}]
        return payload

    _maps, stats = mod.read_run_maps("o/r", transport=graphql)
    assert stats["graphql_errors"], "une erreur GraphQL avec data est muette"


def test_une_page_repository_nulle_est_comptee():
    """`repository: null` rend une carte VIDE : le repli (run_id) s'y applique
    pour TOUTES les PRs du pool. C'est compte, pas absorbé."""
    def graphql(_query, _variables):
        return {"data": {"rateLimit": {"cost": 1, "remaining": 4999},
                         "repository": None}}

    _maps, stats = mod.read_run_maps("o/r", transport=graphql)
    assert stats["null_repository_pages"] == 1


def test_main_annonce_les_quatre_muets(tmp_path, monkeypatch, capsys):
    """Le resume se traduit en annotations NOMMEES : chaque cas muet
    devient une ligne qui cite la PR concernee."""
    def fake_collect(**_kwargs):
        return ([], {
            "prs_listed": 2, "prs_inspected": 1, "prs_omitted": 1,
            "rest_calls": 3, "rest_pages": 3, "graphql_calls": 1,
            "graphql_points": 1, "map_truncated": [],
            "run_conclusion_calls": 0, "run_conclusion_failures": 0,
            "unreadable": {"1": "HTTP 404"},
            "unreadable_prs": [1],
            "unreadable_detail": {}, "last_unreadable": {},
            "truncated_prs": [2], "rest_page_cap": 5000,
            "graphql_errors": ["Some paths are not exposed"],
            "null_repository_pages": 1,
        })
    monkeypatch.setattr(mod, "collect", fake_collect)
    rc = mod.main(["--repo", "o/r", "--prs", str(_listing(tmp_path)),
                   "--out", str(tmp_path / "runs.jsonl")])
    assert rc == 0
    err = capsys.readouterr().err
    assert "PRs illisibles" in err and "#1" in err, err
    assert "lecture tronquee" in err and "#2" in err, err
    assert "erreurs GraphQL partielles" in err, err
    assert "repository nul" in err, err


def test_le_resume_nomme_le_dernier_echec_dans_l_ordre_du_listing():
    """Le dernier echec est celui du LISTING, pas celui de l'arrivee des
    threads : deux executions du meme pool peuvent differer, et le no-op
    doit etre reproductible."""
    def rest(path):
        if "sha1" in path:
            raise mod.CollectionError(
                "GET repos/o/r/commits/sha1/check-runs : gh: Not Found (HTTP 404)")
        if "sha3" in path:
            raise mod.CollectionError(
                "GET repos/o/r/commits/sha3/check-runs : gh: Not Found (HTTP 500)")
        return _rest_page([_rest_run()])

    _lines, summary = mod.collect(
        repo="o/r", prs=_prs(1, 2, 3), rest=rest, use_run_map=False,
        use_run_conclusions=False)
    assert summary["unreadable_prs"] == [1, 3]
    assert summary["last_unreadable"]["pr"] == 3
    assert summary["last_unreadable"]["sha"] == "sha3"
    assert summary["last_unreadable"]["code"] == "HTTP 500"
