"""Tests de scripts/coordination/submodule_watch.py (sans reseau : runner injecte)."""
from __future__ import annotations

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import submodule_watch as sw  # noqa: E402

NOW = datetime(2026, 10, 19, 0, 0, tzinfo=timezone.utc)

GITMODULES = (
    "submodule.A/MGS.path A/MGS\n"
    "submodule.A/MGS.url https://github.com/jsboige/MetaGeneticSharp\n"
    "submodule.B/Fleet.path B/Fleet\n"
    "submodule.B/Fleet.url https://github.com/MyIntelligenceAgency/semantic-fleet.git\n"
    "submodule.B/Fleet.branch stable-from-v0343\n"
)


def _cp(stdout: str = "", rc: int = 0, stderr: str = "") -> subprocess.CompletedProcess:
    return subprocess.CompletedProcess(args=[], returncode=rc, stdout=stdout, stderr=stderr)


def _leg(name: str, verdict: str) -> dict:
    """Une jambe ``CheckRun`` telle que l'API la rend, au verdict demande."""
    if verdict == "FAILURE":
        return {"__typename": "CheckRun", "name": name, "status": "COMPLETED", "conclusion": "FAILURE"}
    if verdict == "PENDING":
        return {"__typename": "CheckRun", "name": name, "status": "IN_PROGRESS", "conclusion": None}
    return {"__typename": "CheckRun", "name": name, "status": "COMPLETED", "conclusion": "SUCCESS"}


def _pr(number: int, created: str, *, bot: bool = False, draft: bool = False, comments: int = 0,
        reviews: int = 0, rollup: str | None = "SUCCESS", legs: dict | None = None) -> dict:
    commit: dict = {}
    if rollup is not None or legs is not None:
        check: dict = {}
        if rollup is not None:
            check["state"] = rollup
        if legs is not None:
            check["contexts"] = {"nodes": [_leg(n, v) for n, v in legs.items()]}
        commit["statusCheckRollup"] = check
    return {
        "number": number, "title": f"pr {number}", "isDraft": draft, "createdAt": created,
        "baseRefName": "main", "mergeable": "MERGEABLE",
        "author": {"__typename": "Bot" if bot else "User", "login": "dependabot" if bot else "jsboige"},
        "comments": {"totalCount": comments}, "reviews": {"totalCount": reviews},
        "commits": {"nodes": [{"commit": commit}]},
    }


def _graphql(nodes: list) -> str:
    return json.dumps({"data": {"repository": {"pullRequests": {"totalCount": len(nodes), "nodes": nodes}}}})


def make_runner(prs_by_repo: dict, *, gitlinks: dict, remotes: dict, fail_repo: str | None = None):
    calls = []

    def run(cmd: list) -> subprocess.CompletedProcess:
        calls.append(cmd)
        if cmd[:3] == ["git", "config", "-f"]:
            return _cp(GITMODULES)
        if cmd[:2] == ["git", "ls-tree"]:
            path = cmd[3]
            return _cp(f"160000 commit {gitlinks[path]}\t{path}\n") if path in gitlinks else _cp("")
        if cmd[:2] == ["git", "ls-remote"]:
            key = (cmd[2], cmd[3])
            return _cp(f"{remotes[key]}\t{cmd[3]}\n") if key in remotes else _cp("", rc=0)
        if cmd[:3] == ["gh", "api", "graphql"]:
            owner = next(a.split("=", 1)[1] for a in cmd if a.startswith("owner="))
            name = next(a.split("=", 1)[1] for a in cmd if a.startswith("name="))
            slug = f"{owner}/{name}"
            if slug == fail_repo:
                return _cp("", rc=1, stderr="HTTP 403")
            return _cp(_graphql(prs_by_repo.get(slug, [])))
        raise AssertionError(f"commande inattendue : {cmd}")

    run.calls = calls
    return run


MGS_URL = "https://github.com/jsboige/MetaGeneticSharp"
FLEET_URL = "https://github.com/MyIntelligenceAgency/semantic-fleet.git"
SAME = {"A/MGS": "a" * 40, "B/Fleet": "b" * 40}
REMOTES_SAME = {(MGS_URL, "HEAD"): "a" * 40, (FLEET_URL, "refs/heads/stable-from-v0343"): "b" * 40}


def test_repo_slug_formes():
    assert sw.repo_slug("https://github.com/jsboige/MetaGeneticSharp") == "jsboige/MetaGeneticSharp"
    assert sw.repo_slug("https://github.com/Org/Repo.git") == "Org/Repo"
    assert sw.repo_slug("git@github.com:Org/Repo.git") == "Org/Repo"
    assert sw.repo_slug("https://gitlab.com/x/y") is None


def test_read_submodules_lit_la_branche_declaree():
    run = make_runner({}, gitlinks=SAME, remotes=REMOTES_SAME)
    subs = {s["path"]: s for s in sw.read_submodules(run)}
    assert subs["A/MGS"]["branch"] is None
    assert subs["B/Fleet"]["branch"] == "stable-from-v0343"
    assert subs["B/Fleet"]["slug"] == "MyIntelligenceAgency/semantic-fleet"


def test_pr_humaine_sans_regard_au_dela_du_seuil_est_unseen():
    # Cas fondateur : MetaGeneticSharp#62, ouverte le 16/10, 0 commentaire, 0 review.
    row = sw.classify_pr(_pr(62, "2026-10-16T10:00:00Z"), NOW, 24.0)
    assert row["state"] == "UNSEEN"


def test_pr_recente_ou_commentee_n_est_pas_unseen():
    assert sw.classify_pr(_pr(1, "2026-10-18T12:00:00Z"), NOW, 24.0)["state"] == "OPEN"
    assert sw.classify_pr(_pr(2, "2026-10-01T00:00:00Z", comments=1), NOW, 24.0)["state"] == "OPEN"
    assert sw.classify_pr(_pr(3, "2026-10-01T00:00:00Z", reviews=1), NOW, 24.0)["state"] == "OPEN"


def test_bot_et_brouillon_ne_sont_pas_unseen():
    assert sw.classify_pr(_pr(4, "2026-09-01T00:00:00Z", bot=True), NOW, 24.0)["state"] == "BOT"
    assert sw.classify_pr(_pr(5, "2026-09-01T00:00:00Z", draft=True), NOW, 24.0)["state"] == "DRAFT"


def test_absence_de_checks_se_lit_none():
    assert sw.classify_pr(_pr(6, "2026-10-18T12:00:00Z", rollup=None), NOW, 24.0)["checks"] == "NONE"


def test_tout_vu_et_gitlinks_alignes_rc0():
    run = make_runner({"jsboige/MetaGeneticSharp": [_pr(1, "2026-10-01T00:00:00Z", reviews=1)]},
                      gitlinks=SAME, remotes=REMOTES_SAME)
    report = sw.watch(24.0, "origin/main", NOW, run)
    assert sw.exit_code(report) == 0


def test_une_pr_unseen_rougit_rc1():
    run = make_runner({"jsboige/MetaGeneticSharp": [_pr(62, "2026-10-16T10:00:00Z")]},
                      gitlinks=SAME, remotes=REMOTES_SAME)
    report = sw.watch(24.0, "origin/main", NOW, run)
    assert sw.exit_code(report) == 1
    assert "UNSEEN #62" in sw.render(report)


def test_les_bots_seuls_ne_rougissent_pas():
    run = make_runner({"MyIntelligenceAgency/semantic-fleet": [_pr(90, "2026-09-01T00:00:00Z", bot=True)]},
                      gitlinks=SAME, remotes=REMOTES_SAME)
    report = sw.watch(24.0, "origin/main", NOW, run)
    assert sw.exit_code(report) == 0
    assert "1 PR(s) de bot" in sw.render(report)


def test_derive_compare_a_la_branche_declaree_pas_a_head():
    # Faux positif #14872 : un sous-module epingle sur sa branche ne se compare jamais a HEAD.
    remotes = dict(REMOTES_SAME)
    remotes[(FLEET_URL, "HEAD")] = "c" * 40  # HEAD distant different, ignore
    run = make_runner({}, gitlinks=SAME, remotes=remotes)
    report = sw.watch(24.0, "origin/main", NOW, run)
    fleet = next(r for r in report["repos"] if r["path"] == "B/Fleet")
    assert fleet["drift"]["state"] == "OK"
    assert fleet["drift"]["remote_ref"] == "refs/heads/stable-from-v0343"


def test_derive_reelle_rougit_rc1():
    remotes = dict(REMOTES_SAME)
    remotes[(MGS_URL, "HEAD")] = "d" * 40
    run = make_runner({}, gitlinks=SAME, remotes=remotes)
    report = sw.watch(24.0, "origin/main", NOW, run)
    assert next(r for r in report["repos"] if r["path"] == "A/MGS")["drift"]["state"] == "DERIVE"
    assert sw.exit_code(report) == 1


def test_ls_remote_muet_est_injoignable_jamais_egal():
    remotes = {(FLEET_URL, "refs/heads/stable-from-v0343"): "b" * 40}  # MGS muet
    run = make_runner({}, gitlinks=SAME, remotes=remotes)
    report = sw.watch(24.0, "origin/main", NOW, run)
    assert next(r for r in report["repos"] if r["path"] == "A/MGS")["drift"]["state"] == "INJOIGNABLE"
    assert sw.exit_code(report) == 2


def test_depot_illisible_est_unknown_jamais_vide():
    run = make_runner({}, gitlinks=SAME, remotes=REMOTES_SAME, fail_repo="jsboige/MetaGeneticSharp")
    report = sw.watch(24.0, "origin/main", NOW, run)
    mgs = next(r for r in report["repos"] if r["path"] == "A/MGS")
    assert mgs["prs"] is None and "403" in mgs["prs_error"]
    assert sw.exit_code(report) == 2
    assert "UNKNOWN" in sw.render(report)


def test_unseen_l_emporte_sur_unknown():
    run = make_runner({"MyIntelligenceAgency/semantic-fleet": [_pr(64, "2026-07-20T00:00:00Z")]},
                      gitlinks=SAME, remotes=REMOTES_SAME, fail_repo="jsboige/MetaGeneticSharp")
    assert sw.exit_code(sw.watch(24.0, "origin/main", NOW, run)) == 1


def test_gel_declare_dans_le_titre_est_hold_et_ne_rougit_pas():
    # Cas Argumentum#666 : « [HOLD post-tag] », gelee sciemment, jamais commentee.
    gel = dict(_pr(666, "2026-09-01T00:00:00Z"), title="[HOLD post-tag] retrait du shim")
    wip = dict(_pr(667, "2026-09-01T00:00:00Z"), title="[wip] essai")
    assert sw.classify_pr(gel, NOW, 24.0)["state"] == "HOLD"
    assert sw.classify_pr(wip, NOW, 24.0)["state"] == "HOLD"
    # Un mot qui commence comme le marqueur, ou un marqueur hors tete de titre, ne gele rien.
    assert sw.classify_pr(dict(gel, title="[WIPE] x"), NOW, 24.0)["state"] == "UNSEEN"
    assert sw.classify_pr(dict(gel, title="fix [HOLD]"), NOW, 24.0)["state"] == "UNSEEN"
    run = make_runner({"jsboige/MetaGeneticSharp": [gel]}, gitlinks=SAME, remotes=REMOTES_SAME)
    report = sw.watch(24.0, "origin/main", NOW, run)
    assert sw.exit_code(report) == 0
    assert "HOLD" in sw.render(report)


def _paged_runner(pages: dict, total: int):
    """Runner GraphQL pagine : ``pages`` associe le curseur demande (None = premiere page) a ses noeuds."""
    order = list(pages)

    def run(cmd: list) -> subprocess.CompletedProcess:
        after = next((a.split("=", 1)[1] for a in cmd if a.startswith("after=")), None)
        idx = order.index(after)
        nxt = order[idx + 1] if idx + 1 < len(order) else None
        page = {"totalCount": total, "nodes": pages[after],
                "pageInfo": {"hasNextPage": nxt is not None, "endCursor": nxt}}
        return _cp(json.dumps({"data": {"repository": {"pullRequests": page}}}))

    return run


def test_pagination_lit_toutes_les_pages():
    p1 = [_pr(n, "2026-10-18T12:00:00Z") for n in range(1, 101)]
    p2 = [_pr(101, "2026-09-01T00:00:00Z")]  # la PR muette est sur la seconde page
    nodes = sw.fetch_prs("jsboige/MetaGeneticSharp", _paged_runner({None: p1, "c1": p2}, total=101))
    assert len(nodes) == 101
    assert sw.classify_pr(nodes[-1], NOW, 24.0)["state"] == "UNSEEN"


def test_compte_lu_different_du_total_rend_le_depot_illisible():
    nodes = [_pr(1, "2026-10-18T12:00:00Z")]
    try:
        sw.fetch_prs("jsboige/MetaGeneticSharp", _paged_runner({None: nodes}, total=3))
    except RuntimeError as exc:
        assert "totalCount=3" in str(exc)
    else:
        raise AssertionError("une lecture tronquee doit lever")

    def run(cmd: list) -> subprocess.CompletedProcess:
        if cmd[:3] == ["gh", "api", "graphql"]:
            page = {"totalCount": 3, "nodes": nodes, "pageInfo": {"hasNextPage": False, "endCursor": None}}
            return _cp(json.dumps({"data": {"repository": {"pullRequests": page}}}))
        return make_runner({}, gitlinks=SAME, remotes=REMOTES_SAME)(cmd)

    report = sw.watch(24.0, "origin/main", NOW, run)
    assert all(r["prs"] is None for r in report["repos"])
    assert sw.exit_code(report) == 2


# --- Lecture par jambe : un rouge d'infra n'est pas le rouge d'une PR -------------------

def _mgs_report(prs: list) -> dict:
    run = make_runner({"jsboige/MetaGeneticSharp": prs}, gitlinks=SAME, remotes=REMOTES_SAME)
    return sw.watch(24.0, "origin/main", NOW, run)


def test_jambe_rouge_sur_toutes_les_prs_est_infra():
    # Cas fondateur Z3.Linq : « Automerge & Label » echoue sur toutes les PRs du depot
    # faute de secrets d'application. L'agregat seul les classait toutes en FAILURE.
    prs = [
        _pr(41, "2026-10-18T12:00:00Z", rollup="FAILURE",
            legs={"Automerge & Label": "FAILURE", "Test": "OK"}),
        _pr(42, "2026-10-18T12:00:00Z", rollup="FAILURE",
            legs={"Automerge & Label": "FAILURE", "Test": "OK"}),
    ]
    report = _mgs_report(prs)
    mgs = next(r for r in report["repos"] if r["path"] == "A/MGS")
    assert mgs["infra"] == {"Automerge & Label": [41, 42]}
    assert [p["checks"] for p in mgs["prs"]] == ["INFRA", "INFRA"]
    assert all(p["own_failing"] == [] for p in mgs["prs"])
    assert "INFRA  jambe(s) rouge(s)" in sw.render(report)
    assert "Automerge & Label (2 PRs)" in sw.render(report)


def test_controle_positif_un_rouge_propre_n_est_jamais_masque():
    # La meme jambe d'infra rougit les deux PRs, mais la seconde porte AUSSI un rouge
    # a elle : le classement doit rendre FAILURE sur celle-la, jamais INFRA.
    prs = [
        _pr(41, "2026-10-18T12:00:00Z", rollup="FAILURE",
            legs={"Automerge & Label": "FAILURE", "Test": "OK"}),
        _pr(42, "2026-10-18T12:00:00Z", rollup="FAILURE",
            legs={"Automerge & Label": "FAILURE", "Test": "FAILURE"}),
    ]
    report = _mgs_report(prs)
    mgs = next(r for r in report["repos"] if r["path"] == "A/MGS")
    rows = {p["number"]: p for p in mgs["prs"]}
    assert rows[41]["checks"] == "INFRA" and rows[41]["own_failing"] == []
    assert rows[42]["checks"] == "FAILURE" and rows[42]["own_failing"] == ["Test"]


def test_jambe_rouge_sur_une_seule_pr_reste_failure():
    # Fail-closed : une jambe portee par une seule PR ne peut pas etre declaree infra.
    solo = _mgs_report([_pr(41, "2026-10-18T12:00:00Z", rollup="FAILURE",
                           legs={"Automerge & Label": "FAILURE"})])
    assert next(r for r in solo["repos"] if r["path"] == "A/MGS")["infra"] == {}
    assert solo["repos"][0]["prs"][0]["checks"] == "FAILURE"
    # Portee par deux PRs mais rouge sur une seule : pas infra non plus.
    demi = _mgs_report([
        _pr(41, "2026-10-18T12:00:00Z", rollup="FAILURE", legs={"Test": "FAILURE"}),
        _pr(42, "2026-10-18T12:00:00Z", rollup="SUCCESS", legs={"Test": "OK"}),
    ])
    assert next(r for r in demi["repos"] if r["path"] == "A/MGS")["infra"] == {}


def test_rollup_sans_jambes_retombe_sur_l_agregat_sans_rien_masquer():
    # L'API peut rendre un rollup sans ``contexts`` : on ne devine pas, on garde l'agregat.
    report = _mgs_report([_pr(41, "2026-10-18T12:00:00Z", rollup="FAILURE")])
    mgs = next(r for r in report["repos"] if r["path"] == "A/MGS")
    assert mgs["infra"] == {}
    assert mgs["prs"][0]["checks"] == "FAILURE"


def test_status_context_lu_comme_une_jambe():
    node = _pr(41, "2026-10-18T12:00:00Z", rollup="FAILURE")
    node["commits"]["nodes"][0]["commit"]["statusCheckRollup"]["contexts"] = {"nodes": [
        {"__typename": "StatusContext", "context": "ci/legacy", "state": "ERROR"},
        {"__typename": "StatusContext", "context": "ci/pending", "state": "PENDING"},
        {"__typename": "StatusContext", "context": "ci/ok", "state": "SUCCESS"},
    ]}
    assert sw.pr_legs(node) == {"ci/legacy": "FAILURE", "ci/pending": "PENDING", "ci/ok": "OK"}


def test_checkrun_non_termine_est_pending_quoi_que_dise_sa_conclusion():
    node = _pr(41, "2026-10-18T12:00:00Z", rollup="PENDING")
    node["commits"]["nodes"][0]["commit"]["statusCheckRollup"]["contexts"] = {"nodes": [
        {"__typename": "CheckRun", "name": "Test", "status": "IN_PROGRESS", "conclusion": "FAILURE"},
    ]}
    assert sw.pr_legs(node) == {"Test": "PENDING"}


def test_un_rouge_d_infra_ne_change_pas_le_code_de_sortie():
    # Les checks n'ont jamais fait rougir l'organe : un rouge d'infra ne doit pas
    # introduire de rouge nouveau, ni en retirer un (UNSEEN reste rouge).
    prs = [_pr(41, "2026-10-18T12:00:00Z", rollup="FAILURE",
               legs={"Automerge & Label": "FAILURE"}, comments=1, reviews=1),
           _pr(42, "2026-10-18T12:00:00Z", rollup="FAILURE",
               legs={"Automerge & Label": "FAILURE"}, comments=1, reviews=1)]
    assert sw.exit_code(_mgs_report(prs)) == 0
