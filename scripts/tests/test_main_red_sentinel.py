"""Tests de la sentinelle de main rouge (#24828).

Le fetch est toujours injecte : aucun appel GitHub dans la suite. Les
scenarios sont synthetiques et nomment ce qu'ils prouvent.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import main_red_sentinel as mrs  # noqa: E402


def _run(run_id, sha, conclusion, created, updated, status="completed"):
    return {
        "id": run_id,
        "head_sha": sha,
        "conclusion": conclusion,
        "status": status,
        "created_at": created,
        "updated_at": updated,
    }


def _commit(sha, subject="sujet", date="2026-11-10T00:00:00Z"):
    return {
        "sha": sha,
        "commit": {"message": subject + "\n\ncorps",
                   "committer": {"date": date}},
    }


def link_first_parent(commits):
    for child, parent in zip(commits, commits[1:]):
        child["parents"] = [{"sha": parent["sha"]}]
    return commits


# --- lecture de verdict ----------------------------------------------------

@pytest.mark.parametrize("conclusion, attendu", [
    ("failure", mrs.RED),
    ("timed_out", mrs.INFRA),
    ("startup_failure", mrs.INFRA),
    ("success", mrs.GREEN),
    ("cancelled", mrs.UNKNOWN),
    ("skipped", mrs.UNKNOWN),
    (None, mrs.UNKNOWN),
    ("", mrs.UNKNOWN),
])
def test_run_state_classe_les_conclusions(conclusion, attendu):
    assert mrs.run_state({"conclusion": conclusion}) == attendu


def test_un_run_annule_ne_prouve_ni_le_rouge_ni_le_vert():
    """Un `cancelled` ne dit rien de la qualite du code : jamais un vert."""
    assert mrs.run_state({"conclusion": "cancelled"}) == mrs.UNKNOWN


def test_l_infra_n_est_ni_le_rouge_ni_le_sans_verdict():
    """`timed_out` / `startup_failure` : le code n'a pas ete juge.

    C'est la distinction demandee par le coordinateur : l'infra est distincte
    du `cancelled` (qui n'a rien dit du tout), et ni l'une ni l'autre ne pose
    de retenue -- seul `failure` en pose une.
    """
    assert mrs.run_state({"conclusion": "timed_out"}) == mrs.INFRA
    assert mrs.run_state({"conclusion": "startup_failure"}) == mrs.INFRA
    assert mrs.INFRA != mrs.UNKNOWN
    assert mrs.INFRA != mrs.RED


def test_le_calcul_de_la_retenue_et_l_organe_ont_le_meme_ensemble_de_rouge():
    """Le seul ensemble qui pose un defaut de code est `failure`."""
    import importlib.util
    import sys

    assert mrs.RED_CONCLUSIONS == ("failure",)

    chemin = Path(__file__).resolve().parents[1] / "coordination" / "merge_ready.py"
    spec = importlib.util.spec_from_file_location("merge_ready_coupling", chemin)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    attendu = getattr(module, "MAIN_RED_CODE_VERDICTS", None)
    if attendu is None:
        pytest.skip(
            "merge_ready n'expose pas encore MAIN_RED_CODE_VERDICTS "
            "(la retenue a ete alignee dans une autre PR, non fusionnee)"
        )
    assert attendu == ("success", "failure")


# --- etat par commit --------------------------------------------------------

def test_le_dernier_run_rendu_prime_sur_les_anciens():
    commits = [_commit("aaa"), _commit("bbb")]
    runs = [
        _run(1, "aaa", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(2, "aaa", "success", "2026-11-10T00:20:00Z", "2026-11-10T00:40:00Z"),
    ]
    states = mrs.commit_states(commits, runs)
    assert states["aaa"]["state"] == mrs.GREEN
    assert states["aaa"]["run"]["id"] == 2
    assert states["bbb"]["state"] == mrs.UNKNOWN


def test_un_commit_sans_run_est_inconnu_et_jamais_vert():
    states = mrs.commit_states([_commit("zzz")], [])
    assert states["zzz"]["state"] == mrs.UNKNOWN
    assert states["zzz"]["run"] is None


def test_un_commit_dont_tous_les_runs_sont_annules_reste_inconnu():
    runs = [_run(1, "aaa", "cancelled", "2026-11-10T00:00:00Z",
                 "2026-11-10T00:05:00Z")]
    states = mrs.commit_states([_commit("aaa")], runs)
    assert states["aaa"]["state"] == mrs.UNKNOWN


# --- premier commit rouge ----------------------------------------------------

def test_le_premier_commit_rouge_est_celui_du_bord_vert_rouge():
    commits = [_commit("c3", "rouge 3"), _commit("c2", "rouge 2"),
               _commit("c1", "vert 1")]
    link_first_parent(commits)
    runs = [
        _run(3, "c3", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
        _run(2, "c2", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
        _run(1, "c1", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
    ]
    states = mrs.commit_states(commits, runs)
    result = mrs.find_first_red(commits, states)
    assert result["verdict"] == mrs.RED
    assert result["first_red_commit"]["sha"] == "c2"
    assert result["first_red_commit_exact"] is True
    assert result["bounds"]["dernier_commit_vert_connu"]["sha"] == "c1"


def test_un_trou_sans_verdict_borne_la_reponse_sans_nommer_de_coupable():
    """Un commit sans run entre le vert et le rouge : la reponse est BORNEE."""
    commits = [_commit("c3", "rouge"), _commit("c2", "sans run"),
               _commit("c1", "vert")]
    runs = [
        _run(3, "c3", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
        _run(1, "c1", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
    ]
    states = mrs.commit_states(commits, runs)
    result = mrs.find_first_red(commits, states)
    assert result["verdict"] == mrs.RED
    assert result["first_red_commit"]["sha"] == "c3"
    assert result["first_red_commit_exact"] is False
    trous = result["bounds"]["commits_sans_verdict_entre_les_deux"]
    assert [t["sha"] for t in trous] == ["c2"]


def test_main_entierement_vert_ne_nomme_aucun_commit_rouge():
    commits = [_commit("c2"), _commit("c1")]
    runs = [
        _run(2, "c2", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(1, "c1", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
    ]
    states = mrs.commit_states(commits, runs)
    result = mrs.find_first_red(commits, states)
    assert result["verdict"] == mrs.GREEN
    assert result["first_red_commit"] is None


def test_main_sans_preuve_nest_pas_declared_vert():
    """Aucun run sur le commit de tete : l'etat est inconnu, pas vert."""
    commits = [_commit("c1")]
    states = mrs.commit_states(commits, [])
    result = mrs.find_first_red(commits, states)
    assert result["verdict"] == mrs.UNKNOWN
    assert result["first_red_commit"] is None


# --- couverture, verdicts, latence -------------------------------------------

def test_la_couverture_distingue_le_run_du_verdit_connu():
    """Un run annule couvre le commit (il a existe) mais ne donne aucun verdict."""
    commits = [_commit("c1"), _commit("c2"), _commit("c3")]
    runs = [
        _run(1, "c1", "success", "2026-11-10T00:00:00Z",
             "2026-11-10T00:10:00Z"),
        _run(2, "c2", "cancelled", "2026-11-10T00:00:00Z",
             "2026-11-10T00:05:00Z"),
    ]
    states = mrs.commit_states(commits, runs)
    coverage = mrs.measure_coverage(commits, states)
    assert coverage["commits"] == 3
    assert coverage["avec_run"] == 2
    assert coverage["verdict_connu"] == 1
    assert coverage["sans_run"] == 1
    assert coverage["taux_run_pct"] == 66.7
    assert coverage["taux_verdict_pct"] == 33.3


def test_l_infra_est_compte_a_part_dans_la_couverture():
    """Un verdict d'infra n'est ni un verdict de code ni une absence de signal."""
    commits = [_commit("c1"), _commit("c2"), _commit("c3")]
    runs = [
        _run(1, "c1", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(2, "c2", "timed_out", "2026-11-10T00:00:00Z",
             "2026-11-10T00:30:00Z"),
    ]
    states = mrs.commit_states(commits, runs)
    coverage = mrs.measure_coverage(commits, states)
    assert coverage["avec_run"] == 2
    assert coverage["verdict_connu"] == 1
    assert coverage["infra"] == 1
    assert coverage["taux_verdict_pct"] == 33.3
    assert coverage["taux_infra_pct"] == 33.3


def test_un_verdict_d_infra_borne_la_reponse_comme_un_trou():
    """Un commit en infra entre le vert et le rouge : la reponse est BORNEE.

    L'organe ne nomme pas de coupable dans un intervalle qu'il ne sait pas
    trancher -- un verdict d'infra ne prouve ni le rouge ni le vert.
    """
    commits = [_commit("c3", "rouge"), _commit("c2", "infra"), _commit("c1", "vert")]
    runs = [
        _run(3, "c3", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
        _run(2, "c2", "timed_out", "2026-11-10T00:00:00Z",
             "2026-11-10T00:30:00Z"),
        _run(1, "c1", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
    ]
    states = mrs.commit_states(commits, runs)
    result = mrs.find_first_red(commits, states)
    assert result["first_red_commit"]["sha"] == "c3"
    assert result["first_red_commit_exact"] is False
    bornes = result["bounds"]["commits_infra_entre_les_deux"]
    assert [c["sha"] for c in bornes] == ["c2"]


def test_une_tete_en_infra_ne_produit_ni_le_rouge_ni_le_vert():
    """L'etat de tete en infra ne nomme aucun commit rouge."""
    commits = [_commit("c1", "infra"), _commit("c0", "vert")]
    runs = [
        _run(1, "c1", "startup_failure", "2026-11-10T00:00:00Z",
             "2026-11-10T00:30:00Z"),
        _run(0, "c0", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
    ]
    states = mrs.commit_states(commits, runs)
    result = mrs.find_first_red(commits, states)
    assert result["verdict"] == mrs.INFRA
    assert result["first_red_commit"] is None


def test_la_repartition_des_verdicts_compte_les_annules():
    runs = [
        _run(1, "a", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(2, "b", "cancelled", "2026-11-10T00:00:00Z",
             "2026-11-10T00:05:00Z"),
        _run(3, "c", "cancelled", "2026-11-10T00:00:00Z",
             "2026-11-10T00:05:00Z"),
    ]
    verdicts = mrs.measure_verdicts(runs)
    assert verdicts["runs_conclus"] == 3
    assert verdicts["par_conclusion"]["cancelled"] == 2
    assert verdicts["taux_annules_pct"] == 66.7


def test_la_latence_ne_conserve_que_les_runs_qui_ont_rendu_un_verdict():
    runs = [
        _run(1, "a", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(2, "b", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:40:00Z"),
        _run(3, "c", "cancelled", "2026-11-10T00:00:00Z",
             "2026-11-10T00:05:00Z"),
    ]
    latence = mrs.measure_latency(runs)
    assert latence["n"] == 2
    assert latence["min"] == 10.0
    assert latence["max"] == 40.0
    assert latence["mediane"] == 25.0


# --- rapport complet ---------------------------------------------------------

def test_le_rapport_combine_les_quatre_vues():
    commits = [_commit("c2", "rouge"), _commit("c1", "vert")]
    runs = [
        _run(2, "c2", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:20:00Z"),
        _run(1, "c1", "success", "2026-11-10T00:00:00Z", "2026-11-10T00:15:00Z"),
    ]

    def fake_fetch(path):
        if "actions/workflows" in path:
            return {"workflow_runs": runs}
        return commits

    report = mrs.sentinel_report(repo="o/r", workflow="w.yml", branch="main",
                                 fetch=fake_fetch)
    assert report["verdict"] == mrs.RED
    assert report["first_red_commit"]["sha"] == "c2"
    assert report["coverage"]["taux_verdict_pct"] == 100.0
    assert report["verdicts"]["par_conclusion"]["failure"] == 1
    assert report["latency_min"]["max"] == 20.0


# --- CLI ---------------------------------------------------------------------

def test_le_cli_sort_1_quand_le_rouge_est_prouve(monkeypatch, capsys):
    rapport = {"verdict": mrs.RED, "first_red_commit": {"sha": "abc123def456",
                                                        "subject": "coupable"},
               "first_red_commit_exact": True,
               "bounds": {"dernier_commit_vert_connu": {"sha": "d0d0d0d0d0d0",
                                                       "subject": "vert"},
                          "commits_sans_verdict_entre_les_deux": []},
               "coverage": {"taux_run_pct": 66.7, "taux_verdict_pct": 26.7,
                              "avec_run": 40, "commits": 60},
               "verdicts": {"taux_annules_pct": 69.7}, "latency_min": {}}
    monkeypatch.setattr(mrs, "sentinel_report", lambda **kw: rapport)
    rc = mrs.main(["--first-red"])
    assert rc == 1
    out = capsys.readouterr().out
    assert "abc123def456" in out
    assert "coupable" in out


def test_le_cli_sort_0_quand_aucun_rouge_nest_prouve(monkeypatch, capsys):
    rapport = {"verdict": mrs.GREEN, "first_red_commit": None,
               "first_red_commit_exact": False, "bounds": {},
               "coverage": {"taux_run_pct": 100.0, "taux_verdict_pct": 100.0,
                              "avec_run": 10, "commits": 10},
               "verdicts": {"taux_annules_pct": 0.0}, "latency_min": {}}
    monkeypatch.setattr(mrs, "sentinel_report", lambda **kw: rapport)
    assert mrs.main(["--first-red"]) == 0
    assert "aucun commit rouge" in capsys.readouterr().out


def test_le_cli_sort_2_quand_l_instrument_est_en_erreur(monkeypatch, capsys):
    def boom(**kw):
        raise mrs.SentinelError("gh api a echoue")
    monkeypatch.setattr(mrs, "sentinel_report", boom)
    assert mrs.main(["--json"]) == 2
    payload = capsys.readouterr().out
    assert "gh api a echoue" in payload


def test_le_cli_ignore_un_fetch_qui_echoue(monkeypatch):
    def bad_fetch(path):
        raise mrs.SentinelError("reponse inattendue de l'API des commits")
    with pytest.raises(mrs.SentinelError):
        mrs.sentinel_report(fetch=bad_fetch)


def test_tete_inconnue_apres_rouge_ne_borne_pas_sa_naissance():
    """Une tête en attente ne précède pas le premier rouge dans l'histoire."""
    commits = [_commit("c3", "pending"), _commit("c2", "red"), _commit("c1", "green")]
    link_first_parent(commits)
    runs = [
        _run(2, "c2", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(1, "c1", "success", "2026-11-09T23:30:00Z", "2026-11-09T23:40:00Z"),
    ]
    result = mrs.find_first_red(commits, mrs.commit_states(commits, runs))
    assert result["verdict"] == mrs.UNKNOWN
    assert result["first_red_commit"]["sha"] == "c2"
    assert result["first_red_commit_exact"] is True
    assert result["bounds"]["commits_sans_verdict_entre_les_deux"] == []


def test_trou_apres_rouge_plus_ancien_ne_borne_pas_son_introduction():
    commits = [_commit("c4"), _commit("c3"), _commit("c2"), _commit("c1")]
    link_first_parent(commits)
    runs = [
        _run(4, "c4", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(2, "c2", "failure", "2026-11-09T23:00:00Z", "2026-11-09T23:10:00Z"),
        _run(1, "c1", "success", "2026-11-09T22:00:00Z", "2026-11-09T22:10:00Z"),
    ]
    result = mrs.find_first_red(commits, mrs.commit_states(commits, runs))
    assert result["first_red_commit"]["sha"] == "c2"
    assert result["first_red_commit_exact"] is True
    assert result["bounds"]["commits_sans_verdict_entre_les_deux"] == []


def test_infra_apres_rouge_ne_borne_pas_son_introduction():
    commits = [_commit("c3"), _commit("c2"), _commit("c1")]
    link_first_parent(commits)
    runs = [
        _run(3, "c3", "timed_out", "2026-11-10T01:00:00Z", "2026-11-10T01:10:00Z"),
        _run(2, "c2", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(1, "c1", "success", "2026-11-09T23:00:00Z", "2026-11-09T23:10:00Z"),
    ]
    result = mrs.find_first_red(commits, mrs.commit_states(commits, runs))
    assert result["verdict"] == mrs.INFRA
    assert result["first_red_commit"]["sha"] == "c2"
    assert result["first_red_commit_exact"] is True
    assert result["bounds"]["commits_infra_entre_les_deux"] == []


@pytest.mark.parametrize("case", ["parent_divergent", "parent_absent", "tete_divergente",
                                  "green_is_second_parent"])
def test_attribution_exacte_exige_chaine_first_parent(case):
    """La liste REST peut mélanger des branches ou omettre les parents."""
    commits = [_commit("pending"), _commit("red"), _commit("green")]
    commits[0]["parents"] = [{"sha": "red"}]
    commits[1]["parents"] = [{"sha": "green"}]
    if case == "parent_divergent":
        commits[1]["parents"] = [{"sha": "other"}]
    elif case == "parent_absent":
        del commits[1]["parents"]
    elif case == "green_is_second_parent":
        commits[1]["parents"] = [{"sha": "other"}, {"sha": "green"}]
    else:
        commits[0]["parents"] = [{"sha": "other"}]
    runs = [
        _run(2, "red", "failure", "2026-11-10T00:00:00Z", "2026-11-10T00:10:00Z"),
        _run(1, "green", "success", "2026-11-09T23:00:00Z", "2026-11-09T23:10:00Z"),
    ]
    result = mrs.find_first_red(commits, mrs.commit_states(commits, runs))
    assert result["verdict"] == mrs.UNKNOWN
    assert result["first_red_commit_exact"] is False
    assert result["bounds"]["chaine_first_parent_verifiee"] is False


def test_cli_ne_present_pas_un_rouge_non_apparente_comme_premier(monkeypatch, capsys):
    rapport = {
        "verdict": mrs.UNKNOWN,
        "first_red_commit": {"sha": "abc123", "subject": "branche"},
        "first_red_commit_exact": False,
        "bounds": {"chaine_first_parent_verifiee": False},
    }
    monkeypatch.setattr(mrs, "sentinel_report", lambda **kw: rapport)
    assert mrs.main(["--first-red"]) == 0
    output = capsys.readouterr().out
    assert "candidat rouge observé" in output
    assert "filiation premier-parent non verifiee" in output
    assert "premier commit rouge" not in output
