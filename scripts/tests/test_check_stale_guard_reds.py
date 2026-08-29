"""Tests for scripts/check_stale_guard_reds.py (#13321).

Aucun appel reseau : `analyse()` est pur, on lui passe des payloads construits
et un `compare_fn` dicționnaire. Les quatre criterions de l'issue :

  1. datation par la base de la merge-ref (ancêtré, pas completedAt) ;
  2. signal quand garde vert sur main ET rouge anterieur au fix ;
  3. remede update-branch, JAMAIS rerun -- rerun rejouerait la base gelee
     (couvert par le cas flake ET par why_not_rerun) ;
  4. CONTROLE POSITIF : un rouge posterieur au fix ressort NON signale.

L'incident fondateur sert de fixture : #13156 porte un rouge
`Scripts Tests (CPU)` rendu contre une base du 2026-08-26, fix 62d47eb7d
arrive sur main le 2026-08-27T08:53Z.
"""
import importlib.util
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_stale_guard_reds.py"
spec = importlib.util.spec_from_file_location("check_stale_guard_reds", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_stale_guard_reds"] = mod
spec.loader.exec_module(mod)

FIX = "62d47eb7df1"  # fix(ci,#13135) windows-self-hosted-tests policy runner (#13148)
OLD_BASE = "5ee60a409f90"  # base gelee reelle du run rouge de #13156 (08-26 18:48)
NEW_BASE = "46c0d210dcda"  # base posterieure au fix


def check(name, conclusion, run_id, status="completed"):
    return {"name": name, "status": status, "conclusion": conclusion,
            "details_url": f"https://github.com/jsboige/CoursIA/actions/runs/{run_id}/job/1"}


def history(verdicts):
    """verdicts: liste du PLUS RECENT au PLUS ANCIEN de (conclusion, head_sha)."""
    runs, by_run = [], {}
    for i, (concl, sha) in enumerate(verdicts):
        rid = 900 - i  # run ids decroissants vers le passe : 900 = plus recent
        runs.append({"id": rid, "head_sha": sha})
        by_run[rid] = {"Scripts Tests (CPU)": {"conclusion": concl, "status": "completed"}}
    return {"runs": runs, "check_by_run": by_run}


def pr_fixture(**over):
    red = check("Scripts Tests (CPU)", "failure", 111)
    pr = {
        "number": 13156, "draft": False, "fork": False,
        "head_sha": "aaa", "merge_commit_sha": "mmm",
        "tested_bases": {"111": OLD_BASE},
        "checks": [red],
        # garde vert aujourd'hui, transition rouge->vert localisee sur FIX :
        # du plus recent au plus ancien : vert(NEW), vert(FIX), rouge(ancien)
        "main_histories": {"111": history([
            ("success", "main-tip"), ("success", FIX), ("failure", "pre-fix")])},
    }
    pr.update(over)
    return {"prs": [pr]}


def cmp_map(m):
    return lambda a, b: m.get((a, b))


# --- criterion 2 + 3 : la classe incident, signalee, remede update-branch ---

def test_stale_red_flagged_with_update_branch_remedy():
    result = mod.analyse(pr_fixture(), cmp_map({}))  # compare indisponible -> non
    # sans compare, conservateur : exclu nomme, pas signale
    assert result["flagged"] == []
    assert "compare indisponible" in result["excluded"][0]["reason"]

    result = mod.analyse(pr_fixture(), cmp_map({(FIX, OLD_BASE): "diverged"}))
    assert len(result["flagged"]) == 1
    f = result["flagged"][0]
    assert f["pr"] == 13156
    assert f["check"] == "Scripts Tests (CPU)"
    assert f["remedy"] == "update-branch"
    assert f["merge_base"] == OLD_BASE
    assert f["fix_head"] == FIX


def test_rerun_would_replay_frozen_base_documented():
    """Criterion 3 : le verdict porte POURQUOI rerun rendrait le meme rouge."""
    result = mod.analyse(pr_fixture(), cmp_map({(FIX, OLD_BASE): "diverged"}))
    why = result["flagged"][0]["why_not_rerun"]
    assert "base gelee" in why
    assert "rendrait le meme rouge" in why
    assert "update-branch" in why


def test_flake_same_base_green_sibling_not_prescribed_update_branch():
    """Un vert du meme nom sur la MEME base GEEELEE prove que le garde passe
    a cette base : rerun de la base est la voie (famille pr-gate-stale-sweep),
    PAS update-branch. Le prescrire serait la fausse piste du criterion 3."""
    green = check("Scripts Tests (CPU)", "success", 222)
    pr = {"prs": [{
        "number": 13156, "draft": False, "fork": False,
        "head_sha": "aaa", "merge_commit_sha": "mmm",
        "tested_bases": {"111": OLD_BASE, "222": OLD_BASE},
        "checks": [check("Scripts Tests (CPU)", "failure", 111), green],
        "main_histories": {},
    }]}
    result = mod.analyse(pr, cmp_map({}))
    assert result["flagged"] == []
    ex = result["excluded"][0]
    assert "flake" in ex["reason"]
    assert "rerun" in ex["reason"]

def test_green_sibling_postfix_base_is_not_a_flake():
    """Un vert de meme nom sur une base DIFFERENTE (post-fix) n_est PAS un
    flake : c_est la signature du rouge perime -- le merge-ref recent passe
    (preuve que update-branch reparait), celui teste par le run rouge non."""
    green = check("Scripts Tests (CPU)", "success", 222)
    pr = {"prs": [{
        "number": 13156, "draft": False, "fork": False,
        "head_sha": "aaa", "merge_commit_sha": "mmm",
        # rouge sur base pre-fix, vert sur base post-fix : differents
        "tested_bases": {"111": OLD_BASE, "222": NEW_BASE},
        "checks": [check("Scripts Tests (CPU)", "failure", 111), green],
        "main_histories": {"111": history([
            ("success", "main-tip"), ("success", FIX), ("failure", "pre-fix")])},
    }]}
    result = mod.analyse(pr, cmp_map({(FIX, OLD_BASE): "behind"}))
    assert len(result["flagged"]) == 1
    assert result["flagged"][0]["remedy"] == "update-branch"


def test_current_merge_ref_drift_does_not_hide_stale_red():
    """La decouverte fondatrice (mesure 2026-08-28 sur #13156) : la merge-ref
    COURANTE de la PR est recalculee quand main bouge -- son parent contient
    deja le fix. Dater par elle declarerait "vrai defaut" un rouge rendu contre
    une base anterieure. La base GELEE du run est le seul instrument juste."""
    pr = pr_fixture()
    # la base GELEE du run 111 predates le fix ; la merge-ref courante
    # (parent de merge_commit_sha) est, elle, POSTERIEURE au fix :
    pr["prs"][0]["merge_commit_sha"] = "mmm"  # parent contiendrait le fix
    result = mod.analyse(pr, cmp_map({(FIX, OLD_BASE): "diverged"}))
    assert len(result["flagged"]) == 1  # signale : c'est la base du RUN qui fait foi


# --- criterion 4 : CONTROLE POSITIF ---

def test_red_posterior_to_fix_not_flagged():
    """Base posterieure au fix (compare 'ahead') = rouge rendu CONTRE le garde
    corrige = vrai defaut : NON signale, exclusion explicite."""
    pr = pr_fixture()
    pr["prs"][0]["tested_bases"] = {"111": NEW_BASE}
    result = mod.analyse(pr, cmp_map({(FIX, NEW_BASE): "ahead"}))
    assert result["flagged"] == []
    assert "vrai defaut" in result["excluded"][0]["reason"]


# --- criterions 2 : gardes fous, exclusions nommees ---

def test_guard_red_on_main_current_not_flagged():
    hist = history([("failure", "main-tip"), ("success", FIX), ("failure", "pre-fix")])
    pr = pr_fixture()
    pr["prs"][0]["main_histories"] = {"111": hist}
    result = mod.analyse(pr, cmp_map({}))
    assert result["flagged"] == []
    assert "garde rouge sur main" in result["excluded"][0]["reason"]


def test_pr_only_guard_absent_on_main_named_exclusion():
    """Un garde pull_request-only n'a JAMAIS de runs sur main : indatable.
    Mesure 2026-08-28 : Papermill ratchet / cell-ordering tombaient en
    "garde rouge sur main" -- message faux, ce sont des gardes PR-only."""
    pr = pr_fixture()
    pr["prs"][0]["main_histories"] = {"111": {"runs": [], "check_by_run": {}}}
    result = mod.analyse(pr, cmp_map({}))
    assert result["flagged"] == []
    assert "ne tourne jamais sur main" in result["excluded"][0]["reason"]


def test_no_red_green_transition_not_flagged():
    """Garde vert de tout temps sur main : aucune preuve de fix, le rouge est
    propre a la PR. Un organe qui blanchirait la classe serait pire que rien."""
    hist = history([("success", "main-tip"), ("success", "older"), ("success", "oldest")])
    pr = pr_fixture()
    pr["prs"][0]["main_histories"] = {"111": hist}
    result = mod.analyse(pr, cmp_map({}))
    assert result["flagged"] == []
    assert "propre a la PR" in result["excluded"][0]["reason"]


# --- bornes de perimetre ---

def test_pr_gate_red_out_of_scope():
    pr = pr_fixture()
    pr["prs"][0]["checks"] = [check("PR gate", "failure", 111)]
    result = mod.analyse(pr, cmp_map({}))
    assert result["flagged"] == [] and result["excluded"] == []


def test_draft_excluded():
    pr = pr_fixture()
    pr["prs"][0]["draft"] = True
    result = mod.analyse(pr, cmp_map({}))
    assert result["flagged"] == [] and result["excluded"][0]["reason"] == "draft"


def test_fork_excluded():
    pr = pr_fixture()
    pr["prs"][0]["fork"] = True
    result = mod.analyse(pr, cmp_map({}))
    assert result["flagged"] == []
    assert "fork" in result["excluded"][0]["reason"]


def test_push_event_run_without_merge_base_excluded():
    """Mesure 2026-08-28 (#13156) : GitHub recalcule la merge-ref courante
    quand main bouge -- dater par elle etait FAUX. Seule la base GELEE du run
    fait foi ; un run push-event n'en a pas : indatable, exclusion nommee."""
    pr = pr_fixture()
    pr["prs"][0]["tested_bases"] = {"111": None}
    result = mod.analyse(pr, cmp_map({}))
    assert result["flagged"] == []
    assert "base testee indisponible" in result["excluded"][0]["reason"]
    assert "push-event" in result["excluded"][0]["reason"]


def test_superseded_incomplete_attempt_does_not_flag():
    """Une tentative interrompue (status != completed) du meme workflow ne
    compte ni rouge ni vert : seule la tentative conclue fait foi."""
    pr = pr_fixture()
    pr["prs"][0]["checks"] = [
        check("Scripts Tests (CPU)", "failure", 111, status="in_progress"),
        check("Scripts Tests (CPU)", "failure", 111),
    ]
    result = mod.analyse(pr, cmp_map({(FIX, OLD_BASE): "diverged"}))
    assert len(result["flagged"]) == 1


# --- criterion 5 : denominateur ---

def test_denominator_reported():
    data = {"prs": [pr_fixture()["prs"][0],
                    {"number": 2, "draft": True, "checks": [], "main_histories": {}}]}
    result = mod.analyse(data, cmp_map({(FIX, OLD_BASE): "diverged"}))
    assert result["examined"] == 2
    d = result["denominator"]
    assert d["examined"] == 2 and d["flagged"] == 1 and d["excluded"] == 1


# --- unites ---

def test_is_ancestor_status():
    assert mod.is_ancestor_status("ahead")       # b en avance : a ancetre de b
    assert not mod.is_ancestor_status("behind")  # b en retard : fix POSTERIEUR a base
    assert not mod.is_ancestor_status("diverged")
    assert not mod.is_ancestor_status(None)


def test_locate_fix_head_ordering():
    hist = history([("success", "s1"), ("success", "s2"), ("failure", "s3"),
                    ("failure", "s4")])
    status, fix = mod.locate_fix_head(hist, "Scripts Tests (CPU)")
    assert status == "green" and fix == "s2"  # serie verte post-fix


def test_locate_fix_head_all_green():
    hist = history([("success", "s1"), ("success", "s2")])
    status, fix = mod.locate_fix_head(hist, "Scripts Tests (CPU)")
    assert status == "green" and fix is None


def test_locate_fix_head_absent_check():
    status, fix = mod.locate_fix_head({"runs": [], "check_by_run": {}}, "X")
    assert status == "absent_on_main" and fix is None


def test_locate_fix_head_red_on_main():
    hist = history([("failure", "s1"), ("success", "s2"), ("failure", "s3")])
    status, fix = mod.locate_fix_head(hist, "Scripts Tests (CPU)")
    assert status == "red_on_main"
