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


# --- re-mesure (#15350) : acceptance 2 (agir), 3 (re-rougir), 4 (DWELL) ---

FAKE_LOG = """Set up job\t2026-09-10T06:54:00Z\tCurrent runner size:
Run pytest\t2026-09-10T06:54:10Z\tFAILED scripts/tests/test_perimeter.py::test_audit_name_too_long - AssertionError: assert 123 > 69
Run pytest\t2026-09-10T06:54:11Z\tFAILED scripts/tests/test_perimeter.py::test_audit_name_too_long - AssertionError: assert 123 > 69
Run pytest\t2026-09-10T06:54:12Z\t1 failed, 431 passed in 38.2s
"""


def test_extract_failed_tests_parses_and_dedups():
    nodes = mod.extract_failed_tests(FAKE_LOG)
    assert nodes == ["scripts/tests/test_perimeter.py::test_audit_name_too_long"]


def test_extract_failed_tests_nested_node_ids():
    log = "FAILED a/b.py::TestCls::test_x - Error\nFAILED a/b.py::test_plain - E\n"
    assert mod.extract_failed_tests(log) == [
        "a/b.py::TestCls::test_x", "a/b.py::test_plain"]


def test_extract_failed_tests_non_pytest_log_empty():
    assert mod.extract_failed_tests("CodeQL analysis finished\nerror: rule X") == []


def test_pytest_rc_table_only_rc1_is_red():
    """Criterion 3 : SEUL l'echec pytest reel (rc=1) est un re-rouge. Un crash,
    un node introuvable (rc=4) ou une collection vide (rc=5) traduits en
    ROUGE fabriqueraient le faux defaut que l'issue interdit."""
    assert mod.PYTEST_RC[0] == "GREEN"
    assert mod.PYTEST_RC[1] == "RED"
    for rc in (2, 3, 4, 5):
        assert mod.PYTEST_RC[rc] == "SKIPPED"
    assert mod.PYTEST_RC.get(137) == "SKIPPED" or mod.PYTEST_RC.get(137) is None


def test_remeasure_lines_three_verdicts():
    green = mod.remeasure_lines({"verdict": "GREEN", "n_tests": 1, "merge_sha": "abcdef12345678"})
    assert "VERT" in green and "abcdef12345678"[:12] in green and "update-branch" in green
    red = mod.remeasure_lines({"verdict": "RED", "n_tests": 2, "merge_sha": "abcdef12345678"})
    assert "ROUGE" in red and "corriger" in red
    skipped = mod.remeasure_lines({"verdict": "SKIPPED", "reason": "log indisponible"})
    assert "non concluante" in skipped and "log indisponible" in skipped
    assert mod.remeasure_lines(None) == ""


def _fake_subprocess(pytest_rc):
    """git/pip verts, pytest au rc parametre ; rev-parse rend un sha stable."""
    def run(cmd, **kw):
        class R:
            returncode = 0
            stdout = ""
            stderr = ""
        if cmd[0] == "git" and "rev-parse" in cmd:
            r = R(); r.stdout = "feedfacefeedface\n"; return r
        if cmd[1:3] == ["-m", "pytest"]:
            r = R(); r.returncode = pytest_rc; return r
        return R()
    return run


def test_remeasure_pr_green_when_replayed_tests_pass(monkeypatch, tmp_path):
    monkeypatch.setattr(mod, "_run_gh", lambda a: FAKE_LOG if a[:3] == ["run", "view", "999"] else "")
    monkeypatch.setattr(mod.subprocess, "run", _fake_subprocess(0))
    v = mod.remeasure_pr("jsboige/CoursIA", 15318, "999", str(tmp_path))
    assert v["verdict"] == "GREEN" and v["n_tests"] == 1
    assert v["merge_sha"] == "feedfacefeedface"


def test_remeasure_pr_red_only_on_real_failures(monkeypatch, tmp_path):
    monkeypatch.setattr(mod, "_run_gh", lambda a: FAKE_LOG)
    monkeypatch.setattr(mod.subprocess, "run", _fake_subprocess(1))
    v = mod.remeasure_pr("jsboige/CoursIA", 15318, "999", str(tmp_path))
    assert v["verdict"] == "RED"


def test_remeasure_pr_usage_error_is_skip_not_red(monkeypatch, tmp_path):
    monkeypatch.setattr(mod, "_run_gh", lambda a: FAKE_LOG)
    monkeypatch.setattr(mod.subprocess, "run", _fake_subprocess(4))
    v = mod.remeasure_pr("jsboige/CoursIA", 15318, "999", str(tmp_path))
    assert v["verdict"] == "SKIPPED" and "rc=4" in v["reason"]


def test_remeasure_pr_no_pytest_nodes_skips(monkeypatch, tmp_path):
    monkeypatch.setattr(mod, "_run_gh", lambda a: "CodeQL finished clean")
    v = mod.remeasure_pr("jsboige/CoursIA", 15318, "999", str(tmp_path))
    assert v["verdict"] == "SKIPPED" and "node ID" in v["reason"]


def test_remeasure_pr_git_failure_skips(monkeypatch, tmp_path):
    def boom(cmd, **kw):
        if cmd[0] == "git":
            class R:
                returncode = 128
                stdout = ""
                stderr = "fatal: not a git repository"
            return R
        class R2:
            returncode = 0
            stdout = ""
            stderr = ""
        return R2()
    monkeypatch.setattr(mod, "_run_gh", lambda a: FAKE_LOG)
    monkeypatch.setattr(mod.subprocess, "run", boom)
    v = mod.remeasure_pr("jsboige/CoursIA", 15318, "999", str(tmp_path))
    assert v["verdict"] == "SKIPPED" and "interrompu" in v["reason"]


def test_flagged_entry_carries_run_id_for_remeasure():
    result = mod.analyse(pr_fixture(), cmp_map({(FIX, OLD_BASE): "diverged"}))
    f = result["flagged"][0]
    assert f["run_id"] == "111"
