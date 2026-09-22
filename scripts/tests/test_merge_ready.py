"""Tests hermetiques de l'organe merge_ready (Q40) -- aucun reseau, aucun gh.

Toutes les commandes passent par un runner scripte : le module sous test
est charge par importlib (meme convention que test_check_adjoint_prevalidation)
et ses sous-processus ne quittent jamais le processus de test.
"""

import importlib.util
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MERGE_READY_PATH = HERE.parent / "coordination" / "merge_ready.py"
_spec = importlib.util.spec_from_file_location("merge_ready_under_test", MERGE_READY_PATH)
mr = importlib.util.module_from_spec(_spec)
sys.modules["merge_ready_under_test"] = mr
_spec.loader.exec_module(mr)

HEAD = "0123456789abcdef0123456789abcdef01234567"
HEAD_MOVED = "fedcba9876543210fedcba9876543210fedcba98"
TOKEN = "tok-myia-ai-01-fake"
GRAIN_MED = "Grain: MED/guard -- lane myia-po-2026:CoursIA -- prev: MED/guard #1"
GRAIN_DEEP = "Grain: DEEP/lean -- lane myia-po-2026:CoursIA -- prev: MED/guard #1"


def dossier_body(b0: str = "clear") -> str:
    """Un corps de dossier valide pour parse_dossier (seul le champ b0 varie)."""
    return "\n".join(
        [
            "[ADJOINT PREFLIGHT]",
            "schema: 1",
            "lane: myia-po-2025:CoursIA-2",
            "pr: 123",
            f"head: {HEAD}",
            "complete: true",
            "body: read",
            "comments-reviewed: 1",
            "reviews-reviewed: 0",
            "threads-reviewed: 0",
            "threads-unresolved: 0",
            "surfaces-sha256: " + "a" * 64,
            "diff-files: 1",
            "diff-additions: 1",
            "diff-deletions: 0",
            "checks: latest-wins-green",
            f"b0: {b0}",
            "scope: pass",
            "domain: pass",
            "verdict: READY",
            "[/ADJOINT PREFLIGHT]",
        ]
    )


def rest_comments(b0: str = "clear") -> list[dict]:
    """Forme REST de gh api issues/N/comments (user.login, pas author.login)."""
    return [{"user": {"login": "jsboige"}, "body": dossier_body(b0)}]


def default_view(
    *,
    pr: int = 123,
    draft: bool = False,
    files: tuple[str, ...] = ("src/a.py",),
    body: str | None = None,
    comments: list[dict] | None = None,
) -> dict:
    return {
        "number": pr,
        "isDraft": draft,
        "body": body if body is not None else GRAIN_MED,
        "headRefOid": HEAD,
        "files": [{"path": p} for p in files],
        "changedFiles": len(files),
        "comments": comments
        if comments is not None
        else [{"body": dossier_body()}],
    }


class ScriptedRunner:
    """Runner fake : dispatch par contenu de commande. Defauts = chemin nominal
    (une PR unique prete au merge, gate READY, b0 clear, B.0 clear, clean)."""

    def __init__(
        self,
        *,
        token: str = TOKEN,
        token_rc: int = 0,
        prs: tuple[int, ...] = (123,),
        views: dict[int, dict] | None = None,
        gate_rc: int = 0,
        comments: list[dict] | None = None,
        nits_rc: int = 0,
        pulls: list[dict] | None = None,
        merge_rc: int = 0,
    ):
        self.token = token
        self.token_rc = token_rc
        self.prs = list(prs)
        self.views = views or {}
        self.gate_rc = gate_rc
        self.comments = comments
        self.nits_rc = nits_rc
        self.pulls = pulls or [{"mergeable_state": "clean", "head": {"sha": HEAD}}]
        self.merge_rc = merge_rc
        self.calls: list[tuple[list[str], dict | None]] = []
        self.sleeps: list[float] = []

    # -- helpers d'assertion -------------------------------------------------

    def cmds(self) -> list[list[str]]:
        return [cmd for cmd, _ in self.calls]

    def flat(self) -> list[str]:
        return [" ".join(cmd) for cmd, _ in self.calls]

    # -- contrat Runner ------------------------------------------------------

    def run(self, cmd: list[str], env: dict | None = None) -> mr.RunResult:
        self.calls.append((list(cmd), env))
        c = list(cmd)
        if c[:4] == ["gh", "auth", "token", "--user"]:
            if self.token_rc != 0:
                return mr.RunResult(self.token_rc, "", "auth failed")
            return mr.RunResult(0, self.token + "\n", "")
        if c[:3] == ["gh", "pr", "list"]:
            return mr.RunResult(
                0, json.dumps([{"number": n} for n in self.prs]), ""
            )
        if c[:3] == ["gh", "pr", "view"]:
            pr = int(c[3])
            view = self.views.get(pr, default_view(pr=pr))
            return mr.RunResult(0, json.dumps(view), "")
        if c[:3] == ["gh", "pr", "merge"]:
            if self.merge_rc == 0:
                return mr.RunResult(0, "", "")
            return mr.RunResult(self.merge_rc, "", "merge refused")
        if c[:2] == ["gh", "api"] and "/comments" in c[2]:
            rows = self.comments if self.comments is not None else rest_comments()
            return mr.RunResult(0, json.dumps(rows), "")
        if c[:2] == ["gh", "api"] and "/pulls/" in c[2]:
            row = self.pulls.pop(0) if len(self.pulls) > 1 else self.pulls[0]
            return mr.RunResult(0, json.dumps(row), "")
        if len(c) > 1 and "check_adjoint_prevalidation.py" in c[1]:
            payload = json.dumps(
                {
                    "pr": int(c[2]),
                    "head": HEAD,
                    "ready": self.gate_rc == 0,
                    "verdict": "READY" if self.gate_rc == 0 else "NO_DOSSIER",
                    "errors": [],
                }
            )
            return mr.RunResult(self.gate_rc, payload, "")
        if len(c) > 1 and "check_unaddressed_nits.py" in c[1]:
            return mr.RunResult(self.nits_rc, "", "")
        raise AssertionError("commande non scriptee : " + " ".join(c))

    def sleep(self, seconds: float) -> None:
        self.sleeps.append(seconds)


def run_organ(tmp_path: Path, runner: ScriptedRunner, extra: tuple[str, ...] = ()) -> tuple[int, list[dict], Path]:
    """Lance un run avec journal isole ; retourne (rc, lignes de journal, chemin)."""
    journal = tmp_path / "journal.jsonl"
    rc = mr.run(["--journal", str(journal), *extra], runner=runner)
    lines = []
    if journal.is_file():
        lines = [json.loads(row) for row in journal.read_text(encoding="utf-8").splitlines() if row.strip()]
    return rc, lines, journal


# --- chaque raison de skip, une par une ----------------------------------------


def test_skip_draft(tmp_path):
    runner = ScriptedRunner(views={123: default_view(draft=True)})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "skipped" and lines[-1]["reason"] == "draft"
    # le gate couteux n'est jamais appele sur un brouillon
    assert not any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())


def test_skip_no_dossier_comment(tmp_path):
    runner = ScriptedRunner(
        views={123: default_view(comments=[{"body": "un commentaire ordinaire"}])}
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "no-adjoint-preflight-comment"
    assert not any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())


def test_skip_file_under_claude_dir(tmp_path):
    runner = ScriptedRunner(views={123: default_view(files=(".claude/rules/x.md",))})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"].startswith("scope:.claude/")


def test_skip_file_claude_md_any_dir(tmp_path):
    for path in ("CLAUDE.md", "docs/reference/CLAUDE.md"):
        runner = ScriptedRunner(views={123: default_view(files=("src/a.py", path))})
        rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
        assert rc == 0, path
        assert lines[-1]["reason"].startswith("scope:CLAUDE.md"), path


def test_skip_file_under_github_dir(tmp_path):
    runner = ScriptedRunner(views={123: default_view(files=(".github/workflows/a.yml",))})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"].startswith("scope:.github/")


def test_skip_grain_deep(tmp_path):
    runner = ScriptedRunner(views={123: default_view(body=GRAIN_DEEP)})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "grain-tier-DEEP"


def test_skip_grain_unparsable(tmp_path):
    runner = ScriptedRunner(views={123: default_view(body="Aucun tag Grain dans ce corps.")})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "grain-tier-unparsable"


def test_skip_grain_tier_hors_grammaire_fail_closed(tmp_path):
    # Tier lisible mais hors (DEEP, MED, LIGHT) : la grammaire ne le connait
    # pas, fail-closed (le mandat couvre DEEP et l'illisible ; l'inconnu
    # l'est aussi).
    runner = ScriptedRunner(
        views={123: default_view(body="Grain: ULTRA/x -- lane myia-po-2026:CoursIA")}
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"].startswith("grain-tier-unknown:")


def test_skip_grain_light_passe_le_filtre(tmp_path):
    # LIGHT est dans le perimetre (b) : la PR arrive jusqu'au merge.
    runner = ScriptedRunner(
        views={123: default_view(body="Grain: LIGHT/guard -- lane myia-po-2026:CoursIA")}
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged" and lines[-1]["merged"] is True


def test_skip_gate_not_ready(tmp_path):
    for gate_rc, expected in (
        (1, "gate:no-dossier"),
        (2, "gate:unknown"),
        (3, "gate:blocked"),
    ):
        runner = ScriptedRunner(gate_rc=gate_rc)
        rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
        assert rc == 0, gate_rc
        assert lines[-1]["reason"] == expected, gate_rc
        # pas d'organe B.0 ni de merge apres un gate non-ready
        assert not any("check_unaddressed_nits.py" in flat for flat in runner.flat())
        assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_skip_dossier_b0_blocked(tmp_path):
    # Le gate dit ready mais le dossier porte b0: blocked -- l'organe
    # controle lui-meme le champ declaratif (ceinture et bretelles : le
    # gate actuel refuse deja un READY sans b0 clear, le mandat demande le
    # controle explicite).
    runner = ScriptedRunner(comments=rest_comments(b0="blocked"))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "dossier-b0-blocked"
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_skip_b0_organ_rc1(tmp_path):
    runner = ScriptedRunner(nits_rc=1)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "b0-organ-blocked"
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_skip_mergeable_state_not_clean(tmp_path):
    for state in ("dirty", "unstable", "blocked", "has_hooks"):
        runner = ScriptedRunner(
            pulls=[{"mergeable_state": state, "head": {"sha": HEAD}}]
        )
        rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
        assert rc == 0, state
        assert lines[-1]["reason"] == f"mergeable-state:{state}", state
        assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())


def test_skip_head_moved(tmp_path):
    # mergeable_state clean mais la tete REST n'est plus celle que le gate
    # a evaluee : le dossier est perime, skip nomme.
    runner = ScriptedRunner(
        pulls=[{"mergeable_state": "clean", "head": {"sha": HEAD_MOVED}}]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "head-moved"


# --- retry unknown -> clean ------------------------------------------------------


def test_mergeable_unknown_then_clean_merges(tmp_path):
    runner = ScriptedRunner(
        pulls=[
            {"mergeable_state": "unknown", "head": {"sha": HEAD}},
            {"mergeable_state": "clean", "head": {"sha": HEAD}},
        ]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged" and lines[-1]["merged"] is True
    # 2 lectures REST (unknown puis clean) + 1 sommeil entre les deux
    assert sum(1 for c in runner.cmds() if c[:2] == ["gh", "api"] and "/pulls/" in c[2]) == 2
    assert runner.sleeps == [mr.MERGEABLE_RETRY_SLEEP_S]


def test_mergeable_unknown_persistant_skippe(tmp_path):
    runner = ScriptedRunner(
        pulls=[{"mergeable_state": "unknown", "head": {"sha": HEAD}}]
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "mergeable-state:unknown"
    # 1 lecture initiale + 3 retries, 3 sommeils
    assert sum(1 for c in runner.cmds() if c[:2] == ["gh", "api"] and "/pulls/" in c[2]) == 4
    assert len(runner.sleeps) == mr.MERGEABLE_RETRIES


# --- dry-run et --apply -----------------------------------------------------------


def test_dry_run_merges_rien(tmp_path):
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=())  # pas de --apply
    assert rc == 0
    # tous les controles lecture-only sont passes...
    assert any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())
    assert any("check_unaddressed_nits.py" in flat for flat in runner.flat())
    # ...mais AUCUN merge
    assert not any(c[:3] == ["gh", "pr", "merge"] for c in runner.cmds())
    assert lines[-1]["verdict"] == "would-merge" and lines[-1]["merged"] is False


def test_apply_merge_commande_canonique(tmp_path):
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged" and lines[-1]["merged"] is True
    merge_cmds = [c for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert len(merge_cmds) == 1
    cmd = merge_cmds[0]
    assert "--repo" in cmd and cmd[cmd.index("--repo") + 1] == "jsboige/CoursIA"
    assert "--squash" in cmd
    assert "--match-head-commit" in cmd and cmd[cmd.index("--match-head-commit") + 1] == HEAD
    assert "--delete-branch" not in cmd
    assert "--admin" not in cmd


def test_max_arrete_le_run(tmp_path):
    runner = ScriptedRunner(prs=(101, 102))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply", "--max", "1"))
    assert rc == 0
    merge_cmds = [c for c in runner.cmds() if c[:3] == ["gh", "pr", "merge"]]
    assert len(merge_cmds) == 1
    # la seconde PR n'est meme pas evaluee une fois le plafond atteint
    assert not any("102" in flat for flat in runner.flat())
    assert [row["pr"] for row in lines] == [101]


def test_erreur_inattendue_arrete_le_run(tmp_path):
    # rc 5 du gate : hors codes documents {0,1,2,3} -> arret, exit 1, et la
    # PR suivante n'est pas touchee.
    runner = ScriptedRunner(prs=(201, 202), gate_rc=5)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 1
    assert lines[-1]["verdict"] == "run-error"
    assert not any("202" in flat for flat in runner.flat())


def test_merge_echoue_arrete_le_run(tmp_path):
    # un merge refuse est une erreur inattendue : jamais de merge en aveugle
    runner = ScriptedRunner(prs=(301, 302), merge_rc=1)
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 1
    assert lines[-1]["verdict"] == "merge-failed" and lines[-1]["merged"] is False
    assert not any("302" in flat for flat in runner.flat())


# --- journal -----------------------------------------------------------------------


def test_journal_ligne_par_pr(tmp_path):
    runner = ScriptedRunner(prs=(401, 402))
    rc, lines, journal = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert journal.is_file()
    assert len(lines) == 2
    for row in lines:
        assert set(row.keys()) == {"ts", "pr", "head", "verdict", "reason", "merged"}
        assert re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", row["ts"])
        assert isinstance(row["pr"], int)
        assert row["merged"] is True and row["verdict"] == "merged"
        assert row["reason"] is None
    assert [row["pr"] for row in lines] == [401, 402]  # ancienne d'abord


# --- jeton --------------------------------------------------------------------------


def test_jeton_epingle_sur_chaque_appel_gh(tmp_path):
    runner = ScriptedRunner(prs=(501,))
    rc, _, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert runner.calls, "le run doit avoir appele au moins le resolve du jeton"
    for cmd, env in runner.calls:
        flat = " ".join(cmd)
        assert "switch" not in flat, "gh auth switch est interdit"
        if cmd[:4] == ["gh", "auth", "token", "--user"]:
            # la resolution elle-meme tourne SANS GH_TOKEN ambiant
            assert env is not None and "GH_TOKEN" not in env
            continue
        assert env is not None, f"env absent pour : {flat}"
        assert env.get("GH_TOKEN") == TOKEN, f"jeton non epingle pour : {flat}"


def test_jeton_irresolu_exit_2(tmp_path):
    runner = ScriptedRunner(token_rc=1)
    journal = tmp_path / "journal.jsonl"
    rc = mr.run(["--journal", str(journal)], runner=runner)
    assert rc == 2
    assert not journal.is_file()
    # aucune commande au-dela de la resolution du jeton
    assert len(runner.calls) == 1


# --- garde de troncature et pre-controle du dossier (revue ai-01) -------------


def test_skip_files_truncated_fail_closed(tmp_path):
    # `gh pr view --json files` plafonne la liste : une PR plus grosse que ce
    # que la vue montre pourrait cacher un fichier hors perimetre.
    view = default_view(files=("src/a.py",))
    view["changedFiles"] = 150
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "files-truncated:1/150"
    assert not any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())


def test_skip_changed_files_absent_fail_closed(tmp_path):
    view = default_view()
    del view["changedFiles"]
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"].startswith("files-truncated:")


def test_precheck_dossier_tete_perimee_sans_gate(tmp_path):
    # Le dernier dossier vise HEAD, la PR a ete poussee depuis : le gate
    # refuserait ; le pre-controle le dit sans payer le gate.
    view = default_view()
    view["headRefOid"] = HEAD_MOVED
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "dossier-head-stale"
    assert not any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())


def test_precheck_dossier_b0_blocked_sans_gate(tmp_path):
    runner = ScriptedRunner(
        views={123: default_view(comments=[{"body": dossier_body(b0="blocked")}])}
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert lines[-1]["reason"] == "dossier-b0-not-clear:blocked"
    assert not any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())


def test_precheck_dossier_illisible_laisse_decider_le_gate(tmp_path):
    # Un dossier que le pre-controle ne sait pas lire n'est PAS refuse ici :
    # la decision reste au gate (qui, dans ce scenario, rend ready).
    runner = ScriptedRunner(
        views={123: default_view(comments=[{"body": "[ADJOINT PREFLIGHT]"}])}
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())
    assert lines[-1]["verdict"] == "merged"
