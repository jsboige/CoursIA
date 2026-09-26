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
    title: str = "fix(x): une PR ordinaire",
    reviews: list[dict] | None = None,
) -> dict:
    return {
        "number": pr,
        "title": title,
        "isDraft": draft,
        "body": body if body is not None else GRAIN_MED,
        "headRefOid": HEAD,
        "files": [{"path": p} for p in files],
        "changedFiles": len(files),
        "comments": comments
        if comments is not None
        else [{"body": dossier_body()}],
        "reviews": reviews if reviews is not None else [],
    }


def review_row(
    *,
    state: str = "APPROVED",
    oid: str = HEAD,
    submitted: str = "2026-09-25T03:00:00Z",
    body: str = "",
    login: str = "clusterManager-Myia",
) -> dict:
    """Forme de ``gh pr view --json reviews`` (l'oid de review est sur ``commit``)."""
    return {
        "author": {"login": login},
        "state": state,
        "body": body,
        "submittedAt": submitted,
        "commit": {"oid": oid},
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
        gate_stderr: str = "",
        fetch_rc: int = 0,
        twin_rc: int = 0,
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
        # stderr du gate : c'est lui qui porte un motif de portee generale
        # (jeton refuse, quota) quand le gate echoue POUR TOUTE la passe.
        self.gate_stderr = gate_stderr
        self.fetch_rc = fetch_rc
        self.twin_rc = twin_rc
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
            return mr.RunResult(self.gate_rc, payload, self.gate_stderr)
        if len(c) > 1 and "check_unaddressed_nits.py" in c[1]:
            return mr.RunResult(self.nits_rc, "", "")
        if c[:1] == ["git"] and "fetch" in c:
            return mr.RunResult(self.fetch_rc, "", "")
        if len(c) > 1 and "check_twin_index_collisions.py" in c[1]:
            return mr.RunResult(self.twin_rc, "", "")
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
    assert lines[-1]["reason"].startswith("scope:.claude:")


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
    assert lines[-1]["reason"].startswith("scope:.github:")


def test_skip_frozen_umbrella_in_title(tmp_path):
    # #17021 : mergee sous le veto densite #17040 sur un dossier READY.
    view = default_view(title="fix(pedagogy,#13410): g59-search-1 — 9 lectures")
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "frozen:#13410(veto #17040)"
    assert not any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())
    assert not any(" merge " in f" {flat} " for flat in runner.flat())


def test_skip_frozen_umbrella_in_body(tmp_path):
    view = default_view(body=GRAIN_MED + "\n\nSee #13410 (densite).")
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "frozen:#13410(veto #17040)"


def test_frozen_umbrella_prefix_number_not_matched():
    assert mr.frozen_umbrella_exclusion("fix: #134100", "voir #134101") is None
    assert mr.frozen_umbrella_exclusion("fix: #13410.", None) is not None


def test_frozen_umbrella_qc_density_round2():
    # #11601 gele le 2026-09-23 sous le meme veto #17040 (#17386 en est la PR ouverte).
    assert (
        mr.frozen_umbrella_exclusion("enrich(qc,#11601): densite QC-Py-06b", None)
        == "frozen:#11601(veto #17040)"
    )
    assert mr.frozen_umbrella_exclusion("fix: #116010", None) is None


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
    # 1 lecture initiale + MERGEABLE_RETRIES relectures, autant de sommeils
    assert sum(1 for c in runner.cmds() if c[:2] == ["gh", "api"] and "/pulls/" in c[2]) == mr.MERGEABLE_RETRIES + 1
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


def test_erreur_de_portee_generale_arrete_le_run(tmp_path):
    # #17672 point 3 : le fail-closed est PRESERVE pour ce qui frappe toute la
    # passe -- ici un jeton refuse dans le gate (marqueur « bad credentials »).
    # rc 5 du gate : hors codes documents {0,1,2,3} -> arret, exit 1, et la PR
    # suivante n'est pas touchee : la repeter ne dirait rien de plus.
    runner = ScriptedRunner(
        prs=(201, 202), gate_rc=5, gate_stderr="gh: Bad credentials (HTTP 401)"
    )
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 1
    assert lines[-1]["verdict"] == "run-error"
    assert not any("202" in flat for flat in runner.flat())


def test_erreur_dune_pr_est_isolee_et_le_balayage_continue(tmp_path, capsys):
    """#17672 point 3 : une erreur attribuable a UNE PR ne gele plus les autres.

    Falsification : avant le correctif, le `break` de la boucle emportait le
    balayage entier -- la PR suivante n'etait meme pas evaluee et le run
    s'arretait sur la premiere PR mal formee. Ici la vue de 201 est illisible
    (`gh pr view 201 : la reponse n'est pas un objet`), 202 est une PR normale.
    """
    runner = ScriptedRunner(prs=(201, 202), views={201: ["pas", "un", "objet"]})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))

    assert rc == 1, "une erreur isolee reste un incident : rc=1"
    assert [row["pr"] for row in lines] == [201, 202]
    assert lines[0]["verdict"] == "run-error"
    assert "n'est pas un objet" in lines[0]["reason"], lines[0]["reason"]
    # La PR SUIVANTE est bien evaluee puis mergee : c'est tout l'objet du point 3.
    assert lines[1]["verdict"] == "merged", lines[1]
    assert any("202" in flat for flat in runner.flat())

    out = capsys.readouterr().out
    # Le run ne s'est PAS arrete : publier « arret » serait un constat faux.
    assert "arret :" not in out
    # ...mais l'erreur isolee doit etre visible, sinon elle disparait du rapport.
    assert "1 erreur(s) isolee(s)" in out, out


def test_is_pass_wide_classe_par_le_texte_de_l_outil():
    # Classification pure, sans boucle : un motif reconnu = portee generale ;
    # tout le reste = attribuable a la PR (donc isole). Le sens de l'erreur par
    # defaut compte : un texte inconnu ne doit JAMAIS arreter le balayage.
    assert mr.is_pass_wide(
        mr.UnexpectedError("gh pr view 9 rc=1 : API rate limit exceeded")
    )
    assert mr.is_pass_wide(
        mr.UnexpectedError("gh pr list rc=1 : could not resolve host: api.github.com")
    )
    assert not mr.is_pass_wide(
        mr.UnexpectedError("gate PR 9 rc=5 hors contrat : (sans message)")
    )
    assert not mr.is_pass_wide(
        mr.UnexpectedError("gh pr view 9 : la reponse n'est pas un objet")
    )


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
        assert set(row.keys()) == {
            "ts", "pr", "head", "verdict", "reason", "merged", "review",
        }
        assert re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", row["ts"])
        assert isinstance(row["pr"], int)
        assert row["merged"] is True and row["verdict"] == "merged"
        assert row["reason"] is None
        # Une ligne mergee porte la disposition CLASSEE, pas « non evaluee » :
        # le verdict terminal est reconstruit apres le merge, il doit heriter de
        # la classification faite avant.
        assert row["review"] == mr.NO_APPROVAL
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


def test_frozen_branch_prefix_without_umbrella_reference():
    # Relais g-XX de #13410 : ni le titre ni le body ne citent le parapluie.
    assert (
        mr.frozen_umbrella_exclusion(
            "fix(search,g77): relocate 12 lectures", "Grain: MED/notebook", "wt/vibe-g77-search-26"
        )
        == "frozen:#13410(veto #17040,branch wt/vibe-*)"
    )
    assert mr.frozen_umbrella_exclusion("fix(x): ordinaire", None, "fix/vibe-check") is None
    assert mr.frozen_umbrella_exclusion("fix(x): ordinaire", None, None) is None


def test_skip_frozen_branch_before_gate(tmp_path):
    view = default_view(title="fix(search,g71): lectures reprises")
    view["headRefName"] = "wt/vibe-g71-search-20"
    runner = ScriptedRunner(views={123: view})
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "frozen:#13410(veto #17040,branch wt/vibe-*)"
    assert not any("check_adjoint_prevalidation.py" in flat for flat in runner.flat())


# --- retenues du coordinateur (hold.txt) ----------------------------------------


def test_hold_skips_before_any_pr_call(tmp_path):
    # La retenue est lue a cote du journal ; la PR retenue n'est ni vue, ni
    # passee au gate, ni mergee -- la PR suivante suit le chemin nominal.
    (tmp_path / "hold.txt").write_text(
        "# retenues ai-01\n\n16808  # rebase sur #17521 d'abord\n", encoding="utf-8"
    )
    runner = ScriptedRunner(prs=(16808, 124))
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    by_pr = {row["pr"]: row for row in lines}
    assert by_pr[16808]["verdict"] == "skipped"
    assert by_pr[16808]["reason"] == "hold:rebase sur #17521 d'abord"
    assert not any(flat.startswith("gh pr view 16808") for flat in runner.flat())
    assert not any("merge 16808" in flat for flat in runner.flat())
    assert by_pr[124]["verdict"] == "merged"


def test_hold_without_reason_names_the_file(tmp_path):
    (tmp_path / "hold.txt").write_text("123\n", encoding="utf-8")
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["reason"] == "hold:hold.txt"


def test_hold_file_absent_means_no_hold(tmp_path):
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 0
    assert lines[-1]["verdict"] == "merged"


def test_hold_hash_number_is_malformed_not_a_comment(tmp_path):
    # `#17530` lu comme un commentaire ferait tomber la retenue en silence :
    # l'organe refuse de demarrer plutot que de merger sans savoir.
    (tmp_path / "hold.txt").write_text("#123 attente decision\n", encoding="utf-8")
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 2
    assert lines == []
    assert not any(" merge " in f" {flat} " for flat in runner.flat())


def test_hold_malformed_line_refuses_to_start(tmp_path):
    (tmp_path / "hold.txt").write_text("PR 123\n", encoding="utf-8")
    runner = ScriptedRunner()
    rc, _, _ = run_organ(tmp_path, runner, extra=("--apply",))
    assert rc == 2
    assert runner.calls == []


def test_hold_file_override(tmp_path):
    other = tmp_path / "ailleurs" / "retenues.txt"
    other.parent.mkdir()
    other.write_text("123 ordre de stack\n", encoding="utf-8")
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(
        tmp_path, runner, extra=("--apply", "--hold-file", str(other))
    )
    assert rc == 0
    assert lines[-1]["reason"] == "hold:ordre de stack"


# --- disposition de review classee a la tete evaluee (point 1 de #17672) ---------


def test_disposition_approbation_a_la_tete():
    view = default_view(reviews=[review_row(oid=HEAD)])
    assert mr.review_disposition(view, HEAD) == mr.APPROVED_EXACT_HEAD


def test_disposition_approbation_sur_une_tete_ancienne():
    # L'approbation existe, mais elle porte sur un commit anterieur : elle ne
    # couvre pas le commit qui va etre merge.
    view = default_view(reviews=[review_row(oid=HEAD_MOVED)])
    assert mr.review_disposition(view, HEAD) == mr.APPROVAL_NOT_ON_HEAD


def test_disposition_verdict_en_corps_compte_a_la_tete():
    # Le jeton de review du cluster ne peut poster que des COMMENT : son
    # approbation vit dans le CORPS de la voix, pas dans l'etat de l'API (#16926).
    view = default_view(
        reviews=[
            review_row(
                state="COMMENTED",
                oid=HEAD,
                body=(
                    "**[Hermes]** — VERDICT: LGTM "
                    "(contrainte token CoursIA : COMMENT only, #15511)"
                ),
            )
        ]
    )
    assert mr.review_disposition(view, HEAD) == mr.APPROVED_EXACT_HEAD


def test_disposition_voix_posterieure_non_approbatrice_retire_l_approbation():
    # Latest-wins sur la tete : une approbation suivie, sur la MEME tete, d'une
    # voix qui n'approuve pas ne gouverne plus.
    view = default_view(
        reviews=[
            review_row(oid=HEAD, submitted="2026-09-25T03:00:00Z"),
            review_row(
                state="COMMENTED",
                oid=HEAD,
                submitted="2026-09-25T04:00:00Z",
                body="VERDICT: CONCERNS (test rouge depuis le dernier push)",
            ),
        ]
    )
    assert mr.review_disposition(view, HEAD) == mr.APPROVAL_NOT_ON_HEAD


def test_disposition_sans_approbation_lue():
    assert mr.review_disposition(default_view(), HEAD) == mr.NO_APPROVAL
    # Une voix qui ne type pas de verdict n'est pas une approbation.
    view = default_view(reviews=[review_row(state="COMMENTED")])
    assert mr.review_disposition(view, HEAD) == mr.NO_APPROVAL


def test_deux_prs_qui_ne_different_que_par_la_tete_de_l_approbation(tmp_path):
    """Le defaut vise : a tout le reste egal, l'organe ne distinguait pas une PR
    approuvee a la tete de la PR approuvee sur un commit anterieur."""
    views = {
        201: default_view(pr=201, reviews=[review_row(oid=HEAD)]),
        202: default_view(pr=202, reviews=[review_row(oid=HEAD_MOVED)]),
    }
    rc, lines, _ = run_organ(tmp_path, ScriptedRunner(prs=(201, 202), views=views))
    assert rc == 0
    assert [row["verdict"] for row in lines] == ["would-merge", "would-merge"]
    reste = [
        {k: row[k] for k in ("head", "verdict", "reason", "merged")} for row in lines
    ]
    assert reste[0] == reste[1]
    assert lines[0]["review"] == mr.APPROVED_EXACT_HEAD
    assert lines[1]["review"] == mr.APPROVAL_NOT_ON_HEAD


def test_un_skip_porte_la_disposition_de_la_tete_evaluee(tmp_path):
    views = {201: default_view(pr=201, draft=True, reviews=[review_row(oid=HEAD)])}
    rc, lines, _ = run_organ(tmp_path, ScriptedRunner(prs=(201,), views=views))
    assert rc == 0
    assert lines[-1]["reason"] == "draft"
    assert lines[-1]["review"] == mr.APPROVED_EXACT_HEAD


def test_le_bilan_compte_les_candidates_par_disposition(tmp_path, capsys):
    views = {
        201: default_view(pr=201, reviews=[review_row(oid=HEAD)]),
        202: default_view(pr=202, reviews=[review_row(oid=HEAD_MOVED)]),
    }
    run_organ(tmp_path, ScriptedRunner(prs=(201, 202), views=views))
    out = capsys.readouterr().out
    assert "candidates : 1 approved-exact-head, 1 approval-not-on-head" in out
    assert "[review: approved-exact-head]" in out

# --- 5bis. collision d'index twin-pairs -----------------------------------------

TWIN_FILE = "scripts/notebook_tools/twin_pairs.d/sw-5-linked-data/0012-2026-09-25-lane.yaml"


def test_twin_organ_not_called_when_registry_untouched(tmp_path):
    """Une PR hors registre twin ne paie ni fetch ni organe."""
    runner = ScriptedRunner()
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[0]["verdict"] == "would-merge"
    assert not any("check_twin_index_collisions.py" in f for f in runner.flat())
    assert not any(cmd[:1] == ["git"] for cmd in runner.cmds())


def test_twin_collision_skips(tmp_path):
    view = default_view(files=("src/a.py", TWIN_FILE))
    runner = ScriptedRunner(views={123: view}, twin_rc=1)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert rc == 0
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-index-collision"


def test_twin_clean_merges_and_compares_the_gated_head(tmp_path):
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, twin_rc=0)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "would-merge"
    twin = [c for c in runner.cmds() if len(c) > 1 and "check_twin_index_collisions.py" in c[1]]
    assert len(twin) == 1
    assert twin[0][twin[0].index("--head") + 1] == HEAD
    assert twin[0][twin[0].index("--base") + 1] == "origin/main"
    # le fetch precede l'organe : le main compare est celui du moment
    flat = runner.flat()
    fetch_at = next(i for i, f in enumerate(flat) if f.startswith("git ") and " fetch " in f)
    twin_at = next(i for i, f in enumerate(flat) if "check_twin_index_collisions.py" in f)
    assert fetch_at < twin_at
    assert "pull/123/head" in flat[fetch_at]


def test_twin_organ_unreadable_is_fail_closed(tmp_path):
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, twin_rc=2)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-collision-unreadable:rc=2"


def test_twin_fetch_failure_is_fail_closed(tmp_path):
    view = default_view(files=(TWIN_FILE,))
    runner = ScriptedRunner(views={123: view}, fetch_rc=128)
    rc, lines, _ = run_organ(tmp_path, runner)
    assert lines[0]["verdict"] == "skipped"
    assert lines[0]["reason"] == "twin-collision-unreadable:fetch"
    assert not any("check_twin_index_collisions.py" in f for f in runner.flat())
