"""Rejeu du rouge issu de deux branches vertes, sans appel GitHub réel (#24828)."""
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "merge_ready_fixtures", Path(__file__).with_name("test_merge_ready.py")
)
fixtures = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fixtures
spec.loader.exec_module(fixtures)


def git(repo, *args):
    return subprocess.run(["git", *args], cwd=repo, check=True,
                          capture_output=True, text=True,
                          encoding="utf-8", errors="replace").stdout.strip()


#: Numero de l'issue du rouge de `main` dans ce scenario : c'est le numero
#: que le runner attribue a la premiere issue qu'il ouvre (#26706).
ISSUE_ROUGE = 26710

#: Reponse scriptee de ``gh issue view`` : l'issue du rouge existe et vit.
#: Elle est lue au DEUXIEME tour, quand la retenue inscrit deja son numero.
VUE_ISSUE_OUVERTE = {
    "number": ISSUE_ROUGE,
    "title": "[main-red] Scripts Tests (CPU) - test_guard.py::test_combined",
    "body": "corps d'un episode anterieur",
    "state": "OPEN",
}


def test_composition_red_survives_pending_and_cancelled(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q", "-b", "main")
    git(repo, "config", "user.name", "Test")
    git(repo, "config", "user.email", "test@example.invalid")
    (repo / "a.py").write_text("value = 0\n")
    (repo / "b.py").write_text("value = 0\n")
    (repo / "test_guard.py").write_text(
        "import a, b\ndef test_combined():\n    assert a.value + b.value <= 1\n"
    )
    git(repo, "add", ".")
    git(repo, "commit", "-qm", "base")

    def check():
        return subprocess.run(
            [sys.executable, "-m", "pytest", "-q", "test_guard.py"], cwd=repo,
            capture_output=True, text=True,
            encoding="utf-8", errors="replace",
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        )

    git(repo, "checkout", "-qb", "first")
    (repo / "a.py").write_text("value = 1\n")
    git(repo, "commit", "-qam", "first")
    assert check().returncode == 0
    git(repo, "checkout", "-q", "main")
    git(repo, "checkout", "-qb", "second")
    (repo / "b.py").write_text("value = 1\n")
    git(repo, "commit", "-qam", "second")
    assert check().returncode == 0
    git(repo, "checkout", "-q", "first")
    git(repo, "merge", "--no-ff", "-qm", "both", "second")
    red_sha = git(repo, "rev-parse", "HEAD")
    red = check()
    assert red.returncode == 1
    assert "FAILED test_guard.py::test_combined" in red.stdout
    git(repo, "commit", "--allow-empty", "-qm", "cancelled")
    cancelled_sha = git(repo, "rev-parse", "HEAD")
    git(repo, "commit", "--allow-empty", "-qm", "pending")
    pending_sha = git(repo, "rev-parse", "HEAD")

    monkeypatch.setattr(fixtures.mr.gate, "default_stack_index", lambda: {})
    monkeypatch.setattr(fixtures.mr, "utc_now_iso", lambda: "2026-11-11T05:00:00Z")
    checks = {
        pending_sha: fixtures._scripts_check(None, status="in_progress", summary=""),
        cancelled_sha: fixtures._scripts_check("cancelled", summary=""),
        red_sha: fixtures._scripts_check(
            "failure", summary="FAILED test_guard.py::test_combined - assertion"
        ),
    }
    hold = tmp_path / "hold.txt"
    hold.write_text("16808 attente utilisateur\n")
    journal = tmp_path / "journal.jsonl"
    for _ in range(2):
        runner = fixtures.ScriptedRunner(
            main_sha=pending_sha,
            main_history=[pending_sha, cancelled_sha, red_sha],
            main_checks_by_sha=checks,
            main_red_views={ISSUE_ROUGE: VUE_ISSUE_OUVERTE},
        )
        rc = fixtures.mr.run(
            ["--journal", str(journal), "--hold-file", str(hold), "--apply"],
            runner=runner,
        )
        assert rc == 0
        assert not any("gh pr merge" in command for command in runner.flat())
        text = hold.read_text()
        assert "16808 attente utilisateur" in text
        assert f"sha={red_sha}" in text
        assert "test=test_guard.py::test_combined" in text
        # La retenue inscrit le numero de l'issue du rouge : le run suivant
        # relit CETTE issue (etat) avant d'ecrire quoi que ce soit.
        assert f"issue={ISSUE_ROUGE}" in text


def _lecture(etat: str) -> tuple[str, dict | None]:
    """Lit l'issue du rouge dans un runner scripte, et rend (etat, issue)."""
    if etat == "ok":
        runner = fixtures.ScriptedRunner(
            main_red_views={ISSUE_ROUGE: dict(VUE_ISSUE_OUVERTE)}
        )
    elif etat == "absent":
        # Le numero rendu ne correspond pas a celui demande : l'issue
        # demandee n'est pas celle que GitHub a rendue.
        runner = fixtures.ScriptedRunner(
            main_red_views={ISSUE_ROUGE: dict(VUE_ISSUE_OUVERTE, number=99999)}
        )
    elif etat == "illisible":
        runner = fixtures.ScriptedRunner(main_red_view_rc=1)
    else:  # pragma: no cover - garde-fou du test lui-meme
        raise AssertionError("etat inconnu : " + etat)
    return fixtures.mr._read_main_red_issue(runner, {}, ISSUE_ROUGE)


def test_lecture_de_l_issue_connue_rend_les_trois_etats():
    """La lecture d'une issue [main-red] connue distingue trois etats.

    `ok` : le payload est conforme. `absent` : le numero rendu ne
    correspond pas. `illisible` : la lecture echoue. Un etat lu de travers
    ferait ecrire ou rouvrir a tort -- le test doit pouvoir echouer.
    """
    etat, item = _lecture("ok")
    assert etat == "ok"
    assert item is not None
    assert item["number"] == ISSUE_ROUGE
    assert item["state"] == "OPEN"

    etat, item = _lecture("absent")
    assert etat == "absent"
    assert item is None

    etat, item = _lecture("illisible")
    assert etat == "illisible"
    assert item is None


def test_lecture_malformee_est_illisible():
    """Un stdout qui n'est pas du JSON est ILLISIBLE, pas absent."""
    runner = fixtures.ScriptedRunner(
        main_red_views={ISSUE_ROUGE: "{ceci n'est pas du json"}
    )
    etat, item = fixtures.mr._read_main_red_issue(runner, {}, ISSUE_ROUGE)
    assert etat == "illisible"
    assert item is None


def test_issue_fermee_et_rouge_tenant_est_rouverte():
    """Une issue du rouge fermee a tort est ROUVRITE (et non laissee fermee).

    La PR de reparation porte `See #` : la fermeture appartient a la
    sentinelle, au vert mesure. Si le rouge tient encore au commit, l'issue
    doit revivre.
    """
    runner = fixtures.ScriptedRunner(
        main_red_views={
            ISSUE_ROUGE: dict(VUE_ISSUE_OUVERTE, state="CLOSED")
        }
    )
    etat, numero = fixtures.mr.ensure_main_red_issue(
        runner, {}, "a" * 40, "Scripts Tests (CPU)",
        "test_guard.py::test_combined", ISSUE_ROUGE,
    )
    assert (etat, numero) == ("reuse", ISSUE_ROUGE)
    assert runner.main_red_reopened == [ISSUE_ROUGE]


def test_lecture_illisible_ne_rouvre_pas_une_issue_fermee():
    """Fail-closed : une lecture ILLISIBLE ne vaut pas preuve que l'issue
    est fermee -- elle ne rouvre donc rien, mais elle n'ecrit pas non plus
    un etat suppose."""
    runner = fixtures.ScriptedRunner(main_red_view_rc=1)
    etat, numero = fixtures.mr.ensure_main_red_issue(
        runner, {}, "a" * 40, "Scripts Tests (CPU)",
        "test_guard.py::test_combined", ISSUE_ROUGE,
    )
    assert (etat, numero) == ("reuse", ISSUE_ROUGE)
    assert runner.main_red_reopened == []
