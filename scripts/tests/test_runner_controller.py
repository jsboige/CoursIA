from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

# The controller is the Windows-confinement companion of the runner manager
# (#12704): idempotent re-registration of ephemeral runners. The apply paths
# below assume the manager module resolves beside the controller.
CI_DIR = Path(__file__).parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

SPEC = importlib.util.spec_from_file_location(
    "runner_controller", CI_DIR / "runner_controller.py"
)
ctl = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = ctl
SPEC.loader.exec_module(ctl)


class FakeRun:
    """Enregistre chaque invocation et sert des reponses calees sur argv."""

    def __init__(self, *, runners: list[dict] | None = None, token: str = "t" * 40,
                 schtasks_error: str | None = None) -> None:
        self.calls: list[tuple[tuple, dict | None]] = []
        self.runners = runners or []
        self.token = token
        self.schtasks_error = schtasks_error

    def __call__(self, argv, **kwargs):
        self.calls.append((tuple(argv), kwargs.get("env")))
        cmd = " ".join(str(a) for a in argv)
        if cmd.startswith("gh api repos/") and "actions/runners" in cmd \
                and "--method" not in cmd:
            lines = "".join(json.dumps(r) + "\n" for r in self.runners)
            return subprocess.CompletedProcess(argv, 0, stdout=lines, stderr="")
        if "--method" in cmd and "--jq" in cmd and ".token" in cmd:
            return subprocess.CompletedProcess(argv, 0, stdout=self.token + "\n", stderr="")
        if cmd.startswith("schtasks"):
            if self.schtasks_error:
                return subprocess.CompletedProcess(argv, 1, stdout="", stderr=self.schtasks_error)
            return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")
        return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")


@pytest.fixture()
def prof(tmp_path):
    root = tmp_path / "fast-guards"
    return ctl.Profile(
        name="test-fast-guards",
        hostname="test-host",
        repository="jsboige/CoursIA",
        runner_name="test-fast-guards",
        account=r".\coursia-runner",
        root=root,
        work=root / "_work",
        log_root=tmp_path / "logs",
        labels=("self-hosted", "coursia-ephemeral", "coursia-fast-guards"),
        version="2.336.0",
        archive_url="https://example.invalid/runner.zip",
        archive_sha256="a" * 64,
        sensitive_templates=(),
    )


def argv_of(fake: FakeRun, needle: str) -> list[tuple]:
    return [c for c in fake.calls if needle in " ".join(c[0])]


def test_status_plan_lists_actions_without_applying(prof):
    fake = FakeRun(runners=[])
    plan = ctl.plan_for(prof, fake)
    assert plan["planned_actions"] == ["fetch-registration-token", "register", "verify"]
    assert not argv_of(fake, "--method POST")  # lecture seule, aucun token negocie


def test_ensure_noop_when_runner_online(prof, monkeypatch):
    fake = FakeRun(runners=[{"name": "test-fast-guards", "status": "online", "busy": False}])
    seen: list[str] = []
    monkeypatch.setattr(ctl, "apply_register", lambda *a, **k: seen.append("register"))
    result = ctl.apply_ensure(prof, fake)
    assert result == {"action": "noop", "reason": "runner already online"}
    assert seen == []  # un runner online n'est jamais re-enregistre


def test_ensure_registers_when_absent(prof, monkeypatch):
    fake = FakeRun(runners=[])
    seen: list[str] = []
    monkeypatch.setenv(ctl.ACCOUNT_PASSWORD_ENV, "pw")
    monkeypatch.setattr(ctl, "apply_register", lambda *a, **k: seen.append("register"))
    monkeypatch.setattr(ctl, "apply_verify", lambda *a, **k: seen.append("verify"))
    result = ctl.apply_ensure(prof, fake)
    assert result == {"action": "registered"}
    assert seen == ["register", "verify"]
    posts = argv_of(fake, "registration-token")
    assert posts, "un token frais doit etre negocie a chaque re-enregistrement"


def test_ensure_requires_password_before_any_token(prof, monkeypatch):
    fake = FakeRun(runners=[])
    monkeypatch.delenv(ctl.ACCOUNT_PASSWORD_ENV, raising=False)
    with pytest.raises(ctl.Broken, match="COURSIA_RUNNER_ACCOUNT_PASSWORD"):
        ctl.apply_ensure(prof, fake)
    assert not argv_of(fake, "--method POST")  # fail-closed avant tout appel reseau


def test_ensure_token_never_in_argv_and_popped_after(prof, monkeypatch):
    fake = FakeRun(runners=[], token="S" * 48)
    monkeypatch.setenv(ctl.ACCOUNT_PASSWORD_ENV, "pw")
    monkeypatch.setattr(ctl, "apply_register", lambda *a, **k: None)
    monkeypatch.setattr(ctl, "apply_verify", lambda *a, **k: None)
    ctl.apply_ensure(prof, fake)
    assert os.environ.get(ctl.REGISTRATION_TOKEN_ENV) is None
    for argv, _ in fake.calls:
        assert "S" * 48 not in " ".join(str(a) for a in argv)


def test_deregister_noop_when_absent_everywhere(prof):
    fake = FakeRun(runners=[])
    result = ctl.apply_deregister(prof, fake)
    assert result["action"] == "noop"
    assert not argv_of(fake, "removal-token")


def test_task_xml_deterministic_and_pinned(prof):
    first, second = ctl.task_xml(prof), ctl.task_xml(prof)
    assert first == second  # deux generations = meme etat (idempotence)
    assert "PT60S" in first
    assert "IgnoreNew" in first
    assert "PT10M" in first  # un tick ne peut pas vivre plus de 10 minutes


def test_task_action_reads_password_from_file_never_embeds_it(prof):
    action = ctl.task_action(prof)
    assert "runner_pwd.txt" in action  # lit le fichier machine local conventionnel
    assert "ensure --profile test-fast-guards --apply" in action
    assert "controller.log" in action


def test_task_install_requires_elevation(prof, monkeypatch):
    monkeypatch.setattr(ctl, "_is_elevated", lambda: False)
    with pytest.raises(ctl.Broken, match="elevated"):
        ctl.apply_task_install(prof, FakeRun())


def test_task_remove_absent_task_is_explicit_success(prof, monkeypatch):
    monkeypatch.setattr(ctl, "_is_elevated", lambda: True)
    fake = FakeRun(schtasks_error="ERROR: The system cannot find the file specified.")
    result = ctl.apply_task_remove(prof, fake)
    assert result["action"] == "task-removed"  # second passage = succes explicite


def test_task_remove_real_error_refuses(prof, monkeypatch):
    monkeypatch.setattr(ctl, "_is_elevated", lambda: True)
    fake = FakeRun(schtasks_error="ERROR: Access is denied.")
    with pytest.raises(ctl.Broken, match="schtasks /Delete failed"):
        ctl.apply_task_remove(prof, fake)
