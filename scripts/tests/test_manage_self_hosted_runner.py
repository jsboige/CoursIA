from __future__ import annotations

import ast
import collections
import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import zipfile
from pathlib import Path

import pytest

# The runner-manager is a Windows-confinement tool (#12704: isolated Windows
# runners, Windows accounts, NTFS ACLs). The tests below that exercise apply
# paths assume a Windows host: USERPROFILE/APPDATA probes, os.name == "nt"
# Path() flavor (a monkeypatched os.name cannot make pathlib instantiate
# WindowsPath on Linux). Linux CI runs the platform-neutral surface only;
# the Windows-hosted surface runs on the Windows runners the tool manages.
requires_windows = pytest.mark.skipif(
    os.name != "nt", reason="Windows-confinement surface (see #12704)"
)

MODULE_PATH = Path(__file__).parents[1] / "ci" / "manage_self_hosted_runner.py"
SPEC = importlib.util.spec_from_file_location("manage_self_hosted_runner", MODULE_PATH)
mod = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = mod
SPEC.loader.exec_module(mod)


def profile(root: Path, *, digest: str = "a" * 64) -> mod.Profile:
    return mod.Profile(
        name="test-fast-guards",
        hostname="test-host",
        repository="jsboige/CoursIA",
        runner_name="test-fast-guards",
        account=r".\coursia-runner",
        root=root,
        work=root / "_work",
        log_root=root.parent / "logs",
        labels=("self-hosted", "coursia-ephemeral", "coursia-fast-guards"),
        version="2.336.0",
        archive_url=(
            "https://github.com/actions/runner/releases/download/v2.336.0/"
            "actions-runner-win-x64-2.336.0.zip"
        ),
        archive_sha256=digest,
        sensitive_templates=(
            (r"{repo_root}\.secrets", r"{repo_root}\.secrets\master.env"),
            (r"{user_profile}\.ssh", r"{user_profile}\.ssh"),
            (r"{appdata}\GitHub CLI\hosts.yml", r"{appdata}\GitHub CLI\hosts.yml"),
        ),
    )


def manifest(target: mod.Profile) -> dict:
    return {
        "schema_version": 1,
        "profile": target.name,
        "root": str(target.root),
        "repository": target.repository,
        "version": target.version,
        "sha256": target.archive_sha256,
        "account": target.account,
    }


def write_installed(target: mod.Profile, *, registered: bool = False) -> None:
    target.root.mkdir(parents=True)
    target.config_cmd.write_text("config", encoding="utf-8")
    target.manifest.write_text(json.dumps(manifest(target)), encoding="utf-8")
    if registered:
        (target.root / ".runner").write_text("registered", encoding="utf-8")


def write_registry(path: Path, base_root: str, **overrides) -> None:
    raw = {
        "hostname": "test-host",
        "repository": "jsboige/CoursIA",
        "runner_name": "test-fast-guards",
        "account": r".\coursia-runner",
        "root": base_root,
        "work": base_root + r"\_work",
        "log_root": str(PureWindows(path.parent / "logs")),
        "labels": ["self-hosted", "coursia-ephemeral", "coursia-fast-guards"],
        "runner": {
            "version": "2.336.0",
            "url": (
                "https://github.com/actions/runner/releases/download/v2.336.0/"
                "actions-runner-win-x64-2.336.0.zip"
            ),
            "sha256": "a" * 64,
        },
        "sensitive_paths": [
            {"deny": r"{repo_root}\.secrets", "probe": r"{repo_root}\.secrets\master.env"},
            {"deny": r"{user_profile}\.ssh", "probe": r"{user_profile}\.ssh\jsboige_key"},
            {"deny": r"{appdata}\GitHub CLI\hosts.yml", "probe": r"{appdata}\GitHub CLI\hosts.yml"},
        ],
    }
    raw.update(overrides)
    path.write_text(
        json.dumps({"schema_version": 1, "profiles": {"test": raw}}),
        encoding="utf-8",
    )


def PureWindows(path: Path) -> str:
    return "C:\\" + "\\".join(path.parts[-3:])


def test_run_powershell_delivers_scripts_via_file_not_stdin():
    # Regression (measured on pwsh 7.5, 2026-08-25): `-Command -` fed over
    # stdin silently stops executing at a PowerShell here-string (@'...'@)
    # and still exits 0, turning every apply script embedding one into a
    # no-op reported as success. Scripts must be delivered via -File.
    seen = {}

    def run(argv, **kwargs):
        seen["argv"] = list(argv)
        seen["env"] = kwargs["env"]
        seen["script"] = Path(argv[-1]).read_text(encoding="utf-8")
        assert "input" not in kwargs
        return completed(argv)

    script = "$c = ConvertFrom-Json @'\n{\"a\": 1}\n'@\nWrite-Output $c.a\n"
    mod._run_powershell(script, {"MARKER": "x"}, run=run)
    assert seen["argv"][1:5] == ["-NoLogo", "-NoProfile", "-NonInteractive", "-File"]
    assert seen["script"] == script
    assert seen["env"]["MARKER"] == "x"
    assert not Path(seen["argv"][-1]).exists()


@requires_windows
def test_generated_apply_scripts_embed_here_strings():
    # If these scripts ever stop embedding here-strings the regression test
    # above loses its teeth: anchor the property the delivery bug broke.
    target = profile(Path("unused"))
    for generator in (mod._account_acl_script, mod._teardown_identity_script):
        assert "@'" in generator(target)


def test_manager_has_no_duplicate_top_level_definitions():
    tree = ast.parse(MODULE_PATH.read_text(encoding="utf-8"))
    names = [
        node.name
        for node in tree.body
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    duplicates = {
        name: count
        for name, count in collections.Counter(names).items()
        if count > 1
    }
    assert duplicates == {}


@requires_windows
def test_committed_profiles_are_valid_and_distributed_across_pushers():
    payload = json.loads(mod.PROFILE_PATH.read_text(encoding="utf-8"))
    assert set(payload["profiles"]) == {
        "myia-po-2023-fast-guards",
        "myia-po-2024-fast-guards",
        "myia-po-2025-fast-guards",
        "myia-po-2026-fast-guards",
    }
    for name in payload["profiles"]:
        loaded = mod.load_profile(name)
        assert set(loaded.labels) == mod.REQUIRED_LABELS
        assert loaded.archive_sha256 == "d59123a43003e357b0805b5d0f611d0bd2f65ab67d51bd070dd4e7a0f685c162"


@requires_windows
def test_profile_accepts_runner_own_checkout_under_work(tmp_path, monkeypatch):
    # #13238 : sur le runner lui-meme, le checkout vit sous <root>/_work —
    # l'invariant "root hors du repository" ne doit pas le refuser.
    registry = tmp_path / "profiles.json"
    root = r"C:\CoursIA-Test\runner"
    write_registry(registry, root)
    monkeypatch.setattr(mod, "REPO_ROOT", Path(root) / "_work" / "CoursIA")
    loaded = mod.load_profile("test", registry)
    assert loaded.name == "test"


@requires_windows
def test_profile_refuses_repository_inside_runner_root_outside_work(tmp_path, monkeypatch):
    # Repo sous la racine runner mais HORS de la zone work : toujours refuse.
    registry = tmp_path / "profiles.json"
    root = r"C:\CoursIA-Test\runner"
    write_registry(registry, root)
    monkeypatch.setattr(mod, "REPO_ROOT", Path(root) / "repo")
    with pytest.raises(mod.Refused, match="outside the repository"):
        mod.load_profile("test", registry)


def test_profile_rejects_unknown_keys(tmp_path):
    registry = tmp_path / "profiles.json"
    root = r"C:\CoursIA-Test\runner"
    write_registry(registry, root, unexpected=True)
    with pytest.raises(mod.Broken, match="exactly"):
        mod.load_profile("test", registry)


@pytest.mark.parametrize(
    "overrides, error",
    [
        ({"repository": "attacker/fork"}, "unexpected repository"),
        ({"account": ".\\SYSTEM"}, "privileged"),
        ({"labels": ["self-hosted", "coursia-ephemeral"]}, "exact dedicated"),
        ({"labels": ["self-hosted", "coursia-ephemeral", "coursia-fast-guards", "ubuntu-latest"]}, "exact dedicated"),
        ({"root": "C:\\", "work": r"C:\_work"}, "volume root"),
        ({"root": r"\\server\share", "work": r"\\server\share\_work"}, "absolute local"),
        ({"runner": {"version": "2.336.0", "url": "https://example.com/runner.zip", "sha256": "a" * 64}}, "official"),
        ({"runner": {"version": "2.336.0", "url": "https://github.com/actions/runner/releases/download/v2.336.0/actions-runner-win-x64-2.336.0.zip", "sha256": "missing"}}, "SHA-256"),
    ],
)
def test_profile_validation_fails_closed(tmp_path, overrides, error):
    registry = tmp_path / "profiles.json"
    write_registry(registry, r"C:\CoursIA-Test\runner", **overrides)
    with pytest.raises((mod.Refused, mod.Broken), match=error):
        mod.load_profile("test", registry)


def test_observe_and_plans_are_idempotent(tmp_path):
    target = profile(tmp_path / "runner")
    absent = mod.observe(target)
    assert absent.state == "absent"
    first = mod.render_plan("install", target, absent)
    assert first["would_change"] is True
    assert first["planned_actions"][0] == "create-account"

    write_installed(target)
    installed = mod.observe(target)
    assert installed.state == "installed"
    second = mod.render_plan("install", target, installed)
    assert second["would_change"] is False
    assert second["planned_actions"] == []
    register = mod.render_plan("register", target, installed)
    assert register["activation_boundary"] is True
    assert register["planned_actions"] == ["verify-isolation", "configure-ephemeral-service"]


def test_drifted_root_is_never_overwritten_or_deleted(tmp_path):
    target = profile(tmp_path / "runner")
    target.root.mkdir()
    assert mod.observe(target).state == "drifted"
    for command in ("install", "teardown", "verify"):
        with pytest.raises(mod.Refused, match="drifted|ownership|matching manifest"):
            mod.render_plan(command, target, mod.observe(target))


def test_manifest_provenance_mismatch_is_refused(tmp_path):
    target = profile(tmp_path / "runner")
    target.root.mkdir()
    wrong = manifest(target)
    wrong["root"] = r"C:\somewhere-else"
    target.manifest.write_text(json.dumps(wrong), encoding="utf-8")
    with pytest.raises(mod.Refused, match="does not own"):
        mod.observe(target)


@pytest.mark.parametrize(
    "member",
    ["../escape", "nested/../../escape", "/absolute", r"C:\escape", r"\\server\share", "file.txt:ads"],
)
def test_safe_extract_rejects_path_traversal_and_ntfs_ads(tmp_path, member):
    archive = tmp_path / "bad.zip"
    with zipfile.ZipFile(archive, "w") as bundle:
        bundle.writestr(member, "bad")
    destination = tmp_path / "out"
    destination.mkdir()
    with pytest.raises(mod.Refused, match="unsafe|alternate"):
        mod.safe_extract(archive, destination)
    assert not (tmp_path / "escape").exists()


def test_safe_extract_rejects_symlink(tmp_path):
    archive = tmp_path / "bad.zip"
    info = zipfile.ZipInfo("link")
    info.create_system = 3
    info.external_attr = (0o120777 << 16)
    with zipfile.ZipFile(archive, "w") as bundle:
        bundle.writestr(info, "target")
    destination = tmp_path / "out"
    destination.mkdir()
    with pytest.raises(mod.Refused, match="symlink"):
        mod.safe_extract(archive, destination)


def test_safe_extract_accepts_regular_files(tmp_path):
    archive = tmp_path / "good.zip"
    with zipfile.ZipFile(archive, "w") as bundle:
        bundle.writestr("bin/Runner.Listener.exe", "runner")
        bundle.writestr("config.cmd", "config")
    destination = tmp_path / "out"
    destination.mkdir()
    mod.safe_extract(archive, destination)
    assert (destination / "bin" / "Runner.Listener.exe").read_text() == "runner"


def make_runner_archive() -> bytes:
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, "w") as bundle:
        bundle.writestr("config.cmd", "config")
        bundle.writestr("svc.cmd", "service")
    return stream.getvalue()


def completed(argv=None, **kwargs):
    return subprocess.CompletedProcess(argv or [], 0, "", "")


@requires_windows
def test_install_refuses_bad_checksum_before_extraction(tmp_path, monkeypatch):
    data = make_runner_archive()
    target = profile(tmp_path / "runner", digest="0" * 64)
    monkeypatch.setattr(mod.os, "name", "nt")
    monkeypatch.setenv(mod.ACCOUNT_PASSWORD_ENV, "local-password")
    calls = []

    def download(url, path):
        path.write_bytes(data)

    def run(*args, **kwargs):
        calls.append((args, kwargs))
        return completed(args[0])

    with pytest.raises(mod.Refused, match="SHA-256"):
        mod.apply_install(target, run=run, download=download)
    assert calls == []
    assert not target.root.exists()


@requires_windows
def test_install_extracts_atomically_and_never_logs_password(tmp_path, monkeypatch):
    data = make_runner_archive()
    target = profile(tmp_path / "runner", digest=hashlib.sha256(data).hexdigest())
    password = "local-password-never-log"
    monkeypatch.setattr(mod.os, "name", "nt")
    monkeypatch.setenv(mod.ACCOUNT_PASSWORD_ENV, password)
    calls = []

    def download(url, path):
        path.write_bytes(data)

    def run(*args, **kwargs):
        calls.append((args, kwargs))
        assert password not in " ".join(args[0])
        assert password not in Path(args[0][-1]).read_text(encoding="utf-8")
        assert kwargs["env"][mod.ACCOUNT_PASSWORD_ENV] == password if len(calls) == 1 else True
        return completed(args[0])

    mod.apply_install(target, run=run, download=download)
    assert target.config_cmd.exists()
    assert json.loads(target.manifest.read_text())["sha256"] == target.archive_sha256
    assert len(calls) == 2


def test_register_requires_tokens_without_spawning(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target)
    monkeypatch.delenv(mod.REGISTRATION_TOKEN_ENV, raising=False)
    monkeypatch.delenv(mod.ACCOUNT_PASSWORD_ENV, raising=False)
    with pytest.raises(mod.Refused, match=mod.REGISTRATION_TOKEN_ENV):
        mod.apply_register(target, run=lambda *a, **k: pytest.fail("must not spawn"))


def test_register_uses_input_environment_not_secret_argv(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target)
    token = "registration-token-private"
    password = "service-password-private"
    monkeypatch.setenv(mod.REGISTRATION_TOKEN_ENV, token)
    monkeypatch.setenv(mod.ACCOUNT_PASSWORD_ENV, password)
    monkeypatch.setattr(mod, "apply_verify", lambda profile, run: None)
    captured = {}

    def run(argv, **kwargs):
        captured["argv"] = argv
        captured["env"] = kwargs["env"]
        return completed(argv)

    mod.apply_register(target, run=run)
    rendered = " ".join(captured["argv"])
    assert token not in rendered
    assert password not in rendered
    assert captured["env"]["ACTIONS_RUNNER_INPUT_TOKEN"] == token
    assert captured["env"]["ACTIONS_RUNNER_INPUT_WINDOWSLOGONPASSWORD"] == password
    assert captured["env"]["ACTIONS_RUNNER_INPUT_EPHEMERAL"] == "true"
    assert set(target.labels) == set(captured["env"]["ACTIONS_RUNNER_INPUT_LABELS"].split(","))
    assert "GH_TOKEN" not in captured["env"]
    assert "GITHUB_TOKEN" not in captured["env"]
    assert captured["argv"][1:] == ["--unattended", "--ephemeral", "--replace", "--runasservice"]


def test_register_refuses_before_config_when_isolation_probe_fails(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target)
    monkeypatch.setenv(mod.REGISTRATION_TOKEN_ENV, "registration-token")
    monkeypatch.setenv(mod.ACCOUNT_PASSWORD_ENV, "service-password")
    monkeypatch.setattr(
        mod, "apply_verify",
        lambda profile, run: (_ for _ in ()).throw(mod.Refused("probe failed")),
    )
    with pytest.raises(mod.Refused, match="probe failed"):
        mod.apply_register(target, run=lambda *a, **k: pytest.fail("config must not run"))


def test_register_redacts_secrets_from_failure(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target)
    token = "registration-token-private"
    password = "service-password-private"
    monkeypatch.setenv(mod.REGISTRATION_TOKEN_ENV, token)
    monkeypatch.setenv(mod.ACCOUNT_PASSWORD_ENV, password)
    monkeypatch.setattr(mod, "apply_verify", lambda profile, run: None)

    def fail(argv, **kwargs):
        return subprocess.CompletedProcess(argv, 1, "", f"bad {token} and {password}")

    with pytest.raises(mod.Refused) as caught:
        mod.apply_register(target, run=fail)
    assert token not in str(caught.value)
    assert password not in str(caught.value)
    assert str(caught.value).count("[REDACTED]") == 2


@requires_windows
def test_probe_requires_three_denials_and_one_write(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target)
    monkeypatch.setenv(mod.ACCOUNT_PASSWORD_ENV, "service-password")
    monkeypatch.setenv("USERPROFILE", str(tmp_path / "user"))
    monkeypatch.setenv("APPDATA", str(tmp_path / "appdata"))

    def run(argv, **kwargs):
        (target.root / ".isolation-probe.json").write_text(
            json.dumps({"sensitive": ["ACCESS_DENIED"] * 3, "work_write": "OK"}),
            encoding="utf-8",
        )
        return completed(argv)

    mod.apply_verify(target, run=run)
    assert not (target.root / ".isolation-probe.ps1").exists()
    assert not (target.root / ".isolation-probe.json").exists()


@requires_windows
def test_probe_rejects_missing_or_ambiguous_results(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target)
    monkeypatch.setenv(mod.ACCOUNT_PASSWORD_ENV, "service-password")
    monkeypatch.setenv("USERPROFILE", str(tmp_path / "user"))
    monkeypatch.setenv("APPDATA", str(tmp_path / "appdata"))

    def run(argv, **kwargs):
        (target.root / ".isolation-probe.json").write_text(
            json.dumps({"sensitive": ["ACCESS_DENIED", "OTHER_ERROR", "ACCESS_DENIED"], "work_write": "OK"}),
            encoding="utf-8",
        )
        return completed(argv)

    with pytest.raises(mod.Refused, match="all four"):
        mod.apply_verify(target, run=run)


@requires_windows
def test_acl_scripts_use_sids_and_check_native_exit_codes(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    monkeypatch.setenv("USERPROFILE", str(tmp_path / "user"))
    monkeypatch.setenv("APPDATA", str(tmp_path / "appdata"))
    install_script = mod._account_acl_script(target)
    root_script = mod._runner_root_acl_script(target)
    teardown_script = mod._teardown_identity_script(target)
    assert "S-1-5-32-544" in install_script
    assert "S-1-5-18" in install_script
    assert "(OI)(CI)R" in install_script
    assert "$LASTEXITCODE" in install_script
    assert "$LASTEXITCODE" in root_script
    assert "$LASTEXITCODE" in teardown_script


def test_service_teardown_is_bounded_to_profile_root(tmp_path):
    target = profile(tmp_path / "runner")
    script = mod._teardown_service_script(target)
    assert json.dumps(str(target.root))[1:-1] in script
    assert "StartsWith($root +" in script
    assert "Get-CimInstance Win32_Service" in script
    assert "sc.exe delete" in script
    assert "Runner service still exists" in script


def test_teardown_absent_is_an_idempotent_empty_plan(tmp_path):
    target = profile(tmp_path / "runner")
    plan = mod.render_plan("teardown", target, mod.observe(target))
    assert plan["would_change"] is False
    assert plan["planned_actions"] == []


def test_teardown_requires_removal_token_for_registered_runner(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target, registered=True)
    monkeypatch.delenv(mod.REMOVAL_TOKEN_ENV, raising=False)
    with pytest.raises(mod.Refused, match=mod.REMOVAL_TOKEN_ENV):
        mod.apply_teardown(target, run=lambda *a, **k: pytest.fail("must not spawn"))
    assert target.root.exists()


@requires_windows
def test_teardown_unregisters_without_secret_argv_and_archives_logs(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target, registered=True)
    (target.root / "_diag").mkdir()
    (target.root / "_diag" / "runner.log").write_text("clean diagnostics", encoding="utf-8")
    token = "removal-token-private"
    monkeypatch.setenv(mod.REMOVAL_TOKEN_ENV, token)
    calls = []

    def run(argv, **kwargs):
        script = Path(argv[-1]).read_text(encoding="utf-8") if argv[0] == "pwsh" else ""
        calls.append((argv, kwargs, script))
        assert token not in " ".join(argv)
        assert token not in calls[-1][2]
        return completed(argv)

    mod.apply_teardown(target, run=run)
    assert not target.root.exists()
    assert (target.log_root / f"{target.runner_name}-diag" / "runner.log").exists()
    assert calls[0][0][1:] == ["remove", "--unattended"]
    assert calls[0][1]["env"]["ACTIONS_RUNNER_INPUT_TOKEN"] == token
    assert calls[1][0][0] == "pwsh"
    assert "Get-CimInstance Win32_Service" in calls[1][2]
    assert "Remove-LocalUser" in calls[2][2]


def test_teardown_refuses_if_archived_log_contains_supplied_secret(tmp_path, monkeypatch):
    target = profile(tmp_path / "runner")
    write_installed(target, registered=True)
    (target.root / "_diag").mkdir()
    token = "removal-token-private"
    (target.root / "_diag" / "runner.log").write_text(f"leak {token}", encoding="utf-8")
    monkeypatch.setenv(mod.REMOVAL_TOKEN_ENV, token)
    with pytest.raises(mod.Refused, match="contains a supplied secret"):
        mod.apply_teardown(target, run=lambda argv, **kwargs: completed(argv))
    assert target.root.exists()


def test_apply_noop_does_not_call_mutator(tmp_path, capsys, monkeypatch):
    target_root = tmp_path / "runner"
    target = profile(target_root)
    write_installed(target)
    monkeypatch.setattr(mod, "load_profile", lambda name, path: target)
    monkeypatch.setattr(mod, "apply", lambda *args: pytest.fail("no-op plan must not mutate"))
    assert mod.main(["install", "--profile", "test", "--apply"]) == mod.EXIT_OK
    result = json.loads(capsys.readouterr().out)
    assert result["mode"] == "apply"
    assert result["applied"] is False


@requires_windows
def test_dry_run_cli_is_deterministic_and_does_not_mutate(tmp_path, capsys):
    registry = tmp_path / "profiles.json"
    root = PureWindows(tmp_path / "runner")
    write_registry(registry, root)
    args = ["install", "--profile", "test", "--profiles", str(registry)]
    assert mod.main(args) == mod.EXIT_OK
    first = capsys.readouterr().out
    assert mod.main(args) == mod.EXIT_OK
    second = capsys.readouterr().out
    assert first == second
    assert json.loads(first)["mode"] == "dry-run"
    assert not Path(root).exists()
