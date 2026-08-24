#!/usr/bin/env python3
"""Prepare and manage isolated ephemeral GitHub Actions runners on Windows.

The default mode is observational: it renders a deterministic JSON plan and
never writes, downloads, registers, or removes anything. Mutations require the
explicit ``--apply`` flag. In particular, ``register --apply`` is the separate
activation button and must not be used while preparing the infrastructure.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import urllib.request
import zipfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath, PureWindowsPath
from typing import Any, Callable, Mapping

EXIT_OK = 0
EXIT_REFUSED = 1
EXIT_BROKEN = 2
PROFILE_PATH = Path(__file__).with_name("self_hosted_runner_profiles.json")
REPO_ROOT = Path(__file__).resolve().parents[2]
REQUIRED_LABELS = {
    "self-hosted",
    "coursia-ephemeral",
    "coursia-fast-guards",
}
HOSTED_LABELS = {
    "ubuntu-latest", "ubuntu-24.04", "ubuntu-22.04", "ubuntu-20.04",
    "ubuntu-slim", "windows-latest", "windows-2025", "windows-2022",
    "windows-2019", "macos-latest", "macos-26", "macos-15", "macos-14",
    "macos-13",
}
PRIVILEGED_ACCOUNTS = {
    "system", "localsystem", "networkservice", "localservice",
    "administrator", "administrators",
}
REGISTRATION_TOKEN_ENV = "GITHUB_RUNNER_REGISTRATION_TOKEN"
REMOVAL_TOKEN_ENV = "GITHUB_RUNNER_REMOVAL_TOKEN"
ACCOUNT_PASSWORD_ENV = "COURSIA_RUNNER_ACCOUNT_PASSWORD"
MANIFEST_NAME = ".coursia-runner-state.json"
RUNNER_PRIVATE_FILES = (".runner", ".credentials", ".credentials_rsaparams")


class Refused(RuntimeError):
    """A safety precondition is not met."""


class Broken(RuntimeError):
    """The profile, tool, or observed state cannot be interpreted safely."""


@dataclass(frozen=True)
class Profile:
    name: str
    hostname: str
    repository: str
    runner_name: str
    account: str
    root: Path
    work: Path
    log_root: Path
    labels: tuple[str, ...]
    version: str
    archive_url: str
    archive_sha256: str
    sensitive_templates: tuple[tuple[str, str], ...]

    @property
    def manifest(self) -> Path:
        return self.root / MANIFEST_NAME

    @property
    def config_cmd(self) -> Path:
        return self.root / "config.cmd"



@dataclass(frozen=True)
class Observation:
    state: str
    root_exists: bool
    manifest: dict[str, Any] | None
    private_files: tuple[str, ...]
    archive_hash_matches: bool | None


CommandRunner = Callable[..., subprocess.CompletedProcess[str]]
Downloader = Callable[[str, Path], None]


def _canonical_absolute(value: str, field: str) -> Path:
    win = PureWindowsPath(value)
    if not win.is_absolute() or value.startswith(("\\\\", "//")):
        raise Broken(f"{field} must be an absolute local path")
    if len(win.parts) <= 1:
        raise Broken(f"{field} cannot be a volume root")
    return Path(value)


def _is_within(child: Path, parent: Path) -> bool:
    try:
        child.resolve(strict=False).relative_to(parent.resolve(strict=False))
        return True
    except ValueError:
        return False


def _validate_profile(name: str, raw: Any) -> Profile:
    required = {
        "hostname", "repository", "runner_name", "account", "root", "work",
        "log_root", "labels", "runner", "sensitive_paths",
    }
    if not isinstance(raw, dict) or set(raw) != required:
        raise Broken(f"profile {name!r} must contain exactly {sorted(required)}")
    runner = raw["runner"]
    if not isinstance(runner, dict) or set(runner) != {"version", "url", "sha256"}:
        raise Broken(f"profile {name!r} has an invalid runner pin")
    labels = raw["labels"]
    if not isinstance(labels, list) or not all(isinstance(x, str) and x for x in labels):
        raise Broken(f"profile {name!r} labels must be non-empty strings")
    if set(labels) != REQUIRED_LABELS or len(labels) != len(REQUIRED_LABELS):
        raise Refused(f"profile {name!r} must use the exact dedicated label set")
    if set(labels) & HOSTED_LABELS:
        raise Refused(f"profile {name!r} may not impersonate a GitHub-hosted label")
    repository = raw["repository"]
    if repository != "jsboige/CoursIA":
        raise Refused(f"profile {name!r} targets an unexpected repository")
    url = runner["url"]
    if not isinstance(url, str) or not re.fullmatch(
        r"https://github\.com/actions/runner/releases/download/v[0-9.]+/"
        r"actions-runner-win-x64-[0-9.]+\.zip", url,
    ):
        raise Refused(f"profile {name!r} must pin an official Windows x64 archive")
    version = runner["version"]
    if not isinstance(version, str) or f"-{version}.zip" not in url:
        raise Broken(f"profile {name!r} runner version and URL disagree")
    digest = runner["sha256"]
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise Broken(f"profile {name!r} has no valid SHA-256 pin")
    account = raw["account"]
    if not isinstance(account, str) or not re.fullmatch(r"(?:\.\\)?[A-Za-z][A-Za-z0-9_.-]{2,40}", account):
        raise Broken(f"profile {name!r} has an invalid local account")
    leaf = account.rsplit("\\", 1)[-1].lower()
    if leaf in PRIVILEGED_ACCOUNTS:
        raise Refused(f"profile {name!r} uses a privileged account")
    root = _canonical_absolute(raw["root"], "root")
    work = _canonical_absolute(raw["work"], "work")
    log_root = _canonical_absolute(raw["log_root"], "log_root")
    if not _is_within(work, root):
        raise Refused(f"profile {name!r} work directory must be below its runner root")
    if _is_within(root, REPO_ROOT) or _is_within(REPO_ROOT, root):
        raise Refused(f"profile {name!r} runner root must be outside the repository")
    sensitive = raw["sensitive_paths"]
    if (
        not isinstance(sensitive, list) or len(sensitive) != 3
        or not all(isinstance(item, dict) and set(item) == {"deny", "probe"} for item in sensitive)
        or not all(isinstance(item["deny"], str) and isinstance(item["probe"], str) for item in sensitive)
    ):
        raise Broken(f"profile {name!r} must define exactly three deny/probe pairs")
    hostname = raw["hostname"]
    if not isinstance(hostname, str) or not hostname:
        raise Broken(f"profile {name!r} has no hostname")
    runner_name = raw["runner_name"]
    if not isinstance(runner_name, str) or not re.fullmatch(r"[A-Za-z0-9_.-]+", runner_name):
        raise Broken(f"profile {name!r} has an invalid runner name")
    return Profile(
        name=name, hostname=hostname, repository=repository,
        runner_name=runner_name, account=account, root=root, work=work,
        log_root=log_root, labels=tuple(labels), version=version,
        archive_url=url, archive_sha256=digest,
        sensitive_templates=tuple((item["deny"], item["probe"]) for item in sensitive),
    )


def load_profile(name: str, path: Path = PROFILE_PATH) -> Profile:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise Broken(f"cannot read profile registry: {exc}") from exc
    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise Broken("unsupported profile registry schema")
    profiles = payload.get("profiles")
    if not isinstance(profiles, dict) or name not in profiles:
        raise Broken(f"unknown profile: {name}")
    return _validate_profile(name, profiles[name])


def _read_manifest(profile: Profile) -> dict[str, Any] | None:
    if not profile.manifest.exists():
        return None
    try:
        value = json.loads(profile.manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise Broken(f"runner manifest is unreadable: {exc}") from exc
    if not isinstance(value, dict):
        raise Broken("runner manifest root must be an object")
    expected = {
        "schema_version": 1, "profile": profile.name,
        "root": str(profile.root), "repository": profile.repository,
        "version": profile.version, "sha256": profile.archive_sha256,
        "account": profile.account,
    }
    if any(value.get(key) != expected_value for key, expected_value in expected.items()):
        raise Refused("runner manifest does not own the configured resources")
    return value


def observe(profile: Profile) -> Observation:
    root_exists = profile.root.exists()
    manifest = _read_manifest(profile) if root_exists else None
    private = tuple(name for name in RUNNER_PRIVATE_FILES if (profile.root / name).exists())
    config_exists = profile.config_cmd.exists()
    if not root_exists:
        state = "absent"
    elif manifest is None:
        state = "drifted"
    elif not config_exists:
        state = "drifted"
    elif private:
        state = "registered"
    else:
        state = "installed"
    return Observation(
        state=state, root_exists=root_exists, manifest=manifest,
        private_files=private, archive_hash_matches=(
            manifest.get("sha256") == profile.archive_sha256 if manifest else None
        ),
    )


def _actions(command: str, observation: Observation) -> list[str]:
    if command == "install":
        if observation.state == "absent":
            return ["create-account", "download-and-verify", "extract-atomically", "apply-acls", "write-manifest"]
        if observation.state in {"installed", "registered"}:
            return []
        raise Refused("install refuses a drifted runner root")
    if command == "register":
        if observation.state == "installed":
            return ["verify-isolation", "configure-ephemeral-service"]
        if observation.state == "registered":
            return []
        raise Refused("register requires a conforming installed runner")
    if command == "verify":
        if observation.state == "absent":
            raise Refused("verify requires an installed runner")
        if observation.state == "drifted":
            raise Refused("verify refuses a drifted runner root")
        return ["probe-sensitive-access"]
    if command == "teardown":
        if observation.state == "absent":
            return []
        if observation.state == "drifted":
            raise Refused("teardown refuses resources without a matching manifest")
        return ["stop-and-remove-service", "unregister", "archive-and-scan-logs", "remove-owned-resources"]
    raise Broken(f"unknown command: {command}")


def render_plan(command: str, profile: Profile, observation: Observation) -> dict[str, Any]:
    actions = _actions(command, observation)
    checks = ["profile-valid", "paths-bounded", "labels-exact"]
    if observation.manifest:
        checks.extend(["manifest-owned", "version-pinned"])
    if command in {"register", "verify"}:
        checks.extend(["dedicated-account", "sensitive-acls"])
    return {
        "ok": True,
        "mode": "dry-run",
        "command": command,
        "profile": profile.name,
        "target_host": profile.hostname,
        "repository": profile.repository,
        "labels": list(profile.labels),
        "observed_state": observation.state,
        "checks": checks,
        "planned_actions": actions,
        "would_change": bool(actions),
        "activation_boundary": command == "register",
    }


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _safe_zip_member(info: zipfile.ZipInfo) -> PurePosixPath:
    raw = info.filename.replace("\\", "/")
    if not raw or raw.startswith(("/", "//")) or re.match(r"^[A-Za-z]:", raw):
        raise Refused(f"unsafe archive member: {info.filename!r}")
    member = PurePosixPath(raw)
    if any(part in {"", ".", ".."} for part in member.parts):
        raise Refused(f"unsafe archive member: {info.filename!r}")
    if any(":" in part for part in member.parts):
        raise Refused(f"NTFS alternate data stream in archive: {info.filename!r}")
    mode = info.external_attr >> 16
    if stat.S_ISLNK(mode):
        raise Refused(f"archive symlink is not allowed: {info.filename!r}")
    return member


def safe_extract(archive: Path, destination: Path) -> None:
    with zipfile.ZipFile(archive) as bundle:
        members = [(info, _safe_zip_member(info)) for info in bundle.infolist()]
        for info, member in members:
            target = destination.joinpath(*member.parts)
            if not _is_within(target, destination):
                raise Refused(f"archive member escapes staging: {info.filename!r}")
        for info, member in members:
            target = destination.joinpath(*member.parts)
            if info.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with bundle.open(info) as source, target.open("wb") as output:
                    shutil.copyfileobj(source, output)


def _minimal_env(extra: Mapping[str, str] | None = None) -> dict[str, str]:
    allowed = ("SystemRoot", "WINDIR", "COMSPEC", "PATH", "PATHEXT", "TEMP", "TMP")
    env = {key: os.environ[key] for key in allowed if key in os.environ}
    if extra:
        env.update(extra)
    return env


def _run_powershell(script: str, env: Mapping[str, str], run: CommandRunner) -> None:
    completed = run(
        ["pwsh", "-NoLogo", "-NoProfile", "-NonInteractive", "-Command", "-"],
        input=script, capture_output=True, text=True, encoding="utf-8",
        env=_minimal_env(env), check=False,
    )
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout or "PowerShell failed").strip()
        raise Refused(detail.replace(os.environ.get(ACCOUNT_PASSWORD_ENV, "\0"), "[REDACTED]"))


def _account_acl_script(profile: Profile) -> str:
    sensitive = _sensitive_paths(profile)
    values = json.dumps({
        "account": profile.account, "root": str(profile.root),
        "log_root": str(profile.log_root), "sensitive": [str(deny) for deny, _ in sensitive],
    })
    return f"""
$ErrorActionPreference = 'Stop'
$c = ConvertFrom-Json @'
{values}
'@
function Invoke-Icacls([string[]]$Arguments) {{
  & icacls @Arguments | Out-Null
  if ($LASTEXITCODE -ne 0) {{ throw "icacls failed with exit $LASTEXITCODE" }}
}}
$password = $env:{ACCOUNT_PASSWORD_ENV}
if (-not $password) {{ throw 'Dedicated account password is missing.' }}
$name = ($c.account -split '\\\\')[-1]
$existing = Get-LocalUser -Name $name -ErrorAction SilentlyContinue
if ($existing) {{ throw 'Dedicated runner account already exists and is not owned by this profile.' }}
$changed = @()
try {{
  $secure = ConvertTo-SecureString $password -AsPlainText -Force
  $user = New-LocalUser -Name $name -Password $secure -AccountNeverExpires -PasswordNeverExpires
  $adminGroup = Get-LocalGroup -SID 'S-1-5-32-544'
  $isAdmin = Get-LocalGroupMember -Group $adminGroup | Where-Object {{ $_.SID -eq $user.SID }}
  if ($isAdmin) {{ throw 'Dedicated runner account is an administrator.' }}
  $userSid = "*$($user.SID.Value)"
  New-Item -ItemType Directory -Force -Path $c.log_root | Out-Null
  Invoke-Icacls -Arguments @($c.log_root, '/inheritance:r', '/grant:r', '*S-1-5-32-544:(OI)(CI)F', '*S-1-5-18:(OI)(CI)F')
  foreach ($path in $c.sensitive) {{
    if (-not (Test-Path -LiteralPath $path)) {{ throw "Sensitive deny path missing: $path" }}
    $item = Get-Item -LiteralPath $path -Force
    $rights = if ($item.PSIsContainer) {{ '(OI)(CI)R' }} else {{ '(R)' }}
    Invoke-Icacls -Arguments @($path, '/deny', "${{userSid}}:${{rights}}")
    $changed += $path
  }}
}} catch {{
  if ($user) {{
    $userSid = "*$($user.SID.Value)"
    foreach ($path in $changed) {{
      & icacls $path /remove:d $userSid | Out-Null
    }}
  }}
  Remove-LocalUser -Name $name -ErrorAction SilentlyContinue
  throw
}}
"""


def _sensitive_paths(profile: Profile) -> tuple[tuple[Path, Path], ...]:
    values = {
        "repo_root": str(REPO_ROOT),
        "user_profile": os.environ.get("USERPROFILE", ""),
        "appdata": os.environ.get("APPDATA", ""),
    }
    if not values["user_profile"] or not values["appdata"]:
        raise Refused("USERPROFILE and APPDATA are required to resolve isolation probes")
    result = []
    for deny_template, probe_template in profile.sensitive_templates:
        try:
            deny = Path(deny_template.format(**values))
            probe = Path(probe_template.format(**values))
        except KeyError as exc:
            raise Broken(f"unknown sensitive path template key: {exc}") from exc
        if not _is_within(probe, deny) and probe != deny:
            raise Refused("sensitive probe must be the denied path or one of its children")
        result.append((deny, probe))
    return tuple(result)


def _runner_root_acl_script(profile: Profile) -> str:
    values = json.dumps({"account": profile.account, "root": str(profile.root)})
    return f"""
$ErrorActionPreference = 'Stop'
$c = ConvertFrom-Json @'
{values}
'@
$name = ($c.account -split '\\\\')[-1]
$user = Get-LocalUser -Name $name -ErrorAction Stop
& icacls $c.root /inheritance:r /grant:r "*$($user.SID.Value):(OI)(CI)F" '*S-1-5-32-544:(OI)(CI)F' '*S-1-5-18:(OI)(CI)F' | Out-Null
if ($LASTEXITCODE -ne 0) {{ throw "icacls failed with exit $LASTEXITCODE" }}
"""


def _teardown_identity_script(profile: Profile) -> str:
    sensitive = _sensitive_paths(profile)
    values = json.dumps({
        "account": profile.account, "sensitive": [str(deny) for deny, _ in sensitive],
    })
    return f"""
$ErrorActionPreference = 'Stop'
$c = ConvertFrom-Json @'
{values}
'@
$name = ($c.account -split '\\\\')[-1]
$user = Get-LocalUser -Name $name -ErrorAction SilentlyContinue
if ($user) {{
  $userSid = "*$($user.SID.Value)"
  foreach ($path in $c.sensitive) {{
    if (Test-Path -LiteralPath $path) {{
      & icacls $path /remove:d $userSid | Out-Null
      if ($LASTEXITCODE -ne 0) {{ throw "icacls failed with exit $LASTEXITCODE" }}
    }}
  }}
  Remove-LocalUser -Name $name
}}
"""


def _teardown_service_script(profile: Profile) -> str:
    values = json.dumps({"root": str(profile.root)})
    return f"""
$ErrorActionPreference = 'Stop'
$c = ConvertFrom-Json @'
{values}
'@
$root = [IO.Path]::GetFullPath($c.root).TrimEnd('\\')
$owned = @(Get-CimInstance Win32_Service | Where-Object {{
  $path = ([string]$_.PathName).Trim().Trim('"')
  $path.StartsWith($root + '\\', [StringComparison]::OrdinalIgnoreCase)
}})
if ($owned.Count -gt 1) {{ throw 'Multiple services point inside the runner root.' }}
foreach ($service in $owned) {{
  if ($service.State -ne 'Stopped') {{ Stop-Service -Name $service.Name -Force -ErrorAction Stop }}
  & sc.exe delete $service.Name | Out-Null
  if ($LASTEXITCODE -ne 0) {{ throw "sc.exe delete failed with exit $LASTEXITCODE" }}
}}
$remaining = @(Get-CimInstance Win32_Service | Where-Object {{
  $path = ([string]$_.PathName).Trim().Trim('"')
  $path.StartsWith($root + '\\', [StringComparison]::OrdinalIgnoreCase)
}})
if ($remaining.Count -ne 0) {{ throw 'Runner service still exists after deletion.' }}
"""


def _teardown_service_script(profile: Profile) -> str:
    values = json.dumps({"root": str(profile.root)})
    return f"""
$ErrorActionPreference = 'Stop'
$c = ConvertFrom-Json @'
{values}
'@
$root = [IO.Path]::GetFullPath($c.root).TrimEnd('\\')
$owned = @(Get-CimInstance Win32_Service | Where-Object {{
  $path = ([string]$_.PathName).Trim().Trim('"')
  $path.StartsWith($root + '\\', [StringComparison]::OrdinalIgnoreCase)
}})
if ($owned.Count -gt 1) {{ throw 'Multiple services point inside the runner root.' }}
foreach ($service in $owned) {{
  if ($service.State -ne 'Stopped') {{ Stop-Service -Name $service.Name -Force -ErrorAction Stop }}
  & sc.exe delete $service.Name | Out-Null
  if ($LASTEXITCODE -ne 0) {{ throw "sc.exe delete failed with exit $LASTEXITCODE" }}
}}
$remaining = @(Get-CimInstance Win32_Service | Where-Object {{
  $path = ([string]$_.PathName).Trim().Trim('"')
  $path.StartsWith($root + '\\', [StringComparison]::OrdinalIgnoreCase)
}})
if ($remaining.Count -ne 0) {{ throw 'Runner service still exists after deletion.' }}
"""


def _default_download(url: str, target: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "CoursIA-runner-manager/1"})
    with urllib.request.urlopen(request, timeout=120) as response, target.open("wb") as output:
        shutil.copyfileobj(response, output)


def apply_install(profile: Profile, run: CommandRunner = subprocess.run, download: Downloader = _default_download) -> None:
    if os.name != "nt":
        raise Refused("install --apply is supported only on Windows")
    password = os.environ.get(ACCOUNT_PASSWORD_ENV)
    if not password:
        raise Refused(f"{ACCOUNT_PASSWORD_ENV} is required for install --apply")
    if profile.root.exists():
        raise Refused("install target already exists; observe it before applying")
    profile.root.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{profile.root.name}-", dir=profile.root.parent))
    archive = staging.with_suffix(".zip")
    extract_dir = staging / "payload"
    identity_created = False
    try:
        download(profile.archive_url, archive)
        actual = _sha256(archive)
        if actual != profile.archive_sha256:
            raise Refused("downloaded runner archive SHA-256 does not match the committed pin")
        extract_dir.mkdir()
        safe_extract(archive, extract_dir)
        if not (extract_dir / "config.cmd").is_file():
            raise Broken("runner archive has no config.cmd")
        manifest = {
            "schema_version": 1, "profile": profile.name,
            "root": str(profile.root), "repository": profile.repository,
            "version": profile.version, "sha256": profile.archive_sha256,
            "account": profile.account,
        }
        (extract_dir / MANIFEST_NAME).write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8",
        )
        _run_powershell(_account_acl_script(profile), {ACCOUNT_PASSWORD_ENV: password}, run)
        identity_created = True
        extract_dir.replace(profile.root)
        _run_powershell(_runner_root_acl_script(profile), {}, run)
    except Exception:
        if identity_created:
            try:
                _run_powershell(_teardown_identity_script(profile), {}, run)
            finally:
                shutil.rmtree(profile.root, ignore_errors=True)
        raise
    finally:
        archive.unlink(missing_ok=True)
        if staging.exists():
            shutil.rmtree(staging, ignore_errors=True)


def _runner_env(profile: Profile, token: str, password: str | None = None) -> dict[str, str]:
    values = {
        "ACTIONS_RUNNER_INPUT_TOKEN": token,
        "ACTIONS_RUNNER_INPUT_URL": f"https://github.com/{profile.repository}",
        "ACTIONS_RUNNER_INPUT_NAME": profile.runner_name,
        "ACTIONS_RUNNER_INPUT_LABELS": ",".join(profile.labels),
        "ACTIONS_RUNNER_INPUT_WORK": str(profile.work),
        "ACTIONS_RUNNER_INPUT_EPHEMERAL": "true",
        "ACTIONS_RUNNER_INPUT_REPLACE": "true",
        "ACTIONS_RUNNER_INPUT_RUNASSERVICE": "true",
        "ACTIONS_RUNNER_INPUT_WINDOWSLOGONACCOUNT": profile.account,
    }
    if password is not None:
        values["ACTIONS_RUNNER_INPUT_WINDOWSLOGONPASSWORD"] = password
    return _minimal_env(values)


def apply_register(profile: Profile, run: CommandRunner = subprocess.run) -> None:
    token = os.environ.get(REGISTRATION_TOKEN_ENV)
    password = os.environ.get(ACCOUNT_PASSWORD_ENV)
    if not token:
        raise Refused(f"{REGISTRATION_TOKEN_ENV} is required for register --apply")
    if not password:
        raise Refused(f"{ACCOUNT_PASSWORD_ENV} is required for the dedicated Windows service")
    if any((profile.root / name).exists() for name in RUNNER_PRIVATE_FILES):
        raise Refused("runner is already registered")
    apply_verify(profile, run=run)
    completed = run(
        [str(profile.config_cmd), "--unattended", "--ephemeral", "--replace", "--runasservice"],
        cwd=profile.root, capture_output=True, text=True, encoding="utf-8",
        env=_runner_env(profile, token, password), check=False,
    )
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout or "runner configuration failed")
        for secret in (token, password):
            detail = detail.replace(secret, "[REDACTED]")
        raise Refused(detail.strip())


def _probe_script(profile: Profile) -> str:
    probes = [str(probe) for _, probe in _sensitive_paths(profile)]
    payload = json.dumps({"sensitive": probes, "work": str(profile.work)})
    return f"""
$ErrorActionPreference = 'Stop'
$c = ConvertFrom-Json @'
{payload}
'@
$results = @()
foreach ($path in $c.sensitive) {{
  try {{ Get-Content -LiteralPath $path -TotalCount 1 -ErrorAction Stop | Out-Null; $status = 'READABLE' }}
  catch [System.UnauthorizedAccessException] {{ $status = 'ACCESS_DENIED' }}
  catch {{ $status = 'OTHER_ERROR' }}
  $results += $status
}}
try {{
  New-Item -ItemType Directory -Force -Path $c.work | Out-Null
  $probe = Join-Path $c.work '.isolation-probe'
  [IO.File]::WriteAllText($probe, 'probe')
  Remove-Item -LiteralPath $probe -Force
  $write = 'OK'
}} catch {{ $write = 'FAILED' }}
[pscustomobject]@{{ sensitive = $results; work_write = $write }} | ConvertTo-Json -Compress
"""


def apply_verify(profile: Profile, run: CommandRunner = subprocess.run) -> None:
    password = os.environ.get(ACCOUNT_PASSWORD_ENV)
    if not password:
        raise Refused(f"{ACCOUNT_PASSWORD_ENV} is required for verify --apply")
    probe_path = profile.root / ".isolation-probe.ps1"
    result_path = profile.root / ".isolation-probe.json"
    probe_path.write_text(_probe_script(profile), encoding="utf-8")
    account = profile.account.replace("'", "''")
    probe_literal = str(probe_path).replace("'", "''")
    result_literal = str(result_path).replace("'", "''")
    script = f"""
$ErrorActionPreference = 'Stop'
$secure = ConvertTo-SecureString $env:{ACCOUNT_PASSWORD_ENV} -AsPlainText -Force
$cred = [pscredential]::new('{account}', $secure)
$p = Start-Process pwsh -Credential $cred -ArgumentList @('-NoProfile','-NonInteractive','-File','{probe_literal}') -RedirectStandardOutput '{result_literal}' -PassThru -Wait
if ($p.ExitCode -ne 0) {{ throw "Isolation probe failed with exit $($p.ExitCode)" }}
"""
    try:
        _run_powershell(script, {ACCOUNT_PASSWORD_ENV: password}, run)
        try:
            result = json.loads(result_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise Refused(f"isolation probe produced no valid result: {exc}") from exc
        if result.get("sensitive") != ["ACCESS_DENIED"] * 3 or result.get("work_write") != "OK":
            raise Refused("dedicated account isolation probe did not satisfy all four checks")
    finally:
        probe_path.unlink(missing_ok=True)
        result_path.unlink(missing_ok=True)


def _scan_logs_for_secrets(root: Path, secrets: tuple[str, ...]) -> None:
    for path in root.rglob("*") if root.exists() else ():
        if not path.is_file():
            continue
        try:
            data = path.read_bytes()
        except OSError as exc:
            raise Refused(f"cannot inspect archived runner log: {path.name}: {exc}") from exc
        for secret in secrets:
            if secret and secret.encode("utf-8") in data:
                raise Refused(f"archived runner log contains a supplied secret: {path.name}")


def apply_teardown(profile: Profile, run: CommandRunner = subprocess.run) -> None:
    manifest = _read_manifest(profile)
    if manifest is None:
        raise Refused("teardown refuses a runner root without its ownership manifest")
    token = os.environ.get(REMOVAL_TOKEN_ENV)
    password = os.environ.get(ACCOUNT_PASSWORD_ENV, "")
    if any((profile.root / name).exists() for name in RUNNER_PRIVATE_FILES) and not token:
        raise Refused(f"{REMOVAL_TOKEN_ENV} is required to unregister this runner")
    diag = profile.root / "_diag"
    destination = profile.log_root / f"{profile.runner_name}-diag"
    if diag.exists() and destination.exists():
        raise Refused("teardown log destination already exists; preserve it before retrying")
    diag = profile.root / "_diag"
    destination = profile.log_root / f"{profile.runner_name}-diag"
    if diag.exists() and destination.exists():
        raise Refused("teardown log destination already exists; preserve it before retrying")
    registered = any((profile.root / name).exists() for name in RUNNER_PRIVATE_FILES)
    if token and profile.config_cmd.exists() and registered:
        completed = run(
            [str(profile.config_cmd), "remove", "--unattended"], cwd=profile.root,
            capture_output=True, text=True, encoding="utf-8",
            env=_minimal_env({"ACTIONS_RUNNER_INPUT_TOKEN": token}), check=False,
        )
        if completed.returncode != 0:
            detail = (completed.stderr or completed.stdout or "runner removal failed").replace(token, "[REDACTED]")
            raise Refused(detail.strip())
    _run_powershell(_teardown_service_script(profile), {}, run)
    if diag.exists():
        profile.log_root.mkdir(parents=True, exist_ok=True)
        shutil.copytree(diag, destination)
        _scan_logs_for_secrets(destination, (token or "", password))
    _run_powershell(_teardown_identity_script(profile), {}, run)
    shutil.rmtree(profile.root)


def apply(command: str, profile: Profile) -> None:
    if command == "install":
        apply_install(profile)
    elif command == "register":
        apply_register(profile)
    elif command == "verify":
        apply_verify(profile)
    elif command == "teardown":
        apply_teardown(profile)
    else:
        raise Broken(f"unknown command: {command}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", choices=("install", "register", "verify", "teardown"))
    parser.add_argument("--profile", required=True)
    parser.add_argument("--profiles", type=Path, default=PROFILE_PATH, help=argparse.SUPPRESS)
    parser.add_argument("--apply", action="store_true", help="perform the planned mutations")
    args = parser.parse_args(argv)
    try:
        profile = load_profile(args.profile, args.profiles)
        observation = observe(profile)
        plan = render_plan(args.command, profile, observation)
        if args.apply:
            plan["mode"] = "apply"
            if plan["planned_actions"]:
                apply(args.command, profile)
                plan["applied"] = True
            else:
                plan["applied"] = False
        print(json.dumps(plan, indent=2, sort_keys=True, ensure_ascii=False))
        return EXIT_OK
    except Refused as exc:
        print(json.dumps({"ok": False, "error": str(exc), "kind": "refused"}, ensure_ascii=False), file=sys.stderr)
        return EXIT_REFUSED
    except Broken as exc:
        print(json.dumps({"ok": False, "error": str(exc), "kind": "broken"}, ensure_ascii=False), file=sys.stderr)
        return EXIT_BROKEN


if __name__ == "__main__":
    raise SystemExit(main())
