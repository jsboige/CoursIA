"""Positive controls for the ``#10143`` class-based FP suppression.

The allowlist regexes in ``.gitleaks.toml`` (lines ~108-128) suppress two
classes of *pedagogical* literals that are NOT secrets:

1. **OpenRouter placeholder** -- ``sk-or-v1-[A-Z][A-Z_]+`` matches the FR
   teaching form ``sk-or-v1-VOTRE_CLE`` (uppercase-only suffix can never be a
   real key). Real OpenRouter keys are ``sk-or-v1-`` + 64 lowercase hex chars.
2. **Truncated JWT example** -- ``eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9\\.\\.\\.``
   matches the bare header followed by ``...`` (the pedagogical truncated form
   in Roo-Code docs). A real JWT is ``header.payload.signature``.

A gate that suppresses a placeholder must NOT disarm the underlying detector --
otherwise the suppression is the ``#9888`` silent-noop failure mode (the
scanner stopped catching real leaks). These two tests are the **positive
controls** that prove the allowlist regexes leave the detector armed: a real
key placed next to the placeholder in the SAME file is STILL flagged.

Unlike ``test_gitleaks_qwen_rule.py`` (which mirrors the custom rule into a
hermetic config to test the rule in isolation), these tests run against the
**production** ``.gitleaks.toml`` directly -- the suppression under test lives
in the production allowlist, so testing a mirror would test nothing about the
shipped config.

The tests invoke the real gitleaks binary (no Python re-implementation of the
regex). The binary resolves in the same order as the sibling test module
(``GITLEAKS_BIN`` env, ``gitleaks`` on PATH, local scratchpad path). If absent,
the test is skipped -- which is exactly the gap ``secret-scan.yml`` wiring
closes (the CI job sets ``GITLEAKS_BIN`` so the skip turns off in CI).

Measurement method (``#10143`` residual, scope point 3): when scanning locally,
ALWAYS scan a ``git archive HEAD`` export, never the repo root -- a root scan
sweeps ``.claude/worktrees/`` + ``.lake/packages`` (44x the tracked content)
and re-surfaces rotated secrets in stale copies the CI never sees.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

# Resolve the gitleaks binary in the same order as test_gitleaks_qwen_rule.py.
GITLEAKS_CANDIDATES = [
    os.environ.get("GITLEAKS_BIN"),
    shutil.which("gitleaks"),
    r"C:\Users\jsboi\AppData\Local\Temp\gitleaks-bin\gitleaks.exe",
]


def _gitleaks_binary() -> str | None:
    for candidate in GITLEAKS_CANDIDATES:
        if candidate and Path(candidate).exists():
            return candidate
    return None


GITLEAKS = _gitleaks_binary()
requires_gitleaks = pytest.mark.skipif(
    GITLEAKS is None,
    reason="gitleaks binary not found on PATH or scratchpad; CI is the authoritative gate",
)

# Production config at the repo root (parents: tests -> secrets -> scripts -> root).
PRODUCTION_CONFIG = Path(__file__).resolve().parents[3] / ".gitleaks.toml"

# A real OpenRouter key is sk-or-v1- + 64 lowercase hex chars (verified format,
# synthetic value -- never a live credential).
REAL_OPENROUTER_HEX = "sk-or-v1-" + "0123456789abcdef" * 4  # 64 hex chars
OPENROUTER_PLACEHOLDER = "sk-or-v1-VOTRE_CLE_ICI"

# A real JWT is header.payload.signature (three base64 segments joined by dots).
# Synthetic value (jsonwebtoken.io sample), never a live credential.
REAL_JWT = (
    "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9."
    "eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkphY2tzb24ifQ."
    "SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c"
)
TRUNCATED_JWT_EXAMPLE = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."

# #10595: a real-shaped synthetic token for the custom qwen-api-token rule.
# Deliberately NOT among the four fixture values stopworded in .gitleaks.toml
# (xK9mZ3vL7n..., aB3xZ9kL7m..., 2%=tVJ6@..., NOT_A_REAL_TOKEN...), so it
# proves any non-listed value in the test directory still rougir.
QWEN_REAL_SHAPED = "xR7$kL2#mN9@pQ4!vT6^wU8*eH1%cJ3"


def _run_gitleaks(source: Path, config: Path) -> list[dict]:
    """Run gitleaks on ``source`` dir with ``config`` and return findings as dicts."""
    assert GITLEAKS is not None
    report = source / "report.json"
    subprocess.run(
        [
            GITLEAKS,
            "detect",
            "--no-git",
            "--source", str(source),
            "--config", str(config),
            "--no-banner",
            "--exit-code", "0",
            "--report-format", "json",
            "--report-path", str(report),
        ],
        capture_output=True,
        text=True,
        timeout=60,
    )
    if not report.exists():
        return []
    with report.open(encoding="utf-8") as f:
        return json.load(f)


def _secrets_containing(findings: list[dict], needle: str) -> list[str]:
    """Return the secret strings of findings whose Secret field contains ``needle``."""
    return [f.get("Secret", "") for f in findings if needle in f.get("Secret", "")]


# --------------------------------------------------------------------------- #
# Positive controls: the allowlist suppresses the placeholder but the REAL
# secret placed beside it in the same file is STILL flagged. If either test
# fails, the allowlist regex has disarmed the detector (#9888 failure mode).
# --------------------------------------------------------------------------- #
@requires_gitleaks
def test_openrouter_real_hex_key_stays_flagged_next_to_placeholder(tmp_path):
    """#10143 positive control: real ``sk-or-v1-<hex>`` stays FLAGGED while the
    uppercase placeholder is SUPPRESSED by the allowlist."""
    (tmp_path / "leak.txt").write_text(
        f"OPENROUTER_API_KEY={REAL_OPENROUTER_HEX}\n"
        f"OPENROUTER_PLACEHOLDER={OPENROUTER_PLACEHOLDER}\n",
        encoding="utf-8",
    )
    findings = _run_gitleaks(tmp_path, PRODUCTION_CONFIG)
    # The real hex key MUST be flagged (generic-api-key detector armed).
    assert _secrets_containing(findings, REAL_OPENROUTER_HEX), (
        "real sk-or-v1-<hex> key was NOT flagged -- the allowlist regex "
        "sk-or-v1-[A-Z][A-Z_]+ has disarmed the OpenRouter detector (#9888)"
    )
    # The uppercase placeholder MUST be suppressed (allowlist active).
    assert not _secrets_containing(findings, OPENROUTER_PLACEHOLDER), (
        "the uppercase placeholder sk-or-v1-VOTRE_CLE_ICI was flagged -- the "
        "allowlist regex sk-or-v1-[A-Z][A-Z_]+ is not suppressing the class"
    )


@requires_gitleaks
def test_real_jwt_stays_flagged_next_to_truncated_example(tmp_path):
    """#10143 positive control: a real full JWT ``header.payload.signature``
    stays FLAGGED while the truncated teaching example is SUPPRESSED."""
    (tmp_path / "leak.txt").write_text(
        f'token_real = "{REAL_JWT}"\n'
        f'token_example = "{TRUNCATED_JWT_EXAMPLE}"\n',
        encoding="utf-8",
    )
    findings = _run_gitleaks(tmp_path, PRODUCTION_CONFIG)
    # The real full JWT MUST be flagged (jwt detector armed).
    assert _secrets_containing(findings, REAL_JWT), (
        "real full JWT (header.payload.signature) was NOT flagged -- the "
        "allowlist regex eyJ...XVCJ9\\.{3} has disarmed the jwt detector (#9888)"
    )
    # The truncated teaching example MUST be suppressed (allowlist active).
    assert not _secrets_containing(findings, "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."), (
        "the truncated JWT teaching example was flagged -- the allowlist regex "
        "eyJ...XVCJ9\\.{3} is not suppressing the truncated class"
    )


@requires_gitleaks
def test_real_secret_under_former_allowlisted_test_path_stays_flagged(tmp_path):
    """#10595 regression: a real secret in a file matching the former
    ``scripts/secrets/tests/test_gitleaks_.*\\.py$`` path entry is FLAGGED.

    Before #10595, that ``[allowlist].paths`` entry made gitleaks skip the
    whole directory BEFORE [[rules]] evaluation -- a content bypass (measured
    8.24.3: ``scanned ~86 bytes`` for two 86-byte files). The path entries are
    removed and the synthetic qwen fixtures are suppressed by stopwords, so
    this test was RED on main and must be GREEN here: the directory is scanned
    again and a real-shaped secret there still rougir.
    """
    target = tmp_path / "scripts" / "secrets" / "tests"
    target.mkdir(parents=True)
    (target / "test_gitleaks_probe.py").write_text(
        f"OPENROUTER_API_KEY = \"{REAL_OPENROUTER_HEX}\"\n"
        f"QWEN_API_TOKEN = \"{QWEN_REAL_SHAPED}\"\n",
        encoding="utf-8",
    )
    findings = _run_gitleaks(tmp_path, PRODUCTION_CONFIG)
    # The real-shaped OpenRouter key MUST be flagged (generic-api-key armed).
    assert _secrets_containing(findings, REAL_OPENROUTER_HEX), (
        "a real sk-or-v1-<hex> key under scripts/secrets/tests/test_gitleaks_*.py "
        "was NOT flagged -- the positive-control directory is not being scanned "
        "or something suppresses it (#10595)"
    )
    # The non-stopworded qwen-shaped token MUST be flagged (custom rule armed).
    assert _secrets_containing(findings, QWEN_REAL_SHAPED), (
        "a qwen-shaped token not listed in the stopwords under "
        "scripts/secrets/tests/test_gitleaks_*.py was NOT flagged -- a "
        "suppression wider than the four listed fixtures is in place (#10595)"
    )
