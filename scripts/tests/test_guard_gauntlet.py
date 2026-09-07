"""Tests pour scripts/ci/guard_gauntlet.py (pilote #15067).

Couvre le contrat HELD/ESCAPED verbatim du dispatch :

  - NO_FAULT (exit 0, status NO_FAULT quand check exit 0)
  - HELD     (exit 0, status HELD quand check exit != 0 sur fault injecte)
  - ESCAPED  (exit 0, status ESCAPED quand check exit == 0 sur fault injecte)
  - USAGE    (exit 2 : invocation mal formee)
  - TIMEOUT  (exit 3 : check ne repond pas dans la fenetre)
  - determinisme (meme fault/meme cible => meme verdict, hors timeout flaky)
  - original intact (le fichier source n'est pas touche par le runner)
  - Windows path-with-spaces (le token {path} accepte les espaces)

Le runner substitue {path} AVANT tokenisation shlex par un argument **deja
quote** (shlex.quote). On construit donc des commandes ou {path} est un
**token final** (sys.argv[1] du check), pas un litteral concatene au script
-c : sinon le path finit dans le script, pas dans argv.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
RUNNER = REPO_ROOT / "scripts" / "ci" / "guard_gauntlet.py"


def _write_target(tmp_path: Path, body: str, name: str = "tiny.txt") -> Path:
    """Ecrit un fichier binaire pour eviter la traduction CRLF de write_text."""
    p = tmp_path / name
    p.write_bytes(body.encode("utf-8"))
    return p


def _make_check_py(tmp_path: Path, body: str, name: str = "check.py") -> Path:
    """Ecrit un check-script autonome (chemin en argv[1]) qu'on appelle comme
    ``python <check.py> {path}``."""
    p = tmp_path / name
    p.write_text(textwrap.dedent(body), encoding="utf-8")
    return p


def _run_gauntlet(
    tmp_path: Path,
    *,
    target: Path,
    check_cmd: str,
    fault: str = "none",
    replace_content: str = "",
    timeout_sec: float = 5.0,
    bitflip_byte: int = 0,
) -> subprocess.CompletedProcess:
    cmd = [
        sys.executable,
        str(RUNNER),
        "--check",
        check_cmd,
        "--target",
        str(target),
        "--fault",
        fault,
        "--timeout-sec",
        str(timeout_sec),
        "--bitflip-byte",
        str(bitflip_byte),
    ]
    if replace_content:
        cmd += ["--replace-content", replace_content]
    return subprocess.run(
        cmd,
        cwd=str(tmp_path),
        env=os.environ.copy(),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
        timeout=60,
    )


def _parse_stdout_json(proc: subprocess.CompletedProcess) -> dict:
    lines = [ln for ln in proc.stdout.splitlines() if ln.strip().startswith("{")]
    assert lines, f"Aucune ligne JSON sur stdout:\n--- STDOUT ---\n{proc.stdout}\n--- STDERR ---\n{proc.stderr}"
    return json.loads(lines[-1])


# -------- NO_FAULT ---------------------------------------------------------------


def test_no_fault_passes_when_check_exits_zero(tmp_path: Path) -> None:
    """fault=none + check qui reussit => status=NO_FAULT, rc=0, original_intact=True."""
    target = _write_target(tmp_path, "x" * 8)
    check = _make_check_py(tmp_path, "import sys\nsys.exit(0)\n")
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(tmp_path, target=target, check_cmd=check_cmd, fault="none")
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "NO_FAULT"
    assert payload["fault"] == "none"
    assert payload["check_exit"] == 0
    assert payload["diagnostics"]["original_intact"] is True
    assert target.read_bytes() == b"x" * 8


# -------- HELD -------------------------------------------------------------------


def test_held_when_check_fails_after_truncate(tmp_path: Path) -> None:
    """fault=truncate sur fichier court + check qui exige len >= 100 => HELD.

    Le truncate reduit le fichier de 25 % (max(1, len // 4)). Avec une cible
    courte (10 bytes) -> nouveau len = 7, check sort en 1 => HELD.
    """
    target = _write_target(tmp_path, "X" * 10)
    check = _make_check_py(
        tmp_path,
        "import sys\n"
        "b = open(sys.argv[1], 'rb').read()\n"
        "assert len(b) >= 100, f'truncated to {len(b)}'\n"
        "sys.exit(0)\n",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(tmp_path, target=target, check_cmd=check_cmd, fault="truncate")
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "HELD", payload
    assert payload["fault"] == "truncate"
    assert payload["diagnostics"]["original_intact"] is True


def test_held_when_check_fails_after_bitflip(tmp_path: Path) -> None:
    """fault=bitflip sur un byte constant + check qui valide le contenu => HELD."""
    target = _write_target(tmp_path, "A" * 16)
    check = _make_check_py(
        tmp_path,
        "import sys\n"
        "b = open(sys.argv[1], 'rb').read()\n"
        "sys.exit(0 if b == b'A' * 16 else 1)\n",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(
        tmp_path, target=target, check_cmd=check_cmd, fault="bitflip", bitflip_byte=5
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "HELD", payload
    assert payload["diagnostics"]["original_intact"] is True


def test_held_when_check_fails_after_replace(tmp_path: Path) -> None:
    """fault=replace + check qui exige une signature 'BEGIN' en tete => HELD."""
    target = _write_target(tmp_path, "BEGIN\n" + "x" * 64)
    check = _make_check_py(
        tmp_path,
        "import sys\n"
        "b = open(sys.argv[1], 'rb').read()\n"
        "sys.exit(0 if b.startswith(b'BEGIN') else 1)\n",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(
        tmp_path,
        target=target,
        check_cmd=check_cmd,
        fault="replace",
        replace_content="GARBAGE\n",
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "HELD", payload


# -------- ESCAPED ----------------------------------------------------------------


def test_escaped_when_check_ignores_fault(tmp_path: Path) -> None:
    """fault=truncate + check qui n'inspecte pas la longueur => ESCAPED.

    Le check est volontairement 'en dehors de la portee' : il valide juste
    que le fichier est non-vide. Le truncate reduit de 25 % mais laisse
    un fichier non-vide, donc le check reussit : ESCAPED.
    """
    target = _write_target(tmp_path, "x" * 100)
    check = _make_check_py(
        tmp_path,
        "import sys\n"
        "b = open(sys.argv[1], 'rb').read()\n"
        "sys.exit(0 if b else 1)\n",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(tmp_path, target=target, check_cmd=check_cmd, fault="truncate")
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "ESCAPED", payload
    assert payload["diagnostics"]["original_intact"] is True


# -------- USAGE ------------------------------------------------------------------


def test_usage_when_no_path_token(tmp_path: Path) -> None:
    """Commande sans {path} => rc=2, USAGE."""
    target = _write_target(tmp_path, "x")
    check = _make_check_py(tmp_path, "import sys\nsys.exit(0)\n")
    proc = _run_gauntlet(
        tmp_path,
        target=target,
        check_cmd=f'"{sys.executable}" "{check}"',  # pas de {path}
        fault="none",
    )
    assert proc.returncode == 2, f"stderr={proc.stderr}"
    assert "USAGE" in proc.stderr or "token" in proc.stderr


def test_usage_when_target_missing(tmp_path: Path) -> None:
    """--target qui n'existe pas => rc=2, USAGE."""
    target = tmp_path / "ghost.txt"  # jamais cree
    check = _make_check_py(tmp_path, "import sys\nsys.exit(0)\n")
    proc = _run_gauntlet(
        tmp_path,
        target=target,
        check_cmd=f'"{sys.executable}" "{check}" {{path}}',
        fault="none",
    )
    assert proc.returncode == 2, f"stderr={proc.stderr}"
    assert "USAGE" in proc.stderr or "fichier" in proc.stderr


def test_usage_when_argparse_fails(tmp_path: Path) -> None:
    """Option inconnue => rc=2 (USAGE ajoute par le runner)."""
    target = _write_target(tmp_path, "x")
    proc = subprocess.run(
        [
            sys.executable,
            str(RUNNER),
            "--check",
            "x {path}",
            "--target",
            str(target),
            "--no-such-flag",
        ],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
        timeout=10,
    )
    assert proc.returncode == 2
    assert "USAGE" in proc.stderr


# -------- TIMEOUT ----------------------------------------------------------------


def test_timeout_when_check_hangs(tmp_path: Path) -> None:
    """Check qui dort plus que le timeout => rc=3, status=TIMEOUT, original intact."""
    target = _write_target(tmp_path, "x")
    check = _make_check_py(
        tmp_path,
        "import sys, time\n"
        "time.sleep(30)\n"
        "sys.exit(0)\n",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(
        tmp_path, target=target, check_cmd=check_cmd, fault="none", timeout_sec=1.0
    )
    assert proc.returncode == 3, f"stderr={proc.stderr}"
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "TIMEOUT"
    assert payload["check_exit"] is None
    assert payload["diagnostics"]["original_intact"] is True


# -------- Determinisme -----------------------------------------------------------


def test_determinism_same_target_same_fault(tmp_path: Path) -> None:
    """Trois runs successifs sur la meme cible + meme fault => meme verdict."""
    target = _write_target(tmp_path, "x" * 32)
    check = _make_check_py(tmp_path, "import sys\nsys.exit(0)\n")
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    statuses = []
    for _ in range(3):
        proc = _run_gauntlet(tmp_path, target=target, check_cmd=check_cmd, fault="none")
        assert proc.returncode == 0
        statuses.append(_parse_stdout_json(proc)["status"])
    assert statuses == ["NO_FAULT", "NO_FAULT", "NO_FAULT"]


# -------- Original intact --------------------------------------------------------


def test_original_intact_under_all_faults(tmp_path: Path) -> None:
    """Aucun fault (truncate/bitflip/replace) ne doit modifier la cible source.

    Le test lit la cible APRES chaque run et verifie byte-identique au snapshot
    avant le run.
    """
    target = _write_target(tmp_path, "BEGIN\n" + "x" * 64 + "\nEND\n")
    original = target.read_bytes()
    check = _make_check_py(
        tmp_path,
        "import sys\n"
        "open(sys.argv[1], 'rb')\n"  # check volontairement faible : pas de validation
        "sys.exit(0)\n",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    for fault in ("truncate", "bitflip", "replace"):
        if fault == "bitflip":
            proc = _run_gauntlet(
                tmp_path,
                target=target,
                check_cmd=check_cmd,
                fault=fault,
                bitflip_byte=10,
            )
        elif fault == "replace":
            proc = _run_gauntlet(
                tmp_path,
                target=target,
                check_cmd=check_cmd,
                fault=fault,
                replace_content="GARBAGE",
            )
        else:
            proc = _run_gauntlet(
                tmp_path, target=target, check_cmd=check_cmd, fault=fault
            )
        assert proc.returncode == 0, (fault, proc.stderr)
        payload = _parse_stdout_json(proc)
        assert payload["diagnostics"]["original_intact"] is True, (fault, payload)
        assert target.read_bytes() == original, fault


# -------- Windows path-with-spaces ----------------------------------------------


@pytest.mark.skipif(os.name != "nt", reason="Windows path-with-spaces = Windows only")
def test_windows_path_with_spaces_in_target(tmp_path: Path) -> None:
    """Le runner accepte une cible source dans un dossier 'avec espaces'.

    Le runner copie la cible dans son propre sandbox (qui n'a pas d'espaces
    par construction — mkdtemp(prefix='gauntlet-')). Le test verifie donc
    que le runner RESOUT correctement un --target dans un dossier quoté,
    qu'il copie le contenu byte-identique, et que le check recoit bien le
    chemin du SANDBOX (espace-libre).
    """
    nested = tmp_path / "espace test"
    nested.mkdir()
    target = nested / "fichier avec espaces.txt"
    payload_in = b"hello world\n"
    target.write_bytes(payload_in)

    check = _make_check_py(
        tmp_path,
        "import sys\n"
        "b = open(sys.argv[1], 'rb').read()\n"
        "sys.stdout.buffer.write(b)\n"
        "sys.exit(0)\n",
        name="checker.py",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(tmp_path, target=target, check_cmd=check_cmd, fault="none")
    assert proc.returncode == 0, f"stderr={proc.stderr}\nstdout={proc.stdout}"
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "NO_FAULT", payload
    # Le contenu est byte-identique entre source et copie sandbox.
    assert payload_in in payload["diagnostics"]["stdout_preview"].encode("utf-8")
    # Original intact (meme si la source a des espaces dans son chemin).
    assert payload["diagnostics"]["original_intact"] is True
    assert target.read_bytes() == payload_in


# -------- Sanity : env minimal ---------------------------------------------------


def test_sandbox_env_vars_present(tmp_path: Path) -> None:
    """Le runner exporte GAUNTLET_SANDBOX et GAUNTLET_TARGET dans env du check."""
    target = _write_target(tmp_path, "x")
    check = _make_check_py(
        tmp_path,
        "import os, sys\n"
        "print(os.environ.get('GAUNTLET_SANDBOX', '<none>'))\n"
        "print(os.environ.get('GAUNTLET_TARGET', '<none>'))\n"
        "sys.exit(0)\n",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(tmp_path, target=target, check_cmd=check_cmd, fault="none")
    assert proc.returncode == 0, f"stderr={proc.stderr}"
    payload = _parse_stdout_json(proc)
    out = payload["diagnostics"]["stdout_preview"]
    assert "<none>" not in out, out
    assert "gauntlet-" in out, out
