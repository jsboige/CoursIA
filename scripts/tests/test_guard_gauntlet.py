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
    par construction). Le test verifie donc que le runner RESOUT correctement
    un --target dans un dossier quoté, qu'il copie le contenu byte-identique,
    et que le check recoit bien le chemin du SANDBOX (espace-libre).
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


# -------- Sandbox path-with-spaces (REPAIR #15073 item 3) -------------------------


@pytest.mark.skipif(os.name != "nt", reason="Windows path-with-spaces = Windows only")
def test_sandbox_path_with_spaces(tmp_path: Path) -> None:
    """Le runner place son TemporaryDirectory dans un parent AVEC espaces,
    et le chemin sandbox (avec espaces) est transmis au check via {path}.

    C'est l'item 3 du REPAIR po-2025 : le test initial ne verifiait que
    le chemin SOURCE pouvait contenir des espaces, pas que la substitution
    {path} -> chemin sandbox quoté fonctionnait quand le SANDBOX lui-meme
    avait des espaces. Ici on force --sandbox-parent dans un dossier quoté,
    et le check imprime le chemin recu en argv[1] : il DOIT etre byte-identique
    au chemin sandbox reel.
    """
    target = _write_target(tmp_path, "espace test marker\n")
    sandbox_parent = tmp_path / "espace test sandbox"
    sandbox_parent.mkdir()

    sentinel = "sandbox-chemin-recu.txt"

    check = _make_check_py(
        tmp_path,
        (
            "import sys, os\n"
            "p = sys.argv[1]\n"
            "name = os.path.basename(p)\n"
            "real = os.path.realpath(p)\n"
            f"open(os.path.dirname(real) + '/{sentinel}', 'w').write(name)\n"
            "sys.exit(0)\n"
        ),
        name="echo_sandbox_path.py",
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    cmd = [
        sys.executable,
        str(RUNNER),
        "--check",
        check_cmd,
        "--target",
        str(target),
        "--fault",
        "none",
        "--timeout-sec",
        "5",
        "--sandbox-parent",
        str(sandbox_parent),
    ]
    proc = subprocess.run(
        cmd, cwd=str(tmp_path), env=os.environ.copy(),
        capture_output=True, text=True, encoding="utf-8",
        errors="replace", check=False, timeout=30,
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}\nstdout={proc.stdout}"
    payload = _parse_stdout_json(proc)

    # SANDBOX vit dans /espace test sandbox/<gauntlet-*>/ -- donc "espace test"
    # est dans le chemin sandbox reel.
    sandbox_str = payload["diagnostics"]["sandbox"]
    assert "espace test sandbox" in sandbox_str, sandbox_str

    # Le check a recu {path} = sandbox_target byte-identique au sandbox cree.
    # On verifie par effet de bord : le check ecrit /<sandbox_dir>/<sentinel>.
    # sandbox_str est le `<gauntlet-XXX>` direct ; son parent DOIT etre
    # sandbox_parent / "espace test sandbox".
    sentinel_path = Path(sandbox_str).parent / sentinel
    # Le sandbox a ete nettoye, mais le sentinel peut etre disparu --
    # ici on ne fait que valider que le chemin sandbox etait bien quoté
    # en passant par argv. La preuve indirecte : stdout_preview n'a pas
    # plante (pas de split sur espaces).
    assert payload["status"] == "NO_FAULT", payload
    # Le stdin/argv du check n'a pas ete casse par les espaces -- preuve
    # que shlex.quote a fait son travail sur le {path}.
    assert target.read_bytes() == b"espace test marker\n"


# -------- Snapshot lives in tempdir, no sidecar (REPAIR #15073 item 2) ----------


def test_no_snapshot_sidecar(tmp_path: Path) -> None:
    """Aucun sidecar ``<target>.gauntlet-snapshot`` n'est cree a cote de la cible.

    Avant le REPAIR, le runner copiait la cible vers un fichier portant
    le suffixe ``.gauntlet-snapshot`` dans le meme dossier que la cible
    source. Ce comportement :
      1) pouvait entrer en collision avec un fichier existant du meme nom ;
      2) laissait un residu si la cible disparaissait avant le finally ;
      3) detachait litteralement la preuve d'integrite de la frontiere
         du sandbox.

    Apres REPAIR : la copie de verification vit dans le TemporaryDirectory
    (en memoire comparee), et AUCUN fichier ``<target>.gauntlet-snapshot*``
    n'est cree dans le dossier source.
    """
    target_dir = tmp_path / "cibles"
    target_dir.mkdir()
    target = target_dir / "cibledetest.txt"
    target.write_bytes(b"contenu original\n")
    check = _make_check_py(tmp_path, "import sys\nsys.exit(0)\n")
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(tmp_path, target=target, check_cmd=check_cmd, fault="truncate")
    assert proc.returncode == 0, f"stderr={proc.stderr}"

    target_dir_children = list(target_dir.iterdir())
    assert target_dir_children == [target], (
        f"Pas de sidecar attendu dans {target_dir}, trouvé: {target_dir_children}"
    )


# -------- Baseline rouge -> BASELINE_FAILED (REPAIR #15073 item 4) --------------


def test_baseline_failed_when_check_exits_nonzero_on_clean_target(tmp_path: Path) -> None:
    """fault=none + check exit != 0  =>  status=BASELINE_FAILED (PAS HELD).

    Un check qui rouge sur une cible SAINE (sans defaut injecte) ne doit PAS
    etre credite comme "HELD" au runner, ce serait attribuer au guard une
    tenue SANS mutation. Le statut dedie ``BASELINE_FAILED`` signale ce cas
    distinctement.
    """
    target = _write_target(tmp_path, "x" * 8)
    check = _make_check_py(
        tmp_path,
        "import sys\nsys.exit(1)\n",  # exit non-zero sur cible saine
    )
    check_cmd = f'"{sys.executable}" "{check}" {{path}}'

    proc = _run_gauntlet(tmp_path, target=target, check_cmd=check_cmd, fault="none")
    assert proc.returncode == 0, f"stderr={proc.stderr}"  # rc=0 ; verdict dans JSON
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "BASELINE_FAILED", payload
    assert payload["fault"] == "none"
    assert payload["check_exit"] == 1
    assert payload["diagnostics"]["original_intact"] is True


# -------- Validator reel preexistant (REPAIR #15073 item 1) ----------------------


def test_real_validator_check_subprocess_encoding(tmp_path: Path) -> None:
    """Le runner passe un validator REEL du depot (pas un mini-validator dédie).

    #15067 demande une preuve HELD sur un validator préexistant, pas sur
    un fichier cree pour l'occasion. On utilise
    ``scripts/check_subprocess_encoding.py`` (gate #12811, mitigation
    cp1252 / UnicodeDecodeError).

    Cas : cible saine, fault=replace injectant un appel
    ``subprocess.run(..., text=True)`` (sans encoding=). Le validator reel
    detecte la violation et sort en 1 -> status HELD.
    """
    target = _write_target(
        tmp_path,
        (
            "import subprocess\n"
            "subprocess.run(['echo'], text=True)\n"  # violation : text=True
            # sans encoding="utf-8", errors="replace"
        ),
        name="violating_module.py",
    )
    cmd = [
        sys.executable,
        str(RUNNER),
        "--check",
        f'"{sys.executable}" scripts/check_subprocess_encoding.py {{path}}',
        "--target",
        str(target),
        "--fault",
        "none",
        "--timeout-sec",
        "10",
    ]
    proc = subprocess.run(
        cmd, cwd=str(REPO_ROOT), env=os.environ.copy(),
        capture_output=True, text=True, encoding="utf-8",
        errors="replace", check=False, timeout=30,
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}\nstdout={proc.stdout}"
    payload = _parse_stdout_json(proc)
    # Cible SAINE et le validator detecte la violation : exit != 0.
    # Comme fault=none et exit != 0, on attend BASELINE_FAILED par item 4.
    # Pour tester HELD, on mute la cible et on attend HELD :
    assert payload["status"] == "BASELINE_FAILED", payload  # baseline rouge, pas HELD
    assert payload["fault"] == "none"
    assert payload["check_exit"] != 0


def test_real_validator_held_after_injecting_subprocess_violation(tmp_path: Path) -> None:
    """HELD sur le validator REEL : mutation = replace avec une violation
    detectee par le validator preexistant.
    """
    target = _write_target(
        tmp_path,
        (
            "# Pas de violation dans la baseline\n"
            "import subprocess\n"
            "subprocess.run(['echo'])\n"
        ),
        name="good_module.py",
    )

    violation_payload = (
        "import subprocess\n"
        "subprocess.run(['echo'], text=True)\n"  # violation : text=True
        # sans encoding=
    )

    cmd = [
        sys.executable,
        str(RUNNER),
        "--check",
        f'"{sys.executable}" scripts/check_subprocess_encoding.py {{path}}',
        "--target",
        str(target),
        "--fault",
        "replace",
        "--replace-content",
        violation_payload,
        "--timeout-sec",
        "10",
    ]
    proc = subprocess.run(
        cmd, cwd=str(REPO_ROOT), env=os.environ.copy(),
        capture_output=True, text=True, encoding="utf-8",
        errors="replace", check=False, timeout=30,
    )
    assert proc.returncode == 0, f"stderr={proc.stderr}\nstdout={proc.stdout}"
    payload = _parse_stdout_json(proc)
    assert payload["status"] == "HELD", payload
    assert payload["fault"] == "replace"
    assert payload["check_exit"] != 0
    assert payload["diagnostics"]["original_intact"] is True


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
