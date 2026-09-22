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
    et le check ecrit le sys.argv[1] recu dans un fichier SURVIVANT (hors
    TemporaryDirectory) -- on le relit apres cleanup du sandbox et on le
    compare byte-pour-byte au chemin sandbox attendu. Si la substitution
    {path} avait ete cassee par les espaces (argv tronque), la valeur
    ecrite differerait du chemin reel et le test echouerait. La preuve est
    explicite (sentinel_path.is_file + assertion de la valeur), pas
    indirecte (REPAIR proof-assertions po-2025 addendum 5573579453 item 2).
    """
    target = _write_target(tmp_path, "espace test marker\n")
    sandbox_parent = tmp_path / "espace test sandbox"
    sandbox_parent.mkdir()

    # Fichier survivant : le runner nettoie son sandbox via TemporaryDirectory
    # a la sortie du `with`, mais tmp_path / sentinel_path est hors du sandbox.
    # On y stocke sys.argv[1] exact tel que recu par le check, puis on le
    # relit depuis le test (pas dans le sandbox). Si le runner sandbox avait
    # un chemin different de ce que {path} a transmis, l'assertion echoue.
    sentinel_path = tmp_path / "received_argv_path.txt"

    check = _make_check_py(
        tmp_path,
        (
            "import sys\n"
            f"open(r'{sentinel_path}', 'w', encoding='utf-8').write(sys.argv[1])\n"
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

    # La matrice de verdict est NO_FAULT (cible saine, check exit 0).
    assert payload["status"] == "NO_FAULT", payload

    # PREUVE DISCRIMINANTE : le check a bien recu {path} = sandbox_target.
    # Le sentinel a ete ecrit hors du TemporaryDirectory (dans tmp_path), donc
    # il survit au cleanup. On relit exactement le sys.argv[1] transmis et on
    # le compare au chemin sandbox attendu. Si shlex.quote avait coupe sur
    # les espaces, sys.argv[1] aurait ete different et l'assertion aurait
    # rate. Si le sentinel n'existe pas (chemin mort, runner ignore, ...),
    # l'assertion explicite le dit -- pas de "preuve indirecte" muette
    # (REPAIR proof-assertions po-2025 addendum 5573579453 item 2).
    assert sentinel_path.is_file(), (
        f"sentinel survivant absent : {sentinel_path}. Le check n'a pas pu "
        f"ecrire sys.argv[1] ; la preuve de substitution {path} est invalide."
    )
    received = sentinel_path.read_text(encoding="utf-8")
    expected_sandbox_target = Path(sandbox_str) / target.name
    assert received == str(expected_sandbox_target), (
        f"sys.argv[1] recu par le check != chemin sandbox attendu.\n"
        f"  recu     = {received!r}\n"
        f"  attendu  = {str(expected_sandbox_target)!r}\n"
        f"shlex.quote a-t-il malencontreusement coupe sur les espaces ?"
    )

    # La cible source n'est pas touchee par le run.
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


# Validator REEL préexistant : chemin ABSOLU obligatoire.
# Le runner execute le check avec `cwd=str(sandbox_dir)`, donc un chemin
# relatif "scripts/check_subprocess_encoding.py" résoudrait contre le
# sandbox (où le script n'existe pas) et Python sortirait non-zéro pour
# une raison qui n'a rien a voir avec le validator -- faux positif HELD /
# BASELINE_FAILED. La commande du smoke (guard_gauntlet_smoke.py) utilise
# deja le chemin absolu ; on l'aligne dans les tests pour eviter la
# derive (REPAIR proof-assertions po-2025 addendum 5573579453 item 1).
REAL_VALIDATOR = REPO_ROOT / "scripts" / "check_subprocess_encoding.py"
# Signature stdout du validator : "f.py:line: text=True without encoding= :: ..."
# Si la sortie du runner contient cette signature, on sait que le validator
# REEL a effectivement examine la cible et detecte la violation -- pas
# seulement un crash Python sur chemin introuvable.
VALIDATOR_SIGNATURE = "text=True without encoding="


def test_real_validator_check_subprocess_encoding(tmp_path: Path) -> None:
    """Le runner passe un validator REEL du depot (pas un mini-validator dédie).

    #15067 demande une preuve HELD sur un validator préexistant, pas sur
    un fichier cree pour l'occasion. On utilise
    ``scripts/check_subprocess_encoding.py`` (gate #12811, mitigation
    cp1252 / UnicodeDecodeError).

    Cas : cible SAINE qui contient deja une violation ``subprocess.run(...,
    text=True)`` sans encoding. Le validator reel detecte la violation et
    sort en 1 -> comme fault=none et exit != 0, status = BASELINE_FAILED
    (REPAIR item 4 : pas un HELD, c'est la baseline qui rouge).

    La preuve discriminante : stdout_preview contient la signature verbatim
    du validator. Sans cette assertion, n'importe quel crash Python sur
    chemin introuvable declencherait artificiellement le verdict.
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
        f'"{sys.executable}" "{REAL_VALIDATOR}" {{path}}',
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
    assert payload["status"] == "BASELINE_FAILED", payload  # baseline rouge, pas HELD
    assert payload["fault"] == "none"
    assert payload["check_exit"] != 0
    # PREUVE DISCRIMINANTE : le validator reel a tourne, pas un crash Python.
    # Si la commande passait par un chemin relatif que Python ne trouvait
    # pas, stdout_preview ne contiendrait PAS cette signature -- mais
    # check_exit serait != 0 aussi, d'ou le faux-positif ferme par item 1
    # du REPAIR proof-assertions.
    assert VALIDATOR_SIGNATURE in payload["diagnostics"]["stdout_preview"], (
        f"stdout_preview manque la signature du validator reel "
        f"({VALIDATOR_SIGNATURE!r}); la detection vient peut-etre d'un crash "
        f"Python sur chemin introuvable.\n"
        f"stdout_preview={payload['diagnostics']['stdout_preview']!r}"
    )


def test_real_validator_held_after_injecting_subprocess_violation(tmp_path: Path) -> None:
    """HELD sur le validator REEL : mutation = replace injectant une violation
    detectee par le validator preexistant.

    On part d'une cible SAINE (pas de violation) ; on injecte via replace un
    contenu qui CONTIENT une violation ; le validator reel detecte et sort
    en 1 ; comme fault=replace et exit != 0, status = HELD.
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
        f'"{sys.executable}" "{REAL_VALIDATOR}" {{path}}',
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
    # Meme preuve discriminante que ci-dessus : la sortie du validator reel
    # doit etre visible dans stdout_preview, pas seulement un crash Python.
    assert VALIDATOR_SIGNATURE in payload["diagnostics"]["stdout_preview"], (
        f"stdout_preview manque la signature du validator reel ; "
        f"le verdict HELD vient peut-etre d'un crash Python.\n"
        f"stdout_preview={payload['diagnostics']['stdout_preview']!r}"
    )


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
