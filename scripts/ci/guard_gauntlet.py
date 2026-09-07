#!/usr/bin/env python3
r"""guard_gauntlet.py -- pilote de mutation fonctionnelle des guards.

## Mandat (issue #15067)

CoursIA possede de nombreux guards (gitleaks, detect_markdown_rendering,
pr_close_keyword_guard, ...) et quelques controles positifs ponctuels, mais
pas d'organe generique permettant de prouver qu'un guard rougit ENCORE
lorsqu'on injecte une forme de defaut qu'il est cense detecter.

Ce runner implemente le **contrat HELD / ESCAPED** (Loop MMT gauntlet,
adaptation CoursIA) :

  - NO_FAULT : aucune injection, le check doit reussir (baseline).
  - HELD     : un defaut canonique est injecte, le check doit echouer
               (= le guard tient = detecte le defaut).
  - ESCAPED  : un defaut volontairement *en dehors* de la portee du check
               est injecte, le check doit reussir (= le guard n'est pas
               magicien, il detecte ce qu'il pretend detecter, rien de plus).
  - USAGE    : invocation mal formee (sortie non-zero, message dedie).
  - TIMEOUT  : le check ne repond pas dans la fenetre impartie.

## Pourquoi ne pas vendor upstream (audit #15067 first-hand)

L'upstream Loop MMT (gifts/gauntlet, MIT, blob
5c7b610d69d7fb9e9172792f661baa9f610b587b) utilise :

  - ``subprocess.run(..., shell=True)`` : injection de commande triviale.
  - heritage de ``cwd`` et ``env`` : le check lit des fichiers au-dela du
    sandbox, contournant le contrat.
  - pas de quote Windows-safe pour le chemin du sandbox (espaces, accents).
  - ``TimeoutExpired`` laisse remonter un traceback brut : pollue le verdict.

L'adaptation CoursIA (cette implementation) impose : argv explicite (liste),
``{path}`` injecte comme un argument unique (pas d'expansion shell),
``cwd=`` fige au sandbox, ``env`` minimal documente, ``timeout`` dedie au
verdict (jamais ``TimeoutExpired`` brut).

## Invocation

CLI (par un humain ou un workflow) :

::

    python scripts/ci/guard_gauntlet.py \
        --check "<commande avec {path} token>" \
        --target <fichier a copier dans le sandbox> \
        --fault <truncate|bitflip|replace|none> \
        --replace-content "<chaine de remplacement>" \
        --timeout-sec 5

Le token ``{path}`` est substitue AVANT tokenisation shlex par un argument
**deja quoté** (``shlex.quote``) : ne **PAS** le mettre dans des guillemets
externes dans le template. Le plus naturel : ``{path}`` est le dernier token
de la commande, recu par le check comme ``sys.argv[1]`` (ou l'equivalent du
runtime). Exemples :

  OK (file-targeting check, lit sys.argv[1]) ::

      --check "python -c \"import sys; open(sys.argv[1],'rb')\" {path}"

  OK (commande externe qui prend le chemin en argument final) ::

      --check "my-validator {path}"

  KO : mettre ``{path}`` dans les guillemets du ``-c`` (``{path}`` n'est
       alors plus un argv[1] mais un litteral concatene au script).

Sortie humaine sur stderr, JSON sur stdout. Le JSON contient ``status``,
``fault``, ``check_exit``, ``diagnostics`` (borne). Exit code :

  - 0 : NO_FAULT, HELD, ou ESCAPED (= le check s'est termine, le verdict
        est dans le JSON, l'appelant decide).
  - 2 : USAGE (mauvaise invocation).
  - 3 : TIMEOUT (verdict dedie, pas de traceback).
  - 4 : erreur interne au runner (sandbox, copy, IO).

## Pourquoi un seul validator a la fois

Le pilote est borne. Body #15067 demande au plus deux validateurs ; cette
implementation en supporte exactement un par run, comme convenu dans la
discussion prealable. Cablage CI global prevu dans une tranche ulterieure,
apres preuves HELD + ESCAPED sur un cas concret.

## Hors scope (body #15067)

  - adoption des 44 gifts Loop MMT ;
  - remplacement de fast_lane, pytest, ou selfchecks existants ;
  - execution de commandes issues d'une issue, dashboard, ou fichier non
    approuve ;
  - orchestration generale de pipelines (conductor) ;
  - nouvelle politique de flotte.
"""

from __future__ import annotations

import argparse
import dataclasses
import enum
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
MAX_DIAGNOSTIC_BYTES = 4096


class Status(enum.Enum):
    NO_FAULT = "NO_FAULT"
    BASELINE_FAILED = "BASELINE_FAILED"
    HELD = "HELD"
    ESCAPED = "ESCAPED"
    USAGE = "USAGE"
    TIMEOUT = "TIMEOUT"
    INTERNAL = "INTERNAL"


class Fault(enum.Enum):
    NONE = "none"
    TRUNCATE = "truncate"
    BITFLIP = "bitflip"
    REPLACE = "replace"


@dataclasses.dataclass(frozen=True)
class Result:
    status: Status
    fault: Fault
    check_exit: int | None
    diagnostics: Mapping[str, object]

    def to_jsonable(self) -> dict:
        return {
            "status": self.status.value,
            "fault": self.fault.value,
            "check_exit": self.check_exit,
            "diagnostics": self._bounded(self.diagnostics),
        }

    @staticmethod
    def _bounded(d: Mapping[str, object]) -> Mapping[str, object]:
        out = {}
        for k, v in d.items():
            if isinstance(v, str) and len(v) > MAX_DIAGNOSTIC_BYTES:
                out[k] = v[:MAX_DIAGNOSTIC_BYTES] + f"...[+{len(v)-MAX_DIAGNOSTIC_BYTES}b truncated]"
            else:
                out[k] = v
        return out


def parse_argv(argv: Sequence[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="guard_gauntlet",
        description="Pilote HELD/ESCAPED pour guards fichier-par-fichier (issue #15067).",
    )
    p.add_argument(
        "--check",
        required=True,
        help="Commande a executer ; le token {path} est substitue par le chemin sandbox.",
    )
    p.add_argument(
        "--target",
        required=True,
        type=Path,
        help="Fichier source a copier dans le sandbox. JAMAIS modifie.",
    )
    p.add_argument(
        "--fault",
        choices=[f.value for f in Fault],
        default=Fault.NONE.value,
        help="Defaut a injecter dans la copie sandbox.",
    )
    p.add_argument(
        "--replace-content",
        default="",
        help="Chaine de remplacement (utilisee par fault=replace).",
    )
    p.add_argument(
        "--timeout-sec",
        type=float,
        default=5.0,
        help="Timeout du check en secondes (defaut 5).",
    )
    p.add_argument(
        "--bitflip-byte",
        type=int,
        default=0,
        help="Pour fault=bitflip : offset du byte a flipper (0 par defaut).",
    )
    p.add_argument(
        "--sandbox-parent",
        default=None,
        type=Path,
        help=(
            "Repertoire PARENT du TemporaryDirectory. Par defaut, tempfile "
            "utilise gettempdir(). Utile pour les tests qui veulent "
            "verifier le passage du chemin sandbox avec espaces / accents."
        ),
    )
    return p.parse_args(list(argv))


def apply_fault(target: Path, fault: Fault, replace_content: str, bitflip_byte: int) -> None:
    if fault is Fault.NONE:
        return
    if fault is Fault.TRUNCATE:
        size = target.stat().st_size
        new_size = max(0, size - max(1, size // 4))
        with target.open("r+b") as fh:
            fh.truncate(new_size)
        return
    if fault is Fault.BITFLIP:
        size = target.stat().st_size
        if size == 0:
            return
        offset = bitflip_byte % size
        with target.open("r+b") as fh:
            fh.seek(offset)
            b = fh.read(1)
            if not b:
                return
            fh.seek(offset)
            fh.write(bytes([b[0] ^ 0x01]))
        return
    if fault is Fault.REPLACE:
        target.write_text(replace_content or "garbage mutation content\n", encoding="utf-8")
        return
    raise ValueError(f"fault inconnue: {fault!r}")


class _NoOpContext:
    """No-op context manager : juste pour que `with X as Y: ...` ait une
    forme symetrique quand on n'a PAS besoin de creer un repertoire parent
    (cas --sandbox-parent fourni par l'appelant ; le repertoire existe deja).

    Rend ``str(self.path)`` a `__enter__` ; ne fait rien a `__exit__`.
    """

    def __init__(self, path: Path) -> None:
        self.path = Path(path)

    def __enter__(self) -> str:
        return str(self.path)

    def __exit__(self, *exc: object) -> None:
        return None


def _quote_path_for_shell(path: str) -> str:
    """Quote un chemin pour shlex.split(posix=True).

    Le runner substitue {path} par str(sandbox_target) AVANT shlex.
    Si le chemin contient des espaces (ex. ``C:\\Users\\foo bar\\...``)
    ou des backslashes, le passage direct dans ``shlex.split`` les coupe
    sur les espaces et traite les backslashes comme des caracteres
    d'echappement. On utilise ``shlex.quote`` qui produit un token
    correctement quoté pour le parser posix.
    """
    import shlex
    return shlex.quote(path)


def run_check(
    cmd_template: str,
    sandbox_target: Path,
    timeout_sec: float,
) -> tuple[int, str, str, bool]:
    """Execute la commande avec {path} substitue.

    Renvoie (exit_code, stdout, stderr, timed_out).
    """
    if "{path}" not in cmd_template:
        raise ValueError("La commande doit contenir le token {path}.")
    rendered = cmd_template.replace("{path}", _quote_path_for_shell(str(sandbox_target)))

    import shlex
    argv = shlex.split(rendered, posix=True)
    if not argv:
        raise ValueError("Commande vide apres substitution.")

    sandbox_dir = sandbox_target.parent
    # env minimal + documente : on supprime les variables qui pourraient
    # detourner le check vers des chemins au-dela du sandbox. PATH est garde
    # pour que le check trouve ses binaires, mais cwd + HOME sont imposes.
    env = {
        "PATH": os.environ.get("PATH", ""),
        "SYSTEMROOT": os.environ.get("SYSTEMROOT", ""),
        "LANG": os.environ.get("LANG", "C.UTF-8"),
        "GAUNTLET_SANDBOX": str(sandbox_dir),
        "GAUNTLET_TARGET": str(sandbox_target),
    }

    t0 = time.monotonic()
    try:
        proc = subprocess.run(
            argv,
            cwd=str(sandbox_dir),
            env=env,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout_sec,
            check=False,
            shell=False,
        )
    except subprocess.TimeoutExpired as exc:
        return (
            -1,
            (exc.stdout or "") if isinstance(exc.stdout, str) else (exc.stdout.decode("utf-8", "replace") if exc.stdout else ""),
            (exc.stderr or "") if isinstance(exc.stderr, str) else (exc.stderr.decode("utf-8", "replace") if exc.stderr else ""),
            True,
        )
    return proc.returncode, proc.stdout, proc.stderr, False


def verify_original_intact(original: Path, expected_bytes: bytes) -> bool:
    """Verifie que le fichier source n'a pas ete modifie par le runner.

    Compare le contenu actuel de la cible avec le snapshot capture AVANT
    la mise en sandbox (le snapshot vit dans le TemporaryDirectory, pas
    en sidecar a cote de la cible -- #15067 acceptance).

    Renvoie True si la cible est byte-identique au snapshot, False sinon.
    Si la cible n'existe plus (cas pathologique), renvoie False.
    """
    if not original.exists():
        return False
    try:
        a = original.read_bytes()
    except OSError:
        return False
    return a == expected_bytes


def main(argv: Sequence[str]) -> int:
    try:
        args = parse_argv(argv)
    except SystemExit as exc:
        # argparse a deja affiche un message ; on rend un JSON USAGE.
        sys.stderr.write(f"[USAGE] argparse exit={exc.code}\n")
        return 2

    target: Path = args.target.resolve()
    if not target.is_file():
        sys.stderr.write(f"[USAGE] --target n'est pas un fichier regulier: {target}\n")
        return 2

    fault = Fault(args.fault)

    # Snapshot du contenu de la cible AVANT toute mutation (evalue en
    # memoire, pas en sidecar : #15067 acceptance -- pas d'ecriture
    # <target>.gauntlet-snapshot a cote de la source). Sert a verifier
    # que la cible n'a pas ete modifiee par le runner.
    try:
        original_bytes = target.read_bytes()
    except OSError as exc:
        sys.stderr.write(f"[INTERNAL] Lecture cible impossible: {exc}\n")
        return 4

    # Le sandbox EST le TemporaryDirectory -- on n'ouvre AUCUN fichier
    # source dans le process principal, on ne cree AUCUN sidecar. La
    # copie sandbox vit et meurt dans ce bloc contextuel. Le parent du
    # tmpdir peut etre surcharge via --sandbox-parent pour tester les
    # espaces (cf. test_sandbox_path_with_spaces).
    sandbox_parent_ctx = (
        tempfile.TemporaryDirectory(prefix="gauntlet-parent-")
        if args.sandbox_parent is None
        else _NoOpContext(args.sandbox_parent)
    )
    with sandbox_parent_ctx as sandbox_parent_str:
        with tempfile.TemporaryDirectory(
            prefix="gauntlet-", dir=sandbox_parent_str
        ) as sandbox_dir_str:
            sandbox_dir = Path(sandbox_dir_str)
            sandbox_target = sandbox_dir / target.name
            try:
                shutil.copy2(target, sandbox_target)
            except OSError as exc:
                sys.stderr.write(f"[INTERNAL] Echec copie sandbox: {exc}\n")
                return 4

            try:
                apply_fault(sandbox_target, fault, args.replace_content, args.bitflip_byte)
            except (OSError, ValueError) as exc:
                sys.stderr.write(f"[INTERNAL] Echec application fault: {exc}\n")
                return 4

            run_t0 = time.monotonic()
            try:
                exit_code, stdout, stderr, timed_out = run_check(
                    args.check, sandbox_target, args.timeout_sec
                )
            except ValueError as exc:
                sys.stderr.write(f"[USAGE] {exc}\n")
                return 2
            elapsed_sec = round(time.monotonic() - run_t0, 3)

            if timed_out:
                status = Status.TIMEOUT
                check_exit: int | None = None
            else:
                check_exit = exit_code
                # Le verdict HELD/ESCAPED est a la charge de l'appelant ;
                # le runner rapporte l'exit code, l'appelant decide du mapping.
                # Convention du pilote (#15067) :
                #   fault=NONE           + exit=0  -> NO_FAULT
                #   fault=NONE           + exit!=0 -> BASELINE_FAILED
                #                            (le check rouge sur cible saine
                #                             n'est PAS un HELD -- ce serait
                #                             crediter au guard une tenue sans
                #                             mutation ; c'est un defaut du
                #                             check lui-meme).
                #   fault=truncate/etc   + exit!=0 -> HELD
                #   fault=truncate/etc   + exit=0  -> ESCAPED
                if fault is Fault.NONE:
                    if exit_code == 0:
                        status = Status.NO_FAULT
                    else:
                        status = Status.BASELINE_FAILED
                else:
                    status = Status.HELD if exit_code != 0 else Status.ESCAPED

            # Verifier que la cible source n'a pas ete modifiee pendant le run.
            # On compare l'etat actuel de la cible au snapshot d'avant (bytes).
            intact = verify_original_intact(target, original_bytes)

            result = Result(
                status=status,
                fault=fault,
                check_exit=check_exit,
                diagnostics={
                    "sandbox": str(sandbox_dir),
                    "elapsed_sec": elapsed_sec,
                    "stdout_bytes": len(stdout),
                    "stderr_bytes": len(stderr),
                    "stdout_preview": stdout[:MAX_DIAGNOSTIC_BYTES] if stdout else "",
                    "stderr_preview": stderr[:MAX_DIAGNOSTIC_BYTES] if stderr else "",
                    "original_intact": intact,
                    "original_sha256_before": _sha256_bytes(original_bytes),
                    "original_sha256_after": _sha256_bytes(target.read_bytes()),
                },
            )

            # Sortie humaine sur stderr.
            human = (
                f"[{status.value}] fault={fault.value} exit={check_exit} "
                f"sandbox={sandbox_dir.name} original_intact={intact}\n"
            )
            sys.stderr.write(human)

            # Sortie JSON sur stdout.
            json.dump(result.to_jsonable(), sys.stdout, ensure_ascii=False, sort_keys=True)
            sys.stdout.write("\n")

            # Exit code du runner : 0 pour verdict clair (meme BASELINE_FAILED
            # -- l'appelant lit le statut dans le JSON), 2/3/4 pour les
            # problemes d'invocation/exec.
            if status is Status.USAGE:
                return 2
            if status is Status.TIMEOUT:
                return 3
            if status is Status.INTERNAL:
                return 4
            return 0


def _sha256_bytes(b: bytes) -> str:
    import hashlib
    return hashlib.sha256(b).hexdigest()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
