#!/usr/bin/env python3
"""Detecteur de kernelspec a `argv[0]` ephemere (#23997).

Origine -- constat de la review `[Hermes]` de #23941, porte par po-2028 :

    "Le kernelspec `coursia-canonical` etait enregistre dans la config Jupyter
     utilisateur avec un `argv[0]` pointant dans un scratchpad de session. Un
     tel noyau fonctionne le jour de sa creation et meurt au nettoyage du
     scratchpad."

CE QUE CE GARDE MESURE
----------------------
Un kernelspec enregistre sur une machine reference un interpreteur par
`argv[0]`. Quand ce chemin vit sous un repertoire temporaire (`%TEMP%`,
`/tmp`, scratchpad de session `claude`), le noyau **fonctionne le jour de sa
creation puis meurt** au premier nettoyage -- et le symptome est eloigne de la
cause : le nom du noyau suggere un canon durable, le chemin dit le contraire.
Un carnet execute sur ce noyau echoue ensuite sur un chemin inexistant.

Trois verdicts par kernelspec, jamais confondus :

    TEMP_ROOT            l'interpreteur est sous une racine temporaire connue
                         (`tempfile.gettempdir()`, `/tmp`, `/var/tmp`, `/dev/shm`)
    SCRATCHPAD_COMPONENT l'interpreteur traverse un composant nomme `scratchpad`
                         (scratchpad de session, nettoye par le harnais)
    MISSING_INTERPRETER  l'interpreteur est un chemin absolu qui n'existe plus
                         (mesure seulement sous `--check-exists`)

CE QU'IL NE MESURE PAS, ET POURQUOI
-----------------------------------
1. **Les commandes nues.** `dotnet`, `wsl`, `wsl.exe`, `python` ne sont pas des
   chemins : ils se resolvent par `PATH` et ne vivent sous aucun temporaire.
   Un garde qui les signalerait ferait rougir la moitie d'un parc sain
   (28 kernelspecs sur ce siege, 5 commandes nues). Seuls les `argv[0]`
   **absolus** sont mesures.
2. **Un `argv[0]` absolu hors temporaire mais absent.** C'est un noyau casse,
   pas un noyau ephemere : c'est un defaut distinct, mesure seulement si on le
   demande (`--check-exists`), pour ne pas melanger deux causes dans un meme
   rouge.
3. **La sante du noyau lui-meme.** Ce garde lit une declaration, il ne lance
   pas `ipykernel` : un interpreteur durable dont les dependances manquent
   passe ce garde et echouera a l'execution. Ce n'est pas son sujet.

POURQUOI CE N'EST PAS CABLÉ EN CI
---------------------------------
Le defaut vit dans la **config utilisateur d'une machine**, pas dans le depot :
un runner CI neuf a des kernelspecs propres et ephemeres, et le garde n'y
mesurerait rien de ce qu'il cherche. Il se lance a la main sur un poste (ou par
une tache planifiee locale) :

    python scripts/notebook_tools/check_kernelspec_temp_paths.py

Usage en test : `--kernelspec-dir` lit une arborescence `<nom>/kernel.json`
sans appeler `jupyter` ; `--from-json` lit une sortie deja capturee de
`jupyter kernelspec list --json`.

Codes de sortie : 0 propre, 1 au moins un offender, 2 incident d'entree
(`jupyter` injoignable, JSON illisible) -- un incident n'est pas un quitus.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

RC_CLEAN = 0
RC_OFFENDERS = 1
RC_INCIDENT = 2

POSIX_TEMP_ROOTS = ("/tmp", "/var/tmp", "/dev/shm")
SCRATCHPAD_COMPONENT = "scratchpad"


def _platform_temp_roots() -> tuple[str, ...]:
    """Les racines POSIX ne valent qu'en POSIX.

    Sous Windows, `os.path.realpath("/tmp")` resout le chemin **relativement au
    lecteur courant** (`D:\\tmp`) : inclure ces entrees y fabriquerait des
    racines qui n'existent pas et pourraient signaler un `D:\\tmp` legitime.
    """
    return () if os.name == "nt" else POSIX_TEMP_ROOTS


def _normcase(path: str) -> str:
    """Normalise pour comparaison : casse (Windows) + separateurs."""
    return os.path.normcase(os.path.normpath(path))


def _resolved(path: str) -> str:
    """Chemin resolu quand il existe, normalise sinon.

    `realpath` degrade proprement sur un chemin absent ; `_normcase` applique
    ensuite la casse et les separateurs de la plateforme.
    """
    return _normcase(os.path.realpath(path))


def temp_roots(extra: list[str] | None = None) -> list[str]:
    """Racines temporaires a considerer, resolues et normalisees.

    Les variables d'environnement sont incluses parce que `TEMP` peut pointer
    ailleurs que `tempfile.gettempdir()` sur certains postes Windows, et un
    noyau installe sous l'un mais pas sous l'autre doit quand meme remonter.
    """
    raw: list[str] = []
    try:
        raw.append(tempfile.gettempdir())
    except (FileNotFoundError, OSError):  # pragma: no cover - poste exotique
        pass
    for var in ("TEMP", "TMP"):
        value = os.environ.get(var)
        if value:
            raw.append(value)
    raw.extend(_platform_temp_roots())
    raw.extend(extra or [])
    seen: list[str] = []
    for root in raw:
        if not root:
            continue
        resolved = _resolved(root)
        if resolved not in seen:
            seen.append(resolved)
    return seen


def _has_scratchpad_component(path: str) -> bool:
    """Vrai si un composant du chemin s'appelle `scratchpad`."""
    parts = Path(path).parts
    return any(part.lower() == SCRATCHPAD_COMPONENT for part in parts)


def classify_interpreter(
    interpreter: str,
    roots: list[str],
    *,
    check_exists: bool = False,
) -> str | None:
    """Rend la raison du signalement, ou None si l'interpreteur est sain.

    Une commande nue (`dotnet`, `wsl`, `python`) n'est jamais mesuree : elle se
    resout par `PATH` et ne residera sous aucun temporaire.
    """
    if not interpreter or not os.path.isabs(interpreter):
        return None
    resolved = _resolved(interpreter)
    for root in roots:
        if resolved == root or resolved.startswith(root + os.sep):
            return "TEMP_ROOT"
    if _has_scratchpad_component(resolved):
        return "SCRATCHPAD_COMPONENT"
    if check_exists and not os.path.exists(interpreter):
        return "MISSING_INTERPRETER"
    return None


def load_specs_from_dir(kernelspec_dir: str) -> dict[str, dict]:
    """Lit `<nom>/kernel.json` sous un repertoire de kernelspecs."""
    base = Path(kernelspec_dir)
    specs: dict[str, dict] = {}
    for kernel_json in sorted(base.glob("*/kernel.json")):
        try:
            specs[kernel_json.parent.name] = json.loads(
                kernel_json.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise ValueError(
                f"kernelspec illisible : {kernel_json} ({exc})") from exc
    return specs


def load_specs_from_jupyter() -> dict[str, dict]:
    """Interroge `jupyter kernelspec list --json`."""
    try:
        done = subprocess.run(
            [sys.executable, "-m", "jupyter", "kernelspec", "list", "--json"],
            capture_output=True, text=True, encoding="utf-8", timeout=120,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ValueError(f"jupyter injoignable : {exc}") from exc
    if done.returncode != 0:
        raise ValueError(
            "jupyter kernelspec list a echoue "
            f"(rc={done.returncode}) : {done.stderr.strip()[:400]}")
    payload = json.loads(done.stdout)
    return payload.get("kernelspecs", payload)


def _argv0(spec: dict) -> str:
    argv = spec.get("argv") if isinstance(spec, dict) else None
    if isinstance(argv, list) and argv:
        return str(argv[0])
    return ""


def audit(
    specs: dict[str, dict],
    roots: list[str],
    *,
    check_exists: bool = False,
) -> list[dict]:
    """Rend la liste des offenders, triee par nom de kernelspec."""
    findings: list[dict] = []
    for name in sorted(specs):
        info = specs[name]
        spec = info.get("spec", info) if isinstance(info, dict) else {}
        interpreter = _argv0(spec)
        reason = classify_interpreter(
            interpreter, roots, check_exists=check_exists)
        if reason:
            findings.append({
                "kernel": name,
                "reason": reason,
                "interpreter": interpreter,
                "exists": bool(interpreter) and os.path.exists(interpreter),
            })
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Detecte les kernelspecs dont argv[0] vit sous un "
                    "repertoire temporaire (#23997).")
    parser.add_argument(
        "--kernelspec-dir",
        help="Lit <nom>/kernel.json sous ce repertoire au lieu d'appeler "
             "jupyter (usage en test).")
    parser.add_argument(
        "--from-json",
        help="Lit une sortie deja capturee de "
             "`jupyter kernelspec list --json`.")
    parser.add_argument(
        "--temp-root", action="append", default=[],
        help="Racine temporaire supplementaire (repetable).")
    parser.add_argument(
        "--check-exists", action="store_true",
        help="Signale aussi les interpretes absolus qui n'existent plus.")
    parser.add_argument(
        "--json", action="store_true", help="Sortie machine.")
    args = parser.parse_args(argv)

    try:
        if args.kernelspec_dir:
            specs = load_specs_from_dir(args.kernelspec_dir)
        elif args.from_json:
            payload = json.loads(
                Path(args.from_json).read_text(encoding="utf-8"))
            specs = payload.get("kernelspecs", payload)
        else:
            specs = load_specs_from_jupyter()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"INCIDENT : {exc}", file=sys.stderr)
        return RC_INCIDENT

    if not specs:
        print("INCIDENT : aucun kernelspec mesure -- un perimetre vide n'est "
              "pas un vert (mauvais repertoire, ou config Jupyter absente).",
              file=sys.stderr)
        return RC_INCIDENT

    roots = temp_roots(args.temp_root)
    findings = audit(specs, roots, check_exists=args.check_exists)

    if args.json:
        print(json.dumps({
            "kernels": len(specs),
            "temp_roots": roots,
            "offenders": findings,
            "verdict": "OFFENDERS" if findings else "CLEAN",
        }, indent=2, ensure_ascii=False))
        return RC_OFFENDERS if findings else RC_CLEAN

    print(f"{len(specs)} kernelspec(s) mesure(s), "
          f"{len(roots)} racine(s) temporaire(s)")
    if not findings:
        print("CLEAN : aucun interpreteur sous un chemin temporaire.")
        return RC_CLEAN
    for finding in findings:
        state = "present" if finding["exists"] else "absent"
        print(f"  {finding['reason']:21} {finding['kernel']:24} "
              f"({state}) {finding['interpreter']}")
    print(f"\n{len(findings)} kernelspec(s) a reprendre : reenregistrer le "
          "noyau sur un interpreteur durable, puis relancer cette commande.")
    return RC_OFFENDERS


if __name__ == "__main__":
    sys.exit(main())
