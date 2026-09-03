"""Suspension du sidecar ``tts-fishaudio-idle-monitor`` pendant une fenetre de chaine.

Epic #1028, residu 2 : sur le livre complet, les phases LLM amont (p3 + p4)
durent ~36 min sans aucun appel TTS -- l'idle monitor (IDLE_TIMEOUT=1200 s)
tue alors le service ``tts-fishaudio`` AVANT que p5 n'arrive, et la chaine
echoue sur port refuse (385/385 echecs au premier run du livre entier, #14059).
Le monitor est une economie GPU legitime : on le SUSPEND pendant la fenetre
de chaine LLM->TTS puis on le redemarre, au lieu d'un geste manuel a ne pas
oublier.

Fail-safe par construction : docker absent, daemon muet, inspect/stop en
echec -- la chaine continue TOUJOURS, au pire avec un avertissement (le
comportement d'avant ce module etait l'echec silencieux en chaine longue).
"""

from __future__ import annotations

import subprocess
from contextlib import contextmanager
from collections.abc import Iterator

MONITOR_CONTAINER = "tts-fishaudio-idle-monitor"

# Phases dont la duree est dominee par le LLM, sans appel TTS.
_LLM_PHASES_BEFORE_TTS = {"p0", "p1", "p1_5", "p2", "p3", "p4"}

_DOCKER_TIMEOUT_S = 30


def _docker(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["docker", *args], capture_output=True, text=True, timeout=_DOCKER_TIMEOUT_S
    )


def chain_needs_suspension(phases: list[str]) -> bool:
    """True si la chaine contient p5 precede d'au moins une phase LLM.

    ``["p5"]`` seul n'a pas besoin de suspension (p5 appelle le TTS
    immediatement, le monitor ne le voit jamais inactif) ; ce sont les
    chaines LLM->TTS qui tuent le service pendant les phases amont.
    """
    seen: set[str] = set()
    for phase in phases:
        if phase == "p5":
            return bool(seen & _LLM_PHASES_BEFORE_TTS)
        seen.add(phase)
    return False


def monitor_is_running() -> bool:
    """True si le conteneur monitor existe ET tourne. Docker absent => False."""
    try:
        result = _docker(["inspect", "-f", "{{.State.Running}}", MONITOR_CONTAINER])
    except (OSError, subprocess.TimeoutExpired):
        return False
    return result.returncode == 0 and result.stdout.strip().lower() == "true"


@contextmanager
def suspended_idle_monitor(phases: list[str]) -> Iterator[bool]:
    """Suspend le monitor pour la duree de la fenetre ; yield True si suspendu.

    Le monitor n'est redemarre que si CETTE fenetre l'a arrete (jamais au
    hasard d'un etat anterieur).
    """
    if not chain_needs_suspension(phases):
        yield False
        return
    if not monitor_is_running():
        print(f"[monitor] {MONITOR_CONTAINER} absent ou arrete -- chaine sans suspension")
        yield False
        return
    stop = _docker(["stop", MONITOR_CONTAINER])
    if stop.returncode != 0:
        print(
            f"[monitor] WARN: stop echoue (rc={stop.returncode}) -- la chaine "
            "continue, le monitor peut tuer tts-fishaudio en cours de route"
        )
        yield False
        return
    print(f"[monitor] {MONITOR_CONTAINER} suspendu pour la fenetre de chaine")
    try:
        yield True
    finally:
        restart = _docker(["start", MONITOR_CONTAINER])
        state = (
            "redemarre"
            if restart.returncode == 0
            else f"ECHEC restart (rc={restart.returncode}) -- relancer docker start {MONITOR_CONTAINER}"
        )
        print(f"[monitor] {MONITOR_CONTAINER} {state}")
