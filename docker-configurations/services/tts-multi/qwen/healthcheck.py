#!/usr/bin/env python3
"""Sonde de sante honnete du service tts-qwen.

Deux conditions, toutes deux mesurees sur ce service le 2026-11-25 :

1. `GET /health` repond 200. Le serveur vLLM-Omni rend ce 200 en une
   milliseconde meme quand un moteur d'etage est mort (ouvrier tue par
   le cgroup) : la condition est necessaire, jamais suffisante.
2. Les deux etages du moteur sont vivants. La config `qwen3_tts.yaml`
   declare deux etages (talker, code2wav) ; chacun porte son processus
   `VLLM::Worker`. Un seul etage vivant laisse `/health` vert et la
   synthese en echec, ce qui est exactement la panne que cette sonde
   existe pour voir.

Sortie 0 seulement si les deux conditions tiennent. Toute duree est
bornee ici, dans le script : le `timeout` du healthcheck Docker ne tue
pas la sonde (221 `curl` bloques en etat S mesures le 2026-11-25, jusqu'a
saturer pids_limit), donc une sonde sans borne fabrique elle-meme
l'indisponibilite qu'elle devrait signaler.
"""

import os
import sys
import time
import urllib.error
import urllib.request

HEALTH_URL = os.environ.get("TTS_QWEN_HEALTH_URL", "http://localhost:8000/health")
HTTP_TIMEOUT = 5
MIN_WORKERS = int(os.environ.get("TTS_QWEN_MIN_WORKERS", "2"))
PROC_DEADLINE_SECONDS = 10


def probe_http():
    """Retourne (code, extrait du corps) ou (None, motif d'echec)."""
    try:
        with urllib.request.urlopen(HEALTH_URL, timeout=HTTP_TIMEOUT) as response:
            return response.getcode(), response.read(200).decode("utf-8", "replace")
    except (urllib.error.URLError, OSError, ValueError) as exc:
        return None, repr(exc)


def count_stage_workers():
    """Compte les processus dont la ligne de commande commence par VLLM::Worker."""
    deadline = time.monotonic() + PROC_DEADLINE_SECONDS
    count = 0
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        if time.monotonic() > deadline:
            raise TimeoutError("lecture de /proc non terminee dans le budget")
        try:
            with open("/proc/%s/cmdline" % entry, "rb") as handle:
                head = handle.read(64).replace(b"\0", b" ")
        except OSError:
            continue
        if head.startswith(b"VLLM::Worker"):
            count += 1
    return count


def main():
    code, detail = probe_http()
    if code != 200:
        print("ECHEC http: %s %s" % (code, detail))
        return 1
    try:
        workers = count_stage_workers()
    except (OSError, TimeoutError) as exc:
        print("ECHEC lecture /proc: %r" % (exc,))
        return 1
    if workers < MIN_WORKERS:
        print("ECHEC etages: %d ouvrier(s) vivant(s), %d attendu(s); http 200" % (workers, MIN_WORKERS))
        return 1
    print("OK http 200, ouvriers=%d" % workers)
    return 0


if __name__ == "__main__":
    sys.exit(main())
