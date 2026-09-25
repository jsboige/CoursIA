#!/usr/bin/env python3
"""release_parked_runs.py -- libere les runs `pull_request` gares par un push bot.

## Pourquoi ce script existe

Un commit pousse par github-actions[bot] sur une PR same-repo cree les runs
`pull_request` en `action_required` -- en attente d'une approbation manuelle
qui, mesuree sur 8 jours consecutifs, n'est jamais venue. Un run gare ne
s'execute jamais, donc le check requis qu'il porte est ABSENT a la tete (pas
rouge : absent), et la PR de livraison reste BLOCKED avec tous les checks
visibles verts (#17532 : #17177 resta BLOCKED 2 jours ; meme classe que
#10136 -- le catalogue de main est reste 9 jours stale pendant que le
workflow rapportait `success` chaque matin).

Deuxieme piege, corrige par #17634 : les runs du head n'existent pas encore a
l'instant du push (GitHub les cree quelques secondes plus tard). Une requete
`gh run list` unique part avant leur creation et rend "no parked run", et les
runs restent gares. On sonde donc jusqu'a un compte non nul ET stable sur
deux sondes, dans une fenetre bornee.

Ce script est l'implementation unique appelee par les deux workflows qui
livrent par PR bot (`catalog-cron.yml` et `qc-research-monitor.yml`) : deux
copies du meme correctif finissent par diverger -- c'est exactement ce qui a
produit #17668 (le jumeau qc-research n'avait pas le sondage borne de #17634).

## Contrat

- Variables d'env (meme contrat que l'ancien step inline) :
    GH_TOKEN                 -- jeton GitHub (lu par le CLI `gh`)
    GITHUB_REPOSITORY        -- fixe par le runner
    BRANCH                   -- branche de livraison garante
    RELEASE_STAGGER_SECONDS  -- delai entre deux approbations (defaut 15 :
                                16 runs approuves en rafale sur un pool sature
                                ont tenu les checks `queued` 19 min, pendant
                                lesquelles "PR gate" a epuise le quota du jeton
                                d'installation, HTTP 403, et echoue fail-closed
                                -- mesure du 2026-09-21)
    RELEASE_CEILING          -- soupape, pas un plafond de debit (defaut 40) :
                                au-dela, c'est que les runs s'empilent sans
                                jamais s'executer ; le depassement est ECRIT
    RELEASE_SETTLE_POLLS     -- fenetre de sonde (defaut 8 x 15 s) : laisser
                                GitHub creer les runs du head
    RELEASE_SETTLE_SECONDS   -- espacement entre deux sondes (defaut 15 ;
                                overridable pour les tests)
- Sortie : exit 0 dans tous les cas geres (le step porte continue-on-error ;
  la panne d'approbation doit rester VISIBLE via ::warning, pas rouge).
"""

import os
import subprocess
import sys
import time


def notice(tag: str, message: str) -> None:
    print(f"::notice title={tag}::{message}")


def warning(tag: str, message: str) -> None:
    print(f"::warning title={tag}::{message}")


def run_git_head() -> str:
    out = subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace",
    )
    return out.stdout.strip()


def list_parked(repo: str, branch: str, head_sha: str) -> list[tuple[str, str]]:
    out = subprocess.run(
        ["gh", "run", "list", "--repo", repo, "--branch", branch, "--limit", "100",
         "--json", "databaseId,headSha,conclusion,workflowName"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if out.returncode != 0:
        return []
    import json
    rows = json.loads(out.stdout or "[]")
    return [
        (str(r["databaseId"]), r["workflowName"])
        for r in rows
        if r.get("conclusion") == "action_required" and r.get("headSha") == head_sha
    ]


def approve(repo: str, run_id: str) -> bool:
    out = subprocess.run(
        ["gh", "api", "-X", "POST", f"repos/{repo}/actions/runs/{run_id}/approve"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    return out.returncode == 0


def main() -> int:
    tag = "Catalog"
    args = sys.argv[1:]
    it = iter(args)
    for arg in it:
        if arg == "--tag":
            tag = next(it, "Catalog")
        else:
            print(f"argument inconnu : {arg}", file=sys.stderr)
            return 2

    repo = os.environ["GITHUB_REPOSITORY"]
    branch = os.environ["BRANCH"]
    stagger = int(os.environ.get("RELEASE_STAGGER_SECONDS", "15"))
    ceiling = int(os.environ.get("RELEASE_CEILING", "40"))
    polls = int(os.environ.get("RELEASE_SETTLE_POLLS", "8"))
    settle = int(os.environ.get("RELEASE_SETTLE_SECONDS", "15"))

    head_sha = run_git_head()
    notice(tag, f"releasing parked runs at {head_sha}")

    parked: list[tuple[str, str]] = []
    prev = -1
    for _ in range(polls):
        time.sleep(settle)
        parked = list_parked(repo, branch, head_sha)
        n = len(parked)
        if n > 0 and n == prev:
            break
        prev = n

    if not parked:
        notice(tag, "no parked run at this head -- nothing to release.")
        return 0

    notice(tag, f"{len(parked)} run(s) parked at this head, staggering {stagger}s apart")
    released = refused = deferred = 0
    for seen, (run_id, name) in enumerate(parked, start=1):
        if seen > ceiling:
            deferred += 1
            continue
        if released > 0:
            time.sleep(stagger)
        if approve(repo, run_id):
            released += 1
        else:
            refused += 1
            warning(tag, f"could not approve run {run_id} ({name})")

    notice(tag, f"released {released} run(s), refused {refused}, deferred {deferred}")
    if deferred > 0:
        warning(
            tag,
            f"{deferred} run(s) left parked by the ceiling of {ceiling} -- this is "
            "NOT normal throughput. Runs are piling up at one head; investigate "
            "before raising the ceiling.",
        )
    if refused > 0:
        warning(
            tag,
            f"{refused} run(s) still parked -- the delivery PR will stay BLOCKED. "
            "Approve them by hand, or grant a token that may approve workflow runs.",
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
