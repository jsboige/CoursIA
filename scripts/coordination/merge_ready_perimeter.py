"""Verdict local du garde de perimetre, pour le merge_ready (#28131, voie L1).

Pourquoi ce module existe
-------------------------
Le garde de perimetre (`perimeter review guard (#11268)`) tourne sur
`ubuntu-latest` -- un declencheur fork-reachable, donc pas de runner
self-hosted (#13363, #22461). Apres chaque APPROVE du coordinateur, ce run
**attend en file** derriere la charge globale du depot (mesure du 22/11 :
9 a 11 min d'attente en file pour 15 a 27 s de travail effectif), et la
fusion attend avec lui.

La voie L1 de #28131 : **le merge n'attend pas la file**. Quand le run
heberge du nom `perimeter review guard (#11268)` est encore en file sur la
tete evaluee, `merge_ready` mesure le perimetre **localement**, avec **le
meme organe** (`scripts/check_pr_perimeter.py <PR> --scan-thread`), et
adopte son verdict.

Ce n'est pas un garde affaibli :
  * c'est le MEME code, sur la MEME tete (verifiee), sur le MEME fil ;
  * un verdict local BLOQUANT bloque, comme un verdict heberge ;
  * la surface officielle (le check-run heberge) reste en place et continue
    de publier son propre verdict ;
  * la grammaire du perimetre n'est PAS dupliquee : elle reste dans
    l'organe, ce module ne fait que l'appeler.

Fail-closed : toute mesure impossible (organe illisible, rc inattendu, tete
deplacee entre la lecture et la mesure) vaut BLOQUANT. Une absence de
mesure n'est pas une mesure favorable.

Le module ne touche ni au `runs-on` du workflow, ni a l'organe
`check_pr_perimeter.py` (ni sa grammaire, ni ses verdicts).
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
ORGAN = "scripts/check_pr_perimeter.py"

#: Nom du check-run publie par le workflow heberge
#: (`.github/workflows/perimeter-review-guard.yml`).
PERIMETER_CHECK_NAME = "perimeter review guard (#11268)"

VERDICT_OK = "VERDICT: OK"
VERDICT_FAIL = "VERDICT: FAIL"


class RunResultLike(Protocol):
    returncode: int
    stdout: str
    stderr: str


class RunnerLike(Protocol):
    def run(self, cmd: list[str], env: dict[str, str] | None = None) -> RunResultLike: ...


@dataclass(frozen=True)
class LocalVerdict:
    """Verdict local du garde de perimetre.

    ``blocking`` :
      * ``False`` -- mesure faite, rien de bloquant ;
      * ``True``  -- mesure faite, quelque chose BLOQUE (verdict local FAIL) ;
      * ``None``  -- mesure IMPOSSIBLE (fail-closed : on Treate comme bloquant).
    """

    blocking: bool | None
    detail: str


def local_perimeter_verdict(
    runner: RunnerLike,
    pr: int,
    head: str,
    gh_env: dict[str, str],
    repo: str,
) -> LocalVerdict:
    """Verdict local du garde de perimetre sur la tete ``head``.

    Trois etapes, dans cet ordre :
      1. **la tete** : la tete courante de la PR doit etre ``head`` -- sinon la
         mesure porterait sur un autre etat que celui qui va etre fusionne
         (fail-closed) ;
      2. **l'organe** : `scripts/check_pr_perimeter.py <PR> --scan-thread`,
         le meme code que le workflow heberge ;
      3. **la lecture** : ``VERDICT: OK`` -> rien de bloquant ;
         ``VERDICT: FAIL`` -> bloquant ; toute autre sortie -> mesure
         impossible (fail-closed).
    """
    sha = _head_sha(runner, pr, gh_env, repo)
    if sha is None:
        return LocalVerdict(None, "tete-inconnue")
    if sha != head:
        return LocalVerdict(None, f"tete-deplacee:{sha}")

    res = runner.run(
        [sys.executable, ORGAN, str(pr), "--scan-thread"],
        env=gh_env,
    )
    out = (res.stdout or "") + (res.stderr or "")
    if VERDICT_FAIL in out:
        return LocalVerdict(True, "verdict-local:FAIL")
    if VERDICT_OK in out:
        return LocalVerdict(False, "verdict-local:OK")
    return LocalVerdict(None, f"verdict-local:illisible(rc={res.returncode})")


def _head_sha(
    runner: RunnerLike, pr: int, gh_env: dict[str, str], repo: str
) -> str | None:
    res = runner.run(
        ["gh", "api", f"repos/{repo}/pulls/{pr}", "--jq", ".head.sha"],
        env=gh_env,
    )
    if res.returncode != 0:
        return None
    sha = (res.stdout or "").strip()
    return sha or None
