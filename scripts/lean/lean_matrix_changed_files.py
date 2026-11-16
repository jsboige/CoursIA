#!/usr/bin/env python3
"""Liste des fichiers modifies d'un evenement, pour le job `changes` de
``.github/workflows/lean-ci-matrix.yml`` (#22065).

Le job doit choisir les lakes a batir : il lit la liste des fichiers
modifies dans l'API REST (pull_request : fichiers de la PR ; push :
compare avant..apres) puis la passe au dispatcher.

Avant ce correctif, la lecture etait faite dans le shell avec un repli
silencieux (``|| echo -n "" > "$out"``) : un 403 de quota transformait la
liste des fichiers modifies en liste VIDE, donc ``any=false``, donc le
build Lean etait ``skipped`` -- et ``skipped`` se replie en vert. Un
build Lean qui n'a pas eu lieu s'affichait comme fait (instance #21999,
run 39814286963 : ``gh: API rate limit exceeded ... (HTTP 403)`` suivi
d'une liste vide, et pourtant le job de build au vert).

Ici l'echec est BRUYANT : une nouvelle tentative (le 403 de quota
d'installation est transitoire -- le rejeu a reussi sur l'instance
mesuree), puis sortie non nulle. Le fichier de sortie n'est ecrit
qu'a la reussite : un ``any=false`` ne peut pas naitre d'une lecture en
echec.

DEUX SORTIES D'ECHEC, DISTINCTES (contrat #26739, instance #26004)
-----------------------------------------------------------------

Le job reste rouge dans les deux cas -- un build qui n'a pas eu lieu ne
doit jamais s'afficher vert. Ce qui change est ce que le rouge **dit** :

* ``EXIT_USAGE = 1`` : l'invocation elle-meme est fausse (evenement non
  gere, ``--pr`` manquant). C'est un defaut a corriger, pas un alea.
  (Le ``2`` qu'argparse rend de son cote pour un argument absent
  appartient a la meme famille : il n'emet aucune annotation.)
* ``EXIT_MEASURE_FAILED = 3`` : la **mesure** a echoue (403 de quota,
  reseau). L'etat du depot est **INCONNU, pas faux**. L'organe emet
  alors une annotation ``INCONCLUSIVE -- ...``, le meme verdict que le
  gate a introduit pour lui-meme (#26739), que les consommateurs d'etats
  savent deja lire (``scripts/ci/gate_verdicts.py`` via
  ``pr_gate.parse_inconclusive_message``) : la PR n'est plus classee en
  rouge reparable, et le seul geste est de rejouer la jambe. Le code
  ``3`` est celui que le gate porte deja pour ce verdict
  (``pr_gate.QUOTA_INCONCLUSIVE_CODE``) : un nombre, un sens.

Instance mesuree (#26004, run 43813462537, job 133120065647) : le gate
a rendu ``failing checks: lean-matrix-changes (failure)`` -- blanc et
noir, indiscernable d'un echec de contenu -- alors que le job etait mort
sur son propre ``gh api`` en 403 et qu'aucun ``lake`` n'avait tourne.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from pathlib import Path

# Self-cover : un evenement manuel est une intention explicite de tout
# lancer (le dispatcher y arrive par le self-cover du gate).
SELF_COVER = ".github/workflows/lean-ci-matrix.yml"


# Deux sorties d'echec distinctes : un defaut d'invocation (1) et un echec
# de MESURE (3). Le second porte l'etat INCONCLUSIVE dans son annotation.
# `3` est le code que le gate porte deja pour ce meme verdict
# (`pr_gate.QUOTA_INCONCLUSIVE_CODE`) ; `2` reste a argparse, qui ne dit
# rien de l'etat du depot.
EXIT_USAGE = 1
EXIT_MEASURE_FAILED = 3

# Prefixe du verdict d'etat lu par `pr_gate.parse_inconclusive_message`
# (via `scripts/ci/gate_verdicts.py`). Le format appartient a l'emetteur ;
# ici l'emetteur est une jambe de matrice, et le prefixe est le contrat.
INCONCLUSIVE_MARKER = "INCONCLUSIVE -- "


class ApiError(RuntimeError):
    """La lecture de l'API GitHub a echoue."""


def inconclusive_annotation(detail: str) -> str:
    """Une commande de workflow `::error::` portant le verdict INCONCLUSIVE.

    GitHub publie le message comme annotation du check-run de la jambe ;
    c'est ce canal, et non le log, que `gate_verdicts.read_annotations`
    consomme. Le message est mis sur une seule ligne et echappe selon les
    regles des commandes de workflow (%, \\r, \\n).
    """
    one_line = " ".join(str(detail).split())
    escaped = (
        one_line.replace("%", "%25")
        .replace("\r", "%0D")
        .replace("\n", "%0A")
    )
    return f"::error::{INCONCLUSIVE_MARKER}{escaped}"


def _gh_api(args: list[str]) -> str:
    proc = subprocess.run(
        ["gh", "api", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or "").strip()
        raise ApiError(
            f"gh api {' '.join(args)} a echoue (rc={proc.returncode}) : {detail}"
        )
    return proc.stdout


def _lines(text: str) -> list[str]:
    return [line.strip() for line in text.splitlines() if line.strip()]


def changed_files_pull_request(repo: str, pr: int) -> list[str]:
    out = _gh_api([
        "--paginate",
        f"repos/{repo}/pulls/{pr}/files",
        "--jq", ".[].filename",
    ])
    return _lines(out)


def changed_files_push(repo: str, before: str, sha: str) -> list[str]:
    if before.startswith("0000000"):
        # Nouvelle histoire de branche : on ne peut pas differencer -> tout.
        return [SELF_COVER]
    out = _gh_api([
        f"repos/{repo}/compare/{before}...{sha}",
        "--jq", ".files[].filename",
    ])
    return _lines(out)


def collect(
    event: str,
    repo: str,
    pr: str | None = None,
    before: str | None = None,
    sha: str | None = None,
) -> list[str]:
    if event == "pull_request":
        if not pr:
            raise ValueError("evenement pull_request sans numero de PR")
        return changed_files_pull_request(repo, int(pr))
    if event == "push":
        if not before or not sha:
            raise ValueError("evenement push sans before/sha")
        return changed_files_push(repo, before, sha)
    if event == "workflow_dispatch":
        return [SELF_COVER]
    raise ValueError(f"evenement non gere : {event}")


def collect_with_retry(
    event: str,
    repo: str,
    pr: str | None = None,
    before: str | None = None,
    sha: str | None = None,
    retries: int = 1,
    sleep_s: float = 5.0,
) -> list[str]:
    """Une nouvelle tentative sur echec de l'API, puis l'echec remonte.

    Le 403 de quota d'installation est transitoire (instance #21999 : le
    rejeu du job a dispatche le build normalement). Au-dela, l'echec
    remonte : mieux vaut un job rouge qu'un build qui n'a pas eu lieu.
    """
    last: Exception | None = None
    for attempt in range(retries + 1):
        try:
            return collect(event, repo, pr=pr, before=before, sha=sha)
        except ApiError as exc:
            last = exc
            if attempt < retries:
                print(
                    f"lecture API en echec ({exc}) -- nouvelle tentative "
                    f"dans {sleep_s}s",
                    file=sys.stderr,
                )
                time.sleep(sleep_s)
    assert last is not None
    raise last


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--event", required=True,
                    help="pull_request | push | workflow_dispatch")
    ap.add_argument("--repo", required=True, help="owner/name")
    ap.add_argument("--pr", default=None, help="numero de PR (pull_request)")
    ap.add_argument("--before", default=None, help="sha avant (push)")
    ap.add_argument("--sha", default=None, help="sha courant (push)")
    ap.add_argument("--out", required=True, type=Path,
                    help="fichier de sortie (une ligne par chemin)")
    ap.add_argument("--retries", type=int, default=1,
                    help="nouvelles tentatives sur echec de l'API")
    ap.add_argument("--sleep", type=float, default=5.0,
                    help="attente entre deux tentatives (secondes)")
    args = ap.parse_args(argv)

    try:
        files = collect_with_retry(
            args.event, args.repo,
            pr=args.pr, before=args.before, sha=args.sha,
            retries=args.retries, sleep_s=args.sleep,
        )
    except ApiError as exc:
        # BRUYANT (aucun fichier de sortie) ET LISIBLE : l'echec est une
        # mesure impossible, pas un verdict sur le depot. L'annotation
        # `INCONCLUSIVE -- ...` est le canal que les consommateurs d'etats
        # savent lire (#26739) ; le job reste rouge pour autant.
        print(f"LEAN-MATRIX CHANGED-FILES: {exc}", file=sys.stderr)
        print(inconclusive_annotation(
            f"lecture API en echec, l'etat des fichiers modifies est INCONNU "
            f"(pas faux) -- rejouer la jambe apres le reset du quota : {exc}"
        ))
        return EXIT_MEASURE_FAILED
    except ValueError as exc:
        # Invocation fausse : c'est un defaut a corriger, pas un alea.
        print(f"LEAN-MATRIX CHANGED-FILES: {exc}", file=sys.stderr)
        return EXIT_USAGE

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        "".join(f"{name}\n" for name in files), encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
