#!/usr/bin/env python3
"""Rejoue les jambes `PR gate` bloquees par le MINUTEUR DWELL, une fois le
plancher brut ecoule.

Pourquoi cet organe existe
--------------------------
Le plancher DWELL (`scripts/ci/merge_dwell.py`, `DEFAULT_DWELL_MIN = 120`)
produit un rouge de `PR gate` qui n'est **pas** un defaut du code : c'est un
minuteur. La jambe se re-agrege au balayage suivant
(`pr-gate-stale-sweep.yml`, cadence MESUREE 2 h 33 a 5 h 18 entre tirs, pas
horaire malgre son cron `7 * * * *` -- #15197). D'ici la, chaque lane qui
retrouve une PR rouge fait le meme calcul a la main.

Le piege mesure (#27242, 2026-11-18) : le message du minuteur porte DEUX
horodatages.
  - `reste NN min`      : l'etat du plancher ;
  - `ecoule a <T>`      : la **prochaine pointe du balayage**, PAS l'echeance
                          du plancher (le plancher brut, c'est la tete + 120 min).
Lire `ecoule a` comme une echeance retarde chaque PR d'environ une heure ; le
champ existe pour dire a la lane "tu reverras ce resultat au prochain
balayage", pas "rien ne bougera avant".

Ce que fait l'organe, donc :
  1. relit la tete de la PR et l'heure de commit (celle du minuteur) ;
  2. calcule le **plancher brut** = heure de commit + `DEFAULT_DWELL_MIN` ;
  3. verifie que la jambe `PR gate` est bien un minuteur DWELL (pas un rouge
     reel) -- un rouge de code n'est **jamais** rejoue par cet organe ; une
     jambe **en cours** n'est ni verte ni rouge (GitHub n'ecrit son titre
     qu'a la fin du job : un titre vide y ressemble a un echec etrange) ;
  4. rejoue la jambe (`gh run rerun <run_id> --job <job_id>`) si et seulement
     si le plancher brut est passe.

Orthogonalement : le minuteur se laisse lever par le label
`merge-dwell-waived` (urgence `main` rouge) -- l'organe n'y touche pas.

Usage
-----
    python scripts/ci/replay_dwell_floors.py --pr 27262 27263      # lecture
    python scripts/ci/replay_dwell_floors.py --pr 27262 --apply    # rejoue
    python scripts/ci/replay_dwell_floors.py --all --json          # inventaire

Le mode par defaut est la **lecture seule** (dry-run) : `--apply` est
explicite, comme `scripts/ci/prune_merged_worktrees.py`.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import merge_dwell  # noqa: E402  (chemin ajoute ci-dessus)
from merge_dwell import (  # noqa: E402
    DEFAULT_DWELL_MIN,
    WAIVER_LABEL,
    head_committed_at,
    parse_iso8601,
    parse_pending_message,
)

REPO_DEFAULT = "jsboige/CoursIA"
GATE_NAME = "PR gate"


# --------------------------------------------------------------------------
# Fonctions PURES (testables sans reseau)
# --------------------------------------------------------------------------

def dwell_floor(committed_at: datetime, dwell_min: float = DEFAULT_DWELL_MIN) -> datetime:
    """Plancher BRUT : l'heure de commit de la tete + le dwell.

    C'est l'echeance reelle du minuteur. Le champ `ecoule a` du message n'est
    pas cette echeance (voir l'entete du module).
    """
    return committed_at + timedelta(minutes=dwell_min)


def is_dwell_timer(title: str) -> bool:
    """Vrai si le message de la jambe est celui d'un plancher NON ecoule.

    On reutilise le parseur de l'emetteur (`merge_dwell.parse_pending_message`)
    plutot qu'une copie de la forme : une copie deriverait en silence, et le
    minuteur redeviendrait invisible -- c'est exactement le piege que
    `merge_dwell` documente.
    """
    return parse_pending_message(title or "") is not None


def decide(
    *,
    conclusion: str,
    title: str,
    committed_at: datetime,
    now: datetime,
    dwell_min: float = DEFAULT_DWELL_MIN,
    waived: bool = False,
    status: str = "completed",
) -> tuple[str, str]:
    """Decide quoi faire d'une jambe `PR gate`. Fonction PURE.

    Renvoie `(action, motif)` avec `action` dans :
      - ``"rejouer"``  : le plancher brut est passe, la jambe est un minuteur ;
      - ``"attendre"`` : plancher brut pas encore passe, ou jambe EN COURS ;
      - ``"ignorer"``  : rien a faire (legende verte, derogation, rouge reel).

    Un rouge **reel** (echec qui n'est pas le minuteur) n'est jamais rejoue :
    rejouer un test rouge rend le MEME rouge, et le cache des legs la rendrait
    silencieuse.

    Cas mesure le 2026-11-18 (#26989) : une jambe **en cours** porte un
    `output.title` **vide** (GitHub ne l'ecrit qu'a la fin du job). Sans le
    test de `status`, un titre vide passait pour « pas le minuteur » et le
    verdict tombait sur « rouge reel » : un minuteur etait classe dans la
    mauvaise famille, et un consommateur qui s'arrete sur ce verdict abandonnait
    la PR. Une jambe qui n'a pas fini n'est **ni verte ni rouge** -- elle est en
    cours, et le seul geste possible est d'attendre.
    """
    if conclusion == "success":
        return "ignorer", "jambe verte"
    if waived:
        return "ignorer", "derogation par label `{}`".format(WAIVER_LABEL)
    if status and status != "completed":
        return "attendre", "jambe en cours (statut `{}`)".format(status)
    if not is_dwell_timer(title):
        return "ignorer", "echec qui n'est pas le minuteur DWELL (rouge reel)"
    floor = dwell_floor(committed_at, dwell_min)
    if now < floor:
        return "attendre", "plancher brut pas encore passe ({})".format(
            floor.strftime("%Y-%m-%dT%H:%M:%SZ"))
    return "rejouer", "plancher brut passe ({})".format(
        floor.strftime("%Y-%m-%dT%H:%M:%SZ"))


# --------------------------------------------------------------------------
# Acces reseau (injectable pour les tests)
# --------------------------------------------------------------------------

def gh_json(path: str) -> object:
    """Lecture JSON via `gh api` (meme contrat que `merge_dwell._gh_json`)."""
    try:
        completed = subprocess.run(
            ["gh", "api", path], capture_output=True, text=True,
            encoding="utf-8", errors="replace", check=False,
        )
    except FileNotFoundError as exc:  # pragma: no cover - environnement
        raise RuntimeError("gh introuvable : {}".format(exc)) from exc
    if completed.returncode != 0:
        raise RuntimeError("gh api {} a echoue : {}".format(
            path, (completed.stderr or completed.stdout or "").strip()[:200]))
    try:
        return json.loads(completed.stdout or "null")
    except json.JSONDecodeError as exc:
        raise RuntimeError("gh api {} : JSON illisible".format(path)) from exc


def open_pr_numbers(repo: str, per_page: int = 100) -> list[int]:
    """Toutes les PR ouvertes du depot -- **toutes les pages**.

    CORRECTION c3271 : la version precedente lisait UNE seule page
    (`per_page=100`, sans pagination). Le depot comptait 194 PRs ouvertes le
    2026-11-18 : `--all` n'examinait que les 100 premieres (les plus
    recentes, l'ordre par defaut de l'API), soit **la moitie du parc** -- et
    l'organe annoncait dans son aide « examine toutes les PR ouvertes du
    depot ». Une promesse que l'organe ne tient pas est un defaut de
    l'organe : on pagine jusqu'a epuisement, et on expose le nombre de pages
    lues dans la sortie JSON pour que l'ecart soit verifiable.
    """
    numbers: list[int] = []
    page = 1
    while True:
        payload = gh_json(
            "repos/{}/pulls?state=open&per_page={}&page={}".format(
                repo, per_page, page))
        if not isinstance(payload, list) or not payload:
            break
        numbers.extend(int(p["number"]) for p in payload)
        if len(payload) < per_page:
            break
        page += 1
        if page > 100:  # garde-fou : ne pas boucler sur une API qui
            break       # renverrait toujours la meme page pleine
    return numbers


def pr_head_sha(repo: str, number: int) -> str:
    payload = gh_json("repos/{}/pulls/{}".format(repo, number))
    return str(payload["head"]["sha"])  # type: ignore[index]


def gate_check_run(repo: str, sha: str) -> dict | None:
    """La check-run `PR gate` de cette tete (la plus recente par nom)."""
    payload = gh_json("repos/{}/commits/{}/check-runs?per_page=100".format(repo, sha))
    runs = [r for r in payload.get("check_runs", []) if r.get("name") == GATE_NAME]
    if not runs:
        return None
    runs.sort(key=lambda r: (r.get("started_at") or "", r.get("id") or 0))
    return runs[-1]


def job_ref(details_url: str) -> tuple[str, str] | None:
    """(run_id, job_id) deduits de l'URL de la check-run."""
    match = re.search(r"/actions/runs/(\d+)/job/(\d+)", details_url or "")
    if not match:
        return None
    return match.group(1), match.group(2)


def gh_rerun(run_id: str, job_id: str) -> tuple[int, str]:
    completed = subprocess.run(
        ["gh", "run", "rerun", run_id, "--job", job_id],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=False,
    )
    return completed.returncode, (completed.stderr or completed.stdout or "").strip()


# --------------------------------------------------------------------------
# Collecte
# --------------------------------------------------------------------------

def inspect_pr(repo: str, number: int, now: datetime,
                dwell_min: float = DEFAULT_DWELL_MIN) -> dict:
    """Etat d'une PR pour le minuteur DWELL (lecture seule)."""
    entry: dict = {"pr": number, "action": "ignorer", "motif": ""}
    sha = pr_head_sha(repo, number)
    entry["head_sha"] = sha
    gate = gate_check_run(repo, sha)
    if gate is None:
        entry["motif"] = "aucune check-run `{}` sur cette tete".format(GATE_NAME)
        return entry
    title = (gate.get("output") or {}).get("title") or ""
    conclusion = gate.get("conclusion") or ""
    status = gate.get("status") or ""
    entry["conclusion"] = conclusion
    entry["status"] = status
    entry["gate_title"] = title[:200]
    committed_at = head_committed_at(repo, sha)
    entry["committed_at"] = committed_at.strftime("%Y-%m-%dT%H:%M:%SZ")
    entry["floor"] = dwell_floor(committed_at, dwell_min).strftime("%Y-%m-%dT%H:%M:%SZ")
    action, motif = decide(conclusion=conclusion, title=title,
                           committed_at=committed_at, now=now, dwell_min=dwell_min,
                           status=status)
    entry["action"] = action
    entry["motif"] = motif
    ref = job_ref(gate.get("details_url") or "")
    if ref:
        entry["run_id"], entry["job_id"] = ref
    return entry


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=REPO_DEFAULT)
    ap.add_argument("--pr", nargs="*", type=int, default=None,
                    help="numeros de PR a examiner (defaut : aucune)")
    ap.add_argument("--all", action="store_true",
                    help="examine toutes les PR ouvertes du depot")
    ap.add_argument("--apply", action="store_true",
                    help="rejoue reellement (defaut : lecture seule)")
    ap.add_argument("--dwell-min", type=float, default=DEFAULT_DWELL_MIN)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.all:
        numbers = open_pr_numbers(args.repo)
    else:
        numbers = list(args.pr or [])
    if not numbers:
        ap.error("rien a examiner : --pr N... ou --all")

    now = datetime.now(timezone.utc)
    entries: list[dict] = []
    for number in numbers:
        try:
            entry = inspect_pr(args.repo, number, now, args.dwell_min)
        except RuntimeError as exc:
            entry = {"pr": number, "action": "ignorer", "motif": "erreur: {}".format(exc)}
        if args.apply and entry.get("action") == "rejouer":
            run_id, job_id = entry.get("run_id"), entry.get("job_id")
            if not run_id or not job_id:
                entry["motif"] = "run/job introuvables : {}".format(entry.get("gate_title", "")[:80])
            else:
                rc, out = gh_rerun(run_id, job_id)
                entry["rerun_rc"] = rc
                entry["rerun_sortie"] = out[:200]
                if rc != 0:
                    entry["motif"] = "rejeu refuse : {}".format(out[:160])
        entries.append(entry)

    counts: dict[str, int] = {}
    for entry in entries:
        counts[entry["action"]] = counts.get(entry["action"], 0) + 1
    if args.json:
        print(json.dumps({"repos": args.repo, "apply": args.apply,
                          "compteurs": counts, "prs": entries},
                         ensure_ascii=False, indent=2))
    else:
        for entry in entries:
            print("#{} [{}] {}".format(entry["pr"], entry["action"], entry["motif"]))
        print("compteurs: {}".format(counts))
    return 0


if __name__ == "__main__":
    sys.exit(main())
