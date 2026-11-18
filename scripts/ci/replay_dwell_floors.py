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


def emitter_floor(title: str) -> tuple[datetime, datetime, float] | None:
    """`(plancher brut, head_at, dwell_min)` lus dans le message de l'emetteur.

    Le plancher n'est plus **recalcule** par l'organe : il est **lu** dans le
    message que l'emetteur a produit pour la tete exacte. `head_at` est la
    date de `last_authoritative_committed_at()` -- le dernier commit qui
    **modifie le cote PR** -- et `dwell_min` est le dwell que l'emetteur a
    reellement applique (il peut differer du defaut du module).

    Pourquoi (c3271, exige du coordinateur) : l'organe recalculait le
    plancher depuis la date de **tete**. Apres un `update-branch` **sans
    conflit**, la date de tete est plus recente que `head_at` -- le
    rafraichissement de base est *prouve* content-free, il ne rearme donc pas
    le plancher -- et le plancher de l'organe etait **plus tardif** que celui
    de l'emetteur : l'organe disait « attendre » la ou le gate disait deja
    « plancher ecoule ». Un plancher **lu** ne peut pas diverger de celui qui
    l'a produit.
    """
    parsed = parse_pending_message(title or "")
    if not parsed:
        return None
    head_at = parse_iso8601(parsed["head_at"])
    dwell_min = float(parsed["dwell_min"])
    return head_at + timedelta(minutes=dwell_min), head_at, dwell_min


def decide(
    *,
    conclusion: str,
    title: str,
    committed_at: datetime,
    now: datetime,
    dwell_min: float = DEFAULT_DWELL_MIN,
    waived: bool = False,
    status: str = "completed",
    draft: bool = False,
) -> tuple[str, str]:
    """Decide quoi faire d'une jambe `PR gate`. Fonction PURE.

    Renvoie `(action, motif)` avec `action` dans :
      - ``"rejouer"``  : le plancher brut est passe, la jambe est un minuteur ;
      - ``"attendre"`` : plancher brut pas encore passe, ou jambe EN COURS ;
      - ``"ignorer"``  : rien a faire (legende verte, derogation, brouillon,
        rouge reel).

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

    Le plancher est celui de l'**emetteur** (`emitter_floor`), pas un recalcul
    depuis `committed_at` : voir la note de `emitter_floor`. `committed_at` et
    `dwell_min` ne servent plus qu'a l'affichage et a la compatibilite de
    l'appel ; le verdict, lui, sort du message.

    Une `head_at` **dans le futur** (decalage d'horloge entre l'hote qui a
    produit le message et celui qui le lit) ne vaut pas un plancher ecoule :
    fail-CLOSED.
    """
    if draft:
        return "ignorer", ("PR en brouillon -- exclue par conception "
                           "(comme le balayeur `pr-gate-stale-sweep.yml`), "
                           "jamais rejouee")
    if conclusion == "success":
        return "ignorer", "jambe verte"
    if waived:
        return "ignorer", "derogation par label `{}`".format(WAIVER_LABEL)
    if status and status != "completed":
        return "attendre", "jambe en cours (statut `{}`)".format(status)
    plancher = emitter_floor(title)
    if plancher is None:
        return "ignorer", "echec qui n'est pas le minuteur DWELL (rouge reel)"
    floor, head_at, _dwell_reel = plancher
    if head_at > now:
        return "attendre", ("tete datee dans le futur ({}) -- fail-CLOSED".format(
            head_at.strftime("%Y-%m-%dT%H:%M:%SZ")))
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


def pr_info(repo: str, number: int) -> dict:
    """Ce qu'il faut de la PR pour decider : tete, labels, etat brouillon.

    Les `labels` et le `draft` sont lus dans la **meme** charge utile que la
    tete : une derogation ne peut etre annoncee respectee que si ses labels
    ont ete **lus** (point 7 du coordinateur, c3271), et un brouillon doit
    etre identifiable pour etre mis a part (point 3 du message de 22:46Z).
    """
    payload = gh_json("repos/{}/pulls/{}".format(repo, number))
    if not isinstance(payload, dict):
        raise RuntimeError("PR {} : charge utile illisible".format(number))
    head = payload.get("head")
    head = head if isinstance(head, dict) else {}
    labels = payload.get("labels")
    labels = labels if isinstance(labels, list) else []
    return {
        "sha": str(head.get("sha") or ""),
        "labels": [str(l.get("name") or "") for l in labels
                   if isinstance(l, dict)],
        "draft": bool(payload.get("draft")),
    }


def gate_check_run(repo: str, sha: str, per_page: int = 100,
                  max_pages: int = 20) -> tuple[dict | None, bool]:
    """`(la check-run `PR gate` la plus recente, couverture complete ?)`.

    CORRECTION c3271 (point 2 du coordinateur) : la lecture ne se limitait pas
    a la premiere page. Au-dela de 100 check-runs sur une tete, la liste est
    **tronquee** et la jambe `PR gate` peut ne pas y etre : decider sur une
    lecture partielle reviendrait a decider sur une absence, et « pas de
    check-run trouve » n'est **pas** une absence. La couverture est donc
    signalee, et l'appelant **refuse de decider** sur une lecture incomplete.
    """
    runs: list[dict] = []
    complete = True
    page = 1
    while True:
        payload = gh_json(
            "repos/{}/commits/{}/check-runs?per_page={}&page={}".format(
                repo, sha, per_page, page))
        if not isinstance(payload, dict):
            raise RuntimeError("check-runs illisibles pour {}".format(sha))
        chunk = payload.get("check_runs")
        chunk = chunk if isinstance(chunk, list) else []
        runs.extend(r for r in chunk if isinstance(r, dict))
        if len(chunk) < per_page:
            break
        page += 1
        if page > max_pages:
            complete = False
            break
    gates = [r for r in runs if r.get("name") == GATE_NAME]
    if not gates:
        return None, complete
    gates.sort(key=lambda r: (r.get("started_at") or "", r.get("id") or 0))
    return gates[-1], complete


def job_ref(details_url: str) -> tuple[str, str] | None:
    """(run_id, job_id) deduits de l'URL de la check-run."""
    match = re.search(r"/actions/runs/(\d+)/job/(\d+)", details_url or "")
    if not match:
        return None
    return match.group(1), match.group(2)


def gh_rerun(run_id: str, job_id: str, repo: str = REPO_DEFAULT) -> tuple[int, str]:
    """Rejoue une jambe. `--repo` est **explicite** (c3271, point 3).

    Sans `--repo`, `gh run rerun` agit sur le depot du **repertoire courant**
    de l'appelant : l'organe pouvait rejouer un run d'un autre depot -- ou
    echouer sur un depot sans ce run -- alors qu'il mesure un repo donne.
    """
    completed = subprocess.run(
        ["gh", "run", "rerun", run_id, "--job", job_id, "--repo", repo],
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
    info = pr_info(repo, number)
    sha = info["sha"]
    entry["head_sha"] = sha
    entry["draft"] = info["draft"]
    entry["labels_lus"] = True
    gate, couverture = gate_check_run(repo, sha)
    if not couverture:
        entry["action"] = "incomplet"
        entry["motif"] = ("couverture des check-runs INCOMPLETE -- lecture "
                          "partielle, aucune decision prise")
        return entry
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
    # Plancher de l'EMETTEUR (lu dans le message), et non recalcule : les deux
    # peuvent diverger apres un `update-branch` sans conflit.
    plancher = emitter_floor(title)
    if plancher is not None:
        floor, head_at, dwell_reel = plancher
        entry["head_at_emetteur"] = head_at.strftime("%Y-%m-%dT%H:%M:%SZ")
        entry["dwell_min_emetteur"] = dwell_reel
        entry["floor"] = floor.strftime("%Y-%m-%dT%H:%M:%SZ")
    else:
        entry["floor"] = dwell_floor(committed_at, dwell_min).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
    # Derogation : annoncee seulement si les labels ont ete LUS (ils viennent
    # de la meme charge utile que la tete).
    waived = WAIVER_LABEL in info["labels"]
    entry["derogation"] = waived
    action, motif = decide(conclusion=conclusion, title=title,
                           committed_at=committed_at, now=now, dwell_min=dwell_min,
                           status=status, waived=waived, draft=info["draft"])
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
    echecs = 0            # geste rate (rejeu refuse) ou PR illisible
    incomplets = 0        # lecture incomplete -> aucune decision possible
    for number in numbers:
        try:
            entry = inspect_pr(args.repo, number, now, args.dwell_min)
        except RuntimeError as exc:
            entry = {"pr": number, "action": "erreur", "motif": "erreur: {}".format(exc)}
            echecs += 1
        if entry.get("action") == "incomplet":
            incomplets += 1
        if args.apply and entry.get("action") == "rejouer":
            run_id, job_id = entry.get("run_id"), entry.get("job_id")
            if not run_id or not job_id:
                entry["motif"] = "run/job introuvables : {}".format(
                    entry.get("gate_title", "")[:80])
                entry["rerun_rc"] = 1
                echecs += 1
            else:
                rc, out = gh_rerun(run_id, job_id, args.repo)
                entry["rerun_rc"] = rc
                entry["rerun_sortie"] = out[:200]
                if rc != 0:
                    entry["motif"] = "rejeu refuse : {}".format(out[:160])
                    echecs += 1
        entries.append(entry)

    counts: dict[str, int] = {}
    for entry in entries:
        counts[entry["action"]] = counts.get(entry["action"], 0) + 1
    brouillons = sum(1 for e in entries if e.get("draft"))
    # Un rejeu refuse doit etre **visible** par le consommateur : l'organe
    # sortait 0 meme apres un echec du geste (c3271, point 4). Ici :
    #   0 = lecture seule, ou tous les gestes tentes ont reussi ;
    #   1 = au moins un geste rate (rejeu refuse) ;
    #   2 = inventaire incomplet (PR illisible ou couverture tronquee).
    rc_final = 1 if echecs else (2 if incomplets else 0)
    if args.json:
        print(json.dumps({"repos": args.repo, "apply": args.apply,
                          "rc": rc_final, "echecs": echecs,
                          "incomplets": incomplets, "brouillons": brouillons,
                          "compteurs": counts, "prs": entries},
                         ensure_ascii=False, indent=2))
    else:
        for entry in entries:
            print("#{} [{}] {}".format(entry["pr"], entry["action"], entry["motif"]))
        print("compteurs: {} (brouillons: {})".format(counts, brouillons))
    return rc_final


if __name__ == "__main__":
    sys.exit(main())
