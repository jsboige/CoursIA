#!/usr/bin/env python3
"""Lot quotidien en ombre : selection des PRs et mesure de la duree.

P3 du plan « CI a deux etages » (#25510). Le PR gate reste, pour l'instant,
le seul juge d'une PR : ce lot ne **bloque** rien, il mesure. Sa valeur est
double :

1. **La selection.** Quelles PRs traiter dans le lot, et selon quelles regles.
   Le verdict de revue est lu dans les **corps** -- jamais dans
   `reviewDecision`, qui vaut `null` a perpetuite sous token COMMENT-only
   (l'ecart est mesure et consigne dans `pool_review_verdicts.py`). Le
   classement de ce module reutilise cet organe : on ne reimplementerait pas
   une lecture de verdict qui a deja couté cher.
2. **La mesure.** Duree d'un lot vert, duree d'un lot rouge, et **fin de lot
   avant l'echeance** de son creneau. Quatre creneaux par jour (UTC) :

   | Creneau | Echeance de fin |
   |---|---|
   | 04:30 | 10:00 |
   | 10:30 | 13:00 |
   | 16:30 | 21:30 |
   | 21:30 | 00:00 (le lendemain) |

   Un lot qui deborde son creneau retarde le suivant : la cadence est alors
   rompue, et c'est la **mesure** de ce debordement qui decide de la suite.

Regles de selection (dans cet ordre) :

- **Garde fork** : une PR issue d'un fork n'entre dans le lot qu'apres
  l'APPROVE du coordinateur (`myia-ai-01`). Le job du lot tourne sans aucun
  secret et avec des permissions minimales : le code d'un fork s'execute
  donc sans rien pouvoir lire ni ecrire de sensible.
- **Verdict** : la PR doit porter un verdict d'approbation, lu dans les corps
  (`APPROVED`, `LGTM`). Une PR sans voix, ou avec une reserve, n'occupe pas
  un creneau de runner.
- **Anciennete** : les plus anciennes d'abord -- une PR qui vieillit est une
  PR que le lot doit servir avant une autre.

**L'arbre d'integration** (phase d'integration) :

Le lot ne teste pas chaque PR isolement. Il construit l'arbre **qui va
reellement atterrir** -- `main` plus les PRs du lot, dans l'ordre du lot --
et joue la suite lourde dessus. C'est la seule forme qui supprime par
construction la classe de #24821 (`main` rouge apres le merge de PRs vertes
a leur propre tete).

Quand l'arbre est rouge, la PR fautive est isolee par **`git bisect run`**
(l'organe natif), jamais par une recherche maison. Chaque fusion porte le
sujet `lot: PR #N` : le commit que la bissection isole porte donc le numero
de la PR, et le coupable est **nomme** sans table de correspondance externe.

Usage :
    python scripts/ci/heavy_batch.py --repo jsboige/CoursIA --max-prs 4 --json
    python scripts/ci/heavy_batch.py --slot
    python scripts/ci/heavy_batch.py --results .tmp/batch_results.json
    python scripts/ci/heavy_batch.py --run --plan .tmp/plan.json --integration
    git bisect run python scripts/ci/heavy_batch.py --bisect-run

Exit 0 = lot produit (ou resume produit). Exit 2 = instrument ou donnees
illisibles -- jamais un lot vide presente comme un lot vert.

En mode `--bisect-run`, le code de sortie est celui que `git bisect run`
attend : 0 (bon), 1 (mauvais), 125 (indetermine -- ce commit ne se teste
pas). Ce mode est **le** commande de la bissection : il ne lit aucun etat du
depot, il teste et rend un code.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

CI_DIR = Path(__file__).resolve().parents[1]
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import pool_review_verdicts as pool  # noqa: E402

DEFAULT_REPO = "jsboige/CoursIA"

#: Le coordinateur : son APPROVE est la porte d'entree des PRs de fork.
COORDINATOR_LOGIN = "myia-ai-01"

#: Verdicts qui autorisent une PR a occuper un creneau de runner. Lus dans
#: les corps par `pool_review_verdicts.classify_pr`.
APPROVING_VERDICTS = frozenset({"APPROVED", "LGTM"})

#: Nombre de PRs detaillees par lot. La liste complete des PRs ouvertes est
#: lisible en une passe legere ; le detail (verdict, approbation) est lu sur
#: une liste courte, parce que la lecture en une passe de 100 PRs fait
#: echouer la requete GraphQL sur la limite de ressources.
SHORTLIST = 15

#: La suite **lourde** : ce que l'etage 2 joue sur l'arbre d'integration.
#: C'est la suite de tests du depot, pas la selection ciblee de P2 -- l'etage
#: 2 teste l'arbre entier, c'est ce qui le distingue de l'etage 1.
HEAVY_TARGET = ("scripts/tests",)


class Slot:
    """Un creneau de lot : une heure de depart et une echeance de fin (UTC)."""

    def __init__(self, name: str, start: tuple[int, int], deadline: tuple[int, int]) -> None:
        self.name = name
        self.start = start
        self.deadline = deadline

    @property
    def start_minutes(self) -> int:
        return self.start[0] * 60 + self.start[1]

    @property
    def deadline_minutes(self) -> int:
        return self.deadline[0] * 60 + self.deadline[1]

    def as_dict(self) -> dict[str, Any]:
        return {
            "nom": self.name,
            "debut_utc": f"{self.start[0]:02d}:{self.start[1]:02d}",
            "echeance_utc": f"{self.deadline[0] % 24:02d}:{self.deadline[1]:02d}",
        }


#: Les quatre creneaux du plan (UTC). L'echeance du dernier creneau est
#: celle du lendemain 00:00.
SLOTS: tuple[Slot, ...] = (
    Slot("creneau-1", (4, 30), (10, 0)),
    Slot("creneau-2", (10, 30), (13, 0)),
    Slot("creneau-3", (16, 30), (21, 30)),
    Slot("creneau-4", (21, 30), (24, 0)),
)


def active_slot(now: datetime) -> Slot | None:
    """Creneau actif a l'instant donne.

    Fonction pure : elle ne lit pas l'horloge, elle raisonne sur l'instant
    qu'on lui donne -- c'est ce qui la rend testable. Les quatre fenetres
    pavent la journee, la derniere a cheval sur minuit (21:30 -> 04:30).
    """
    minutes = now.hour * 60 + now.minute
    for index, slot in enumerate(SLOTS):
        following = SLOTS[(index + 1) % len(SLOTS)]
        if index == len(SLOTS) - 1:
            # fenetre a cheval sur minuit
            if minutes >= slot.start_minutes or minutes < following.start_minutes:
                return slot
        elif slot.start_minutes <= minutes < following.start_minutes:
            return slot
    return None


def build_entry(
    node: dict[str, Any],
    *,
    verdict: str | None = None,
    approved_by_coordinator: bool | None = None,
) -> dict[str, Any]:
    """Normalise une PR en fiche de lot (fonction pure).

    `verdict` et `approved_by_coordinator` peuvent etre fournis : la lecture
    en ligne les calcule depuis le noeud complet, la lecture par phases les
    fournit deja calcules (c'est plus econome sur l'API).
    """
    reviews = node.get("reviews") or []
    comments = node.get("comments") or []
    if verdict is None:
        verdict = pool.classify_pr(
            {
                "number": node.get("number"),
                "title": node.get("title") or "",
                "createdAt": node.get("createdAt") or "",
                "mergeStateStatus": node.get("mergeStateStatus") or "",
                "reviewDecision": node.get("reviewDecision"),
                "reviews": {"nodes": reviews},
                "comments": {"nodes": comments},
            }
        )["verdict"]
    if approved_by_coordinator is None:
        approved_by_coordinator = any(
            (review.get("author") or {}).get("login") == COORDINATOR_LOGIN
            and (review.get("state") or "") == "APPROVED"
            for review in reviews
        )
    return {
        "number": node.get("number"),
        "title": node.get("title") or "",
        "created_at": node.get("createdAt") or "",
        "fork": bool(node.get("isCrossRepository")),
        "approved_by_coordinator": approved_by_coordinator,
        "verdict": verdict,
        "merge_state_status": node.get("mergeStateStatus") or "",
    }


def select_batch(
    entries: list[dict[str, Any]], max_prs: int
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Choisit les PRs du lot et nomme l'exclusion de chacune des autres.

    Fonction pure : elle raisonne sur des fiches deja normalisees, sans lire
    l'API. L'ordre est l'anciennete (la plus ancienne d'abord) -- une PR qui
    vieillit passe avant les autres.
    """
    ordered = sorted(entries, key=lambda e: (e.get("created_at") or "", e.get("number") or 0))
    selected: list[dict[str, Any]] = []
    excluded: list[dict[str, Any]] = []
    for entry in ordered:
        if len(selected) >= max_prs:
            excluded.append({**entry, "motif": "lot plein (taille maximale atteinte)"})
            continue
        if entry["fork"] and not entry["approved_by_coordinator"]:
            excluded.append({**entry, "motif": "PR de fork sans l'APPROVE du coordinateur"})
            continue
        if entry["verdict"] not in APPROVING_VERDICTS:
            excluded.append({**entry, "motif": f"verdict {entry['verdict']}"})
            continue
        selected.append(entry)
    return selected, excluded


def has_coordinator_approval(repo: str, number: int) -> bool:
    """Vrai si le coordinateur a APPROVE la PR.

    Lecture REST leger (les reviews d'une PR), et non le champ
    `reviewDecision` : ce dernier vaut `null` a perpetuite sous token
    COMMENT-only (mesure de `pool_review_verdicts.py`).
    """
    try:
        raw = pool.run_gh(["api", f"repos/{repo}/pulls/{number}/reviews", "--paginate"])
    except RuntimeError:
        return False
    try:
        reviews = json.loads(raw)
    except ValueError:
        return False
    if not isinstance(reviews, list):
        return False
    return any(
        (review.get("user") or {}).get("login") == COORDINATOR_LOGIN
        and (review.get("state") or "") == "APPROVED"
        for review in reviews
    )


def fetch_entries(repo: str, limit: int) -> list[dict[str, Any]]:
    """Lit les PRs ouvertes du depot, en deux phases bornees.

    Phase 1 : une liste legere (`number`, `createdAt`, `isCrossRepository`).
    Phase 2 : les PRs les plus anciennes sont detaillees -- verdict lu par
    l'organe `pool_review_verdicts`, approbation du coordinateur lue en REST.

    La lecture en une seule passe serait trop lourde : demander les reviews
    ET les commentaires de 100 PRs d'un coup fait **echouer** la requete
    GraphQL sur la limite de ressources (mesure firsthand sur ce depot le
    2026-11-09). La liste courte est donc la forme qui passe.
    """
    raw = pool.run_gh(
        [
            "pr",
            "list",
            "--repo",
            repo,
            "--state",
            "open",
            # Les plus anciennes d'abord : c'est l'ordre du tapis, et c'est
            # la liste qui agedit (une PR qui vieillit doit passer avant une
            # PR fraiche). `gh pr list` n'a pas de `--sort` : le tri se
            # demande par la recherche.
            "--search",
            "sort:created-asc",
            "--limit",
            str(limit),
            "--json",
            "number,title,createdAt,isCrossRepository",
        ]
    )
    nodes = json.loads(raw)
    if not isinstance(nodes, list):
        raise RuntimeError("payload gh inattendu (liste attendue)")
    nodes.sort(key=lambda node: node.get("createdAt") or "")
    shortlist = nodes[:SHORTLIST]
    numbers = [int(node["number"]) for node in shortlist]
    classified = pool.fetch_prs(repo, numbers)
    entries = []
    for node in shortlist:
        number = int(node["number"])
        detail = classified.get(number) or {}
        entries.append(
            build_entry(
                node,
                verdict=detail.get("verdict") or "SANS-REVIEW",
                approved_by_coordinator=has_coordinator_approval(repo, number),
            )
        )
    return entries


def pr_dispatched_autorise(entry: dict[str, Any]) -> tuple[bool, str]:
    """Une PR designee par le coordinateur entre-t-elle dans le lot ?

    La garde fork n'est pas negociable : le lot execute du code de PR sur
    nos runners, et une PR de fork n'y entre qu'apres l'APPROVE du
    coordinateur. **Une designation ne leve pas cette garde** -- la
    designation autorise le test, elle n'autorise pas l'execution d'un code
    de fork.

    La regle de verdict, elle, est couverte par la designation : le
    coordinateur demande *ce* test-la.

    Fonction pure : elle raisonne sur la fiche, sans lire l'API.
    """
    if entry.get("fork") and not entry.get("approved_by_coordinator"):
        return False, "PR de fork sans l'APPROVE du coordinateur"
    return True, ""


def fetch_entry_for_pr(repo: str, number: int) -> dict[str, Any]:
    """Fiche de lot d'UNE PR, lue en REST.

    Sert la voie « avance du coordinateur » : une PR precise, tout de suite.
    Le verdict est lu par l'organe `pool_review_verdicts` (les corps), et
    l'approbation du coordinateur en REST.
    """
    raw = pool.run_gh(["api", f"repos/{repo}/pulls/{number}"])
    node = json.loads(raw)
    head_repo = ((node.get("head") or {}).get("repo") or {}).get("full_name")
    base_repo = ((node.get("base") or {}).get("repo") or {}).get("full_name")
    detail = pool.fetch_prs(repo, [number]).get(number) or {}
    return build_entry(
        {
            "number": number,
            "title": node.get("title") or "",
            "createdAt": node.get("created_at") or "",
            "isCrossRepository": bool(head_repo and base_repo and head_repo != base_repo),
        },
        verdict=detail.get("verdict") or "SANS-REVIEW",
        approved_by_coordinator=has_coordinator_approval(repo, number),
    )


def summarize(results: dict[str, Any], now: datetime) -> dict[str, Any]:
    """Mesure d'un lot : duree, fin dans les temps, etat par PR.

    Fonction pure : elle lit un resultat de lot deja produit et le rend. Le
    creneau de reference est celui du lot lui-meme (son heure de **debut**),
    pas celui de l'instant de la lecture : un lot lance a 04:30 qui se termine
    a 11:00 doit etre juge sur l'echeance de 10:00, pas sur celle du creneau
    suivant. La comparaison se fait en **ecart au debut du creneau**, ce qui
    rend le cas du dernier creneau (echeance a minuit le lendemain) correct.
    """
    started = results.get("started_at")
    finished = results.get("finished_at")
    duration_s = results.get("duration_s")

    anchor: datetime | None = None
    if started:
        try:
            anchor = _parse_iso(started)
        except ValueError:
            anchor = None
    slot = active_slot(anchor) if anchor is not None else active_slot(now)

    if duration_s is None and started and finished:
        try:
            delta = _parse_iso(finished) - _parse_iso(started)
            duration_s = delta.total_seconds()
        except ValueError:
            duration_s = None
    within = None
    if slot is not None and finished and anchor is not None:
        try:
            end = _parse_iso(finished)
        except ValueError:
            end = None
        if end is not None:
            elapsed = (end.hour * 60 + end.minute - slot.start_minutes) % (24 * 60)
            allowed = (slot.deadline_minutes - slot.start_minutes) % (24 * 60)
            within = elapsed <= allowed
    prs = results.get("prs") or []
    integration = results.get("integration") or {}
    arbre = integration.get("arbre") or {}
    bissection = integration.get("bissection") or {}
    return {
        "creneau": slot.as_dict() if slot else None,
        "duree_lot_s": duration_s,
        "fin_avant_echeance": within,
        "prs_concernes": len(prs),
        "prs_rouges": sum(1 for p in prs if (p.get("statut") or "") == "rouge"),
        "prs": prs,
        "arbre_integration": {
            "statut": integration.get("statut"),
            "prs_integrees": arbre.get("prs_integrees") or [],
            "conflits": arbre.get("conflits") or [],
            "pr_coupable": bissection.get("pr_coupable"),
            "bissection": bissection.get("statut"),
        },
    }


def _parse_iso(value: str) -> datetime:
    """Lit un horodatage ISO ; sans fuseau, on suppose UTC."""
    parsed = datetime.fromisoformat(value)
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed


# --- Execution du lot ------------------------------------------------------


def run_git(root: Path, args: list[str], check: bool = True) -> tuple[int, str]:
    """Execute une commande git dans la racine du depot."""
    proc = subprocess.run(
        ["git", "-C", str(root), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if check and proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or "git a echoue").strip()[:300])
    return proc.returncode, proc.stdout


# --- Arbre d'integration et bissection -------------------------------------
#
# L'etage 2 du plan (#25510) ne teste pas chaque PR isolement : il teste
# l'arbre **qui va reellement atterrir** -- `main` plus les PRs du lot, dans
# l'ordre du lot. C'est la seule forme qui supprime par construction la
# classe de #24821 (`main` rouge apres le merge de PRs vertes a leur propre
# tete).
#
# Deuxapingots natifs sont utilises, jamais reimplementes :
#
#   - `git merge` construit l'arbre (un worktree jetable, un commit de fusion
#     par PR) ;
#   - `git bisect run` isole la PR fautive quand l'arbre est rouge.
#
# Le lien entre les deux est le **sujet du commit** : chaque fusion porte
# `lot: PR #N`. La bissection trouve un commit ; le commit porte le numero de
# la PR. C'est ce qui rend le coupable **nomme** sans table de correspondance
# externe.

#: Sujet du commit de fusion d'une PR dans l'arbre d'integration.
MERGE_SUBJECT = "lot: PR #{number}"

#: Identite imposee au commit de fusion : un runner GitHub Actions n'a pas
#: forcement de `user.name` configure, et un commit sans identite est refuse.
MERGE_IDENTITY = (
    "-c",
    "user.name=heavy-batch",
    "-c",
    "user.email=heavy-batch@localhost",
)

#: Codes de sortie de `git bisect run` : 0 = bon, 1 = mauvais, 125 =
#: indetermine (ce commit ne se teste pas). Tout autre code >= 126 annule la
#: bissection.
BISECT_GOOD = 0
BISECT_BAD = 1
BISECT_SKIP = 125

#: Marqueurs d'une sortie pytest qui rend la mesure **impossible** (pas
#: rouge) : une dependance absente n'est pas une regression.
UNMEASURABLE_MARKERS = ("ModuleNotFoundError", "ImportError while importing")


def pr_number_from_subject(subject: str | None) -> int | None:
    """Numero de la PR que porte le commit d'une fusion.

    Fonction pure : elle lit le **sujet** du commit. Un sujet qui ne porte
    pas la marque rend `None` -- un commit qui n'est pas un des nôtres n'est
    jamais designe comme coupable.
    """
    match = re.search(r"lot: PR #(\d+)", subject or "")
    return int(match.group(1)) if match else None


def _rev_parse(root: Path, rev: str) -> str | None:
    """SHA d'une revision, ou None si elle est illisible."""
    try:
        code, out = run_git(root, ["rev-parse", rev], check=False)
    except Exception:  # noqa: BLE001 -- une revision absente n'est pas fatale
        return None
    value = (out or "").strip()
    return value if code == 0 and value else None


def _commit_subject(root: Path, rev: str = "HEAD") -> str | None:
    """Sujet d'un commit, ou None s'il est illisible."""
    try:
        code, out = run_git(root, ["log", "-1", "--format=%s", rev], check=False)
    except Exception:  # noqa: BLE001
        return None
    value = (out or "").strip()
    return value if code == 0 and value else None


def build_integration_tree(
    root: Path, numbers: list[int], work_root: Path, dry_run: bool = False
) -> dict[str, Any]:
    """Construit l'arbre d'integration : `main` plus les PRs du lot, dans l'ordre.

    L'arbre vit dans un worktree **jetable**. Chaque PR du lot est fusionnee
    dans l'ordre du lot ; un conflit est **nomme** (le numero de la PR) et la
    PR sort de l'arbre -- elle n'est pas reputee verte pour autant : elle
    n'est pas testee du tout.

    Une PR dont la ref de fusion est absente (fetch impossible) est pareil
    nommee, jamais silencieuse.
    """
    tree = work_root / "integration"
    record: dict[str, Any] = {
        "chemin": str(tree),
        "base": None,
        "tip": None,
        "prs_integrees": [],
        "prs_introuvables": [],
        "conflits": [],
        "commits": [],
        "statut": "echec",
    }
    if dry_run:
        record["statut"] = "simulation"
        commandes = [
            " ".join(
                [
                    "git",
                    "-C",
                    str(root),
                    "fetch",
                    "--no-tags",
                    "origin",
                    f"+pull/{n}/merge:refs/pr/{n}/merge",
                ]
            )
            for n in numbers
        ]
        commandes.append(
            " ".join(
                ["git", "-C", str(root), "worktree", "add", "--detach", str(tree), "origin/main"]
            )
        )
        commandes.extend(
            " ".join(
                [
                    "git",
                    "-C",
                    str(tree),
                    "merge",
                    "--no-ff",
                    "-m",
                    MERGE_SUBJECT.format(number=n),
                    f"refs/pr/{n}/merge",
                ]
            )
            for n in numbers
        )
        record["commandes"] = commandes
        return record

    work_root.mkdir(parents=True, exist_ok=True)
    if tree.exists():
        run_git(root, ["worktree", "remove", "--force", str(tree)], check=False)
    for number in numbers:
        code, _ = run_git(
            root,
            ["fetch", "--no-tags", "origin", f"+pull/{number}/merge:refs/pr/{number}/merge"],
            check=False,
        )
        if code != 0:
            record["prs_introuvables"].append(number)
    code, _ = run_git(root, ["worktree", "add", "--detach", str(tree), "origin/main"], check=False)
    if code != 0:
        record["statut"] = "worktree-echoue"
        return record
    record["base"] = _rev_parse(tree, "HEAD")
    for number in numbers:
        if number in record["prs_introuvables"]:
            continue
        code, out = run_git(
            tree,
            [
                *MERGE_IDENTITY,
                "merge",
                "--no-ff",
                "-m",
                MERGE_SUBJECT.format(number=number),
                f"refs/pr/{number}/merge",
            ],
            check=False,
        )
        if code != 0:
            run_git(tree, ["merge", "--abort"], check=False)
            record["conflits"].append(
                {"pr": number, "detail": (out or "").strip().splitlines()[-1][:200] if out else ""}
            )
            continue
        sha = _rev_parse(tree, "HEAD")
        record["prs_integrees"].append(number)
        record["commits"].append({"pr": number, "commit": sha})
    record["tip"] = _rev_parse(tree, "HEAD")
    record["statut"] = "construit"
    return record


def run_heavy_suite(
    tree: Path, targets: list[str], timeout: int = 3600
) -> tuple[int, str]:
    """Lance la suite lourde dans l'arbre d'integration.

    Rend le code de sortie de pytest et la sortie (tronquee). Un
    `ModuleNotFoundError` ne rend pas la suite rouge : il la rend
    **indeterminee** -- c'est le traitement que fait l'appelant.
    """
    try:
        proc = subprocess.run(
            [sys.executable, "-m", "pytest", *targets, "-q", "--tb=short"],
            cwd=str(tree),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return 124, "delai depasse"
    except Exception as exc:  # noqa: BLE001 -- le lot ne doit pas mourir
        return 125, str(exc)[:300]
    return proc.returncode, ((proc.stdout or "") + (proc.stderr or ""))[-4000:]


def bisect_run(tree: Path, targets: list[str], timeout: int = 3600) -> int:
    """Une passe de bissection : le code de sortie que `git bisect run` attend.

    Cette fonction **est** la commande que `git bisect run` invoque : elle
    teste le commit courant et rend

    - `0` (bon) si la suite passe ;
    - `1` (mauvais) si la suite echoue ;
    - `125` (indetermine) si la suite ne peut pas etre executee ici --
      une dependance absente, une cible absente. C'est le code que `git
      bisect run` reserve a « ce commit ne se teste pas ».

    Elle ne lit **jamais** l'etat du depot : elle teste, et rend un code.
    """
    for target in targets:
        if not (tree / target).exists():
            # La cible n'existe pas dans ce commit : ce commit ne se teste
            # pas. C'est `indetermine`, pas `mauvais` -- sinon la bissection
            # accuserait un commit qui n'a jamais ete teste.
            return BISECT_SKIP
    rc, output = run_heavy_suite(tree, targets, timeout=timeout)
    if rc == 0:
        return BISECT_GOOD
    if any(marker in output for marker in UNMEASURABLE_MARKERS):
        return BISECT_SKIP
    if rc == 124:
        # Un delai depasse n'est pas une preuve de faute : c'est
        # indetermine, pas mauvais.
        return BISECT_SKIP
    return BISECT_BAD


def pr_culpable(tree: Path, culprit: str | None, merges: list[dict[str, Any]]) -> int | None:
    """La PR que porte le commit coupable.

    Deux lectures, dans cet ordre :

    1. **le sujet** du commit (``lot: PR #N``) -- c'est le cas quand la
       bissection s'arrete sur une fusion du lot ;
    2. **l'ascendance** : la premiere fusion du lot dont le commit contient
       le coupable. C'est le cas quand la bissection s'arrete sur un commit
       de la *branche* de la PR -- qui est bien un ancetre de sa fusion.

    La lecture par ascendance est la lecture de confiance : elle ne depend
    d'aucun nom. Elle est aussi ce qui rend le resultat juste quand la
    ref de fusion d'une PR est elle-meme un commit de fusion (c'est la
    forme que GitHub produit) : le coupable est alors un membre de l'ANCESTRE
    de la fusion, pas la fusion elle-meme.
    """
    if not culprit:
        return None
    direct = pr_number_from_subject(_commit_subject(tree, culprit))
    if direct is not None:
        return direct
    for merge in merges:
        sha = merge.get("commit")
        if not sha:
            continue
        code, _ = run_git(tree, ["merge-base", "--is-ancestor", culprit, sha], check=False)
        if code == 0:
            return int(merge["pr"])
    return None


def bisect_lot(
    tree: Path,
    base_commit: str | None,
    bad_commit: str | None,
    script: Path,
    targets: list[str],
    timeout: int = 3600,
    merges: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Isole la PR fautive par bissection native (`git bisect run`).

    L'organe est `git bisect` : on ne reimplemente ni la recherche du
    coupable ni la strategie de moitie. Le script passe en mode
    `--bisect-run` rend 0/1/125 selon le resultat de la suite.

    Le coupable est le commit sur lequel `git bisect` s'est arrete ; son
    **sujet** porte `lot: PR #N`, et c'est de la que vient le numero. Un
    sujet sans la marque rend `pr_coupable: None` : un commit qui n'est pas
    une fusion du lot n'est jamais accuse.
    """
    record: dict[str, Any] = {
        "statut": "echec",
        "pr_coupable": None,
        "commit": None,
        "sujet": None,
        "journal": "",
    }
    if not base_commit or not bad_commit:
        record["statut"] = "bornes-absentes"
        return record
    run_git(tree, ["bisect", "reset"], check=False)
    code, _ = run_git(tree, ["bisect", "start"], check=False)
    if code != 0:
        record["statut"] = "bisect-demarre-echoue"
        return record
    run_git(tree, ["bisect", "bad", bad_commit], check=False)
    run_git(tree, ["bisect", "good", base_commit], check=False)
    command = [
        sys.executable,
        str(script),
        "--bisect-run",
        "--bisect-target",
        *targets,
    ]
    try:
        proc = subprocess.run(
            ["git", "-C", str(tree), "bisect", "run", *command],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
        )
        record["journal"] = ((proc.stdout or "") + (proc.stderr or ""))[-3000:]
        record["code"] = proc.returncode
    except subprocess.TimeoutExpired:
        record["statut"] = "delai-depasse"
        run_git(tree, ["bisect", "reset"], check=False)
        return record
    culprit = _rev_parse(tree, "HEAD")
    subject = _commit_subject(tree, "HEAD")
    run_git(tree, ["bisect", "reset"], check=False)
    record["commit"] = culprit
    record["sujet"] = subject
    record["pr_coupable"] = pr_culpable(tree, culprit, merges or [])
    if record["pr_coupable"] is None:
        record["statut"] = "coupable-non-nomme"
    else:
        record["statut"] = "bissection-effectuee"
    return record


def plan_commands(
    root: Path, number: int, worktree: Path, selector: Path | None
) -> list[list[str]]:
    """Commandes que le lot executerait pour une PR donnee.

    Fonction pure : elle rend la liste des commandes, sans les lancer. C'est
    ce qui permet de tester le geste sans runner, et de le relire.
    """
    ref = f"refs/pr/{number}/merge"
    commands = [
        ["git", "-C", str(root), "fetch", "--no-tags", "origin", f"+pull/{number}/merge:{ref}"],
        ["git", "-C", str(root), "worktree", "add", "--detach", str(worktree), ref],
    ]
    if selector is not None:
        commands.append(
            [
                sys.executable,
                str(selector),
                "--repo-root",
                str(worktree),
                "--changed",
                "@DIFF",
                "--json",
            ]
        )
        commands.append([sys.executable, "-m", "pytest", "@TESTS", "-q", "--tb=short"])
    commands.append(["git", "-C", str(root), "worktree", "remove", "--force", str(worktree)])
    return commands


def run_one(
    root: Path,
    number: int,
    work_root: Path,
    selector: Path | None,
    dry_run: bool = False,
) -> dict[str, Any]:
    """Execute le lot sur une PR et rend sa mesure.

    La PR est materializee dans un worktree jetable ; les tests concernes
    sont designes par le selecteur (P2) ; la duree et le statut sont mesures.
    Une dependance manquante rend la PR **non mesurable** -- jamais rouge :
    un environnement incomplet n'est pas une regression.
    """
    started = time.monotonic()
    worktree = work_root / f"pr-{number}"
    record: dict[str, Any] = {"number": number, "statut": "echec", "duree_s": 0.0}
    try:
        if dry_run:
            commands = plan_commands(root, number, worktree, selector)
            record["statut"] = "simulation"
            record["commandes"] = [" ".join(c) for c in commands]
            return record

        ref = f"refs/pr/{number}/merge"
        code, _ = run_git(
            root, ["fetch", "--no-tags", "origin", f"+pull/{number}/merge:{ref}"], check=False
        )
        if code != 0:
            record["statut"] = "fetch-echoue"
            return record
        code, _ = run_git(root, ["worktree", "add", "--detach", str(worktree), ref], check=False)
        if code != 0:
            record["statut"] = "worktree-echoue"
            return record
        try:
            _, diff = run_git(root, ["diff", "--name-only", "origin/main", ref], check=False)
            changed = [line.strip() for line in diff.splitlines() if line.strip()]
            record["fichiers_touches"] = len(changed)
            if selector is None:
                record["statut"] = "selecteur-absent"
                return record
            select_cmd = [
                sys.executable,
                str(selector),
                "--repo-root",
                str(worktree),
                "--json",
            ]
            for path in changed:
                select_cmd += ["--changed", path]
            sel = subprocess.run(
                select_cmd, capture_output=True, text=True, encoding="utf-8", errors="replace"
            )
            if sel.returncode != 0:
                record["statut"] = "selecteur-echoue"
                record["detail"] = (sel.stderr or sel.stdout or "")[-300:]
                return record
            payload = json.loads(sel.stdout)
            tests = sorted(payload.get("selected") or {})
            record["tests_selectionnes"] = len(tests)
            record["tests_total_depot"] = (payload.get("stats") or {}).get("fichiers_de_test_du_depot")
            if not tests:
                record["statut"] = "aucun-test-concerne"
                return record
            pytest = subprocess.run(
                [sys.executable, "-m", "pytest", *tests, "-q", "--tb=short"],
                cwd=str(worktree),
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
            )
            output = (pytest.stdout or "") + (pytest.stderr or "")
            record["pytest_rc"] = pytest.returncode
            if "ModuleNotFoundError" in output or "ImportError while importing" in output:
                record["statut"] = "non-mesurable"
            elif pytest.returncode == 0:
                record["statut"] = "vert"
            else:
                record["statut"] = "rouge"
            record["resume"] = output.strip().splitlines()[-1][:200] if output.strip() else ""
        finally:
            run_git(root, ["worktree", "remove", "--force", str(worktree)], check=False)
            run_git(root, ["update-ref", "-d", f"refs/pr/{number}/merge"], check=False)
    except Exception as exc:  # noqa: BLE001 -- le lot ne doit pas mourir sur une PR
        record["statut"] = "erreur"
        record["detail"] = str(exc)[:300]
    record["duree_s"] = round(time.monotonic() - started, 1)
    return record


def run_batch(
    root: Path,
    plan: dict[str, Any],
    work_root: Path,
    selector: Path | None,
    dry_run: bool = False,
    integration: bool = False,
    heavy_target: list[str] | None = None,
) -> dict[str, Any]:
    """Execute le lot planifie et rend le resultat mesure.

    Deuxtemps, dans cet ordre :

    1. **Par PR** : la PR est materialisee dans un worktree jetable et les
       tests **concernes** (selection P2) sont joues. C'est la mesure fine.
    2. **Arbre d'integration** (demande) : `main` plus les PRs du lot, dans
       l'ordre du lot, et la suite **lourde** sur cet arbre. C'est la mesure
       qui ressemble a ce qui va atterrir. Si l'arbre est rouge, la
       bissection native nomme la PR fautive.
    """
    started_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    work_root.mkdir(parents=True, exist_ok=True)
    prs = [
        run_one(root, int(entry["number"]), work_root, selector, dry_run=dry_run)
        for entry in plan.get("selectionnees") or []
    ]
    results: dict[str, Any] = {
        "started_at": started_at,
        "finished_at": "",
        "prs": prs,
    }
    if integration:
        numbers = [int(entry["number"]) for entry in plan.get("selectionnees") or []]
        results["integration"] = run_integration(
            root, numbers, work_root, dry_run=dry_run, heavy_target=heavy_target
        )
    results["finished_at"] = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    return results


def run_integration(
    root: Path,
    numbers: list[int],
    work_root: Path,
    dry_run: bool = False,
    heavy_target: list[str] | None = None,
) -> dict[str, Any]:
    """Construit l'arbre d'integration, le teste, et bissectionne s'il est rouge.

    L'arbre se decompose en trois lectures :

    - **l'arbre** : les PRs du lot fusionnees dans l'ordre du lot ; un
      conflit est nomme et la PR sort de l'arbre (elle n'est pas testee) ;
    - **la suite** : la suite lourde sur cet arbre ;
    - **la bissection** : si la suite est rouge, la PR fautive est isolee par
      `git bisect run` et **nommee** par le sujet du commit coupable.

    Un arbre **non construit** (pas de PR integrable) n'est pas un arbre
    vert : le statut est `non-mesurable`.
    """
    targets = heavy_target or list(HEAVY_TARGET)
    tree_record = build_integration_tree(root, numbers, work_root, dry_run=dry_run)
    record: dict[str, Any] = {"arbre": tree_record, "statut": "echec"}
    if dry_run:
        record["statut"] = "simulation"
        return record
    if tree_record.get("statut") != "construit":
        record["statut"] = tree_record.get("statut") or "echec"
        return record
    tree = Path(tree_record["chemin"])
    if not tree_record["prs_integrees"]:
        record["statut"] = "non-mesurable"
        record["detail"] = "aucune PR integrable dans le lot"
        return record
    rc, output = run_heavy_suite(tree, targets)
    record["pytest_rc"] = rc
    record["suite"] = output.strip().splitlines()[-1][:200] if output.strip() else ""
    if rc == 0:
        record["statut"] = "vert"
        return record
    if any(marker in output for marker in UNMEASURABLE_MARKERS):
        record["statut"] = "non-mesurable"
        return record
    record["statut"] = "rouge"
    record["bissection"] = bisect_lot(
        tree,
        tree_record.get("base"),
        tree_record.get("tip"),
        Path(__file__).resolve(),
        targets,
        merges=tree_record.get("commits") or [],
    )
    return record


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", default=DEFAULT_REPO, help="depot cible")
    parser.add_argument("--max-prs", type=int, default=4, help="taille maximale du lot")
    parser.add_argument("--limit", type=int, default=100, help="PRs ouvertes inspectees")
    parser.add_argument("--json", action="store_true", help="sortie JSON machine")
    parser.add_argument("--slot", action="store_true", help="afficher le creneau actif et son echeance")
    parser.add_argument("--results", type=Path, default=None, help="resumer un lot deja produit")
    parser.add_argument("--run", action="store_true", help="executer le lot planifie")
    parser.add_argument("--plan", type=Path, default=None, help="plan du lot (JSON)")
    parser.add_argument(
        "--results-out", type=Path, default=None, help="fichier de resultat du lot (JSON)"
    )
    parser.add_argument(
        "--work-root", type=Path, default=None, help="racine des worktrees jetables du lot"
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="ecrire les commandes sans les lancer"
    )
    parser.add_argument(
        "--integration",
        action="store_true",
        help="construire l'arbre d'integration et jouer la suite lourde dessus",
    )
    parser.add_argument(
        "--bisect-run",
        action="store_true",
        help=(
            "mode bissection : tester le commit courant et rendre 0 (bon), "
            "1 (mauvais) ou 125 (indetermine). C'est la commande que "
            "`git bisect run` invoque."
        ),
    )
    parser.add_argument(
        "--pr",
        type=int,
        default=None,
        help=(
            "lancer le lot sur UNE PR (avance du coordinateur). La garde fork "
            "reste applicable : une PR de fork sans l'APPROVE du "
            "coordinateur est refusee."
        ),
    )
    parser.add_argument(
        "--bisect-target",
        nargs="+",
        default=list(HEAVY_TARGET),
        help="cibles de la suite lourde (mode --bisect-run et phase d'integration)",
    )
    args = parser.parse_args(argv)

    now = datetime.now(timezone.utc)

    if args.bisect_run:
        # `git bisect run` invoque cette commande dans le worktree
        # bissecte : le repertoire courant EST l'arbre teste.
        tree = Path.cwd()
        code = bisect_run(tree, list(args.bisect_target))
        sys.exit(code)

    if args.run:
        plan: dict[str, Any]
        if args.plan is not None:
            try:
                plan = json.loads(args.plan.read_text(encoding="utf-8"))
            except (OSError, ValueError) as exc:
                print(f"plan de lot illisible : {exc}", file=sys.stderr)
                return 2
        else:
            try:
                entries = fetch_entries(args.repo, args.limit)
            except RuntimeError as exc:
                print(f"lecture du pool impossible : {exc}", file=sys.stderr)
                return 2
            selected, _excluded = select_batch(entries, args.max_prs)
            plan = {"selectionnees": selected}
        root = Path(__file__).resolve().parents[2]
        selector = root / "scripts" / "ci" / "select_tests.py"
        work_root = args.work_root or (root / ".tmp" / "heavy-batch")
        results = run_batch(
            root,
            plan,
            work_root,
            selector if selector.is_file() else None,
            dry_run=args.dry_run,
            integration=args.integration,
            heavy_target=list(args.bisect_target),
        )
        if args.results_out is not None:
            args.results_out.parent.mkdir(parents=True, exist_ok=True)
            args.results_out.write_text(
                json.dumps(results, ensure_ascii=False, indent=2), encoding="utf-8"
            )
        summary = summarize(results, now)
        print(json.dumps(summary, ensure_ascii=False, indent=2) if args.json else _render_summary(summary))
        return 0

    if args.slot:
        slot = active_slot(now)
        payload = {
            "maintenant_utc": now.isoformat(),
            "creneau": slot.as_dict() if slot else None,
            "creneaux": [s.as_dict() for s in SLOTS],
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2) if args.json else _render_slot(payload))
        return 0

    if args.results is not None:
        try:
            results = json.loads(args.results.read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            print(f"resultat de lot illisible : {exc}", file=sys.stderr)
            return 2
        payload = summarize(results, now)
        print(json.dumps(payload, ensure_ascii=False, indent=2) if args.json else _render_summary(payload))
        return 0

    if args.pr is not None:
        # Voie « avance du coordinateur » : une PR designee. La garde fork
        # n'est pas negociable (le lot execute du code sur nos runners) ;
        # la regle de verdict, elle, est couverte par la designation
        # elle-meme -- le coordinateur demande CE test-la.
        try:
            entry = fetch_entry_for_pr(args.repo, args.pr)
        except (RuntimeError, ValueError) as exc:
            print(f"PR #{args.pr} illisible : {exc}", file=sys.stderr)
            return 2
        autorise, motif = pr_dispatched_autorise(entry)
        if not autorise:
            print(
                f"PR #{args.pr} refusee : {motif}. La garde fork n'est pas "
                "levee par une designation.",
                file=sys.stderr,
            )
            return 2
        selected, excluded = [entry], []
    else:
        try:
            entries = fetch_entries(args.repo, args.limit)
        except RuntimeError as exc:
            print(f"lecture du pool impossible : {exc}", file=sys.stderr)
            return 2
        selected, excluded = select_batch(entries, args.max_prs)
    payload = {
        "maintenant_utc": now.isoformat(),
        "creneau": active_slot(now).as_dict() if active_slot(now) else None,
        "taille_du_lot": args.max_prs,
        "selectionnees": selected,
        "exclues": excluded,
        "pool_inspecte": len(entries) if args.pr is None else 1,
    }
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(_render_batch(payload), end="")
    return 0


def _render_slot(payload: dict[str, Any]) -> str:
    lines = [f"maintenant (UTC) : {payload['maintenant_utc']}"]
    slot = payload.get("creneau")
    if slot:
        lines.append(f"creneau actif : {slot['nom']} ({slot['debut_utc']} -> {slot['echeance_utc']})")
    else:
        lines.append("creneau actif : aucun (hors creneau)")
    for entry in payload["creneaux"]:
        lines.append(f"  - {entry['nom']} : {entry['debut_utc']} -> {entry['echeance_utc']}")
    return "\n".join(lines) + "\n"


def _render_batch(payload: dict[str, Any]) -> str:
    lines = ["## Lot en ombre", ""]
    lines.append(f"- PRs inspectees : **{payload['pool_inspecte']}**")
    lines.append(f"- PRs selectionnees : **{len(payload['selectionnees'])}**")
    lines.append("")
    lines.append("| PR | titre | fork | verdict |")
    lines.append("|---|---|---|---|")
    for entry in payload["selectionnees"]:
        lines.append(
            f"| #{entry['number']} | {entry['title'][:60]} | "
            f"{'oui' if entry['fork'] else 'non'} | {entry['verdict']} |"
        )
    if payload["exclues"]:
        lines.append("")
        lines.append("### Exclues")
        lines.append("")
        for entry in payload["exclues"]:
            lines.append(f"- #{entry['number']} — {entry['motif']}")
    return "\n".join(lines) + "\n"


def _render_summary(payload: dict[str, Any]) -> str:
    lines = ["## Mesure du lot", ""]
    slot = payload.get("creneau")
    if slot:
        lines.append(f"- creneau : **{slot['nom']}** ({slot['debut_utc']} -> {slot['echeance_utc']})")
    duration = payload.get("duree_lot_s")
    lines.append(f"- duree du lot : **{duration if duration is not None else 'inconnue'}** s")
    within = payload.get("fin_avant_echeance")
    lines.append(
        f"- fin dans les temps : **{'oui' if within else ('non' if within is False else 'indetermine')}**"
    )
    lines.append(f"- PRs concernees : **{payload['prs_concernes']}** (dont {payload['prs_rouges']} rouges)")
    arbre = payload.get("arbre_integration")
    if arbre:
        lines.append("")
        lines.append("### Arbre d'integration")
        lines.append("")
        lines.append(f"- statut : **{arbre.get('statut')}**")
        lines.append(f"- PRs integrees : **{arbre.get('prs_integrees')}**")
        if arbre.get("conflits"):
            lines.append(
                "- conflits : "
                + ", ".join(f"#{c.get('pr')}" for c in arbre["conflits"])
            )
        lines.append(f"- bissection : **{arbre.get('bissection')}**")
        if arbre.get("pr_coupable"):
            lines.append(f"- **PR coupable : #{arbre['pr_coupable']}**")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.exit(main())
