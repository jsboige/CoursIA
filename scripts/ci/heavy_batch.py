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

Usage :
    python scripts/ci/heavy_batch.py --repo jsboige/CoursIA --max-prs 4 --json
    python scripts/ci/heavy_batch.py --slot
    python scripts/ci/heavy_batch.py --results .tmp/batch_results.json

Exit 0 = lot produit (ou resume produit). Exit 2 = instrument ou donnees
illisibles -- jamais un lot vide presente comme un lot vert.
"""

from __future__ import annotations

import argparse
import json
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
    return {
        "creneau": slot.as_dict() if slot else None,
        "duree_lot_s": duration_s,
        "fin_avant_echeance": within,
        "prs_concernes": len(prs),
        "prs_rouges": sum(1 for p in prs if (p.get("statut") or "") == "rouge"),
        "prs": prs,
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
) -> dict[str, Any]:
    """Execute le lot planifie et rend le resultat mesure."""
    started_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    work_root.mkdir(parents=True, exist_ok=True)
    prs = [
        run_one(root, int(entry["number"]), work_root, selector, dry_run=dry_run)
        for entry in plan.get("selectionnees") or []
    ]
    finished_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    return {
        "started_at": started_at,
        "finished_at": finished_at,
        "prs": prs,
    }


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
    args = parser.parse_args(argv)

    now = datetime.now(timezone.utc)

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
            root, plan, work_root, selector if selector.is_file() else None, dry_run=args.dry_run
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
        "pool_inspecte": len(entries),
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
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.exit(main())
