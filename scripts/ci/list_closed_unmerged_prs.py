#!/usr/bin/env python3
"""PRs fermees SANS merge dont la branche porte encore du contenu absent de main.

Pourquoi cet organe existe (#22166)
-----------------------------------
`merge_ready`, le tapis, les dossiers de prevalidation et B.0 ne lisent que des
PRs **ouvertes**. Une PR fermee sans merge sort de toutes les surfaces au moment
meme ou son contenu devient orphelin : la branche survit, les commits aussi, et
personne ne les regarde plus.

Cas fondateur #20374 (mesure le 2026-10-23) : la lane avait pousse une tete
identique a sa base (`reset --hard` vers la tete de la PR de base) ; le diff est
devenu vide, GitHub a ferme la PR, et le vrai commit est arrive une seconde plus
tard -- une PR fermee ne se rouvre pas d'elle-meme. Pendant onze jours, rien ne
l'a vu : la lane a lu un « cache GitHub obsolete », un dossier `READY` a ete
ecrit avec `diff-files: 0`, et l'audit suivant a adapte la navigation a l'etat
casse.

Verdicts (un seul par PR)
-------------------------
``ACCIDENTAL_EMPTY_CLOSE``
    Evenement ``closed`` dans les 60 s d'un ``head_ref_force_pushed`` du meme
    acteur, **et** branche distante encore presente avec du contenu absent de
    ``main``. C'est la signature exacte de #20374.
``ORPHANED_CONTENT``
    Fermee sans merge, aucun commentaire de fermeture qui nomme une raison ou un
    successeur, branche presente avec du contenu absent de ``main``.
``SUPERSEDED``
    Le body ou un commentaire de fermeture nomme une PR successeure, **ou** donne
    une raison explicite d'abandon (obsolete, doublon, sans objet, abandonne).
    Le contenu a ete ecarte deliberement -- ce n'est pas une perte.
``INTEGRATED``
    Le contenu de la branche est present sur ``main`` (identite de contenu via
    l'organe ``orphan_branch_scan``, robuste au squash).
``UNKNOWN``
    API ou depot illisible, branche supprimee alors que le contenu n'est pas
    verifiable, ou merge-base introuvable. **Ce n'est jamais un vert.**

Ce que l'organe ne fait pas
---------------------------
Il **lit et nomme**. Il ne rouvre, ne recree et ne ferme rien : la decision
revient au coordinateur. Il sort 0 dans tous les cas -- ce n'est pas un gate CI.

Ordre d'evaluation
------------------
``UNKNOWN`` (illisible) -> ``INTEGRATED`` (contenu sur main) -> ``SUPERSEDED``
(ecarte deliberement) -> ``ACCIDENTAL_EMPTY_CLOSE`` (signature du force-push) ->
``ORPHANED_CONTENT``. Un contenu deja sur ``main`` n'est jamais un accident, et
une fermeture expliquee n'est jamais un orphelin.

Usage
-----
    python scripts/ci/list_closed_unmerged_prs.py
    python scripts/ci/list_closed_unmerged_prs.py --window-days 30 --json
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import orphan_branch_scan as obs  # noqa: E402

REPO = "jsboige/CoursIA"
DEFAULT_WINDOW_DAYS = 14
#: Fenetre d'accident : un `closed` qui suit de moins de 60 s un force-push.
FORCE_PUSH_WINDOW_S = 60.0
#: Fenetre de lecture des commentaires de fermeture (avant/apres `closed_at`).
CLOSING_COMMENT_WINDOW_S = 1800.0

ACCIDENTAL = "ACCIDENTAL_EMPTY_CLOSE"
ORPHANED = "ORPHANED_CONTENT"
SUPERSEDED = "SUPERSEDED"
INTEGRATED = "INTEGRATED"
UNKNOWN = "UNKNOWN"
VERDICTS = (ACCIDENTAL, ORPHANED, SUPERSEDED, INTEGRATED, UNKNOWN)

#: Un successeur doit etre nomme explicitement. ``See #N`` et ``Part of #N`` sont
#: volontairement EXCLUS : dans le body d'une PR empilee ils designent le parent,
#: pas un successeur -- #20374 porte « Part of #20316 » et n'est pas superseded.
_SUCCESSOR_RE = re.compile(
    r"(?:superseded\s+by|replaced\s+by|successor\s*:?|closed\s+in\s+favou?r\s+of|"
    r"remplac[ée]e?s?\s+par|reprise?s?\s+(?:dans|par)|reprend\s+(?:dans|par)|"
    r"duplicate\s+of|doublon\s+de|en\s+faveur\s+de)"
    r"\s*:?\s*#(\d+)",
    re.IGNORECASE,
)

#: Une raison d'abandon explicite. Liste close : elle ne s'elargit pas a la prose
#: ordinaire, qui classerait n'importe quelle fermeture comme deliberee.
_ABANDON_RE = re.compile(
    r"\b(?:abandonn[ée]e?|obsolet[e]?s?|sans\s+objet|plus\s+d'actualit[ée]|"
    r"won'?t\s+fix|wontfix|not\s+needed|no\s+longer\s+needed|"
    r"doublon|duplicate|revert[ée]e?|annul[ée]e?)\b",
    re.IGNORECASE,
)


# ---------------------------------------------------------------------------
# Classification pure (testable sans reseau)
# ---------------------------------------------------------------------------

def verdict_of(
    *,
    api_error: bool = False,
    integrated: bool | None = None,
    successor: int | None = None,
    abandon_reason: bool = False,
    force_push_to_close_s: float | None = None,
    branch_present: bool | None = None,
    content_lost: int | None = None,
) -> tuple[str, str]:
    """Classe UNE PR fermee sans merge.

    Tous les faits sont injectes : la fonction ne lit ni le reseau ni le depot.

    Args:
        api_error: l'API n'a pas repondu pour cette PR -> ``UNKNOWN``.
        integrated: ``True`` si le contenu de la branche est sur ``main``,
            ``False`` s'il en manque, ``None`` si non verifiable.
        successor: numero de la PR successeure nommee, s'il y en a une.
        abandon_reason: un commentaire de fermeture donne une raison d'abandon.
        force_push_to_close_s: delai en secondes entre le dernier
            ``head_ref_force_pushed`` et la fermeture (``None`` si aucun).
        branch_present: la branche distante existe-t-elle encore ?
        content_lost: nombre de fichiers absents/divergents de ``main``.

    Returns:
        ``(verdict, detail)`` -- ``verdict`` parmi :data:`VERDICTS`.
    """
    if api_error:
        return (UNKNOWN, "API illisible pour cette PR -- jamais un vert")
    if integrated is True:
        return (INTEGRATED, "contenu de la branche present sur main")
    if successor is not None:
        return (SUPERSEDED, f"successeur nomme : #{successor}")
    if abandon_reason:
        return (SUPERSEDED, "raison d'abandon explicite dans un commentaire de fermeture")
    if integrated is None:
        return (UNKNOWN, "contenu non verifiable (merge-base introuvable ou branche supprimee)")
    if branch_present and content_lost:
        if force_push_to_close_s is not None and 0.0 <= force_push_to_close_s <= FORCE_PUSH_WINDOW_S:
            return (
                ACCIDENTAL,
                f"fermee {force_push_to_close_s:.0f} s apres un head_ref_force_pushed ; "
                f"{content_lost} fichier(s) absent(s)/divergent(s) de main",
            )
        return (
            ORPHANED,
            f"{content_lost} fichier(s) absent(s)/divergent(s) de main, "
            f"aucune raison de fermeture nommee",
        )
    if branch_present and not content_lost:
        return (INTEGRATED, "branche presente, contenu byte-identique a main")
    return (UNKNOWN, "branche supprimee et contenu non verifiable")


# ---------------------------------------------------------------------------
# Lecture gh / git
# ---------------------------------------------------------------------------

def _run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, check=False, encoding="utf-8")


def _gh_json(args: list[str]):
    proc = _run(["gh", *args])
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def _parse_ts(value: str | None) -> datetime | None:
    if not value:
        return None
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def closed_unmerged(repo: str, since: datetime) -> list[dict]:
    """PRs fermees sans merge dont ``closed_at`` tombe apres ``since``.

    Pagine ``pulls?state=closed&sort=updated&direction=desc`` et s'arrete des que
    la page depasse la fenetre (le tri par date de mise a jour garantit qu'aucune
    PR plus recente ne suit).
    """
    out: list[dict] = []
    page = 1
    while page <= 50:
        data = _gh_json([
            "api",
            f"repos/{repo}/pulls?state=closed&sort=updated&direction=desc"
            f"&per_page=100&page={page}",
        ]) or []
        if not data:
            break
        oldest = None
        for pr in data:
            closed = _parse_ts(pr.get("closed_at"))
            if closed is not None and (oldest is None or closed < oldest):
                oldest = closed
            if pr.get("merged_at") or closed is None:
                continue
            if closed >= since:
                out.append(pr)
        if len(data) < 100 or (oldest is not None and oldest < since):
            break
        page += 1
    return out


def timeline(repo: str, number: int) -> list[dict]:
    return _gh_json(["api", f"repos/{repo}/issues/{number}/timeline?per_page=100", "--paginate"]) or []


def comments(repo: str, number: int) -> list[dict]:
    return _gh_json(["api", f"repos/{repo}/issues/{number}/comments?per_page=100", "--paginate"]) or []


def force_push_to_close_seconds(events: list[dict], closed_at: datetime) -> float | None:
    """Delai du dernier ``head_ref_force_pushed`` a la fermeture, meme acteur.

    L'acteur compte : un force-push d'une autre lane suivi d'une fermeture n'est
    pas la signature d'un ``reset --hard`` malheureux.
    """
    closer = next((e.get("actor") or {} for e in events if e.get("event") == "closed"), {})
    closer_login = closer.get("login")
    best: float | None = None
    for ev in events:
        if ev.get("event") != "head_ref_force_pushed":
            continue
        actor = (ev.get("actor") or {}).get("login")
        if closer_login and actor != closer_login:
            continue
        ts = _parse_ts(ev.get("created_at"))
        if ts is None:
            continue
        delta = (closed_at - ts).total_seconds()
        if delta < 0:
            continue
        if best is None or delta < best:
            best = delta
    return best


def closing_evidence(body: str, comments_: list[dict], closed_at: datetime) -> tuple[int | None, bool]:
    """``(successeur, raison_d_abandon)`` depuis le body et les commentaires proches.

    Seuls les commentaires dans :data:`CLOSING_COMMENT_WINDOW_S` autour de la
    fermeture comptent : un ``superseded by #N`` poste trois semaines plus tot
    parlait d'autre chose.
    """
    successor: int | None = None
    reason = False
    comment_texts: list[str] = []
    for c in comments_:
        ts = _parse_ts(c.get("created_at"))
        if ts is None:
            continue
        if abs((ts - closed_at).total_seconds()) <= CLOSING_COMMENT_WINDOW_S:
            comment_texts.append(c.get("body") or "")
    # Successeur : le body ET les commentaires de fermeture (un body peut porter
    # « superseded by #N »).
    for text in [body or ""] + comment_texts:
        if successor is None:
            m = _SUCCESSOR_RE.search(text)
            if m:
                successor = int(m.group(1))
    # Raison d'abandon : UNIQUEMENT les commentaires de fermeture. Le body est
    # le pitch de la PR, jamais une raison de la fermer -- y chercher « doublon
    # »/« duplicate » y trouve un descripteur de contenu, pas une decision
    # (#20374 portait « duplicate » dans sa description et sortait SUPERSEDED).
    for text in comment_texts:
        if _ABANDON_RE.search(text):
            reason = True
            break
    return (successor, reason)


def content_state(branch: str, tip: str, main_ref: str) -> tuple[bool | None, int | None]:
    """``(integre, fichiers_perdus)`` pour une branche, via l'organe existant.

    Reutilise ``orphan_branch_scan.content_diff`` (identite de contenu robuste au
    squash) plutot que de reimplementer la comparaison.
    """
    mb = _run(["git", "merge-base", main_ref, tip]).stdout.strip()
    if not mb:
        return (None, None)
    files = obs.content_diff(branch, tip, main_ref)
    lost = [f for f in files if f["status"] in (obs.STATUS_DIFF, obs.STATUS_ABSENT)]
    return (not lost, len(lost))


def evaluate_pr(pr: dict, repo: str, main_ref: str, branches: dict[str, str]) -> dict:
    """Applique :func:`verdict_of` a une PR reelle. Toute erreur -> ``UNKNOWN``."""
    number = pr.get("number")
    branch = ((pr.get("head") or {}).get("ref")) or ""
    closed_at = _parse_ts(pr.get("closed_at"))
    row = {
        "number": number,
        "title": (pr.get("title") or "")[:120],
        "branch": branch,
        "base": (pr.get("base") or {}).get("ref"),
        "closed_at": pr.get("closed_at"),
        "url": pr.get("html_url"),
    }
    try:
        events = timeline(repo, number)
        cmts = comments(repo, number)
    except RuntimeError as exc:
        row.update({"verdict": UNKNOWN, "detail": f"timeline/commentaires illisibles : {exc}"})
        return row

    delta = force_push_to_close_seconds(events, closed_at) if closed_at else None
    successor, abandon = closing_evidence(pr.get("body") or "", cmts, closed_at) if closed_at else (None, False)

    present = branch in branches
    if present:
        integrated, lost = content_state(branch, branches[branch], main_ref)
    else:
        integrated, lost = (None, None)

    verdict, detail = verdict_of(
        integrated=integrated,
        successor=successor,
        abandon_reason=abandon,
        force_push_to_close_s=delta,
        branch_present=present,
        content_lost=lost,
    )
    row.update({
        "verdict": verdict,
        "detail": detail,
        "force_push_to_close_s": None if delta is None else round(delta, 1),
        "files_lost": lost,
    })
    return row


def scan(repo: str = REPO, window_days: float = DEFAULT_WINDOW_DAYS, now: datetime | None = None,
         prs: list[dict] | None = None, branches: dict[str, str] | None = None,
         main_ref: str = "origin/main") -> dict:
    """Enumere, classe et agrege. ``prs``/``branches`` injectables pour les tests."""
    now = now or datetime.now(timezone.utc)
    since = now - timedelta(days=window_days)
    if prs is None:
        prs = closed_unmerged(repo, since)
    if branches is None:
        branches = obs.remote_branches(repo)
    rows = [evaluate_pr(pr, repo, main_ref, branches) for pr in prs]
    counts = {v: 0 for v in VERDICTS}
    for row in rows:
        counts[row["verdict"]] = counts.get(row["verdict"], 0) + 1
    order = {v: i for i, v in enumerate(VERDICTS)}
    rows.sort(key=lambda r: (order.get(r["verdict"], len(VERDICTS)), -(r["number"] or 0)))
    return {
        "repo": repo,
        "window_days": window_days,
        "since": since.isoformat(),
        "counts": counts,
        "rows": rows,
    }


MARKER_START = "<!-- CLOSED-UNMERGED-PR-SCAN:START -->"
MARKER_END = "<!-- CLOSED-UNMERGED-PR-SCAN:END -->"


def render(result: dict) -> str:
    """Corps de rapport markdown, encadre par les marqueurs d'upsert."""
    c = result["counts"]
    lines = [
        MARKER_START,
        f"### PRs fermees sans merge -- {result['window_days']:g} j (depuis {result['since']})",
        "",
        "| Verdict | Compte |",
        "|---|---|",
    ]
    for v in VERDICTS:
        lines.append(f"| `{v}` | {c.get(v, 0)} |")
    for v in (ACCIDENTAL, ORPHANED):
        rows = [r for r in result["rows"] if r["verdict"] == v]
        if not rows:
            continue
        lines += ["", f"#### `{v}` ({len(rows)})", ""]
        for r in rows:
            lines.append(
                f"- **#{r['number']}** `{r['branch']}` (base `{r['base']}`, "
                f"fermee {r['closed_at']}) -- {r['detail']} -- {r['url']}"
            )
    unknown = c.get(UNKNOWN, 0)
    if unknown:
        lines += ["", f"`{UNKNOWN}` = {unknown} : API illisible ou contenu non verifiable. "
                      "Ce n'est pas un vert, c'est une mesure manquante."]
    lines.append(MARKER_END)
    return "\n".join(lines)


def upsert_report(issue_number: int, result: dict, current_body: str) -> str:
    """Remplace la zone marquee du body de l'issue, ou l'ajoute.

    Pure : le body courant est injecte, la fonction renvoie le nouveau body
    complet. L'upsert par marqueur garantit qu'un re-balayage quotidien ne
    multiplie pas les blocs.
    """
    block = render(result)  # porte les marqueurs aux deux bouts
    if MARKER_START in current_body and MARKER_END in current_body:
        start = current_body.index(MARKER_START)
        end = current_body.index(MARKER_END) + len(MARKER_END)
        return current_body[:start] + block + current_body[end:]
    return (current_body.rstrip() + "\n\n" + block + "\n") if current_body.strip() else block + "\n"


def post_report(repo: str, issue_number: int, result: dict) -> None:
    """POSTe/upserte le rapport sur l'issue. Toute erreur est logguee, jamais fatale."""
    payload = _gh_json(["api", f"repos/{repo}/issues/{issue_number}"])
    current = (payload or {}).get("body") or ""
    new_body = upsert_report(issue_number, result, current)
    _gh_json([
        "api", f"repos/{repo}/issues/{issue_number}",
        "-X", "PATCH", "-f", "body=" + new_body,
    ])


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=REPO)
    ap.add_argument("--window-days", type=float, default=DEFAULT_WINDOW_DAYS)
    ap.add_argument("--main-ref", default="origin/main")
    ap.add_argument("--post-to", type=int, default=None,
                    help="numero d'issue sur laquelle upserter le rapport marker-guarde")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    result = scan(args.repo, args.window_days, main_ref=args.main_ref)
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        print(render(result))
    if args.post_to is not None:
        try:
            post_report(args.repo, args.post_to, result)
        except RuntimeError as exc:
            print(f"RAPPORT NON POSTE (advisory) : {exc}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
