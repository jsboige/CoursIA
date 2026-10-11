#!/usr/bin/env python3
"""Filet des Concerns user sans reponse sur les issues (#20183, phase 0 de #20185).

Le depot a un filet pour les remarques du user sur les PRs (B.0,
``scripts/check_unaddressed_nits.py``, exit 1 au merge). Il n'avait rien pour les
remarques du user sur les **issues** : un commentaire « Concern: ... » du
mainteneur pouvait rester sans reponse indefiniment — le merge-gate ne le voit pas
(ce n'est pas une PR), le tapis sert l'issue selon ses propres criteres (le grain,
pas le fil), et la condensation du dashboard emporte le signalement.

Cette premiere livraison couvre la classe ``user-concern`` de la campagne #20185.
Les cinq autres classes viendront chacune par sa propre PR.

Deux pieges mesures, et la raison pour laquelle ce n'est pas un ``grep`` :

* **FP classe 1 — l'accuse de reception d'une lane.** Sous le login partage, une
  lane repond « Concern pris en compte » : un ``^Concern`` naif le compte comme un
  Concern user neuf (#17889, #16757). Le sous-pattern ``^Concern (pris|note|...)``
  se classe ACK et sort du recensement.
* **La reponse n'est pas garantie de citer le mot.** #18601 : la reponse existe et
  ne dit jamais « Concern » — elle cite l'horodatage du Concern. Exiger le mot
  fabriquerait un faux « sans reponse ».

Un geste de lane pose apres le Concern (claim, verification, livraison, dossier de
cloture) n'est **pas** une reponse : il laisse le Concern ouvert et leve le drapeau
aggravant ``gesture-after`` (#19898 : deux gestes entre les deux Concerns).

Deux regles bornent ce qui **referme** un Concern (#20186) :

* **Le compte ne decide pas.** Les lanes ecrivent sous plusieurs logins
  (``jsboige``, les sieges ``myia-*``, le bot reviewer) ; un accuse de reception se
  juge par sa **forme**, sous n'importe lequel. Router sur le seul compte du
  mainteneur laissait les posts des autres comptes tomber dans le seau **sans
  plancher de substance**, ou un « Concern pris » nu refermait le fil.
* **Le mot seul ne referme pas.** Une citation **forte** — l'horodatage du Concern,
  ou un extrait de son texte — referme ; le mot « Concern » seul ne referme que
  porte par un acquittement de lane qui franchit ``ACK_SUBSTANCE_MIN``.

Plancher ``MANUAL_REVIEW``, fail-closed : un Concern dont le traitement n'est pas
prouve reste dans la liste, quitte a sur-signaler. L'arbitrage fin est humain.

Usage::

    python scripts/ci/check_issue_concerns.py                  # issues ouvertes
    python scripts/ci/check_issue_concerns.py --json
    python scripts/ci/check_issue_concerns.py --issues 19898 16757 17889 18601
    python scripts/ci/check_issue_concerns.py --as-of 2026-10-08T23:59:59Z
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone

REPO = "jsboige/CoursIA"

#: Le mainteneur ecrit sous ce login. Les lanes ecrivent sous le meme compte
#: (login partage) : l'auteur ne suffit donc pas a distinguer un Concern user d'un
#: post de lane — c'est la FORME du corps qui tranche (#20185, classe
#: ``user-remark``). Pour ``user-concern``, le prefixe reste un signal fort.
CONCERN_AUTHOR = "jsboige"

#: Les comptes sous lesquels une lane de la flotte ecrit : le compte partage du
#: mainteneur, les sieges de worker (``myia-*``) et les bots reviewers. Un post de
#: lane se juge par la meme regle **quel que soit** le compte qui le porte
#: (#20186) : indexer la garde sur le seul ``jsboige`` laissait un accuse de
#: reception nu franchir le plancher de substance des qu'il etait ecrit sous un
#: autre login, alors que la menace nommee par l'organe est precisement le compte
#: partage.
LANE_LOGIN = re.compile(
    rf"^(?:{re.escape(CONCERN_AUTHOR)}|myia-[a-z0-9-]+|clusterManager-Myia)$"
)

#: Forme mesuree du user (#19898, #16757, #17889, #18601).
CONCERN_PREFIX = re.compile(r"^Concern\b", re.IGNORECASE)

#: FP classe 1 : l'accuse de reception d'une lane, poste sous le compte partage.
ACK_PATTERN = re.compile(
    r"^Concern\s+(pris|note|traite|acquitte|ack)", re.IGNORECASE
)

#: Un geste de lane pose apres le Concern — drapeau aggravant ``gesture-after``.
#: Reconnu a son tag de protocole ou a sa signature de lane. Un geste n'est PAS
#: une reponse : il ne retire pas le Concern de la liste.
GESTURE_PATTERN = re.compile(
    r"^\[(?:CLAIMED|CLAIMED-AMEND|VERIFICATION|DELIVERED|RELEASED|INFO|DONE|"
    r"LIVRAISON|COMPLEMENT|ADJOINT PREFLIGHT|CLOSURE PREFLIGHT|OVERRIDE|"
    r"WARN|ERROR|BLOCKED|ASK|REPLY|ACK|PROPOSAL)\]|lane\s+myia-",
    re.IGNORECASE,
)

#: Le tag de geste n'est cherche que dans les premiers caracteres : un tag de
#: protocole situe au-dela d'un long preambule n'est pas vu (donc ni
#: ``gesture-after``, ni exclusion du seau des reponses). La borne est assumee —
#: c'est elle qui empeche un long commentaire de lane de compter comme reponse —
#: et elle est nommee ici pour ne pas etre decouverte par surprise (#20186).
GESTURE_WINDOW = 400

_WS = re.compile(r"\s+")
_DECORATION = re.compile(r"^[\s*_#>`]+")
_LINK = re.compile(r"https?://\S+")
_WORD_CONCERN = re.compile(r"\bConcerns?\b", re.IGNORECASE)

GRAPHQL_SEARCH = """
query($q: String!, $after: String) {
  search(query: $q, type: ISSUE, first: 100, after: $after) {
    pageInfo { hasNextPage endCursor }
    nodes { ... on Issue { number } }
  }
}
"""


# --------------------------------------------------------------------------- #
# Modele
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class Comment:
    id: int
    author: str
    created_at: str
    body: str

    @property
    def when(self) -> datetime:
        return datetime.strptime(self.created_at, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc
        )


@dataclass
class ConcernFinding:
    comment_id: int
    created_at: str
    excerpt: str
    status: str
    proof: int | None
    gesture_after: bool

    def as_dict(self) -> dict:
        return {
            "comment_id": self.comment_id,
            "created_at": self.created_at,
            "excerpt": self.excerpt,
            "status": self.status,
            "proof": self.proof,
            "gesture_after": self.gesture_after,
        }


@dataclass
class IssueReport:
    number: int
    concerns: list[ConcernFinding]

    @property
    def unresolved(self) -> list[ConcernFinding]:
        return [c for c in self.concerns if c.status != "REPONDU"]

    @property
    def gesture_after(self) -> bool:
        return any(c.gesture_after for c in self.concerns)

    def as_dict(self) -> dict:
        return {
            "number": self.number,
            "gesture_after": self.gesture_after,
            "concerns": [c.as_dict() for c in self.concerns],
        }


# --------------------------------------------------------------------------- #
# Classification (pur, sans reseau — c'est ce que les tests exercent)
# --------------------------------------------------------------------------- #


def normalise(body: str) -> str:
    return _WS.sub(" ", (body or "").strip())


def excerpt(body: str, width: int = 200) -> str:
    return normalise(body)[:width]


def classify(comment: Comment) -> str:
    """Classe un commentaire : ``concern`` | ``ack`` | ``gesture`` | ``other``.

    La decoration markdown de tete est neutralisee avant le match : une reponse
    « **Concern pris (ai-01).** » doit se lire comme un ACK, pas comme un Concern.

    Le routage porte sur **l'ensemble** des logins de lane (``LANE_LOGIN``), pas sur
    le seul compte du mainteneur : router sur un login unique faisait tomber les
    posts des autres comptes dans ``other``, le seul seau **sans plancher de
    substance** — un accuse de reception nu y refermait un Concern (#20186).
    """
    stripped = _DECORATION.sub("", comment.body or "")
    if LANE_LOGIN.match(comment.author or "") and CONCERN_PREFIX.match(stripped):
        return "ack" if ACK_PATTERN.match(stripped) else "concern"
    if GESTURE_PATTERN.search((comment.body or "")[:GESTURE_WINDOW]):
        return "gesture"
    return "other"


def hhmm_token(created_at: str) -> str:
    """``2026-10-07T15:30:59Z`` -> ``15:30Z`` (la forme citee par #18601).

    Rend ``""`` sur toute forme non ``Z`` (milliseconde, offset, ``null``) au lieu
    de lever : un seul commentaire mal forme tuait le run sur les 580 issues pour
    une donnee non essentielle (#20186). Un jeton vide **n'est pas** une citation —
    ``cite_strength`` le teste explicitement avant de s'en servir.
    """
    try:
        dt = datetime.strptime(created_at, "%Y-%m-%dT%H:%M:%SZ")
    except (TypeError, ValueError):
        return ""
    return f"{dt.hour:02d}:{dt.minute:02d}Z"


def _shares_quote(source: str, reply: str, width: int = 40, step: int = 20) -> bool:
    """Une fenetre du texte de ``source`` se retrouve-t-elle dans ``reply`` ?

    Les parametres etaient nommes a l'envers (``body``/``text``) alors que le
    premier recoit toujours le **Concern** et le second la **reponse** : le
    comportement etait correct, la lecture ne l'etait pas (#20186).
    """
    src = normalise(_LINK.sub("", source))
    if len(src) < width:
        return False
    for i in range(0, len(src) - width + 1, step):
        window = src[i : i + width]
        if window.count(" ") > width * 0.5:
            continue
        if window in reply:
            return True
    return False


#: Force d'une citation. Les trois formes mesurees ne se valent pas : l'horodatage
#: du Concern et la citation de son texte s'obtiennent en **lisant** le Concern ;
#: le mot seul s'ecrit sans l'avoir lu. La docstring historique de ``cites``
#: concedait deja que « le mot seul ne suffit pas a distinguer un acquittement ».
CITE_STRONG = "strong"
CITE_WEAK = "weak"
CITE_NONE = "none"


def cite_strength(concern: Comment, reply: Comment) -> str:
    """``strong`` (horodatage ou citation) | ``weak`` (le mot seul) | ``none``."""
    text = normalise(reply.body)
    token = hhmm_token(concern.created_at)
    if token and token in text:
        return CITE_STRONG
    if _shares_quote(concern.body, text):
        return CITE_STRONG
    if _WORD_CONCERN.search(text):
        return CITE_WEAK
    return CITE_NONE


def cites(concern: Comment, reply: Comment) -> bool:
    """La reponse traite-t-elle CE Concern, au sens **faible** ?

    Vrai des qu'une des trois formes est presente, le mot compris : c'est le
    predicat de *reference*. Ce qui **referme** un Concern est ``proves``, qui
    separe les formes fortes de la forme faible.
    """
    return cite_strength(concern, reply) != CITE_NONE


def proves(concern: Comment, reply: Comment, kind: str) -> bool:
    """La reponse REFERME-t-elle le Concern ?

    Une citation **forte** referme. La forme **faible** (le mot seul) ne referme
    que portee par un acquittement de lane qui franchit le plancher de substance —
    doctrine de #17889 (« une lane qui prend le Concern ET pose du fond y repond »),
    et ``is_response_candidate`` a deja ecarte les acquittements nus. Hors de la,
    un commentaire qui ne fait que nommer le mot laisse le Concern en
    ``MANUAL_REVIEW`` : ni prouve traite, ni ignore (#20186).
    """
    strength = cite_strength(concern, reply)
    if strength == CITE_STRONG:
        return True
    if strength == CITE_WEAK:
        return kind == "ack"
    return False


#: Un acquittement de lane ne repond pas s'il ne fait qu'accuser reception. Une
#: lane qui prend le Concern ET pose du fond y repond (#17889 : « Concern pris en
#: compte — oui, les transcripts portent plus que la premiere vague… », 2410
#: caracteres). Seuil de substance, volontairement bas : au-dela du seul accuse.
ACK_SUBSTANCE_MIN = 120


def is_response_candidate(kind: str, comment: Comment) -> bool:
    if kind in ("gesture", "concern"):
        return False
    if kind == "ack":
        return len(normalise(comment.body)) >= ACK_SUBSTANCE_MIN
    return True


def analyse_comments(number: int, comments: list[Comment]) -> IssueReport:
    kinds = [classify(c) for c in comments]
    findings: list[ConcernFinding] = []
    for i, comment in enumerate(comments):
        if kinds[i] != "concern":
            continue
        later = list(zip(comments[i + 1 :], kinds[i + 1 :]))
        candidates = [
            (other, kind)
            for other, kind in later
            if is_response_candidate(kind, other)
        ]
        proof = None
        for other, kind in candidates:
            if proves(comment, other, kind):
                proof = other.id
                break
        if proof is not None:
            status = "REPONDU"
        elif candidates:
            status = "MANUAL_REVIEW"
        else:
            status = "NON REPONDU"
        findings.append(
            ConcernFinding(
                comment_id=comment.id,
                created_at=comment.created_at,
                excerpt=excerpt(comment.body),
                status=status,
                proof=proof,
                gesture_after=any(kind == "gesture" for _, kind in later),
            )
        )
    return IssueReport(number=number, concerns=findings)


# --------------------------------------------------------------------------- #
# Acces reseau
# --------------------------------------------------------------------------- #


def gh_json(args: list[str]):
    proc = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8"
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} -> rc={proc.returncode}: {proc.stderr[:300]}")
    return json.loads(proc.stdout)


def list_issue_numbers(since: str, state: str) -> list[int]:
    query = f"repo:{REPO} is:issue updated:>={since}"
    if state == "open":
        query += " is:open"
    elif state == "closed":
        query += " is:closed"
    numbers: list[int] = []
    after = None
    while True:
        args = ["api", "graphql", "-f", f"query={GRAPHQL_SEARCH}", "-f", f"q={query}"]
        if after:
            args += ["-f", f"after={after}"]
        data = gh_json(args)["data"]["search"]
        numbers.extend(node["number"] for node in data["nodes"])
        page = data["pageInfo"]
        if not page["hasNextPage"]:
            return numbers
        after = page["endCursor"]


def fetch_comments(number: int) -> list[Comment]:
    out: list[Comment] = []
    page = 1
    while True:
        batch = gh_json(
            ["api", f"repos/{REPO}/issues/{number}/comments?per_page=100&page={page}"]
        )
        out.extend(
            Comment(
                id=item["id"],
                author=item["user"]["login"],
                created_at=item["created_at"],
                body=item.get("body") or "",
            )
            for item in batch
        )
        if len(batch) < 100:
            return out
        page += 1


# --------------------------------------------------------------------------- #
# Rendu
# --------------------------------------------------------------------------- #


def render_text(reports: list[IssueReport], since: str, state: str, scanned: int) -> str:
    unresolved = [(r, c) for r in reports for c in r.unresolved]
    total = sum(len(r.concerns) for r in reports)
    lines = [
        f"=== Concerns user sans reponse (issues {state}, depuis {since}) ===",
        f"{len(unresolved)} non resolu(s) sur {total} recense(s), "
        f"dans {len({r.number for r, _ in unresolved})} issue(s) — "
        f"{scanned} issue(s) lue(s).",
    ]
    if not unresolved:
        lines.append("Aucun — le fil est propre sur la fenetre.")
        return "\n".join(lines)
    grouped: dict[int, IssueReport] = {}
    for report, _ in unresolved:
        grouped.setdefault(report.number, report)
    ordered = sorted(
        grouped.values(),
        key=lambda r: (not r.gesture_after, min(c.created_at for c in r.unresolved)),
    )
    for report in ordered:
        flag = "  [gesture-after]" if report.gesture_after else ""
        lines.append("")
        lines.append(f"#{report.number} — {len(report.unresolved)} concern(s){flag}")
        for finding in report.unresolved:
            proof = f" (piste c{finding.proof})" if finding.proof else ""
            lines.append(
                f"  - {finding.created_at} c{finding.comment_id}  "
                f"{finding.status}{proof}"
            )
            lines.append(f"      {finding.excerpt}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--since", default="2026-09-25", help="issues mises a jour depuis (AAAA-MM-JJ)")
    parser.add_argument("--state", choices=["open", "closed", "all"], default="open")
    parser.add_argument("--issues", type=int, nargs="*", help="issues explicites (controles)")
    parser.add_argument("--as-of", help="figer le fil a cet instant (ISO, ex 2026-10-08T23:59:59Z)")
    parser.add_argument("--limit", type=int, default=0, help="ne lire que N issues (0 = toutes)")
    parser.add_argument("--jobs", type=int, default=8, help="lectures de fils en parallele")
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    parser.add_argument("--fail-on-open", action="store_true", help="exit 1 si un Concern reste ouvert")
    args = parser.parse_args(argv)

    if args.issues:
        numbers = list(dict.fromkeys(args.issues))
    else:
        numbers = list_issue_numbers(args.since, args.state)
    if args.limit:
        numbers = numbers[: args.limit]

    cutoff = None
    if args.as_of:
        cutoff = datetime.strptime(args.as_of, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc
        )

    print(f"lecture de {len(numbers)} issue(s)…", file=sys.stderr)

    def work(number: int) -> IssueReport:
        comments = fetch_comments(number)
        if cutoff is not None:
            comments = [c for c in comments if c.when <= cutoff]
        return analyse_comments(number, comments)

    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        reports = list(pool.map(work, numbers))

    reports = [r for r in reports if r.concerns]

    if args.json:
        unresolved = sum(len(r.unresolved) for r in reports)
        payload = {
            "since": args.since,
            "state": args.state,
            "as_of": args.as_of,
            "issues_scanned": len(numbers),
            "concerns_total": sum(len(r.concerns) for r in reports),
            "concerns_unresolved": unresolved,
            "issues": [
                r.as_dict()
                for r in sorted(
                    reports,
                    key=lambda r: (not r.gesture_after, r.number),
                )
                if r.unresolved
            ],
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(render_text(reports, args.since, args.state, len(numbers)))

    unresolved = sum(len(r.unresolved) for r in reports)
    if args.fail_on_open and unresolved:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
