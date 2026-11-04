#!/usr/bin/env python3
"""detect_family_recurrence -- read-only detector of OPEN issue families.

Why this exists
---------------
Rule Q162 b (signed by the maintainer on 2026-11-03, `.claude/rules/
pr-review-discipline.md` §A bis): *"Un constat petit et local s'écrit en une
ligne dans l'issue de sa série ou de sa famille, pas dans une issue neuve."*

The rule is only as good as its measurement. Measured on 2026-11-04 (pool
c2767): 397 issues created in 7 days, 250 still open, **66 of them on our own
tools** (organs, false positives, CI, harnais). Several of those describe the
SAME organ from different angles -- the maintainer's own wording is "une seule
issue par organe". The rule says the extra issues should have been one-liners
inside the family issue; they were opened as new issues instead.

What it does
------------
Reads the OPEN issue pool (``gh issue list --state open``) and groups the
issues by **family key**. A family key is one of:

  1. ``organ:<basename>`` -- an organ of THIS repository (a ``*.py`` file that
     exists under ``scripts/``) named in the title, else cited in the body;
  2. ``title:<skeleton>`` -- the *gabarit* of the title: issue numbers, digits,
     backticked code and quoted segments removed.

Every issue has exactly ONE key (``primary_key``): the families are a
**partition** of the pool, not a cover. Without that, an issue citing three
organs was counted in three families and its "host" was whichever group
scored highest -- on the measured pool, that made an Origami notebook issue
the host of a nav-chain family.

The series (``MyIA.AI.Notebooks/<name>/``) is deliberately NOT a family key:
it is far too coarse -- 66 open issues cite ``SymbolicAI``, and grouping them
would call the whole series a "family". The series is kept as a **supporting
signal** (it counts among the keys two issues share) and as a tie-break, never
as a family on its own.

An issue labelled ``candidate-delivered`` is **not** a family member: it is
already attested as delivered and awaits a closure. It is reported apart, as a
closure candidate.

For each family with more than one open issue, the detector names ONE **host**
(the issue of the family that keeps the family) and reports the others as
**recurrences** -- each with the one line that should be folded into the host's
body. The host is, in order:

  1. the issue whose TITLE names the family (the issue IS about that organ);
  2. the oldest issue that ``issue_containers.looks_container`` recognises as a
     container (an ``[Audit #N]`` partition, an EPIC, a task list naming other
     issues) -- a container is exactly the place where a family gathers;
  3. otherwise the oldest issue of the group.

The detector proposes; it never writes, never closes, never labels.

Organ-first
-----------
This detector does NOT re-implement the family's semantics:

  - the classification of a family/container comes from
    ``scripts/issue_containers.py`` (``looks_container``), the shared predicate
    that ``candidate_delivered.py`` and ``verifier_cleanup.py`` also use -- the
    module states its own contract: "The predicate lives in ONE module so the
    two organs cannot drift";
  - the inventory of "what is an organ of this repository" is read from the
    repository itself (``scripts/**/*.py``), not from a hand-written list;
  - the title-equality family (burst duplicates) is NOT re-implemented: it
    belongs to ``scripts/detect_duplicate_issues.py`` (exact title, 60 s
    window). What that organ deliberately does NOT do -- compare bodies, or
    catch a recurrence days later under a neighbouring title -- is what this
    detector adds.

Usage
-----
::

    # Scan the open pool (default 400 issues) and report the families:
    python scripts/detect_family_recurrence.py

    # Only the issues created in the last 7 days (default 14):
    python scripts/detect_family_recurrence.py --window-days 7

    # Offline, on a captured pool (used by the tests):
    python scripts/detect_family_recurrence.py --from-file pool.json

    # Self-test: the known positive control must be found, else exit 2:
    python scripts/detect_family_recurrence.py --self-test

Exit codes:
  0 -- no recurrence found, OR the self-test passed.
  1 -- recurrences found (non-zero count).
  2 -- self-test FAILED (the positive control is missing -- the detector is
       broken, and a broken detector must not be read as "0 recurrence").
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from issue_containers import looks_container  # noqa: E402  (shared predicate)


#: Positive control: a family measured on 2026-11-04 (pool c2767) and read
#: firsthand. The detector MUST find this recurrence in any healthy run,
#: otherwise it is broken and its "0 recurrence" must not be believed. If the
#: pair is closed in the future, the control goes stale -- refresh it then,
#: do not delete it silently.
#:
#: #24294 (2026-11-02T19:42Z) is a small, local finding on the organ
#: ``scan_d5_prose_outputs_alignment.py``; its own body says "Sans parent :
#: defaut d'un organe de controle, **decouvert en corrigeant #24268** (meme
#: fichier, classe differente de celle qui y est corrigee)". #24268
#: (2026-11-02T17:23Z) is the family issue -- the same organ, the same
#: false-positive class. This is exactly what rule Q162 b forbids: a small
#: local finding opened as a NEW issue instead of one line in the family
#: issue.
KNOWN_POSITIVE_CONTROL = {
    "recurrence": 24294,
    "host": 24268,
    "signal": "organ",
}

#: ``MyIA.AI.Notebooks/<Series>/`` -- the family path of a notebook series.
_SERIES_RE = re.compile(r"MyIA\.AI\.Notebooks/([A-Za-z0-9_.-]+)")

#: A python file cited as ``path/to/name.py`` -- the organ reference.
_SCRIPT_RE = re.compile(r"\b([A-Za-z0-9_][A-Za-z0-9_./-]*\.py)\b")

#: ``[Audit #17073]`` prefix, ``partition`` word, ``epic`` word -- the
#: container markers of the shared predicate (mirrors issue_containers, which
#: stays the single source of truth for the DECISION).
_AUDIT_MARKER_RE = re.compile(r"^\s*\[audit\s+#\d+\]", re.IGNORECASE)
_EPIC_WORD_RE = re.compile(r"\bepic\b", re.IGNORECASE)

#: Fragments removed from a title before comparing the gabarits.
_TITLE_NOISE_RES = (
    (re.compile(r"`[^`]*`"), " "),          # backticked code / paths
    (re.compile(r"\"[^\"]*\""), " "),       # quoted segments
    (re.compile(r"'[^']*'"), " "),           # quoted segments
    (re.compile(r"#[0-9]+"), " #N "),        # issue references
    (re.compile(r"\d+"), " #"),              # bare digits (partition numbers)
    (re.compile(r"[^\w#]+", re.UNICODE), " "),  # punctuation
)

#: A title shorter than this is not a gabarit.
_MIN_SKELETON_CHARS = 12


def _now() -> datetime:
    return datetime.now(timezone.utc)


def _parse_ts(value: str) -> datetime:
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except Exception:  # noqa: BLE001 -- a malformed date must not kill the scan
        return _now()


@dataclass
class Issue:
    """Minimal issue record (number, title, body, labels, creation date)."""

    number: int
    title: str
    body: str
    createdAt: str
    labels: list[str] = field(default_factory=list)

    @property
    def text(self) -> str:
        return f"{self.title}\n{self.body}"

    @classmethod
    def from_gh_dict(cls, d: dict) -> "Issue":
        labels = d.get("labels") or []
        if labels and isinstance(labels[0], dict):
            labels = [l.get("name", "") for l in labels]
        return cls(
            number=int(d["number"]),
            title=(d.get("title") or "").strip(),
            body=(d.get("body") or ""),
            createdAt=d.get("createdAt") or "",
            labels=[l for l in labels if l],
        )


@dataclass
class Recurrence:
    """One issue that belongs to an already-open family."""

    issue: int
    host: int
    signal: str            # "organ" | "title"
    detail: str            # the organ basename / title skeleton
    shared: int            # how many keys the two issues share
    host_score: int        # how much the host looks like THE issue of the family
    names_family: bool     # the recurrence's TITLE names the family (organ/audit)
    group_size: int        # how many OPEN issues share the family key
    title: str
    one_line: str

    @property
    def confidence(self) -> str:
        """``forte`` when the fold-back is obvious, ``faible`` when it is a candidate.

        ``forte`` needs BOTH: a host that is about the family (its title names
        the organ) AND a recurrence that is visibly about that family (its
        title names it too, or the two issues share two keys). Otherwise the
        group only shares a CITATION -- an EPIC that mentions an organ is not
        a member of the organ's family -- and the pair is a candidate to
        triage, not a fold-back to perform.
        """
        if self.host_score >= 4 and (self.names_family or self.shared >= 2):
            return "forte"
        return "faible"

    def as_dict(self) -> dict:
        return {
            "issue": self.issue,
            "host": self.host,
            "signal": self.signal,
            "detail": self.detail,
            "shared": self.shared,
            "host_score": self.host_score,
            "names_family": self.names_family,
            "group_size": self.group_size,
            "confidence": self.confidence,
            "title": self.title,
            "one_line": self.one_line,
        }


def organ_inventory(root: Path = REPO_ROOT) -> set[str]:
    """Basenames of the python organs of THIS repository.

    The inventory is read from the tree: a hand-written list would drift, and
    the drift would be invisible (a cited organ that no longer exists would
    silently stop being a family key).
    """
    names: set[str] = set()
    scripts_dir = root / "scripts"
    if not scripts_dir.is_dir():
        return names
    for path in scripts_dir.rglob("*.py"):
        if path.name.startswith("__"):
            continue
        names.add(path.name)
    return names


def title_skeleton(title: str) -> str:
    """The gabarit of a title: what survives when the specifics are removed."""
    text = title or ""
    for pattern, repl in _TITLE_NOISE_RES:
        text = pattern.sub(repl, text)
    return " ".join(text.lower().split())


def family_keys(issue: Issue, organs: set[str]) -> set[str]:
    """The family keys of one issue: the organ it cites, the gabarit of its title.

    The audit-partition families (``[Audit #17073] ... partition ...``) are
    deliberately NOT keys: the partitions are the LIVING STRUCTURE of an
    audit, not duplicates of each other. The directive of the maintainer
    (2026-11-01, 22h30Z) makes ``#17073`` and its partitions the pool of the
    audit corrections -- folding them into their parent would destroy the
    backlog the campaign is made of.
    """
    keys: set[str] = set()
    text = issue.text
    for path in set(_SCRIPT_RE.findall(text)):
        base = path.rsplit("/", 1)[-1]
        if base in organs:
            keys.add(f"organ:{base}")
    skeleton = title_skeleton(issue.title)
    if len(skeleton) >= _MIN_SKELETON_CHARS:
        keys.add(f"title:{skeleton}")
    return keys


def primary_key(issue: Issue, organs: set[str]) -> str | None:
    """The ONE family key of an issue -- the family it belongs to.

    A family must be a **partition** of the pool, not a cover: an issue that
    cites three organs belongs to exactly ONE family, otherwise the
    consolidation table counts it three times and its "host" is whichever
    group happened to score highest -- which, on the measured pool, made an
    Origami notebook issue the host of a nav-chain family.

    The key is chosen by how strong the signal is, not by the first match:

      1. an organ named in the **title** (the issue IS about that organ);
      2. an organ cited in the body (the issue touches it);
      3. the gabarit of the title (a burst of issues with the same shape).
    """
    title = issue.title or ""
    cited: list[str] = []
    for path in _SCRIPT_RE.findall(issue.text):
        base = path.rsplit("/", 1)[-1]
        if base in organs and base not in cited:
            cited.append(base)
    for base in cited:
        if base.lower() in title.lower():
            return f"organ:{base}"
    if cited:
        return f"organ:{cited[0]}"
    skeleton = title_skeleton(title)
    if len(skeleton) >= _MIN_SKELETON_CHARS:
        return f"title:{skeleton}"
    return None


def supporting_keys(issue: Issue) -> set[str]:
    """The supporting signals: the notebook series the issue names.

    They NEVER make a family on their own (a series holds dozens of unrelated
    issues); they only count among the keys two issues share.
    """
    return {f"series:{s}" for s in set(_SERIES_RE.findall(issue.text))}


def _is_container(issue: Issue) -> bool:
    return looks_container(issue.title, issue.labels, issue.body)


def _names_family(issue: Issue, kind: str, detail: str) -> bool:
    """True when the issue's TITLE names the family (not merely its body).

    An EPIC that mentions an organ in its body is NOT about that organ: its
    fold-back into the organ's family issue would be wrong.
    """
    title = (issue.title or "").lower()
    if kind == "organ":
        return detail.lower() in title
    return True  # a title gabarit is, by construction, the same for all its members


def _cites_other_issues(issue: Issue, count: int = 2) -> bool:
    """True when the issue ENUMERATES other issues in its body.

    This is the strongest "I am the issue of my family" signal there is: an
    issue that names its siblings already gathers them. On the measured pool,
    #22983 ("Tapis : refondre le tirage ... **sept issues de rustines**")
    names the seven issues of its family and states that it will close them
    when the refonte lands -- it IS the family issue, although its title does
    not name the organ.
    """
    return _cited_issue_count(issue) >= count


def _cited_issue_count(issue: Issue) -> int:
    """How many OTHER issues the body of this issue names."""
    cited = {int(n) for n in re.findall(r"#(\d+)", issue.body or "")}
    cited.discard(issue.number)
    return len(cited)


def _gathered_siblings(issue: Issue, group_numbers: set[int]) -> int:
    """How many SIBLINGS of the family this issue names in its body.

    Only the siblings count. An issue that cites the issue which happens to
    be its host is not gathering its family -- it is pointing at it. The
    measure that matters is the one that says "this issue already lists its
    family": on the measured pool, #22983 ("Tapis : refondre le tirage ...
    sept issues de rustines") names the seven issues of its family and
    promises to close them when the refonte lands. It IS the family issue,
    although its title does not name the organ.
    """
    cited = {int(n) for n in re.findall(r"#(\d+)", issue.body or "")}
    return len((cited & group_numbers) - {issue.number})


def _host_rank(issue: Issue, key: str, group_numbers: set[int]) -> tuple:
    """The ranking of the candidates to HOST a family -- most significant first.

    The order is lexicographic, not additive: an additive score let a weak
    signal (a body that happens to mention two issues) outweigh the strong
    one (the issue that enumerates its family). Measured on the pool, the
    additive score made #24516 host the tape family, while #22983 -- the
    issue that literally names the seven rustines and promises to close them
    -- was only a member.

    1. the number of SIBLINGS the candidate names (an issue that gathers its
       family IS the family issue);
    2. the candidate whose TITLE names the organ;
    3. the title gabarit match;
    4. the shared container predicate;
    5. the oldest.
    """
    kind, _, detail = key.partition(":")
    title = (issue.title or "").lower()
    names_organ = 1 if (kind == "organ" and detail.lower() in title) else 0
    gabarit = 1 if (kind == "title" and title_skeleton(issue.title) == detail) else 0
    container = 1 if _is_container(issue) else 0
    # The threshold matters: an issue that names ONE sibling is pointing at
    # it, not gathering its family. Two named siblings is the signal.
    gathered = _gathered_siblings(issue, group_numbers)
    if gathered < 2:
        gathered = 0
    return (-gathered, -names_organ, -gabarit, -container,
            issue.createdAt or "", issue.number)


def _host_score(issue: Issue, key: str) -> int:
    """A readable score for the report (the ranking itself is lexicographic)."""
    kind, _, detail = key.partition(":")
    title = (issue.title or "").lower()
    score = 0
    if kind == "organ" and detail.lower() in title:
        score += 4
    elif kind == "title" and title_skeleton(issue.title) == detail:
        score += 4
    if _cites_other_issues(issue):
        score += 3
    if _is_container(issue):
        score += 1
    return score


def detect(
    issues: list[Issue],
    organs: set[str],
    window_days: int = 14,
    now: datetime | None = None,
) -> list[Recurrence]:
    """Report every open issue that belongs to an already-open family.

    The grouping is a **partition**: every issue has ONE primary family key,
    so a family never overlaps another one and the host of a family is the
    host of that family, not of some other group the issue happens to touch.
    """
    now = now or _now()
    horizon = now - timedelta(days=window_days)

    keys_per_issue: dict[int, set[str]] = {}
    support_per_issue: dict[int, set[str]] = {}
    by_key: dict[str, list[Issue]] = defaultdict(list)
    for issue in issues:
        keys = family_keys(issue, organs)
        keys_per_issue[issue.number] = keys
        support_per_issue[issue.number] = supporting_keys(issue)
        if "candidate-delivered" in (issue.labels or []):
            continue  # delivered: a closure candidate, not a family member
        primary = primary_key(issue, organs)
        if primary:
            by_key[primary].append(issue)

    # Host per group: the issue that is ABOUT the family, else the oldest.
    host_of_group: dict[str, Issue] = {}
    for key, group in by_key.items():
        numbers = {i.number for i in group}
        host_of_group[key] = min(group, key=lambda i: _host_rank(i, key, numbers))

    # A recurrence is a RECENT issue whose host is a DIFFERENT, older issue.
    recurrences: list[Recurrence] = []
    for key, group in by_key.items():
        host = host_of_group[key]
        for issue in group:
            if issue.number == host.number:
                continue
            if _parse_ts(issue.createdAt) < horizon:
                continue  # not recent enough (older than the window)
            kind, _, detail = key.partition(":")
            shared = (len(keys_per_issue[issue.number] & keys_per_issue[host.number])
                      + len(support_per_issue[issue.number] & support_per_issue[host.number]))
            recurrences.append(Recurrence(
                issue=issue.number,
                host=host.number,
                signal=kind,
                detail=detail,
                shared=shared,
                host_score=_host_score(host, key),
                names_family=_names_family(issue, kind, detail),
                group_size=len(by_key[key]),
                title=issue.title,
                one_line=f"#{issue.number} — {issue.title}",
            ))
    return sorted(recurrences, key=lambda r: (r.host, r.issue))


def family_table(issues: list[Issue], organs: set[str]) -> list[dict]:
    """The consolidation table: one row per family, with its open members.

    This is the shape the coordinator asked for ("l'issue de famille retenue +
    les issues absorbables + le motif"): the host, the key that gathers the
    family, and every OPEN issue that shares it.

    Two properties make the table usable:

      - the families are **disjoint** (an issue belongs to one family);
      - an issue labelled ``candidate-delivered`` is **not** a member: it is
        already attested as delivered and awaits a closure -- folding it into
        another issue would destroy the delivery proof. It is reported apart,
        as a closure candidate.
    """
    by_key: dict[str, list[Issue]] = defaultdict(list)
    for issue in issues:
        if "candidate-delivered" in (issue.labels or []):
            continue  # delivered: a closure candidate, not a family member
        primary = primary_key(issue, organs)
        if primary:
            by_key[primary].append(issue)

    host_of_group: dict[str, Issue] = {}
    for key, group in by_key.items():
        numbers = {i.number for i in group}
        host_of_group[key] = min(group, key=lambda i: _host_rank(i, key, numbers))

    table: dict[int, dict] = {}
    for key, group in by_key.items():
        host = host_of_group[key]
        row = table.setdefault(host.number, {
            "host": host.number,
            "host_title": host.title,
            "key": key,
            "members": {},
        })
        for issue in group:
            if issue.number != host.number:
                row["members"][issue.number] = issue.title

    out = []
    for number, row in table.items():
        out.append({
            "host": number,
            "host_title": row["host_title"],
            "key": row["key"],
            "n_open": len(row["members"]) + 1,
            "members": [
                {"issue": n, "title": t} for n, t in sorted(row["members"].items())
            ],
        })
    return sorted(out, key=lambda r: (-r["n_open"], r["host"]))


def delivered_candidates(issues: list[Issue]) -> list[dict]:
    """The open issues the repo already attests as delivered.

    They are not duplication candidates: the work is done and the issue
    awaits a closure, which belongs to the coordinator, not to a fold-back.
    """
    out = []
    for issue in issues:
        if "candidate-delivered" in (issue.labels or []):
            out.append({"issue": issue.number, "title": issue.title})
    return sorted(out, key=lambda r: r["issue"])


def _gh_issue_list(repo: str, limit: int) -> list[Issue]:
    raw = subprocess.run(
        ["gh", "issue", "list", "--repo", repo, "--state", "open",
         "--limit", str(limit), "--json", "number,title,body,createdAt,labels"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if raw.returncode != 0:
        raise RuntimeError(f"gh issue list a echoue : {(raw.stderr or raw.stdout)[:300]}")
    return [Issue.from_gh_dict(d) for d in json.loads(raw.stdout or "[]")]


def _gh_issue_view(repo: str, number: int) -> Issue | None:
    """One issue, whatever its state (used to pour the self-test control in)."""
    raw = subprocess.run(
        ["gh", "issue", "view", str(number), "--repo", repo,
         "--json", "number,title,body,createdAt,labels,state"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if raw.returncode != 0:
        return None
    try:
        return Issue.from_gh_dict(json.loads(raw.stdout or "{}"))
    except Exception:  # noqa: BLE001
        return None


def _pour_control(issues: list[Issue], repo: str) -> list[Issue]:
    """Add the control issues to the scanned lot, even if they left it (#18039).

    The control pair is a handful of issue numbers behind the head of the
    pool; a counted window slides with the repository's head and would drop
    it, which would turn the self-test permanently red. The pour fetches the
    real issues -- the detector still has to find the pair by itself.
    """
    lot = list(issues)
    known = {i.number for i in lot}
    for number in (KNOWN_POSITIVE_CONTROL["recurrence"], KNOWN_POSITIVE_CONTROL["host"]):
        if number in known:
            continue
        issue = _gh_issue_view(repo, number)
        if issue is not None:
            lot.append(issue)
    return lot


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--limit", type=int, default=400)
    parser.add_argument("--window-days", type=int, default=14)
    parser.add_argument("--from-file", default=None,
                        help="lit le pool depuis un JSON capture (mode hors-ligne)")
    parser.add_argument("--self-test", action="store_true",
                        help="le controle positif doit etre trouve, sinon exit 2")
    parser.add_argument("--json", action="store_true", help="sortie JSON seule sur stdout")
    args = parser.parse_args(argv)

    if args.from_file:
        raw = json.loads(Path(args.from_file).read_text(encoding="utf-8"))
        issues = [Issue.from_gh_dict(d) for d in raw]
    else:
        issues = _gh_issue_list(args.repo, args.limit)

    organs = organ_inventory()
    recurrences = detect(issues, organs, window_days=args.window_days)

    report = {
        "n_issues": len(issues),
        "n_organs": len(organs),
        "window_days": args.window_days,
        "n_recurrences": len(recurrences),
        "n_recurrences_fortes": sum(1 for r in recurrences if r.confidence == "forte"),
        "n_recurrences_faibles": sum(1 for r in recurrences if r.confidence == "faible"),
        "n_hosts": len({r.host for r in recurrences}),
        "recurrences": [r.as_dict() for r in recurrences],
        "families": family_table(issues, organs),
        "delivered_candidates": delivered_candidates(issues),
    }

    if args.self_test:
        control = KNOWN_POSITIVE_CONTROL
        # The pour is a NETWORK-mode convenience: it re-fetches the control
        # issues when the counted window has slid past them. On an explicit
        # ``--from-file`` pool, the file IS the lot -- pouring would hide a
        # broken control.
        lot = issues if args.from_file else _pour_control(issues, args.repo)
        recurrences = detect(lot, organs, window_days=args.window_days)
        found = [r for r in recurrences if r.issue == control["recurrence"]]
        ok = bool(found) and found[0].host == control["host"]
        report["self_test"] = {
            "control": control,
            "found": bool(found),
            "host": found[0].host if found else None,
            "signal": found[0].signal if found else None,
            "verdict": "OK" if ok else "MISSING",
        }
        report["n_recurrences"] = len(recurrences)
        report["n_hosts"] = len({r.host for r in recurrences})
        report["n_recurrences_fortes"] = sum(1 for r in recurrences if r.confidence == "forte")
        report["n_recurrences_faibles"] = sum(1 for r in recurrences if r.confidence == "faible")
        report["recurrences"] = [r.as_dict() for r in recurrences]
        print(json.dumps(report, ensure_ascii=False, indent=2))
        if not ok:
            print("SELF-TEST BROKEN : le controle positif est absent -- le detecteur est muet",
                  file=sys.stderr)
            return 2
        return 0

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(json.dumps(report, ensure_ascii=False, indent=2))
        print(f"\n{len(recurrences)} recurrence(s) sur {report['n_issues']} issues ouvertes "
              f"({report['n_hosts']} famille(s) d'hote) — "
              f"{report['n_recurrences_fortes']} forte(s), {report['n_recurrences_faibles']} faible(s)",
              file=sys.stderr)
        for rec in recurrences:
            print(f"  #{rec.issue} -> #{rec.host}  [{rec.signal}:{rec.detail}] "
                  f"({rec.shared} cle(s) commune(s), {rec.confidence})  {rec.title[:90]}", file=sys.stderr)
    return 1 if recurrences else 0


if __name__ == "__main__":
    raise SystemExit(main())
