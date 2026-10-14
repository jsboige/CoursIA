#!/usr/bin/env python3
"""issue_containers -- shared predicate for issue CONTAINERS (#17956).

An issue **container** is an issue whose body tracks MANY work targets: a
series-partition audit (``[Audit #N] Serie ... — partition Hermes``), an EPIC,
or a task list enumerating sub-issues. One merged PR delivers at most ONE
tranche of it (a partition audit spans 27-82 notebooks, an EPIC dozens of
leaf issues), so the closure pipeline must never treat a container as
close-ready:

  - ``candidate_delivered.py`` excludes containers from the label (a container
    that receives ``candidate-delivered`` desynchronises the picker from the
    closure pass -- #17956 complement DM, constraint 1);
  - ``verifier_cleanup.py`` renders them ``CONTAINER`` instead of ``READY``
    (measured 2026-09-26: 7 of the 29 READY verdicts were partition audits,
    7 of 7 wrongly close-ready -- the dominant failure class of the crible).

The predicate lives in ONE module so the two organs cannot drift: a container
that slips through one but not the other is precisely the divergence the
dispatch forbids.

Detection signals, in order of measured reliability:

  1. **Title carries an audit-partition marker** -- ``[Audit #N]`` prefix or
     the word ``partition``. All 7 misclassified issues of the 2026-09-26
     crible matched this signal.
  2. **EPIC by title or label** (word ``epic``). This is candidate_delivered's
     existing ``is_epic`` signal, folded in so the closure pass and the label
     organ agree on the same class.
  3. **Body enumerates sub-issues in a task list** -- >= 2 distinct ``#N``
     references on task-list lines (``- [ ] #12`` / ``- [x] #34``). The
     checkbox heuristic is deliberately NOT applied to plain acceptance
     checkboxes (measured unreliable both ways, cf candidate_delivered's
     #10466 note: EPIC #1454 carries no checkboxes, leaf #10143 carries 4);
     only a list that NAMES other issues is a container signal.

Pure stdlib, no network: the predicate sees title/labels/body as strings.
"""

from __future__ import annotations

import re

#: ``[Audit #17073]`` prefix -- the partition-audit series pattern.
_AUDIT_PARTITION_RE = re.compile(r"^\s*\[audit\s+#\d+\]", re.IGNORECASE)

#: The word ``partition`` anywhere in the title (partition Hermes, partition
#: par serie, ...). Word-bounded: "repartitioning" must not fire.
_PARTITION_WORD_RE = re.compile(r"\bpartition(s)?\b", re.IGNORECASE)

#: EPIC by title/label -- same word-boundary rule as candidate_delivered's
#: ``_EPIC_RE`` ("Epictetus" / "epicycle" must not fire).
_EPIC_WORD_RE = re.compile(r"\bepic\b", re.IGNORECASE)

#: A task-list line that references an issue: ``- [ ] #12``, ``* [x] #34``.
#: The issue number is captured; non-issue task items (``- [ ] write docs``)
#: are NOT container evidence.
_TASKLIST_ISSUE_RE = re.compile(r"^\s*[-*]\s+\[[ xX]\]\s+.*?#(\d+)\b", re.MULTILINE)


def is_epic_like(title: str, labels=()) -> bool:
    """True if title or any label carries the word ``epic``."""
    if _EPIC_WORD_RE.search(title or ""):
        return True
    return any(_EPIC_WORD_RE.search(lab or "") for lab in labels or ())


def title_carries_partition(title: str) -> bool:
    """True for ``[Audit #N] ...`` titles or titles naming a partition."""
    t = title or ""
    return bool(_AUDIT_PARTITION_RE.search(t) or _PARTITION_WORD_RE.search(t))


def subissue_tasklist_count(body: str) -> int:
    """Distinct issue numbers named on task-list lines of the body."""
    return len(set(_TASKLIST_ISSUE_RE.findall(body or "")))


def looks_container(title: str, labels=(), body: str | None = None) -> bool:
    """True iff the issue is a container (audit partition, EPIC, sub-issue list).

    The title signals (partition, epic) are evaluated independently of the
    body; the task-list signal requires the body to NAME >= 2 distinct issues.
    """
    if title_carries_partition(title):
        return True
    if is_epic_like(title, labels):
        return True
    return body is not None and subissue_tasklist_count(body) >= 2
