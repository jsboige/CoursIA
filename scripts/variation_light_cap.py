#!/usr/bin/env python3
"""Detect G-VAR-2 cap-reached: a LIGHT PR merged past the lane's daily budget.

G-VAR-2 (variation-protocol.md) caps the protocol at **max(1, lane grains
merged today // 3) LIGHT PRs per lane per day, all LIGHT sub-categories
confounded** (guard, doc, refs, ... share a single budget). The cap is a
RATIO, not a flat one-per-day: see `light_budget()` below and the rationale
block above it. It is the only gate of the protocol that is **cross-PR** -- it
needs to know what the lane has ALREADY merged today -- so until now it was
counted by hand by the coordinator, who merged a 2nd LIGHT twice in one cycle
(issue #8964: measured firsthand on the 2026-07-30 wave). This tool makes the
fact VISIBLE (advisory, exit 0), it does not block.

Input: a JSON array of the day's merged PRs, each `{number, body, mergedAt}`,
produced by:

    gh pr list --state merged --search 'merged:<YYYY-MM-DD>' \
        --json number,body,mergedAt

Modes
-----
  --replay <file>      Acceptance-test mode (#8964): for every LIGHT PR in the
                       dataset, report whether it is cap-reached (a LIGHT of the
                       same lane merged EARLIER today). Prints a table + a JSON
                       summary on stdout. The replay over the 2026-07-30 wave
                       must flag #8951 (2nd LIGHT of myia-po-2023:CoursIA) and
                       NOT flag #8909 / #8910 / #8913 (each the 1st LIGHT of its
                       lane).

  --check-pr <N>       CI mode (the current PR): report whether PR <N> would be
                       cap-reached given the already-merged PRs in <file>.
                       Consumes BOTH cap axes as a single source (#10480): the
                       TIER cap (declared/effective LIGHT count) AND the GENRE
                       cap (LIGHT-genre count, regardless of declared tier). A
                       MED/readme can therefore be `cap_reached` even though its
                       declared tier never spends the TIER budget -- closing the
                       bypass where --check-pr returned `false` while
                       --genre-signals returned `CAP-EXCEEDED-BY-GENRE` on the
                       same lane-day. Emits `cap_reached` (the union, when the
                       candidate carries the LIGHT-genre motif, #10341),
                       `tier_cap_reached`, `cap_exceeded_by_genre`, `lane`,
                       `consumed_by`, and a `counts: "tier+genre"` disclosure.

Parsing
-------
Bodies are read as FULL TEXT, never line-by-line. The line-by-line bug measured
hand counted "18/38 untagged" when the true figure was "2/38": the tag is often
on the 2nd+ line of a multi-line body, and a per-line scan misses it (#8964).

Agnostic to separator and case (#8938): the three shapes observed in the wild
all parse identically after markdown noise is stripped --

    Grain: LIGHT/guard -- lane myia-po-2023:CoursIA      (em-dash)
    **Grain:** LIGHT/guard - lane myia-ai-01:CoursIA     (bold, hyphen)
    `Grain: LIGHT/refs` . **Lane:** myia-po-2024:CoursIA-2  (backticks, middot)

Exit 0 always (advisory).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# --- parsing ---------------------------------------------------------------

# The Grain-tag reader lives in scripts/grain_tag.py -- a SHARED extractor so
# the CI guard (variation-tag-guard.yml) and this organ read the tag the SAME
# way (#9485). The historical divergence -- a bash `grep 'Grain:'` here, a
# Python `Grain:\s*` there -- left 38% of a day's merges unattributed because
# both required the colon and a `## Grain` title form matched neither. See
# grain_tag.parse_grain_tag for the tolerated forms (title, no-colon, bold).
#
# `parse_grain` keeps the historical {tier, lane} return (no genre -- the organ
# never needed it) so the 21 existing tests asserting that exact shape do not
# break; the genre the extractor also reads is simply dropped here.
from grain_tag import GENRES, parse_grain_tag  # noqa: E402


def parse_grain(body: str) -> dict | None:
    """Extract {tier, lane} from a PR body, form-tolerant via the shared reader.

    Returns None when no `<TIER>/<GENRE>` can be read anywhere (the guard then
    flags `variation-tag-missing`). `tier` is upper-cased (LIGHT/MED/DEEP);
    `lane` is the "<machine>:<workspace>" token or None (the guard then flags
    `variation-tag-lane-missing`).
    """
    g = parse_grain_tag(body)
    if g is None:
        return None
    return {"tier": g["tier"], "lane": g["lane"]}


# --- requalification (coordinator override of the declared tag) ------------

# variation-protocol says the DECLARED `Grain:` tag is not self-executing: the
# coordinator re-qualifies it at merge (up: a declared LIGHT read as MED on the
# strength of the diff; down: a declared DEEP read as LIGHT). Until #8970 that
# decision lived only in a dashboard post -- invisible to this job, which then
# flagged legitimately re-qualified work (1 FP / 2 flags on the 2026-07-30
# wave: #8930, re-qualified LIGHT->MED, was still flagged CAP-REACHED).
#
# The channel is a GitHub LABEL applied at merge -- `grain-requalified:<TIER>`
# -- machine-readable, leaves the worker's body intact, cheap to query
# (`gh pr list --json ...,labels` adds the field to the SAME call, no extra
# quota). A present label OVERRIDES the declared tier for counting, in BOTH
# directions: up-qualification spares the LIGHT budget, down-qualification
# consumes it (the symmetric case #8970 asks for). The LANE is structural
# (the worker's workspace) and is never re-qualified -- it still comes from
# the declared body.
_REQUAL_LABEL_RE = re.compile(
    r"grain-requalified:\s*(LIGHT|MED|DEEP)", re.IGNORECASE
)


def label_names(pr: dict) -> list[str]:
    """Flatten a PR's `labels` field to a list of names.

    Robust to the two shapes `gh ... --json labels` can return: a list of
    strings (names) or a list of objects `{name, color, ...}` (the default).
    """
    out: list[str] = []
    for lab in pr.get("labels") or []:
        if isinstance(lab, str):
            out.append(lab)
        elif isinstance(lab, dict):
            name = lab.get("name")
            if name:
                out.append(name)
    return out


def load_labels_file(path: Path) -> list[str]:
    """Load the current PR's labels from a JSON file written by the CI workflow.

    The workflow writes ``gh pr view --json labels`` output, which is the
    OBJECT ``{"labels": [{name,...}]}`` -- not a bare array (#9971). ``gh pr
    list`` returns a bare array of PR objects (each carrying ``.labels``), and
    a hand-written file may hold a bare ``[{...}]`` or ``["str"]``. Accept all
    three shapes so the verdict never depends on which ``gh`` subcommand fed
    the file: previously the object form was double-wrapped into
    ``{"labels": {"labels": [...]}}`` and ``label_names`` iterated only the key
    string ``"labels"``, silently dropping every real label.
    """
    if path.exists() and path.read_text(encoding="utf-8").strip():
        try:
            raw = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            raw = []
    else:
        # Tolerate a missing/empty file (treat as no labels) rather than crash:
        # the CI workflow always writes valid JSON (`gh pr view` or a `printf
        # '[]'` fallback), but a manual invocation should not hard-fail.
        raw = []
    if isinstance(raw, dict):
        raw = raw.get("labels") or []
    return label_names({"labels": raw})


def effective_tier(body: str | None, labels: list[str]) -> str | None:
    """The TIER that counts for G-VAR-2.

    A `grain-requalified:<TIER>` label (if present) OVERRIDES the declared
    `Grain:` tag, in both directions -- up (LIGHT->MED spares the budget) and
    down (DEEP->LIGHT consumes it). Returns the declared tier when no
    requalification label is present, or None when neither is readable.
    """
    for lab in labels:
        m = _REQUAL_LABEL_RE.search(lab)
        if m:
            return m.group(1).upper()
    g = parse_grain(body or "")
    return g["tier"] if g else None


# --- cap logic -------------------------------------------------------------

# G-VAR-2 is a RATIO, not an absolute cap (2026-07-31, user sign-off).
#
# The old `1 LIGHT/lane/day` scored a 1-PR lane and a 19-merge/13-DEEP lane
# identically -- the second is the OPPOSITE of monoculture and was sanctioned
# the same. A cap blind to throughput does not measure monoculture, it caps
# throughput. Worse, it MANUFACTURES the duplicate work it claims to save:
# #8961 (the strip->update ordering doc) sat held for a day; during that hold
# the doc never reached `main`, and two other sessions rewrote it (#8983,
# #8996, closed as duplicates) -- ~98 lines written three times.
#
# Budget = max(1, lane_grains_merged_today // 3). A lane merging 1-3 grains
# keeps EXACTLY the old ceiling of one LIGHT (the small-lane case was never
# the problem); a lane merging 19 gets six. The floor is what makes this a
# strict relaxation: no lane is worse off than under the absolute cap.
#
# Anti-blanchiment corollary (#10290, 2026-08-10): the 1-LIGHT/lane/day cap
# that the ratio replaced manufactured duplicate work. The same shape of
# blindness would attach to any "anti-blanchiment de genre" organ that flags
# by file-class signature (e.g. "this PR is .ipynb-only + zero code modif +
# declared MED/notebook-*") without measuring throughput-adjusted signal.
# The 7-day census (Aug 3-10, see docs/reference/variation-genre-census-
# 2026-08-10.md) measured markdown-only `.ipynb` PRs at 1.51 % of the merge
# universe (15/996) -- all 5 heuristically-flagged drift candidates were
# spot-checked as legitimate MED-declared GFM-table or cost-metadata fixes.
# An organ that flips the SAME ratio cap into a per-file-class signal would
# have flagged genuine work for zero genuine blanchiment: same blind-spot,
# inverted direction. Hence the organ was retired; the census remains the
# deliverable so the question can be re-asked if the proportion rises.
LIGHT_RATIO_DIVISOR = 3


def light_budget(lane_grain_count: int) -> int:
    """LIGHT allowance for a lane that merged `lane_grain_count` grains today.

    `max(1, n // 3)`: floor of 1 so a low-output lane keeps the old ceiling,
    then one extra LIGHT per full slice of 3 grains.
    """
    return max(1, lane_grain_count // LIGHT_RATIO_DIVISOR)


def _lane_of(pr: dict) -> str | None:
    """Declared lane of a PR, or None when untagged.

    The lane is STRUCTURAL (the worker's workspace) and is never re-qualified:
    it always comes from the body, even when a `grain-requalified:` label
    overrides the tier. An untagged PR has no lane, so it cannot be attributed
    -- it counts neither as a LIGHT nor in any lane's denominator.
    """
    g = parse_grain(pr.get("body", "") or "")
    return g["lane"] if g else None


def unattributed(merged_prs: list[dict]) -> list[dict]:
    """PRs the organ could NOT attribute to any lane (no readable `Grain:` tag).

    These are invisible to every count above: absent from each lane's
    numerator AND denominator. That is the right arithmetic -- guessing a lane
    would be worse -- but it must never be reported as a clean day. An audit
    that says `cap-reached: 0` over a set where most PRs landed here has
    measured nothing; the summary prints this count so the two cannot be
    confused (#9465).
    """
    return [pr for pr in merged_prs if _lane_of(pr) is None]


def lane_grains(merged_prs: list[dict], target_lane: str) -> list[dict]:
    """Every merged PR attributed to `target_lane`, ANY tier.

    This is the ratio's denominator: DEEP and MED grains are what EARN the
    LIGHT budget, so they must be counted, not just the LIGHTs.
    """
    return [pr for pr in merged_prs if _lane_of(pr) == target_lane]


def lane_lights(merged_prs: list[dict], target_lane: str) -> list[dict]:
    """Merged PRs of `target_lane` whose EFFECTIVE tier is LIGHT (#8970).

    A declared LIGHT re-qualified up to MED does NOT spend the budget; a
    declared DEEP re-qualified down to LIGHT DOES.
    """
    out = []
    for pr in merged_prs:
        if _lane_of(pr) != target_lane:
            continue
        if effective_tier(pr.get("body", ""), label_names(pr)) != "LIGHT":
            continue
        out.append(pr)
    return out


def light_cap_status(merged_prs: list[dict], target_lane: str) -> dict:
    """Given the day's ALREADY-MERGED PRs, would a NEW LIGHT of `target_lane`
    exceed its budget?

    CI semantics: the current PR is OPEN (not yet merged), so it is NOT in
    `merged_prs`. It is nonetheless counted in the denominator (`+ 1`): the
    candidate is itself a grain of the day. Counting it is deliberately
    conservative early in the day -- it stops a lane front-loading LIGHTs at
    02:00 against a throughput it has not produced yet.

    Returns {cap_reached, budget, spent, lane_grains, consumed_by} where
    consumed_by is the earliest merged LIGHT of the lane (kept for the
    workflow's message), or None.
    """
    grains = lane_grains(merged_prs, target_lane)
    lights = lane_lights(merged_prs, target_lane)
    budget = light_budget(len(grains) + 1)  # +1 = the open candidate
    lights.sort(key=lambda p: p.get("mergedAt", ""))
    reached = len(lights) >= budget
    first = lights[0] if lights else None
    return {
        "cap_reached": reached,
        "budget": budget,
        "spent": len(lights),
        "lane_grains": len(grains) + 1,
        "consumed_by": (
            {"number": first.get("number"), "mergedAt": first.get("mergedAt")}
            if reached and first else None
        ),
    }


def replay(merged_prs: list[dict]) -> list[dict]:
    """For every LIGHT PR in the set, decide cap_reached against the FULL set.

    The day is over here (audit path), so each lane's denominator is KNOWN:
    its budget is `max(1, lane_grains // 3)` over the whole set. The k-th LIGHT
    of a lane (chronological, 1-based) is cap-reached iff `k > budget`. Under a
    budget of 1 this reduces exactly to the old rule -- the first LIGHT of each
    lane is never flagged.

    Returns the list sorted by mergedAt (chronological replay).
    """
    # denominator per lane: ALL attributed grains, any tier (they earn budget)
    grains_by_lane: dict[str, int] = {}
    for pr in merged_prs:
        lane = _lane_of(pr)
        if lane:
            grains_by_lane[lane] = grains_by_lane.get(lane, 0) + 1

    lights = []
    for pr in merged_prs:
        lane = _lane_of(pr)
        if not lane:
            continue
        if effective_tier(pr.get("body", ""), label_names(pr)) != "LIGHT":
            continue
        lights.append({**pr, "_tier": "LIGHT", "_lane": lane})
    lights.sort(key=lambda p: p.get("mergedAt", ""))

    # one pass: per lane, the k-th LIGHT spends the k-th unit of budget
    spent: dict[str, list[int]] = {}
    out = []
    for pr in lights:
        lane = pr["_lane"]
        budget = light_budget(grains_by_lane.get(lane, 0))
        prior = spent.setdefault(lane, [])
        cap = len(prior) >= budget
        out.append({
            "number": pr.get("number"),
            "lane": lane,
            "mergedAt": pr.get("mergedAt"),
            "cap_reached": cap,
            "budget": budget,
            "lane_grains": grains_by_lane.get(lane, 0),
            # the LIGHT that spent the last budget unit, for the message
            "consumed_by": prior[-1] if cap and prior else None,
        })
        if not cap:
            prior.append(pr.get("number"))
    return out


# --- genre-based cap (G-VAR-2/3 by GENRE, #10020) ---------------------------
#
# The tier is an AUTO-DECLARATION (gameable without intent to game): a lane
# that never declares `LIGHT` is never capped, whatever the substance of the
# merges. Measured firsthand on the 2026-08-08 UTC day set (issue #10020,
# §Le defaut, mesure): po-2025:CoursIA-2 merged 16 grains, declared 0 LIGHT,
# 8 of which were GENRE-LIGHT (5 readme + 2 docs + 1 guard via alias). Five
# readme consecutive, all declared MED -- the G-VAR-3 ban "pas 2 meme genre
# LIGHT consecutif" was violated FOUR times without any gate turning red.
#
# The GENRE is harder to deviate than the TIER:
#
#   * the enumeration is CLOSED (#9485 §1: lean, qc, training, genai,
#     notebook-python, notebook-dotnet, docs, guard, refactor, ledger, readme,
#     test, tooling, research-code) and an ALIAS TABLE normalises the
#     observed variants (docs-translation -> docs, lean-ci -> guard,
#     test-coverage -> test, data -> ledger, <famille>-<genre> -> its HEAD);
#   * the genre is CORROBORATED by the diff paths -- a grain whose diff is
#     only `*.md` files (outside the durable `docs/**` background of a repo)
#     is readme/docs regardless of the declared genre.
#
# This module computes the parallel tally and emits FOUR advisory signals:
#
#   1. TIER-INFLATION         -- declared LIGHT count vs effective LIGHT-genre
#                                count diverge on a lane-day (the declaration
#                                and the substance disagree).
#   2. GENRE-RUN              -- >= 2 consecutive grains of the same LIGHT
#                                genre for a lane, regardless of declared TIER
#                                (G-VAR-3 by GENRE, the ban the defect
#                                bypassed).
#   3. CAP-EXCEEDED-BY-GENRE  -- LIGHT-genre count exceeds the G-VAR-2 budget
#                                (the cap that was empty because the LIGHT
#                                counter looked at the wrong axis).
#   4. GENRE-MISMATCH         -- declared genre disagrees with the genre
#                                inferred from the diff paths (e.g. declared
#                                `tooling` but the diff is README-only).
#
# Each signal is ADVISORY (exit 0, surfacing in the label of the workflow);
# the G-VAR-2 budget's hard arithmetic is preserved -- a lane can still be
# budget-capped the old way, and these signals stack ON TOP without
# rewriting either rule. No wildcard exemption: every whitelist (lane, genre)
# would be an explicit named argument, the same cliquet as `allow-axioms`
# and `--allow-unbuilt`.
#
# See issue #10020 for the full motivation and acceptance; the per-issue
# reference case (`po-2025:CoursIA-2` 2026-08-08) is replayed as
# `test_replay_po2025_signals_genre_run` below.

# variation-protocol §1 alias table -- the same one the §1 rule uses for
# self-correction (the worker is not sanctioned for an alias; the alias
# folds to its head). `<famille>-<genre>` patterns (`cjk-ci`,
# `audit-tooling`) are REDUCED to their head via `_FAMILY_GENRE_RE`
# below, and then matched against the synonym map.
_GENRE_ALIASES = {
    "docs-translation": "docs",
    "translation": "docs",          # po-2025 emits "MED/translation" (observed)
    "lean-ci": "guard",
    "cjk-ci": "guard",              # alias family: cjk-*-ci -> guard
    "audit-tooling": "tooling",
    "test-coverage": "test",
    "data": "ledger",
    "slidev": "slides",              # outil -> type de travail (cf #11059)
}

# Compoments `<famille>-<genre>` always reduce to the head genre (the family
# is already the path of the diff, not the type of work). The pattern matches
# a hyphen-separated tail; the head token at the head of the tail is returned.
_FAMILY_GENRE_RE = re.compile(r"^[A-Za-z0-9]+-([A-Za-z0-9_-]+)$")


def canonicalize_genre(genre: str | None) -> str | None:
    """Return the genre that counts for G-VAR-2/3, after alias normalisation.

    The input is the token from the body (`grain_tag.parse_grain_tag`), already
    lower-cased by the extractor. The output is:
      * the input itself when it IS in the canonical GENRES list -- the
        canonical list contains hyphenated forms on purpose
        (`notebook-python`, `notebook-dotnet`) which the compound rule
        below would otherwise decapitate to `python` / `dotnet`
        (a real bug caught by `test_lane_genre_tally_po2025_day`
        on 2026-08-08: the tally raised `KeyError: 'notebook-python'`).
      * the alias-map hit (e.g. `translation` -> `docs`)
      * the head of a `<famille>-<genre>` compound (e.g. `cjk-ci` -> `ci`
        then `ci` is not aliased so it stays `ci` -- `ci` is NOT in the
        enumeration, it falls to `None`? No: `ci` as a head is preserved
        verbatim. The map is exhaustive for the observed compound forms.)
      * the input itself if no rule matches.

    Returns `None` when the input is `None` or empty.
    """
    if not genre:
        return None
    g = genre.strip().lower()
    if not g:
        return None
    # Canonical genres (including the hyphenated forms) are preserved verbatim.
    # Without this guard, `notebook-python` would fall to `python` under the
    # compound rule below, which is NOT in the canonical enumeration and
    # therefore not in `by_genre` keys.
    if g in GENRES:
        return g
    if g in _GENRE_ALIASES:
        return _GENRE_ALIASES[g]
    # Compound form `<famille>-<genre>` -> head. The head is the LAST
    # hyphen-separated segment, NOT the first -- `lean-ci` is family=`lean`,
    # genre=`ci`; `cjk-ci` is family=`cjk`, genre=`ci`; `audit-tooling` is
    # family=`audit`, genre=`tooling`. The head is `ci` or `tooling`, and
    # the alias map handles those.
    if "-" in g:
        head = g.rsplit("-", 1)[-1]
        if head in _GENRE_ALIASES:
            return _GENRE_ALIASES[head]
        return head
    return g


# LIGHT-genre set -- the genres G-VAR-3 bans consecutively AND G-VAR-2's
# budget counts against. Sourced from variation-protocol.md §1 / §3: a genre
# in this set is one where "pourrais-je en generer une douzaine en scannant
# l'instance suivante" lands on YES (the litmus that separates LIGHT from
# MED/DEEP). The compound of "the lockout genres" + "the budget genres" is
# intentional -- a genre banned from adjacency is, by the same litmus, a
# genre that counts against the budget.
LIGHT_GENRES = frozenset({"docs", "readme", "guard", "ledger", "test"})


def effective_genre(body: str | None, labels: list[str]) -> str | None:
    """The CANONICAL genre for G-VAR-2/3.

    The declared genre (read by `grain_tag.parse_grain_tag`) folded through
    `canonicalize_genre`. Labels are accepted for symmetry with
    `effective_tier` but do NOT currently override the genre (the
    `grain-requalified:<TIER>` label is tier-only; the genre is the worker's
    substance claim, not a coordinator re-qualification field). Returns
    `None` when no genre can be read from the body.
    """
    g = parse_grain_tag(body or "")
    if g is None:
        return None
    return canonicalize_genre(g["genre"])


def _candidate_record(merged_prs: list[dict], target_lane: str) -> list[dict]:
    """For each merged PR, return the per-lane per-grain record.

    Each record is a dict with {number, lane, tier, genre, canonical_genre,
    is_light_genre, mergedAt} -- the flat shape the signals iterate over.
    PRs without a readable Grain tag are dropped (unattributed, never
    counted, same policy as `lane_grains`).
    """
    out = []
    for pr in merged_prs:
        body = pr.get("body", "") or ""
        labels = label_names(pr)
        g = parse_grain_tag(body)
        if g is None or not g["lane"]:
            continue
        if g["lane"] != target_lane:
            continue
        out.append({
            "number": pr.get("number"),
            "lane": g["lane"],
            "tier": effective_tier(body, labels),
            "genre": g["genre"],
            "canonical_genre": canonicalize_genre(g["genre"]),
            "is_light_genre": canonicalize_genre(g["genre"]) in LIGHT_GENRES,
            "mergedAt": pr.get("mergedAt", ""),
        })
    out.sort(key=lambda r: r["mergedAt"])
    return out


def lane_genre_tally(merged_prs: list[dict], target_lane: str) -> dict:
    """The day-tally that G-VAR-2/3 by GENRE needs.

    Returns a dict with:
      * `lane_grains` -- same denominator as `lane_grains()` (every grain
        of the lane, any tier -- DEEP and MED earn the budget).
      * `light_declared` -- grains whose EFFECTIVE tier is LIGHT (the
        existing G-VAR-2 numerator, unchanged).
      * `light_genre` -- grains whose CANONICAL genre is in `LIGHT_GENRES`
        (the new numerator, regardless of declared tier). A declared
        LIGHT/refactor that aliases to nothing in the LIGHT set does NOT
        contribute; a declared MED/readme DOES contribute.
      * `by_genre` -- dict {canonical_genre: count} over the lane's
        tagged grains, sorted by descending count (the histogram that
        surfaces the GENRE-RUN at a glance).
      * `cap` -- the G-VAR-2 budget = `max(1, lane_grains // 3)`,
        identical to the existing organ's budget. The genre-cap and the
        tier-cap share the budget: same ratio, two numerators.

    Untagged PRs are EXCLUDED (matching `lane_grains`); a day whose lane
    has only untagged PRs returns `lane_grains == 0` and `cap == 1`,
    matching the existing floor.
    """
    recs = _candidate_record(merged_prs, target_lane)
    light_declared = sum(1 for r in recs if r["tier"] == "LIGHT")
    light_genre = sum(1 for r in recs if r["is_light_genre"])
    by_genre: dict[str, int] = {}
    for r in recs:
        cg = r["canonical_genre"]
        if cg is None:
            continue
        by_genre[cg] = by_genre.get(cg, 0) + 1
    return {
        "lane_grains": len(recs),
        "light_declared": light_declared,
        "light_genre": light_genre,
        "cap": light_budget(len(recs)),
        "by_genre": dict(sorted(by_genre.items(), key=lambda kv: (-kv[1], kv[0]))),
    }


def genre_runs(merged_prs: list[dict], target_lane: str) -> list[dict]:
    """Runs of consecutive grains of the SAME LIGHT-genre for `target_lane`.

    A run is a maximal sequence of chronologically-adjacent grains (no
    break by a different genre) whose canonical genre is in `LIGHT_GENRES`.
    Returns a list of `{genre, count, numbers}` dicts, one per run.

    The unit is a run of `count >= 1`. G-VAR-3 by GENRE bans runs of
    `count >= 2`: the organ reports each run that crosses the threshold,
    the merger step decides whether to HOLD. An isolated `readme` (count
    1) is NOT a run -- it is a single grain of a banned genre, the budget
    catches that, not the adjacency rule.

    The function is pure (the order is `mergedAt` ascending, the same as
    `_candidate_record`); it does not consult the declared tier. The
    "regardless of declared tier" wording of issue #10020 §GENRE-RUN is
    the point: a MED/readme consecutive to a MED/readme is the same
    violation as a LIGHT/readme consecutive to a LIGHT/readme.
    """
    recs = _candidate_record(merged_prs, target_lane)
    runs: list[dict] = []
    current: dict | None = None
    for r in recs:
        if not r["is_light_genre"]:
            # Non-LIGHT-genre grain breaks the run; the current LIGHT-genre
            # streak (if any) closes and starts fresh on the next LIGHT-genre.
            current = None
            continue
        cg = r["canonical_genre"]
        if current is not None and current["genre"] == cg:
            current["count"] += 1
            current["numbers"].append(r["number"])
        else:
            current = {"genre": cg, "count": 1, "numbers": [r["number"]]}
            runs.append(current)
    return runs


def _genre_from_paths(files: list[str] | None) -> str | None:
    """Best-effort GENRE inferred from a PR's diff file paths.

    Issue #10020 §Corroboration, refined by #10102: the heuristic can only
    arbitrate the `docs`/`readme` axis, and ONLY for diffs that are 100%
    `*.md`. Implemented as:

      * paths absent or empty                    -> None (no signal)
      * any non-`*.md` path present              -> None (a code PR; the
        heuristic cannot distinguish `lean`/`notebook-python`/`qc`/...,
        so it abstains -- forcing `tooling` here would MISMATCH 12 of 14
        honest code declarations, #10102)
      * any `*.md` under `docs/` or `.claude/`   -> `docs` (prose/rule work)
      * all `*.md` named `README*`               -> `readme`
      * other `*.md`-only diffs                  -> None (cannot classify
        confidently, e.g. a lone series .md; abstain)

    The signal therefore fires ONLY in the case the heuristic can decide: a
    100%-`*.md` diff whose paths pin the genre to `docs` or `readme`,
    contrasted with a declared genre that disagrees. A code PR (any
    non-`*.md` file) sees NO GENRE-MISMATCH -- the previous `tooling`
    inference flagged every honest code declaration (#10102 measured 6 of 7
    open PRs). A missing `--files` is INACTIVE: a missing input is a missing
    signal, never a false positive.
    """
    if not files:
        return None
    # Normalise Windows backslashes to forward slashes for the prefix test.
    norm = [f.replace("\\", "/") for f in files]
    if not all(f.endswith(".md") for f in norm):
        # Any non-md file -> a code-change PR. The heuristic cannot
        # distinguish code genres (`lean`/`notebook-python`/`qc`/...), so it
        # abstains (None) rather than force a `tooling` inference that would
        # MISMATCH 12 of 14 honest code declarations (#10102).
        return None
    # md-only diff: classify the prose work.
    if any(f.startswith("docs/") or f.startswith(".claude/") for f in norm):
        return "docs"
    if all(f.rsplit("/", 1)[-1].upper().startswith("README") for f in norm):
        return "readme"
    # md-only but neither docs/.claude/ nor all-README (e.g. a lone series
    # .md): the heuristic cannot confidently classify -> abstain.
    return None


def compute_signals(
    merged_prs: list[dict],
    target_lane: str,
    *,
    candidate_genre: str | None = None,
    candidate_files: list[str] | None = None,
) -> dict:
    """Compute the four advisory G-VAR-2/3-by-GENRE signals for `target_lane`.

    The tally is over the merged PRs (the day set); the candidate is the
    OPEN PR currently being assessed (NOT in the merged set, but counted
    in the denominator for G-VAR-2 status). For signal emission:

      * `TIER-INFLATION`         -- `tally["light_genre"] > tally["light_declared"] + 1`
                                    at the lane-day level. The +1 tolerance
                                    absorbs the open candidate without
                                    declaring every single-MED-then-LIGHT
                                    day as inflation.
      * `GENRE-RUN`              -- any run in `genre_runs()` of `count >= 2`.
                                    Returned as the list of runs (each
                                    `{genre, count, numbers}`); the workflow
                                    flags a label when the list is non-empty.
      * `CAP-EXCEEDED-BY-GENRE`  -- `tally["light_genre"] > tally["cap"]`.
      * `GENRE-MISMATCH`         -- `candidate_genre is not None` AND
                                    `_genre_from_paths(candidate_files)` is
                                    not None AND the two disagree.

    Three of the four signals (TIER-INFLATION, GENRE-RUN, CAP-EXCEEDED-BY-
    GENRE) are LANE-DAY aggregates: they are True when the lane's merged
    set of the day trips the rule, regardless of whether the OPEN
    candidate contributes. GENRE-MISMATCH alone carries on the candidate
    (declared genre vs its own diff paths). The return therefore also
    exposes `candidate_is_light_genre` so the workflow can avoid posing
    an aggregate label on a CONTENT candidate that does not contribute to
    the pattern it denounces (#10341 -- otherwise the merge-gate, which
    reads the LABEL, would HOLD the grain that REMEDIES the motif instead
    of the META grains that caused it).

    The function returns the tally, the list of runs, and the four signals
    ON the tally/candidate -- the workflow decides what to label. The
    G-VAR-2 organ (the original `light_cap_status`) is unchanged: a PR
    that is `cap_reached=False` for the TIER can still trip
    `CAP-EXCEEDED-BY-GENRE` here, and vice versa -- the two signals are
    independent axes of the same day arithmetic.

    `candidate_genre` defaults to `None` (no claim from the open PR's tag)
    which makes GENRE-MISMATCH inactive; `candidate_files` defaults to
    `None` which makes it inactive too. Pass both to opt in.
    """
    tally = lane_genre_tally(merged_prs, target_lane)
    runs = genre_runs(merged_prs, target_lane)
    long_runs = [r for r in runs if r["count"] >= 2]

    # TIER-INFLATION: the GENRE-LIGHT count is more than 1 above the
    # DECLARED-LIGHT count. Tolerance +1 absorbs the natural case "one
    # declared MED that reads as a LIGHT-genre (e.g. MED/readme) -- that
    # is NOT inflation, that is the subtler observation the defect
    # tracks". The signal is raised when the inflation is sustained (>1).
    inflation = tally["light_genre"] > tally["light_declared"] + 1

    cap_exceeded = tally["light_genre"] > tally["cap"]

    inferred = _genre_from_paths(candidate_files) if candidate_files is not None else None
    can_canon = canonicalize_genre(candidate_genre) if candidate_genre else None
    genre_mismatch = (
        inferred is not None
        and can_canon is not None
        and inferred != can_canon
    )

    return {
        "lane": target_lane,
        "tally": tally,
        "runs": runs,
        "signals": {
            "TIER-INFLATION": inflation,
            "GENRE-RUN": bool(long_runs),
            "CAP-EXCEEDED-BY-GENRE": cap_exceeded,
            "GENRE-MISMATCH": genre_mismatch,
        },
        "long_runs": long_runs,
        "inferred_genre_from_paths": inferred,
        "candidate_genre_canonical": can_canon,
        # Whether the OPEN candidate is itself a LIGHT-genre grain, i.e. a
        # CONTRIBUTOR to the pattern the three aggregate signals denounce.
        # False when the candidate is CONTENT (genai/lean/qc/notebook-.../)
        # or carries no readable genre -- in both cases it cannot contribute
        # to light_genre / a genre-run / the cap numerator, so an aggregate
        # label posed on it would misattribute a lane-day pattern to a grain
        # that does not carry it (#10341). GENRE-MISMATCH is unaffected: it
        # is the one signal whose subject IS the candidate by construction.
        "candidate_is_light_genre": can_canon in LIGHT_GENRES,
    }


# --- CLI -------------------------------------------------------------------

# `gh pr list` pagine a 30 par defaut et ne le dit pas. Un dataset de
# *exactement* 30 PRs est donc presque toujours une page tronquee, pas une
# journee a 30 merges -- et la troncature attaque le DENOMINATEUR du ratio
# G-VAR-2 : lane_grains sous-compte, `max(1, n // 3)` retombe sur son plancher
# de 1, et l'organe accuse de CAP-EXCEEDED la lane la plus productive du jour
# (exactement l'inverse de ce que le ratio existe pour proteger). Constate le
# 2026-08-10 sur #10328 : 60 PRs mergees, l'organe en voyait 30, la lane
# `myia-po-2024:CoursIA` comptait 11 grains vus comme <=2 -> cap=1, faux
# positif. Le correctif est le `--limit` cote workflow ; ce tell existe pour
# que la PROCHAINE copie de l'idiome ne puisse pas le reintroduire en silence.
_GH_DEFAULT_PAGE = 30


def _load(path: str) -> list[dict]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(data, list):
        sys.exit(f"--replay/--check-pr expects a JSON array, got {type(data).__name__}")
    if len(data) == _GH_DEFAULT_PAGE:
        print(
            f"AVERTISSEMENT: le jeu de comptage fait exactement {_GH_DEFAULT_PAGE} "
            "entrees = la taille de page par defaut de `gh pr list`. Si le "
            "producteur du dataset n'a pas passe --limit, le set est TRONQUE : "
            "le denominateur de G-VAR-2 sous-compte et le cap retombe a son "
            "plancher de 1 (faux CAP-EXCEEDED sur les lanes productives).",
            file=sys.stderr,
        )
    return data


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--replay", metavar="FILE",
                   help="JSON array of the day's merged PRs (the counting set)")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--replay-mode", action="store_true",
                   help="acceptance-test mode: report cap_reached for every "
                        "LIGHT in the --replay set")
    g.add_argument("--check-pr", metavar="N", type=int,
                   help="CI mode: assess PR <N> (the current open PR) against "
                        "the --replay merged set")
    g.add_argument("--genre-signals", action="store_true",
                   help="emit the four G-VAR-2/3-by-GENRE signals (#10020): "
                        "TIER-INFLATION, GENRE-RUN, CAP-EXCEEDED-BY-GENRE, "
                        "GENRE-MISMATCH. Pairs with --lane (the lane to "
                        "assess). Advisory, exit 0; signal carried in the "
                        "output JSON and intended for the workflow label.")
    p.add_argument("--body", metavar="TEXT",
                   help="--check-pr / --genre-signals: body of the current PR "
                        "(used to read its Grain tag -- not in the merged set)")
    p.add_argument("--body-file", metavar="FILE",
                   help="--check-pr / --genre-signals: path to a file holding "
                        "the current PR body (alternative to --body)")
    p.add_argument("--labels-file", metavar="FILE",
                   help="--check-pr / --genre-signals: JSON array of the "
                        "current PR's labels (so a requalification label on "
                        "the open PR is honored; symmetric to the "
                        "requalification read on merged PRs)")
    p.add_argument("--lane", metavar="LANE",
                   help="--genre-signals only: target lane (machine:workspace). "
                        "Required for --genre-signals; not used by the other "
                        "modes (which read the lane from the current PR body)")
    p.add_argument("--files", metavar="LIST",
                   help="--genre-signals only: comma-separated list of diff "
                        "paths of the current PR (for the GENRE-MISMATCH "
                        "corroboration). If absent, GENRE-MISMATCH is "
                        "inactive (no false positive on missing input).")
    args = p.parse_args(argv)

    if not args.replay:
        p.error("--replay FILE (the merged-PR set) is required")

    merged = _load(args.replay)

    if args.check_pr is not None:
        # CI mode: the current PR is OPEN, so its body is NOT in the merged set.
        #
        # G-VAR-2 by GENRE (#10480): the verdict consumes BOTH cap axes -- the
        # TIER cap (declared/effective LIGHT count, `light_cap_status`) AND the
        # GENRE cap (LIGHT-genre count, `lane_genre_tally`). The defect this
        # closes: a lane declared MED on readme grains saw `cap_reached: false`
        # from --check-pr (the tier axis was empty) while --genre-signals
        # screamed `CAP-EXCEEDED-BY-GENRE` (the genre axis was saturated) --
        # same lane, same day, same script, contradictory verdicts, and the
        # merge-gate (which reads --check-pr) let the bypass through. The
        # single-source fix: --check-pr surfaces both axes, the `counts` field
        # discloses which were tallied, and `cap_reached` is the UNION when the
        # candidate itself carries the LIGHT-genre motif (#10341 preserves the
        # innocent-CONTENT candidate from a lane-day aggregate it does not
        # contribute to).
        body = None
        if args.body is not None:
            body = args.body
        elif args.body_file:
            body = Path(args.body_file).read_text(encoding="utf-8")
        if body is None:
            p.error("--check-pr requires --body or --body-file")
        cur_labels: list[str] = []
        if args.labels_file:
            cur_labels = load_labels_file(Path(args.labels_file))
        # Effective tier (#8970): a requalification label overrides the declared
        # one. Only an EFFECTIVE LIGHT spends the TIER budget. The GENRE budget
        # is read off the declared genre (`effective_genre`), which a
        # requalification label does NOT override -- the genre is the worker's
        # substance claim, not a coordinator re-qualification field.
        eff = effective_tier(body, cur_labels)
        g = parse_grain(body)
        cand_genre = effective_genre(body, cur_labels)
        candidate_is_light_genre = cand_genre in LIGHT_GENRES

        # UNASSESSABLE vs ASSESSED (#9465). `cap_reached: false` must mean one
        # thing only: "assessed, and within budget". A body with no readable
        # tag, or a tag without a lane, is not an exemption -- it is a
        # measurement the organ could not take, and reporting it as `false`
        # made the gate green precisely where it was blind. `null` is the
        # third state; the caller (variation-tag-guard.yml) compares against
        # "True", so this stays advisory and no CI behaviour changes.
        if eff is None or not g:
            print(json.dumps({
                "cap_reached": None,
                "reason": "unassessable -- no Grain: tag in body",
            }))
            return 0
        lane = g["lane"]
        # A non-LIGHT tier never spends the TIER budget; a non-LIGHT-GENRE
        # grain never spends the GENRE budget. A candidate that carries
        # NEITHER axis (DEEP/lean, MED/tooling) gets the historical "not
        # LIGHT" verdict -- the #10341 guard: a lane-day aggregate pattern
        # must not be posed on a CONTENT candidate that does not carry it.
        # Only a non-LIGHT tier that IS a LIGHT-genre (the MED/readme defect
        # case) falls through to the structured assessment where the genre
        # cap can flip `cap_reached`.
        if eff != "LIGHT" and not candidate_is_light_genre:
            out: dict = {"cap_reached": False, "reason": f"not LIGHT (effective {eff})"}
            if lane:
                # The lane's genre-cap may already be saturated by OTHER
                # grains of the day. Surface it informationally (it does NOT
                # flip `cap_reached` -- this candidate does not carry the
                # motif) so the coordinator sees the lane-day pattern at
                # merge time without the gate holding an innocent grain.
                tally_info = lane_genre_tally(merged, lane)
                if tally_info["light_genre"] > tally_info["cap"]:
                    out["lane_genre_saturated"] = True
            print(json.dumps(out))
            return 0
        if not lane:
            # An effective LIGHT (or a LIGHT-genre MED) with no lane is the one
            # case where an axis is known and the answer still cannot be
            # computed: both budgets are per-lane, so without a lane there is
            # no denominator to compare to on either axis.
            print(json.dumps({
                "cap_reached": None,
                "reason": "unassessable -- LIGHT (or LIGHT-genre) but no lane in tag",
            }))
            return 0
        # Structured assessment: effective LIGHT, OR a LIGHT-genre MED/DEEP.
        # The two cap axes share the SAME CI window (lane_grains + 1 -- the
        # open candidate is itself a grain of the day, counted in both
        # denominators). The GENRE axis is aligned on the TIER window here;
        # --genre-signals (the audit path) keeps the merged-only window
        # because the day is over there and the denominator is KNOWN.
        status = light_cap_status(merged, lane)
        tally = lane_genre_tally(merged, lane)
        light_genre_count = tally["light_genre"] + (1 if candidate_is_light_genre else 0)
        genre_cap = light_budget(tally["lane_grains"] + 1)  # +1 candidate, aligned
        cap_exceeded_by_genre = light_genre_count > genre_cap
        tier_cap_reached = status["cap_reached"]
        # UNION only when the candidate carries the genre motif (#10341): a
        # LIGHT/tooling (tier LIGHT, genre not LIGHT) cannot trip the genre
        # cap; a MED/readme (tier MED, genre LIGHT) can. Both directions of
        # the defect are closed -- the declared-MED bypass AND the coherence
        # with --genre-signals.
        cap_reached = tier_cap_reached or (cap_exceeded_by_genre and candidate_is_light_genre)
        print(json.dumps({
            "pr": args.check_pr,
            "lane": lane,
            "cap_reached": cap_reached,
            "tier_cap_reached": tier_cap_reached,
            "cap_exceeded_by_genre": cap_exceeded_by_genre,
            "budget": status["budget"],
            "spent": status["spent"],
            "light_genre": light_genre_count,
            "genre_cap": genre_cap,
            "lane_grains": status["lane_grains"],
            "consumed_by": status["consumed_by"],
            "counts": "tier+genre",
        }))
        return 0

    if args.genre_signals:
        # --genre-signals mode (#10020): emit the four advisory signals for
        # `--lane`. The candidate PR's body is read for GENRE-MISMATCH
        # (compared to the diff paths passed via --files). When the body
        # is absent, GENRE-MISMATCH stays inactive -- a missing input is
        # a missing signal, never a false positive.
        if not args.lane:
            p.error("--genre-signals requires --lane LANE")
        cand_body = None
        if args.body is not None:
            cand_body = args.body
        elif args.body_file:
            cand_body = Path(args.body_file).read_text(encoding="utf-8")
        cand_labels: list[str] = []
        if args.labels_file:
            cand_labels = load_labels_file(Path(args.labels_file))
        cand_genre = effective_genre(cand_body, cand_labels) if cand_body else None
        cand_files = [f.strip() for f in (args.files or "").split(",") if f.strip()] \
            if args.files is not None else None
        sig = compute_signals(
            merged,
            args.lane,
            candidate_genre=cand_genre,
            candidate_files=cand_files,
        )
        # The workflow reads the JSON and applies a label per True signal;
        # we do NOT throw a non-zero exit -- the gate is advisory, the
        # consumer is the coordinator at merge time. Same posture as
        # --check-pr's cap_reached branch.
        print(json.dumps(sig, ensure_ascii=False))
        return 0

    # replay mode: the acceptance test
    rows = replay(merged)
    flagged = [r for r in rows if r["cap_reached"]]
    blind = unattributed(merged)
    print(f"LIGHT PRs replayed: {len(rows)} | cap-reached: {len(flagged)}"
          f" | unattributed: {len(blind)}/{len(merged)}")
    if blind:
        # Without this line a day whose PRs are all untagged prints exactly
        # like a clean day (#9465): `replayed: 0 | cap-reached: 0`.
        print(f"  WARNING: {len(blind)} of {len(merged)} merged PRs carry no "
              f"readable `Grain:` tag -- they are counted in NO lane, so the "
              f"figures above measure only the tagged remainder.")
        print("  unattributed: "
              + ", ".join(f"#{pr.get('number')}" for pr in blind))
    print(f"{'PR':>7}  {'lane':<28} {'mergedAt':<21} cap")
    for r in rows:
        mark = "CAP-REACHED" if r["cap_reached"] else "ok"
        print(f"  #{r['number']:<5} {r['lane']:<28} {r['mergedAt']:<21} {mark}"
              + (f"  (consumed by #{r['consumed_by']})" if r["cap_reached"] else ""))
    print(json.dumps({
        "rows": rows,
        "unattributed": [pr.get("number") for pr in blind],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
