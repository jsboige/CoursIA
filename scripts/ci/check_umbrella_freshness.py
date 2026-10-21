#!/usr/bin/env python3
r"""Confront an umbrella/EPIC body with the repository BEFORE judging it actionable.

Context (#11900): the picker is the first gesture of every cycle, and it weights
*delassement* (days since last activity) to surface what the fleet neglects. But
the older an EPIC is, the more likely its body is false -- so the harder the
picker does its job, the more apparent dead-ends it raises. #11900 measured this
on two consecutive draws (#2874, #7357); both EPICs were fully actionable and
both blocking paragraphs had outlived their own resolution.

The cost is paid by every lane that draws the umbrella: it reads a body dated
from its writing, concludes "blocked on someone else", and re-shelves it. This
organ makes the mechanical half of that confrontation cheap, so the verdict is
measured rather than felt.

Two of the three surfaces #11900 names are decided mechanically:

  1. referenced CONTENT numbers (#N) -> resolve each one's kind and state. An
     EPIC whose every referenced child issue is CLOSED has nothing left to pick
     inside it: the picker offered a container, not a grain.
  2. cited FILE PATHS -> checked against the working tree. A body that points at
     a path which no longer exists is the #2874 signature (the lake moved to
     SymbolicAI/Lean/ and the body kept the old location).

The third surface -- a pending DECISION request -- is NOT machine-decidable: the
answer is usually in the first comment. This organ emits it as an explicit
manual step rather than guessing at it.

Verdicts:
    SATURATED   every referenced issue is CLOSED (exit 1)
    FRESH       at least one OPEN reference declares a filiation with this
                umbrella (exit 0)
    UNRESOLVED  the body references no child issue, the filiation of an OPEN
                reference could not be read, or every OPEN reference is a
                cross-reference without declared filiation (exit 0, advisory)

The filiation is read in BOTH directions: the referenced issue may declare
this umbrella as its parent ("Part of #N", "Fille de #N", ...), and this
umbrella may declare the referenced issue as its own parent or grand-parent
("Fille de #17578 ... petite-fille de l'EPIC #10355"). Without that
distinction, a container whose children are all closed is declared FRESH
because of an unrelated issue mentioned in prose, and the lane serves a closed
sub-grain (measured on #4362, c.2266).

The converse is NOT decided here: an umbrella can hold open work that no issue
declares (a body naming it as a "brique" without a filiation sentence).
A red would then be forged, so that case stays ADVISORY -- the umbrella's own
body is the arbiter.

Missing cited paths are reported as `warnings` and never decide the exit code:
a path may legitimately have moved, and a guard must not fabricate a red on a
signal it cannot interpret. Exit 1 is reserved for the one reading that is not
ambiguous -- an umbrella with every door closed.

Usage:
    python scripts/ci/check_umbrella_freshness.py <issue> [<issue> ...]
    python scripts/ci/check_umbrella_freshness.py <issue> --json
    python scripts/ci/check_umbrella_freshness.py <issue> --repo-root .

Unknown inputs (network failure, gh unavailable) exit 0 with verdict "unknown"
plus a ::warning -- infrastructure never forges a red (#14849).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = "jsboige/CoursIA"

# This repository's oldest live content numbers are 3-digit (#221, #498, #833),
# so a 3-digit floor keeps them while dropping noise like "§12" or "PR #12".
REF_RE = re.compile(r"#(\d{3,6})")

# Backticked tokens that plausibly name a repository path. A path must contain a
# separator and be either a directory (trailing /) or carry an extension. Globs
# are excluded: their existence is not a yes/no question.
PATH_RE = re.compile(r"`([A-Za-z0-9_][A-Za-z0-9_./-]*/[A-Za-z0-9_./-]+)`")
EXT_RE = re.compile(r"\.[A-Za-z0-9]{1,6}$")


def extract_refs(body: str, self_number: int) -> list[int]:
    """Content numbers referenced by the body, self-reference removed."""
    seen: list[int] = []
    for match in REF_RE.finditer(body or ""):
        number = int(match.group(1))
        if number != self_number and number not in seen:
            seen.append(number)
    return seen


def extract_paths(body: str) -> list[str]:
    """Repository paths cited in backticks, globs and artefacts excluded."""
    found: list[str] = []
    for match in PATH_RE.finditer(body or ""):
        candidate = match.group(1)
        if "*" in candidate or "{" in candidate:
            continue
        if not candidate.endswith("/") and not EXT_RE.search(candidate):
            continue
        if candidate not in found:
            found.append(candidate)
    return found


def classify_ref(number: int, raw: dict | None) -> dict:
    """Normalise one GitHub issue/PR payload into kind + state."""
    if raw is None:
        return {"number": number, "kind": "unknown", "state": "UNKNOWN",
                "merged": False}
    pull = raw.get("pull_request")
    is_pr = isinstance(pull, dict)
    merged = bool(is_pr and pull.get("merged_at"))
    return {
        "number": number,
        "kind": "pr" if is_pr else "issue",
        "state": str(raw.get("state") or "").upper(),
        "merged": merged,
    }


# --- relation enfant : l'issue referencee declare-t-elle CET umbrella comme parent ? ---
#
# Le corps d'un umbrella cite des numeros qui ne sont pas tous ses enfants : un
# lien transversal ("voir aussi #4208") se lit comme une reference ouverte et
# fait dire FRESH a un conteneur vide. Mesure (c.2266) : #4362, umbrella Lean
# dont les 8 enfants Lean sont CLOSES, etait declare FRESH a cause d'un EPIC
# sans rapport cite dans son corps -- la lane a donc servi un sous-grain ferme.
#
# Le critere mesurable est la declaration faite par l'ENFANT : la convention du
# depot est que l'issue nomme son parent ("Part of #N"). C'est cette
# declaration qui fait la relation, et elle se lit sans ambiguite.

def parent_decl_patterns(parent_number: int) -> list[re.Pattern]:
    """Phrases de declaration de filiation, mesurees sur le corps/titre d'un issue.

    La convention du depot n'a pas une forme unique : un enfant declare son
    parent ("Part of #N", "Fille de #N", "Sous-issue de #N", "parent: #N") et
    un petit-enfant declare son grand-parent ("petite-fille de l'EPIC #N",
    "EPIC grand-mere #N"). Les deux sens sont lus avec le meme jeu de motifs :
    c'est la FILIATION qui compte, pas le sens ou elle s'exprime.
    """
    number = parent_number
    return [
        re.compile(rf"part\s+of\s+#{number}\b", re.IGNORECASE),
        re.compile(rf"child\s+of\s+#{number}\b", re.IGNORECASE),
        re.compile(rf"fille\s+de\s+#{number}\b", re.IGNORECASE),
        re.compile(rf"fils\s+de\s+#{number}\b", re.IGNORECASE),
        re.compile(rf"sous[-\s]issue\s+de\s+#{number}\b", re.IGNORECASE),
        re.compile(rf"enfant\s+de\s+#{number}\b", re.IGNORECASE),
        re.compile(rf"issue\s+fille\s+de\s+#{number}\b", re.IGNORECASE),
        re.compile(rf"parent\s*:?\s+#{number}\b", re.IGNORECASE),
        re.compile(rf"petite[-\s]fille\s+de\s+(l['’]\s*)?(EPIC\s+)?#{number}\b",
                   re.IGNORECASE),
        re.compile(rf"petit[-\s]fils\s+de\s+(l['’]\s*)?(EPIC\s+)?#{number}\b",
                   re.IGNORECASE),
        re.compile(rf"grand[-\s]m[eè]re\s+(de\s+)?(l['’]\s*)?(EPIC\s+)?#{number}\b",
                   re.IGNORECASE),
        re.compile(rf"anc[eê]tre\s+de\s+#{number}\b", re.IGNORECASE),
    ]


def declares_parent(child_body: str, parent_number: int) -> bool:
    """Ce corps (ou ce titre) declare-t-il la filiation avec ce numero ?"""
    body = child_body or ""
    return any(pattern.search(body) for pattern in parent_decl_patterns(parent_number))


def classify(refs: list[dict], missing_paths: list[str],
             child_flags: dict[int, bool | None] | None = None) -> dict:
    """Apply the verdict rules. Pure: the caller supplies measured states.

    `child_flags` maps the number of an OPEN referenced issue to the measured
    FILIATION relation: True (the two issues declare each other as parent /
    child / grand-parent in one direction or the other), False (no declared
    filiation -- a cross-reference) or None (unreadable). When it is None the
    whole mapping is unmeasured, and the verdict keeps its historical reading
    (any open reference keeps the umbrella FRESH).
    """
    issues = [r for r in refs if r["kind"] == "issue"]
    open_issues = [r for r in issues if r["state"] == "OPEN"]

    warnings = [
        f"cited path not found in the working tree: {path}"
        for path in missing_paths
    ]

    if issues and not open_issues:
        return {
            "verdict": "SATURATED",
            "reason": (
                f"all {len(issues)} referenced child issue(s) are CLOSED -- "
                "the umbrella has nothing left to pick inside it"
            ),
            "child_issues": len(issues),
            "child_open": 0,
            "warnings": warnings,
        }
    if open_issues:
        if child_flags is None:
            # Relation parent/enfant non mesuree : on garde la lecture
            # historique (une reference ouverte suffit a dire FRESH).
            return {
                "verdict": "FRESH",
                "reason": (
                    f"{len(open_issues)} of {len(issues)} referenced child issue(s) "
                    "are OPEN"
                ),
                "child_issues": len(issues),
                "child_open": len(open_issues),
                "warnings": warnings,
            }
        flags = {r["number"]: child_flags.get(r["number"]) for r in open_issues}
        declared = sorted(n for n, flag in flags.items() if flag is True)
        unknown = sorted(n for n, flag in flags.items() if flag is None)
        cross = sorted(n for n, flag in flags.items() if flag is False)
        if declared:
            return {
                "verdict": "FRESH",
                "reason": (
                    f"{len(declared)} referenced child issue(s) declare this "
                    "umbrella as their parent and are OPEN"
                ),
                "child_issues": len(issues),
                "child_open": len(declared),
                "warnings": warnings,
                "children_open": declared,
                "cross_references": cross,
            }
        if unknown:
            # Fail-CLOSED : une relation qu'on n'a pas pu lire ne fabrique
            # jamais un rouge.
            return {
                "verdict": "UNRESOLVED",
                "reason": (
                    "the parent relation of the OPEN referenced issue(s) "
                    f"{unknown} could not be read -- mechanical verdict "
                    "unavailable; read the comments for a pending decision "
                    "(#11900 surface 3)"
                ),
                "child_issues": len(issues),
                "child_open": 0,
                "warnings": warnings + [
                    f"relation parent/enfant illisible : #{n}" for n in unknown
                ],
                "children_open": [],
                "cross_references": cross,
            }
        # Toutes les references ouvertes sont des liens transversaux : ni elles
        # ni cet umbrella ne declarent de filiation.
        #
        # Le conteneur peut etre vide -- mais ce n'est PAS decidable
        # mecaniquement, et le verdict rouge reste reserve a la seule lecture non
        # ambigue (toutes les references fermees).
        #
        # Mesure (c.2266, echantillon de 12 EPIC ouverts) : #19821 porte un
        # travail VIVANT que son corps designe par des "briques" sans issue
        # fille ("brique 6 -- ombre mensuelle par strategie gelee", "brique 7
        # -- regles du panier appliquees a une premiere revue", hors-
        # echantillon de LeveragedETFMomentum #19587, cite sans filiation).
        # Aucun de ces travaux n'est joignable par une declaration de parent :
        # un rouge ici aurait fait sauter un conteneur plein.
        #
        # Donc : advisory, et le corps de l'umbrella tranche.
        return {
            "verdict": "UNRESOLVED",
            "reason": (
                f"the {len(cross)} OPEN referenced issue(s) declare no filiation "
                "with this umbrella (neither they nor it name the other as "
                "parent/child) -- no declared child is OPEN, but the open work "
                "may be listed without a filiation declaration: the umbrella's "
                "own body is the arbiter before picking here"
            ),
            "child_issues": len(issues),
            "child_open": 0,
            "warnings": warnings + [
                f"reference ouverte sans filiation declaree : #{n} "
                "(ni elle ni cet umbrella ne se nomment parent/enfant)"
                for n in cross
            ],
            "children_open": [],
            "cross_references": cross,
        }
    return {
        "verdict": "UNRESOLVED",
        "reason": (
            "the body references no child issue -- mechanical verdict "
            "unavailable; read the comments for a pending decision (#11900 "
            "surface 3)"
        ),
        "child_issues": 0,
        "child_open": 0,
        "warnings": warnings,
    }


def _gh_json(args: list[str]) -> dict | None:
    try:
        proc = subprocess.run(
            ["gh", *args], capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=60,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if proc.returncode != 0:
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None


def missing_paths(cited: list[str], repo_root: Path) -> list[str]:
    absent: list[str] = []
    for path in cited:
        target = repo_root / path.rstrip("/")
        if not target.exists():
            absent.append(path)
    return absent


def assess(number: int, repo_root: Path, repo: str) -> dict:
    payload = _gh_json(["api", f"repos/{repo}/issues/{number}"])
    if payload is None:
        return {"number": number, "verdict": "unknown", "warning":
                "gh unavailable or request failed", "refs": [], "warnings": []}

    body = payload.get("body") or ""
    numbers = extract_refs(body, number)
    payloads: dict[int, dict | None] = {}
    refs = []
    for n in numbers:
        child_payload = _gh_json(["api", f"repos/{repo}/issues/{n}"])
        payloads[n] = child_payload
        refs.append(classify_ref(n, child_payload))

    # Relation de FILIATION, mesuree dans les DEUX sens : l'issue ouverte
    # referencee declare-t-elle cet umbrella comme son parent (ou grand-
    # parent), ou cet umbrella declare-t-il cette issue comme son parent ?
    # Un lien transversal (aucune declaration dans un sens ou dans l'autre)
    # ne prouve pas que le conteneur est vivant.
    child_flags: dict[int, bool | None] = {}
    for ref in refs:
        if ref["kind"] != "issue" or ref["state"] != "OPEN":
            continue
        child_payload = payloads.get(ref["number"])
        if child_payload is None:
            child_flags[ref["number"]] = None
            continue
        child_body = child_payload.get("body") or ""
        child_title = child_payload.get("title") or ""
        kin = (declares_parent(child_body, number)
               or declares_parent(child_title, number)
               or declares_parent(body, ref["number"]))
        child_flags[ref["number"]] = kin

    cited = extract_paths(body)
    result = classify(refs, missing_paths(cited, repo_root), child_flags)
    result["number"] = number
    result["title"] = payload.get("title") or ""
    result["refs"] = refs
    result["cited_paths"] = cited
    result["child_flags"] = child_flags
    return result


def render_text(result: dict) -> str:
    lines = [f"#{result['number']}  {result['title']}"]
    lines.append(f"  verdict: {result['verdict']} -- {result['reason']}")
    flags = result.get("child_flags") or {}
    for ref in result.get("refs", []):
        suffix = " (merged)" if ref["merged"] else ""
        relation = ""
        if ref["number"] in flags:
            flag = flags[ref["number"]]
            if flag is True:
                relation = "  [enfant declare]"
            elif flag is False:
                relation = "  [reference croisee]"
            else:
                relation = "  [relation illisible]"
        lines.append(
            f"    #{ref['number']}  {ref['kind']}  {ref['state']}{suffix}{relation}"
        )
    for warning in result.get("warnings", []):
        lines.append(f"    ! {warning}")
    if result["verdict"] == "SATURATED":
        lines.append("    -> do not pick here; the picker offered a container, "
                     "not a grain")
    if result["verdict"] == "UNRESOLVED":
        lines.append("    -> read `gh issue view N --comments` for a pending "
                     "decision before concluding the umbrella is blocked")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Confront an umbrella body with the repository (#11900).")
    parser.add_argument("issues", nargs="+", type=int)
    parser.add_argument("--repo", default=REPO)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    root = Path(args.repo_root).resolve()
    results = [assess(n, root, args.repo) for n in args.issues]

    if args.json:
        print(json.dumps(results, indent=2, ensure_ascii=False))
    else:
        for result in results:
            print(render_text(result))
            print()

    for result in results:
        if result["verdict"] == "unknown":
            print(f"::warning::#{result['number']} freshness unresolved "
                  f"({result.get('warning', 'unknown')})", file=sys.stderr)

    return 1 if any(r["verdict"] == "SATURATED" for r in results) else 0


if __name__ == "__main__":
    raise SystemExit(main())
