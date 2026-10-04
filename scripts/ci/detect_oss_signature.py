#!/usr/bin/env python3
r"""Detect Aliyun OSS signed-URL fragments in tracked files.

Why: gitleaks `Secret Scan` failed on PR #17434 (c.820, 2026-09-24) because two
GenAI image metadata JSONs contained `image_url_signed_full` with a 24-hour
presigned URL carrying `Signature=<token>` + `OSSAccessKeyId=LTAI****` (masked
example -- real values are 20 chars after the LTAI prefix). Tell c.820 /
secrets-hygiene rule 1: a presigned Signature IS a secret derived from the
provider's SecretAccessKey, even when the AccessKey itself looks like a public
identifier. The merge-gate intercepted it; the follow-up is to make sure the
same shape never lands again.

Pattern (a 3-tuple signature) -- the organ, and only the organ:
    Signature=<base64-like token>     (URL fragment inside the query string)
    OSSAccessKeyId=LTAI<...>          (Aliyun's AccessKey prefix is LTAI / STS.)
    X-OSS-Security-Token=<opaque>     (STS session token, sibling of OSSAccessKeyId)

Aliyun AccessKey prefixes are documented (LTAI for permanent, LT for STS), but
the organ does not key on a prefix -- it keys on the fragment WHOLE key, which
is the universal signature form across providers. A user could legitimately
write `Signature: <placeholder>` in prose; we exempt short matches (< 28 chars)
and matches containing only word chars (which would be template/placeholder
syntax).

Scope: tracked `*.json` and `*.ipynb` files under the whole repo. JSON metadata
(`.json`) and notebook outputs (`*.ipynb` -- cell `outputs` blocks in
serialized JSON) are the two measured surfaces. The detector runs `git ls-files`
with `*.json` and `*.ipynb` pathspec filters -- ~1866 files in current main,
finishes in <30s.

The detector is local (no GH API), exits 0/1/2:
    CLEAN     no signed-URL fragment found in scope  (exit 0)
    DIRTY     at least one match found               (exit 1)
    ERROR     git or filesystem failure              (exit 2)

Masking -- the payload is consumed by a PUBLIC log. The caller workflow
`cat`s this JSON (`always-on-guards.yml`, step "Detecteur OSS signature
fragments") and then re-prints every `match` inside a `::error::` annotation,
so whatever this organ puts in `match`/`context` ends up readable by anyone.
A finding therefore never carries the detected value: `match` and `context`
expose the key, the line and a non-reversible digest -- never the fragment.
The value IS the secret (a presigned Signature is derived from the provider's
SecretAccessKey), so masking happens HERE, at the single source both
consumers inherit. Cf secrets-hygiene rule 6 and the adjoint bound on
PR #18895 (2026-10-04T01:12:52Z).

Usage:
    python scripts/ci/detect_oss_signature.py            # lint (json/ipynb)
    python scripts/ci/detect_oss_signature.py --json     # structured verdicts
    python scripts/ci/detect_oss_signature.py --strict   # also flag prose comments mentioning Signature in py/cs/md

The `--strict` flag opens a SECOND pathspec filter (py/cs/md), separate from
the default json/ipynb scope: previously the strict path iterated over the
json/ipynb file list and then filtered on py/cs/md -- which never matched
anything (CR myia-ai-01 22:36Z on PR #18835). The second filter now reads
its own list from `git ls-files -- '*.py' '*.cs' '*.md'`, so prose comments
mentioning `Signature=` are actually reachable.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

# REPO_ROOT derive du script par defaut ; surchargeable via
# l'env REPO_ROOT_OVERRIDE pour les tests qui scannent un repo minimal
# isole (cf test_caller_workflow_json_passe_dirty_comme_dirty_avec_findings).
# Sans cette surcharge, le test temoin positif ne pourrait pas executer le
# script sur une fixture : il scannera toujours le depot CoursIA-2 reel.
_DEFAULT_REPO_ROOT = Path(__file__).resolve().parent.parent.parent
REPO_ROOT = Path(os.environ["REPO_ROOT_OVERRIDE"]) if os.environ.get("REPO_ROOT_OVERRIDE") else _DEFAULT_REPO_ROOT

# Pathspec filters for `git ls-files` -- cheap on Windows (avoids the 12k
# file enumeration of the full repo scope).
DEFAULT_PATHSPECS = ["*.json", "*.ipynb"]
# Strict mode reads a SEPARATE file list -- iterating over DEFAULT_PATHSPECS
# and re-filtering on py/cs/md is structurally empty by construction.
STRICT_PATHSPECS = ["*.py", "*.cs", "*.md"]

# The 3 fragment keys that together mark a presigned URL.
FRAGMENT_KEYS = ("Signature", "OSSAccessKeyId", "X-OSS-Security-Token")

# Minimum length of a "real" signature value -- a 24-char placeholder in prose
# does not trigger the organ. Real Aliyun signatures are 28 base64-ish chars
# after URL-decoding; STS tokens 32+. Threshold lowered from 40 -> 28 to
# match the documented signature length (a Signature= realistic isolated in
# prose would otherwise pass under the old threshold -- CR myia-ai-01 22:36Z
# on PR #18835).
MIN_VALUE_LEN = 28

# Patterns keyed on the canonical Aliyun fragment shape.
PATTERNS = [
    re.compile(rf"Signature=[A-Za-z0-9%+/=]{{{MIN_VALUE_LEN},}}"),
    re.compile(rf"OSSAccessKeyId=LTAI[0-9A-Za-z]{{8,18}}"),
    re.compile(rf"X-OSS-Security-Token=[A-Za-z0-9%+/=]{{{MIN_VALUE_LEN},}}"),
]


def list_tracked_files(pathspecs: list[str]) -> list[str] | None:
    """Return the tracked paths matching any of `pathspecs`, or None on git failure."""
    cmd = ["git", "ls-files", "--"] + pathspecs
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=180,
                             cwd=REPO_ROOT, encoding="utf-8", errors="replace")
    except (subprocess.TimeoutExpired, OSError):
        return None
    if out.returncode != 0:
        return None
    return [line.strip() for line in out.stdout.splitlines() if line.strip()]


def redact(value: str) -> str:
    """Return a non-reversible stand-in for a detected secret value.

    The payload built from this organ reaches a PUBLIC CI log (see the module
    docstring, "Masking"). Length + a short digest let a PR author confirm
    "that is my token" without the log carrying the token itself.
    """
    digest = hashlib.sha256(value.encode("utf-8", "replace")).hexdigest()[:12]
    return f"<redacted len={len(value)} sha256:{digest}>"


def redact_line(line: str) -> str:
    """Blank every fragment-value occurrence inside `line`, keep the rest.

    A context line carries the secret by definition -- it is the line the
    match was found on. Redacting the matched spans (and only those) keeps
    the diagnostic readable: the surrounding JSON key, the file and the line
    number all survive.
    """
    for pat in PATTERNS:
        line = pat.sub(lambda m: redact(m.group(0)), line)
    return line


def scan_file(path: Path) -> list[dict]:
    """Return matches found in `path`, with line context."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except (OSError, UnicodeError):
        return []
    hits = []
    for line_no, line in enumerate(text.splitlines(), start=1):
        for pat in PATTERNS:
            m = pat.search(line)
            if m is None:
                continue
            hits.append({
                "line": line_no,
                "pattern": pat.pattern[:48] + "...",
                # Redacted at the source: `match` and `context` are printed in
                # clear by BOTH consumers (the workflow `cat`s the JSON, then
                # re-prints `match` in a ::error:: annotation). See "Masking".
                "match": redact(m.group(0)),
                "context": redact_line(line)[:200],
            })
    return hits


def classify(rel: str) -> str:
    """Surface classification -- JSON metadata / notebook output / other."""
    if rel.endswith(".json"):
        return "json"
    if rel.endswith(".ipynb"):
        return "ipynb"
    if rel.endswith((".py", ".cs", ".md")):
        return "prose"
    return "other"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="emit structured JSON")
    ap.add_argument("--strict", action="store_true",
                    help="also flag prose comments mentioning Signature (more FPs)")
    args = ap.parse_args()

    files = list_tracked_files(DEFAULT_PATHSPECS)
    if files is None:
        sys.stderr.write("ERROR: git ls-files failed; cannot scan\n")
        return 2

    findings = []
    for rel in files:
        p = REPO_ROOT / rel
        if not p.is_file():
            continue
        hits = scan_file(p)
        if not hits:
            continue
        findings.append({
            "file": rel,
            "surface": classify(rel),
            "hits": hits,
        })

    if args.strict:
        # Second pathspec filter -- py/cs/md only. The previous iteration
        # over `files` (json/ipynb) re-filtered on these suffixes and could
        # never retain anything; the second list is now read separately.
        strict_files = list_tracked_files(STRICT_PATHSPECS) or []
        PROSE_RE = re.compile(r"#\s*Signature=|//\s*Signature=")
        for rel in strict_files:
            p = REPO_ROOT / rel
            if not p.is_file():
                continue
            try:
                text = p.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for line_no, line in enumerate(text.splitlines(), start=1):
                if PROSE_RE.search(line):
                    findings.append({
                        "file": rel,
                        "surface": "prose",
                        "hits": [{"line": line_no, "pattern": "comment-mention",
                                  "match": redact_line(line)[:120],
                                  "context": redact_line(line)[:200]}],
                    })

    verdict = "DIRTY" if findings else "CLEAN"
    if args.json:
        json.dump({"verdict": verdict, "findings": findings,
                   "scanned_files": len(files), "min_value_len": MIN_VALUE_LEN},
                  sys.stdout, ensure_ascii=False, indent=2)
        sys.stdout.write("\n")
    else:
        print(f"{verdict} -- scanned {len(files)} files matching {DEFAULT_PATHSPECS}")
        if findings:
            print(f"  found {len(findings)} file(s) with matches:")
            for f in findings:
                print(f"    {f['surface']:>4}  {f['file']}  ({len(f['hits'])} hit(s))")
                for h in f["hits"][:3]:
                    print(f"        L{h['line']} {h['pattern']} :: {h['match']}")

    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())