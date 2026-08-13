#!/usr/bin/env python3
"""Extract + anonymize a fallacy-detection corpus from a Reddit Data Export.

Phase 1 / livrable 3 of EPIC #10355 (fallacy detection via Qwen FT+PT, gated by
SAE). The source is a Reddit account Data Export (.zip) whose ``comments.csv``
and ``posts.csv`` carry the account's full posting history. This script:

1. reads the .zip from a path supplied **only** via the ``JESSYNOO_DUMP_PATH``
   env var (no default literal — the path is personal PII, secrets-hygiene rule 6:
   a personal path leaks by construction in a public repo);
2. selects ``subreddit == "fallacy"`` rows from comments + posts;
3. drops PII columns: ``ip`` (PII by nature), ``permalink``/``link`` (the
   Reddit comment/post URL is reversible to the original and would undermine the
   ``u/`` anonymization of third parties mentioned in the body);
4. anonymizes every ``u/<third-party>`` mention in ``body``/``title`` to a stable
   ``u/[USER_N]`` token (sorted by name for determinism). Subreddit mentions
   (``r/...``) and reference URLs (wikipedia, rationalwiki, ...) are kept — they
   are public content, not PII;
5. writes a single anonymized CSV (``kind`` column distinguishes comment/post).

The raw .zip is NEVER committed (PII by construction — see #10356 gate 3'). Only
the anonymized corpus + this reproducible script are committed. The account
itself (``Jessynoo``) is the repo owner's own handle (self-attribution
pedagogique assumee, cf owner comments on #10356); anonymization targets
**third-party** usernames cited inside the bodies.

Usage:
    JESSYNOO_DUMP_PATH="C:/path/to/export.zip" \
        python extract_jessynoo_fallacy.py --out <anonymized.csv> [--verbose]

Exit codes: 0 = ok, 1 = no fallacy rows found, 2 = dump missing/unreadable.
Hermetic: stdlib only (zipfile, csv, re, argparse, os, sys).
"""

import argparse
import csv
import io
import os
import re
import sys
import zipfile
from pathlib import Path

# u/<name> : third-party Reddit username mention. 3+ chars to avoid matching
# ``u/`` inside URLs or abbreviations. The captured name is alphanumeric +
# underscore + hyphen (Reddit username charset).
U_MENTION_RE = re.compile(r"\bu/([A-Za-z0-9_-]{3,20})")

# Anonymized corpus schema. ``id`` is the opaque Reddit base36 id (useful for
# dedup, NOT reversible without the Reddit API + post slug). ``date`` is the UTC
# timestamp (allowed by owner). ``kind`` distinguishes comment vs post.
OUT_FIELDS = ["id", "date", "subreddit", "kind", "title", "url", "body"]

ENV_DUMP_PATH = "JESSYNOO_DUMP_PATH"


def build_user_index(rows):
    """Collect the set of third-party usernames cited across bodies/titles and
    assign each a deterministic ``u/[USER_N]`` token (sorted by name).

    Determinism (sorted, not first-seen order) makes the anonymization
    reproducible across runs regardless of row iteration order.
    """
    names = set()
    for r in rows:
        for field in ("body", "title"):
            for m in U_MENTION_RE.finditer(r.get(field) or ""):
                names.add(m.group(1))
    # Filter out the self-handle (kept as self-attribution). The export owner's
    # own username, when cited, stays verbatim (it is the author, not a third
    # party). The owner handle is passed explicitly so the script does not
    # hardcode it.
    return names


def anonymize_text(text, mapping):
    """Replace each ``u/<name>`` in ``text`` with ``mapping[name]`` (or keep if
    the name is the owner's self-handle)."""
    if not text:
        return text

    def repl(m):
        name = m.group(1)
        return f"u/{mapping[name]}" if name in mapping else m.group(0)

    return U_MENTION_RE.sub(repl, text)


def read_fallacy_rows(zip_path, owner_handle="Jessynoo"):
    """Read the .zip, return fallacy-subset rows (comments + posts) with a
    ``kind`` discriminator. Raises FileNotFoundError if the zip is missing.
    """
    if not os.path.isfile(zip_path):
        raise FileNotFoundError(
            f"Dump introuvable: {zip_path!r} (env {ENV_DUMP_PATH}). "
            f"Le path est personnel et ne se commite pas — le fournir via l'env."
        )
    rows = []
    with zipfile.ZipFile(zip_path) as z:
        # comments.csv -> kind="comment", posts.csv -> kind="post".
        for fname, kind in (("comments.csv", "comment"), ("posts.csv", "post")):
            try:
                raw = z.read(fname).decode("utf-8", errors="replace")
            except KeyError:
                print(f"  WARN: {fname} absent du dump — ignoré.", file=sys.stderr)
                continue
            for r in csv.DictReader(io.StringIO(raw)):
                if (r.get("subreddit") or "").lower() != "fallacy":
                    continue
                rows.append(
                    {
                        "id": r.get("id", ""),
                        "date": r.get("date", ""),
                        "subreddit": r.get("subreddit", "fallacy"),
                        "kind": kind,
                        "title": r.get("title", "") if kind == "post" else "",
                        "url": r.get("url", "") if kind == "post" else "",
                        "body": r.get("body", ""),
                    }
                )
    return rows


def extract(dump_path, out_path, owner_handle="Jessynoo", verbose=False):
    """Full extraction + anonymization pipeline. Returns (rows, n_anonymized)."""
    rows = read_fallacy_rows(dump_path, owner_handle)
    if not rows:
        return rows, 0

    # Build the third-party username index (exclude the owner self-handle).
    names = build_user_index(rows) - {owner_handle}
    mapping = {name: f"[USER_{i + 1}]" for i, name in enumerate(sorted(names))}

    for r in rows:
        r["body"] = anonymize_text(r["body"], mapping)
        r["title"] = anonymize_text(r["title"], mapping)

    if verbose:
        print(f"  {len(rows)} items r/fallacy, {len(mapping)} third-party "
              f"usernames anonymized:")
        for name, tok in sorted(mapping.items(), key=lambda kv: kv[1]):
            print(f"    u/{name} -> u/{tok}")

    return rows, len(mapping)


def main(argv=None):
    p = argparse.ArgumentParser(
        description="Extract + anonymize r/fallacy corpus from a Reddit Data Export (EPIC #10355)."
    )
    p.add_argument("--out", type=Path, required=True,
                   help="Output anonymized CSV path.")
    p.add_argument("--owner-handle", default="Jessynoo",
                   help="Owner Reddit handle to keep verbatim (self-attribution). Default: Jessynoo.")
    p.add_argument("--verbose", action="store_true", help="Print per-user anonymization map.")
    args = p.parse_args(argv)

    dump_path = os.environ.get(ENV_DUMP_PATH)
    if not dump_path:
        print(
            f"ERROR: env {ENV_DUMP_PATH} non definie. Le path du dump est "
            f"personnel (PII) et ne se commite pas — le fournir via l'env.",
            file=sys.stderr,
        )
        return 2

    try:
        rows, n_anon = extract(dump_path, args.out, args.owner_handle, args.verbose)
    except FileNotFoundError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    if not rows:
        print(f"ERROR: 0 items r/fallacy trouves dans {dump_path}.", file=sys.stderr)
        return 1

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=OUT_FIELDS, quoting=csv.QUOTE_MINIMAL,
                           lineterminator="\n")
        w.writeheader()
        w.writerows(rows)

    n_comment = sum(1 for r in rows if r["kind"] == "comment")
    n_post = sum(1 for r in rows if r["kind"] == "post")
    print(
        f"[extract] {args.out.name}: {len(rows)} items "
        f"({n_comment} comments + {n_post} posts), "
        f"{n_anon} third-party usernames -> u/[USER_N]."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
