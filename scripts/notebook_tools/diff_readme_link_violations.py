#!/usr/bin/env python3
"""Delta comparator for README-vs-.ipynb violations (F2 of #18970).

Reads two JSON artefacts produced by `dump_readme_link_violations.py` (base
and head) and reports ONLY the violations that the PR introduces (head minus base).

This is the guard that the fast-lane `delta_argv` slot consumes: it lets the
PR gate stay blocking on NEW HTML_404 (#18911 geste 2, 2026-10-09) without
rouging on the 618 historical backlog committed before the guard existed.

Exit codes:
    0 = no NEW violation (PR clean)
    1 = at least one NEW violation (PR must be fixed)
    2 = invocation error

Rename pairing (#20274): a `git mv` of a directory re-keys every violation
touching it, in two shapes -- the identical triple under a new README path
(violations INSIDE the renamed folder), and a changed href inside an
unchanged README (violations in referent READMEs pointing INTO the renamed
folder). Both leave the backlog count unchanged (measured on the T2-01
rename: NOUVELLES=12, CORRIGEES=12, strictly symmetric; 8 of shape 1,
4 of shape 2).

Pairing requires a GIT rename mapping (review reserve on #20274: absence
on disk proves nothing about the relation -- only a rename recorded by
Git does). The mapping is `git diff --name-status --find-renames
--diff-filter=R $FAST_LANE_BASE...HEAD` resolved at the repo root (cwd),
the same base convention as the fast-lane engine (env `FAST_LANE_BASE`,
default `origin/main`). Fail-closed: if git is unavailable, the ref is
unknown or the diff fails, the mapping is EMPTY and no pairing happens --
every new violation stays a NEW violation.

  shape 1 -- a "new" (class, readme, href) whose exact (class, href) twin
  sits in the fixed set AND whose base-side README maps to it by Git
  rename (old readme path -> new readme path) AND no longer exists on
  disk is a MOVED violation.
  shape 2 -- a "new" (class, readme, href') in the SAME readme as a fixed
  (class, readme, href), where the resolved old href maps to the resolved
  new href by Git rename (old target -> new target) AND the new target's
  parent directory exists: the link tracked a folder that moved.

The Git mapping keeps the pairing honest -- a re-key whose base-side file
was deleted without a rename, or whose new target is an unrelated fresh
file, is NOT a move and stays a NEW violation.

Usage:
    python diff_readme_link_violations.py <base.json> <head.json>
"""
from __future__ import annotations

import argparse
import json
import os
import posixpath
import subprocess
import sys
from pathlib import Path


def _key(v: dict) -> tuple[str, str, str]:
    return (v.get("class", ""), v.get("readme", ""), v.get("href", ""))


def _resolve_href(readme: str, href: str) -> str:
    return posixpath.normpath(posixpath.join(posixpath.dirname(readme), href))


def _resolve_base_ref() -> str:
    """Base du delta pour le mapping Git (meme convention que le fast-lane).

    FAST_LANE_BASE si posee, sinon origin/main. Sur un PUSH main
    (origin/main == HEAD, le runner checkout la tete poussee), le delta
    pertinent est le commit pousse : HEAD^ -- sinon le mapping serait vide
    et un rename merge par push rougirait le garde a tort.
    """
    ref = os.environ.get("FAST_LANE_BASE", "origin/main")
    if ref == "origin/main":
        try:
            head = subprocess.run(["git", "rev-parse", "HEAD"],
                                  capture_output=True, text=True, timeout=15,
                                  encoding="utf-8", errors="replace")
            origin = subprocess.run(["git", "rev-parse", "origin/main"],
                                    capture_output=True, text=True, timeout=15,
                                    encoding="utf-8", errors="replace")
        except (subprocess.SubprocessError, OSError):
            return ref
        if (head.returncode == 0 and origin.returncode == 0
                and head.stdout == origin.stdout):
            return "HEAD^"
    return ref


def _git_renames(base_ref: str) -> dict[str, str]:
    """Git rename mapping base...HEAD : ancien chemin -> nouveau chemin.

    Fail-closed (reserve #20274) : toute defaillance (git absent, pas de
    depot, ref inconnue, timeout) rend une map VIDE -- aucun appariement
    MOVED n'est alors autorise, chaque violation nouvelle reste une
    NOUVELLE. L'absence sur disque ne prouve pas la relation ; seul un
    rename enregistre par Git la prouve.
    """
    try:
        proc = subprocess.run(
            ["git", "diff", "--name-status", "--find-renames",
             "--diff-filter=R", f"{base_ref}...HEAD"],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=30,
        )
    except (subprocess.SubprocessError, OSError):
        return {}
    if proc.returncode != 0:
        return {}
    renames: dict[str, str] = {}
    for line in proc.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) == 3 and parts[0].startswith("R"):
            renames[parts[1]] = parts[2]
    return renames


def _pair_renames(
    new: list[tuple[str, str, str]], fixed: list[tuple[str, str, str]],
    renames: dict[str, str],
) -> tuple[list[tuple[str, str, str, str, str]], list[tuple[str, str, str]]]:
    """Split `new` into (moved, still_new) against `fixed`.

    moved entries are (class, old_readme, old_href, new_readme, new_href);
    each fixed entry pairs at most once. Chaque appariement exige le mapping
    Git de renommages (reserve #20274) : l'absence sur disque seule n'apparie
    plus rien.
    """
    fixed_by_ch: dict[tuple[str, str], list[str]] = {}
    fixed_by_cr: dict[tuple[str, str], list[str]] = {}
    for cls, readme, href in fixed:
        fixed_by_ch.setdefault((cls, href), []).append(readme)
        fixed_by_cr.setdefault((cls, readme), []).append(href)
    moved: list[tuple[str, str, str, str, str]] = []
    still_new: list[tuple[str, str, str]] = []
    for cls, readme, href in new:
        # shape 1 -- le README lui-meme a demenage, href inchangé : le
        # rename Git doit mapper l'ancien README exactement sur le nouveau.
        candidates = fixed_by_ch.get((cls, href), [])
        source = next(
            (r for r in candidates
             if renames.get(r) == readme and not Path(r).is_file()),
            None,
        )
        if source is not None:
            candidates.remove(source)
            fixed_by_cr.get((cls, source), []).remove(href)
            moved.append((cls, source, href, readme, href))
            continue
        # shape 2 -- README inchangé, le href suit une cible deplacee : le
        # rename Git doit mapper la cible resolue ancienne sur la nouvelle.
        paired_href = None
        for h_old in fixed_by_cr.get((cls, readme), []):
            if h_old == href:
                continue
            p_old = _resolve_href(readme, h_old)
            p_new = _resolve_href(readme, href)
            if p_old == p_new:
                continue
            if renames.get(p_old) == p_new and Path(p_new).parent.is_dir():
                paired_href = h_old
                break
        if paired_href is not None:
            fixed_by_cr[(cls, readme)].remove(paired_href)
            fixed_by_ch.get((cls, paired_href), []).remove(readme)
            moved.append((cls, readme, paired_href, readme, href))
        else:
            still_new.append((cls, readme, href))
    return moved, still_new


def _load(path: Path) -> list[dict]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return data.get("violations", [])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("base_json", type=Path, help="JSON dump sur la base (main)")
    ap.add_argument("head_json", type=Path, help="JSON dump sur la tete (PR)")
    args = ap.parse_args()

    if not args.base_json.is_file():
        print(f"::error::base JSON introuvable: {args.base_json}", file=sys.stderr)
        return 2
    if not args.head_json.is_file():
        print(f"::error::head JSON introuvable: {args.head_json}", file=sys.stderr)
        return 2

    base_set = {_key(v) for v in _load(args.base_json)}
    head_set = {_key(v) for v in _load(args.head_json)}
    new = sorted(head_set - base_set)
    fixed = sorted(base_set - head_set)

    base_ref = _resolve_base_ref()
    renames = _git_renames(base_ref)
    moved, still_new = _pair_renames(new, fixed, renames)
    consumed = {(cls, old_readme, old_href) for cls, old_readme, old_href, _, _ in moved}
    fixed = [t for t in fixed if t not in consumed]

    print(f"README-link delta: base={len(base_set)} head={len(head_set)} "
          f"NOUVELLES={len(still_new)} CORRIGEES={len(fixed)} "
          f"DEPLACEES={len(moved)} git-renames={len(renames)} (base {base_ref})")
    for cls, readme, href in still_new:
        print(f"  + {cls}  {readme}  ->  {href}")
    for cls, old_readme, old_href, new_readme, new_href in moved:
        if old_href == new_href:
            print(f"  ~ MOVED {cls}  {old_readme}  =>  {new_readme}  ->  {new_href}")
        else:
            print(f"  ~ MOVED {cls}  {old_readme}  {old_href}  =>  {new_href}")
    for cls, readme, href in fixed:
        print(f"  - {cls}  {readme}  ->  {href}")

    if still_new:
        # Meme format que le scanner (regen_quarto_render.py emet
        # `::error::<CLASSE> ...` sur stderr) pour que les outils en
        # aval qui grep le pattern continuent de fonctionner. La classe
        # est celle du dump, pas une constante : depuis #18911 c'est
        # HTML_404, avant c'etait STALE_LINK.
        for cls, readme, href in still_new:
            print(f"::error::{cls} {readme} -> {href}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
