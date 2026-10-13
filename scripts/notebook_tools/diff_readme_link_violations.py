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

A pair classifies as MOVED only against RENAMES PROVEN BY GIT
(`--base-sha`/`--head-sha`, evidence from `git diff --name-status
--find-renames`), never from circumstantial disk signals alone. Three
reproduced false negatives motivated the proof requirement (adjoint review
of #20274, 2026-10-11): (1) an old href into a deleted directory plus a
NEW href into an unrelated existing directory satisfied the old
"old parent gone + new parent exists" heuristic without any rename
existing; (2) a deleted README plus an unrelated new README sharing the
same href satisfied the old "base-side README gone" heuristic; (3) the
rename of a SIBLING file (a.txt) induced a directory mapping that
acquitted a README that git itself reports as delete+add -- the mapping
of a neighbour is not a proof about the document. Deletion is not
renaming. Pairing rules:

  shape 1 -- a "new" (class, readme, href) whose exact (class, href) twin
  sits in the fixed set, whose base-side README no longer exists on disk
  AND whose README move is git-proven by the README's OWN R* entry
  (old_readme -> new_readme in the rename map). A directory mapping
  deduced from other files does NOT acquit a README that git reports as
  delete+add: a rewritten README is a new document, and its links are new
  links (#20357, adjoint 14:00).
  shape 2 -- a "new" (class, readme, href') in the SAME readme as a fixed
  (class, readme, href), where the resolved targets differ exactly by a
  git-proven directory rename (same suffix under old_dir/new_dir) and the
  resolved old href's parent directory has vanished while the new one
  exists. The dir-level proof is deliberate here: an HTML_404 target is
  absent from the repo by definition, so its own rename can NEVER be
  proven -- requiring it would false-positive every real re-key. The
  re-addressed broken link is the SAME broken link, not a new one.

Fail-closed: without --base-sha/--head-sha, or on any git failure, the
rename map is empty and NOTHING classifies as MOVED -- every re-keyed
violation stays NEW. A blocking guard must not whiten on a coincidence;
the fast-lane passes both SHAs (delta_argv in fast_lane_registry.py).

Usage:
    python diff_readme_link_violations.py <base.json> <head.json> \
        [--base-sha <sha> --head-sha <sha>]
"""
from __future__ import annotations

import argparse
import json
import posixpath
import subprocess
import sys
from pathlib import Path


def _key(v: dict) -> tuple[str, str, str]:
    return (v.get("class", ""), v.get("readme", ""), v.get("href", ""))


def _resolve_href(readme: str, href: str) -> str:
    return posixpath.normpath(posixpath.join(posixpath.dirname(readme), href))


def _git_rename_evidence(
    base_sha: str, head_sha: str
) -> tuple[dict[str, str], dict[str, str]]:
    """Renvoie (file_renames, dir_renames) prouves par git, fail-closed.

    file_renames : ancien chemin -> nouveau chemin pour chaque entree R*
    de `git diff --name-status --find-renames base head`. dir_renames :
    ancien dossier -> nouveau dossier, deduit des fichiers renommes qui
    partagent un suffixe de chemin non vide (la partie deplacee est le
    dossier). Sans SHA, ou sur le moindre echec git : ({}, {}) -- aucune
    classification MOVED n'est alors possible.
    """
    if not base_sha or not head_sha:
        return {}, {}
    try:
        proc = subprocess.run(
            ["git", "diff", "--name-status", "--find-renames",
             "--diff-filter=R", base_sha, head_sha],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=60,
        )
    except (subprocess.TimeoutExpired, OSError):
        return {}, {}
    if proc.returncode != 0:
        return {}, {}
    file_renames: dict[str, str] = {}
    dir_renames: dict[str, str] = {}
    for line in proc.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 3 or not parts[0].startswith("R"):
            continue
        _status, old, new = parts
        file_renames[old] = new
        oc, nc = old.split("/"), new.split("/")
        k = 0
        while (k < len(oc) and k < len(nc)
               and oc[len(oc) - 1 - k] == nc[len(nc) - 1 - k]):
            k += 1
        if 1 <= k < len(oc) and k < len(nc):
            d_old = "/".join(oc[:len(oc) - k])
            d_new = "/".join(nc[:len(nc) - k])
            if d_old != d_new:
                dir_renames.setdefault(d_old, d_new)
    return file_renames, dir_renames


def _readme_move_proven(
    old_readme: str, new_readme: str,
    file_renames: dict[str, str], dir_renames: dict[str, str],
) -> bool:
    """Le demenagement du README lui-meme est-il prouve par git ? Seule
    preuve admise : l'entree R* exacte old_readme -> new_readme. Un mapping
    de dossier deduit d'un fichier VOISIN (FN 3, #20357) n'acquitte pas un
    README que git rapporte comme delete+add -- un README reecrit est un
    nouveau document, et ses liens sont des liens nouveaux. `dir_renames`
    reste parameter (consomme par la shape 2) mais ne participe plus ici."""
    return file_renames.get(old_readme) == new_readme


def _targets_differ_by_dir_rename(
    p_old: str, p_new: str, dir_renames: dict[str, str]
) -> bool:
    """Les deux cibles resoleues ne different-elles QUE par un dossier
    que git prouve renomme (meme suffixe sous old_dir/new_dir) ?"""
    for d_old, d_new in dir_renames.items():
        if (p_old.startswith(d_old + "/") and p_new.startswith(d_new + "/")
                and p_old[len(d_old):] == p_new[len(d_new):]):
            return True
    return False


def _pair_renames(
    new: list[tuple[str, str, str]], fixed: list[tuple[str, str, str]],
    file_renames: dict[str, str], dir_renames: dict[str, str],
) -> tuple[list[tuple[str, str, str, str, str]], list[tuple[str, str, str]]]:
    """Split `new` into (moved, still_new) against `fixed`.

    moved entries are (class, old_readme, old_href, new_readme, new_href);
    each fixed entry pairs at most once. Every pairing requires git rename
    evidence (fail-closed): a coincidence of keys or a deletion is NOT a
    move.
    """
    fixed_by_ch: dict[tuple[str, str], list[str]] = {}
    fixed_by_cr: dict[tuple[str, str], list[str]] = {}
    for cls, readme, href in fixed:
        fixed_by_ch.setdefault((cls, href), []).append(readme)
        fixed_by_cr.setdefault((cls, readme), []).append(href)
    moved: list[tuple[str, str, str, str, str]] = []
    still_new: list[tuple[str, str, str]] = []
    for cls, readme, href in new:
        # shape 1 -- le README lui-meme a demenage, href inchangé.
        candidates = fixed_by_ch.get((cls, href), [])
        source = next(
            (r for r in candidates
             if not Path(r).is_file()
             and _readme_move_proven(r, readme, file_renames, dir_renames)),
            None,
        )
        if source is not None:
            candidates.remove(source)
            fixed_by_cr.get((cls, source), []).remove(href)
            moved.append((cls, source, href, readme, href))
            continue
        # shape 2 -- README inchangé, le href suit un dossier deplacé.
        paired_href = None
        for h_old in fixed_by_cr.get((cls, readme), []):
            if h_old == href:
                continue
            p_old = _resolve_href(readme, h_old)
            p_new = _resolve_href(readme, href)
            if p_old == p_new:
                continue
            if (not Path(p_old).parent.is_dir() and Path(p_new).parent.is_dir()
                    and _targets_differ_by_dir_rename(p_old, p_new, dir_renames)):
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
    ap.add_argument("--base-sha", default="",
                    help="SHA de la base (fast-lane {base_sha}) ; sans lui, "
                         "aucun appariement MOVED (fail-closed)")
    ap.add_argument("--head-sha", default="",
                    help="SHA de la tete (fast-lane {head_sha})")
    args = ap.parse_args()

    if not args.base_json.is_file():
        print(f"::error::base JSON introuvable: {args.base_json}", file=sys.stderr)
        return 2
    if not args.head_json.is_file():
        print(f"::error::head JSON introuvable: {args.head_json}", file=sys.stderr)
        return 2

    file_renames, dir_renames = _git_rename_evidence(
        args.base_sha, args.head_sha)
    if not args.base_sha or not args.head_sha:
        print("pairing: SHA base/head absents -- classification MOVED "
              "desactivee (fail-closed, chaque re-key reste NOUVELLE)")
    elif not file_renames and not dir_renames:
        print("pairing: aucune preuve de renommage git base->head "
              "(fail-closed, chaque re-key reste NOUVELLE)")

    base_set = {_key(v) for v in _load(args.base_json)}
    head_set = {_key(v) for v in _load(args.head_json)}
    new = sorted(head_set - base_set)
    fixed = sorted(base_set - head_set)

    moved, still_new = _pair_renames(new, fixed, file_renames, dir_renames)
    consumed = {(cls, old_readme, old_href) for cls, old_readme, old_href, _, _ in moved}
    fixed = [t for t in fixed if t not in consumed]

    print(f"README-link delta: base={len(base_set)} head={len(head_set)} "
          f"NOUVELLES={len(still_new)} CORRIGEES={len(fixed)} "
          f"DEPLACEES={len(moved)}")
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
