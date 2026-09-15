#!/usr/bin/env python3
"""Base-not-main PR signaler -- part (a) of issue #10918.

A PR whose base is NOT ``main`` delivers its content onto a branch. If that
branch is never wired to main afterwards, the deliverable is orphaned (see
orphan_branch_scan.py, part (b)). This tool signals the risk AT PR TIME: it
labels the PR ``base-not-main`` and posts an advisory comment telling the
reader whether the base currently has an open PR towards main.

The count of open PRs on the base is what makes the warning useful:

  - 1+ open PR from the base towards main  -> a legitimate stack, the
    deliverable is in flight (comment says so);
  - 0 open PRs                            -> an orphan in formation, nothing
    is scheduled to carry this content to main (comment says so).

ADVISORY, never blocking: label + comment only, exit 0 always. Idempotent:
re-runs (synchronize events) update the marker-guarded comment, never spam.

Usage::

    python scripts/base_not_main.py --pr 10770 --dry-run
    python scripts/base_not_main.py --pr 10770          # apply (CI)

Exit code is always 0 (advisory).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

import yaml

LABEL_NAME = "base-not-main"
LABEL_COLOR = "fbca04"  # yellow -- "targets a non-main base, orphan risk"
LABEL_DESC = "PR dont la base != main : livraison sur branche, risque d'orphelin (#10918)"

MARKER_START = "<!-- BASE-NOT-MAIN:START -->"
MARKER_END = "<!-- BASE-NOT-MAIN:END -->"

REPO_ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS_DIR = REPO_ROOT / ".github" / "workflows"

# Nombre de workflows nommes dans le commentaire avant repli en "... et N autres".
MAX_NAMED_SKIPPED = 12


def count_open_prs_on_base(repo: str, base: str) -> int:
    """Open PRs whose head is ``base`` and that target ``main`` (the stack)."""
    data = _gh_json([
        "pr", "list", "--repo", repo, "--state", "open",
        "--search", f'head:"{base}" base:main',
        "--json", "number",
    ]) or []
    return len(data)


# ---------------------------------------------------------------------------
# Couverture CI perdue sur une base empilee (#16194)
# ---------------------------------------------------------------------------
#
# Le compte de PR ouvertes ci-dessus dit si le STACK est legitime. Il ne dit
# rien de ce que ce stack a COUTE en couverture. Mesure firsthand du depot
# (2026-09-15) : 162 fichiers workflow, 90 declarent un trigger
# `pull_request`, et 80 de ces 90 gatent ce trigger sur `branches: [main]`.
# Une PR dont la base n'est pas `main` ne les declenche donc jamais -- et
# GitHub rend quand meme `mergeStateStatus: CLEAN`. L'advisory ne disait
# jusqu'ici que « la cible de livraison n'est pas main » ; un reviewer
# attentif en a tire l'inverse (« ce n'est donc pas un defaut », #15940). Le
# trou restait invisible la ou on le regarde.
#
# L'issue #16194 annonce « 80 des 148 ». Le numerateur reproduit exactement ;
# le denominateur non -- 148 ne correspond ni aux 90 declarants ni aux 162
# fichiers. Ce module porte la mesure, pas le chiffre de l'issue.
#
# Ces trois fonctions mesurent le trou : quels workflows se declencheraient si
# la base etait `main`, et ne se declenchent pas ici.

def _glob_to_regex(pattern: str) -> re.Pattern:
    """Traduit un glob GitHub Actions (`*`, `**`, `?`) en regex ancree.

    ``fnmatch`` ne convient pas : son ``*`` traverse les ``/``, donc
    ``scripts/*`` y matcherait ``scripts/a/b.py``. Un workflow declare pour un
    seul niveau serait alors compte comme declenche, et l'ecart annonce au
    reviewer serait faux -- exactement le tort que #16194 mesure.

    Sous-ensemble traduit : ``*``, ``**``, ``?``. Les formes ``+``, ``[...]``
    et le ``!`` initial des filtres GitHub ne le sont **pas** -- elles seraient
    lues litteralement. Mesure du 2026-09-15 : aucun des 162 workflows du
    depot ne les emploie dans ``paths``/``branches``, donc la mesure n'en
    depend pas aujourd'hui. La semantique exacte du ``?`` GitHub n'a pas ete
    verifiee firsthand : si un filtre vient a l'employer, la verifier avant de
    s'y fier.
    """
    out: list[str] = []
    i, n = 0, len(pattern)
    while i < n:
        c = pattern[i]
        if c == "*":
            if pattern.startswith("**/", i):
                out.append("(?:.*/)?")  # `**/` peut matcher zero niveau
                i += 3
            elif pattern.startswith("**", i):
                out.append(".*")
                i += 2
            else:
                out.append("[^/]*")
                i += 1
        elif c == "?":
            out.append("[^/]")
            i += 1
        else:
            out.append(re.escape(c))
            i += 1
    return re.compile("^" + "".join(out) + "$")


def _as_list(value: object) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value]
    return [str(v) for v in value] if isinstance(value, list) else []


def _branch_filter_matches(pr_config: object, branch: str) -> bool:
    """Le trigger `pull_request` se declenche-t-il pour une PR visant `branch` ?

    Sans filtre de branche, GitHub declenche sur TOUTE branche cible (y compris
    une base empilee) -- donc ``True``. Semantique GitHub : `branches-ignore`
    est evalue en premier, puis `branches`.
    """
    if not isinstance(pr_config, dict):
        return True
    ignore = _as_list(pr_config.get("branches-ignore"))
    if any(_glob_to_regex(p).match(branch) for p in ignore):
        return False
    branches = _as_list(pr_config.get("branches"))
    if branches:
        return any(_glob_to_regex(p).match(branch) for p in branches)
    return True


def _paths_filter_matches(pr_config: object, changed_files: list[str]) -> bool:
    """Le filtre de chemins est-il satisfait par les fichiers de la PR ?

    Semantique GitHub : un fichier est retenu s'il matche au moins un motif
    positif ET aucun motif negatif (`!x`) ; le workflow tourne si au moins un
    fichier est retenu. Avec `paths-ignore` seul, il tourne sauf si TOUS les
    fichiers modifies sont ignores.

    Le filtre de chemins est ce qui distingue « ce workflow aurait tourne » de
    « ce workflow matche le depot » : c'est le point que #15751 documente (les
    fichiers matches terme a terme, c'est `branches: [main]` qui a tout eteint).
    """
    if not isinstance(pr_config, dict):
        return True
    patterns = _as_list(pr_config.get("paths"))
    ignore = _as_list(pr_config.get("paths-ignore"))
    if not patterns and not ignore:
        return True
    negatives = [_glob_to_regex(p) for p in ignore]
    if not patterns:
        return any(not any(g.match(f) for g in negatives) for f in changed_files)
    positives = [_glob_to_regex(p) for p in patterns]
    for f in changed_files:
        if any(g.match(f) for g in positives) and not any(g.match(f) for g in negatives):
            return True
    return False


def _would_run(pr_config: object, branch: str, changed_files: list[str]) -> bool:
    return (_branch_filter_matches(pr_config, branch)
            and _paths_filter_matches(pr_config, changed_files))


def _on_block(data: dict) -> dict | None:
    """Bloc `on:` du workflow. PyYAML normalise la cle `on` en `True`."""
    for key in (True, "on"):
        block = data.get(key)
        if isinstance(block, dict):
            return block
    return None


def workflows_skipped_by_base(workflows_dir: Path, base: str,
                              changed_files: list[str]) -> list[str]:
    """Workflows qui tourneraient sur `main` et pas sur `base` (#16194).

    Mesure le manque, pas le depot : un workflow ne compte que si sa conjonction
    (filtre de branche cible, filtre de chemins) est satisfaite pour `main` ET
    ne l'est pas pour `base`. Un workflow sans filtre de branche tourne sur les
    deux et n'est donc jamais compte, meme s'il porte un `paths:`.

    `pull_request_target` est traite comme `pull_request` : le filtre de branche
    cible y a la meme semantique, et un check absent est absent quelle que soit
    la variante du trigger.
    """
    if not workflows_dir.is_dir():
        return []
    skipped: list[str] = []
    for fname in sorted(workflows_dir.iterdir()):
        if fname.suffix not in (".yml", ".yaml"):
            continue
        try:
            data = yaml.safe_load(fname.read_text(encoding="utf-8"))
        except (yaml.YAMLError, OSError, UnicodeDecodeError):
            continue
        if not isinstance(data, dict):
            continue
        on = _on_block(data)
        if not on:
            continue
        for trigger in ("pull_request", "pull_request_target"):
            if trigger not in on:
                continue
            cfg = on.get(trigger)
            if (_would_run(cfg, "main", changed_files)
                    and not _would_run(cfg, base, changed_files)):
                skipped.append(fname.name)
                break
    return skipped


def fetch_changed_files(repo: str, number: int) -> list[str]:
    """Chemins modifies par la PR, sans troncature a 100 fichiers.

    ``gh pr view --json files`` rend la premiere page (100 max) et ne dit pas
    qu'il a coupe. Sous-compter les fichiers sous-compterait la couverture
    perdue -- un silence qui relache, exactement le defaut que #16194 mesure.
    On ne pagine donc que lorsque c'est necessaire (cas rare ici : aucun des
    200 derniers PRs ne depasse 90 fichiers).
    """
    pr = _gh_json(["pr", "view", str(number), "--repo", repo,
                   "--json", "files,changedFiles"]) or {}
    files = [f.get("path") for f in (pr.get("files") or []) if f.get("path")]
    total = pr.get("changedFiles") or 0
    if len(files) >= total:
        return files
    paged = _gh_json(["api", "--paginate", "--slurp",
                      f"repos/{repo}/pulls/{number}/files?per_page=100",
                      "--jq", "[.[][] | .filename]"]) or []
    if isinstance(paged, list) and paged:
        return [str(p) for p in paged]
    return files


def _skipped_section(skipped: list[str]) -> list[str]:
    """Bloc du commentaire nommant les workflows perdus, ou rien."""
    if not skipped:
        return []
    named = skipped[:MAX_NAMED_SKIPPED]
    lines = [
        "",
        "### Couverture CI perdue sur cette base (mesure, #16194)",
        "",
        f"**{len(skipped)} workflow(s)** se declencheraient si cette PR visait "
        f"`main`, et ne se declenchent pas ici : leur filtre de branche cible "
        f"les eteint, alors que leur filtre de chemins est satisfait par les "
        f"fichiers de cette PR.",
        "",
    ]
    lines += [f"- `{name}`" for name in named]
    if len(skipped) > len(named):
        lines.append(f"- ... et {len(skipped) - len(named)} autre(s)")
    lines += [
        "",
        "**Un check absent n'est pas un check vert.** `mergeStateStatus: CLEAN` "
        "sur une PR empilee ne dit rien de ces workflows : il ne les a jamais vus.",
    ]
    return lines


def build_comment(base: str, open_count: int, title: str,
                  skipped: list[str] | None = None) -> str:
    if open_count > 0:
        stack = (
            f"Cette PR ne livre pas sur `main` : son contenu attend le merge de "
            f"`{base}`. **{open_count} PR ouverte(s)** de `{base}` vers `main` "
            f"existe(nt) a cet instant -- c'est un **stack legitime**, le "
            f"contenu est en vol. Verifier au moment du merge que la base est "
            f"effectivement reliee a `main`."
        )
    else:
        stack = (
            f"Cette PR ne livre pas sur `main` : son contenu attend le merge de "
            f"`{base}`. **Aucune PR ouverte** de `{base}` vers `main` a cet "
            f"instant -- si la base n'est jamais mergee, le livrable "
            f"(`{title}`) devient un **orphelin** (personne ne le verra jamais, "
            f"cf. #10918). Remede : ouvrir une PR de `{base}` vers `main`, ou "
            f"rebaser cette PR sur `main`."
        )
    return "\n".join([
        MARKER_START,
        "## Base != main (advisory, #10918)",
        "",
        stack,
        *_skipped_section(skipped or []),
        MARKER_END,
    ])


# ---------------------------------------------------------------------------
# gh wiring
# ---------------------------------------------------------------------------

def _gh_json(args: list[str]) -> object:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True,
                          check=False, encoding="utf-8")
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def ensure_label(repo: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "label", "create", LABEL_NAME, "--repo", repo,
         "--color", LABEL_COLOR, "--description", LABEL_DESC, "--force"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def existing_comment(repo: str, number: int) -> int | None:
    comments = _gh_json(["pr", "view", str(number), "--repo", repo,
                         "--json", "comments"]) or {}
    for c in (comments.get("comments") or []):
        if MARKER_START in (c.get("body") or ""):
            return c["id"]
    return None


def update_comment(repo: str, comment_id: int, body: str) -> None:
    subprocess.run(
        ["gh", "api", f"repos/{repo}/issues/comments/{comment_id}",
         "-X", "PATCH", "-f", f"body={body}"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def post_comment(repo: str, number: int, body: str) -> None:
    subprocess.run(
        ["gh", "pr", "comment", str(number), "--repo", repo, "--body", body],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--pr", type=int, required=True, help="PR number to signal")
    ap.add_argument("--dry-run", action="store_true", help="log only, apply nothing")
    ap.add_argument("--repo", default=None, help="repo (default: gh default / GITHUB_REPOSITORY)")
    args = ap.parse_args(argv)

    repo = args.repo or (subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True, text=True, encoding="utf-8").stdout.strip()
        or "jsboige/CoursIA")

    pr = _gh_json(["pr", "view", str(args.pr), "--repo", repo,
                   "--json", "baseRefName,title"]) or {}
    base = pr.get("baseRefName", "")
    title = pr.get("title", "")

    if not base or base == "main":
        print(f"[base-not-main] #{args.pr} base={base or '?'} -- pas un defaut, rien a faire")
        return 0

    changed = fetch_changed_files(repo, args.pr)
    open_count = count_open_prs_on_base(repo, base)
    skipped = workflows_skipped_by_base(WORKFLOWS_DIR, base, changed)
    print(f"[base-not-main] #{args.pr} base={base} open_prs_to_main={open_count} "
          f"ci_skipped={len(skipped)} files={len(changed)} "
          f"mode={'dry-run' if args.dry_run else 'apply'}")
    if args.dry_run:
        print(build_comment(base, open_count, title, skipped))
        return 0

    ensure_label(repo, False)
    body = build_comment(base, open_count, title, skipped)
    cid = existing_comment(repo, args.pr)
    if cid is not None:
        update_comment(repo, cid, body)
        print(f"[base-not-main] comment updated ({cid})")
    else:
        post_comment(repo, args.pr, body)
        print("[base-not-main] comment posted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
