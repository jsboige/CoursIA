#!/usr/bin/env python3
"""check_orphan_post_merge_commits.py — detecte le travail pousse APRES le merge de sa PR.

Classe de defaut visee : une PR est mergee, puis des commits sont pousses sur sa
branche de tete. Le contenu de ces commits n'atteint jamais `main` et **rien ne le
signale** : la PR affiche `MERGED`, son titre peut avoir ete edite pour annoncer le
travail complet, et le rapport de l'auteur herite du titre plutot que de l'historique.

Incident fondateur (#6724, 2026-07-29) : le capstone `evolve_shift` a ete pousse
**11 minutes apres** le merge de sa PR. Cinq theoremes sont restes absents de `main`
pendant deux cycles alors que le titre de la PR annoncait « chain COMPLETE ». Le
travail n'a survecu que parce que la branche n'avait pas ete supprimee au merge
(`--delete-branch` est interdit dans ce depot, cf .claude/rules/git-workflow.md).

Deux filtres anti-faux-positifs, sans lesquels l'outil serait inutilisable :

1. **Les originaux d'un squash-merge ne sont PAS orphelins.** Apres un squash, les
   commits d'origine restent inaccessibles depuis `main` par construction — leur
   contenu, lui, y est. Seuls les commits **dates apres** `mergedAt` sont candidats.
2. **Le contenu re-atterri par une autre route n'est PAS orphelin.** Un cherry-pick
   ulterieur peut avoir apporte les memes lignes. On ne signale que si les fichiers
   touches **different encore** entre `main` et la branche.

Un finding est donc : *au moins un commit poste-merge dont le contenu manque toujours
a `main`*. C'est verifiable en une commande, et c'est ce que la sortie affiche.

Usage :
    py scripts/audit/check_orphan_post_merge_commits.py --days 14
    py scripts/audit/check_orphan_post_merge_commits.py --from-json prs.json
    py scripts/audit/check_orphan_post_merge_commits.py --days 30 --strict
    py scripts/audit/check_orphan_post_merge_commits.py --days 7 --json-out out.json

Exit codes :
    0 — advisory par defaut : n'echoue jamais, meme avec des findings
    1 — findings ET `--strict` (a n'activer qu'une fois la classe de FP mesuree a zero)
    2 — erreur d'execution (git absent, depot invalide, JSON illisible)
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable


class GitError(RuntimeError):
    """Echec d'une commande git — remonte en exit 2, jamais en finding."""


def run_git(repo: Path, *args: str, check: bool = True) -> str:
    """Execute git dans `repo` et rend stdout strippe."""
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if check and proc.returncode != 0:
        raise GitError(f"git {' '.join(args)} -> {proc.returncode}: {proc.stderr.strip()}")
    return proc.stdout.strip()


def parse_ts(value: str) -> datetime:
    """Parse un horodatage ISO 8601 (git %cI ou gh mergedAt) en datetime aware."""
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    parsed = datetime.fromisoformat(text)
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed


def branch_exists(repo: Path, ref: str) -> bool:
    """Vrai si la ref existe (branche locale, distante, ou tag)."""
    proc = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "--verify", "--quiet", ref],
        capture_output=True,
        text=True,
    )
    return proc.returncode == 0


def commits_not_in_base(repo: Path, base_ref: str, branch_ref: str) -> list[dict]:
    """Commits presents sur `branch_ref` et inaccessibles depuis `base_ref`.

    Rend une liste de dicts {sha, committed_at, subject}, du plus recent au plus ancien.
    """
    out = run_git(
        repo,
        "log",
        "--format=%H%x1f%cI%x1f%s",
        f"{base_ref}..{branch_ref}",
    )
    commits: list[dict] = []
    for line in out.splitlines():
        if not line.strip():
            continue
        parts = line.split("\x1f")
        if len(parts) != 3:
            continue
        sha, committed_at, subject = parts
        commits.append({"sha": sha, "committed_at": committed_at, "subject": subject})
    return commits


def files_touched(repo: Path, shas: Iterable[str]) -> list[str]:
    """Union des chemins touches par les commits donnes."""
    paths: set[str] = set()
    for sha in shas:
        out = run_git(repo, "show", "--pretty=", "--name-only", sha)
        paths.update(p for p in out.splitlines() if p.strip())
    return sorted(paths)


def content_missing_from_base(
    repo: Path, base_ref: str, branch_ref: str, paths: list[str]
) -> bool:
    """Vrai si les chemins donnes different encore entre base et branche.

    Diff **deux-points** volontairement : on compare les arbres tels qu'ils sont
    aujourd'hui, pas depuis la base de fusion. Un diff trois-points reintroduirait
    le contenu deja squashe et rendrait tout squash-merge suspect.
    """
    if not paths:
        return False
    proc = subprocess.run(
        ["git", "-C", str(repo), "diff", "--quiet", base_ref, branch_ref, "--", *paths],
        capture_output=True,
        text=True,
    )
    if proc.returncode == 0:
        return False  # identique -> le contenu est deja dans la base
    if proc.returncode == 1:
        return True  # differe -> contenu absent de la base
    raise GitError(f"git diff --quiet -> {proc.returncode}: {proc.stderr.strip()}")


def analyse_pr(repo: Path, pr: dict, base_ref: str, remote: str) -> dict:
    """Analyse une PR mergee. Rend un dict de resultat, avec `status` explicite.

    Statuts possibles :
      ``orphan``       — commits poste-merge dont le contenu manque a la base (finding)
      ``clean``        — rien de poste-merge, ou contenu deja re-atterri
      ``branch_gone``  — branche supprimee : indetectable, signale sans etre un finding
      ``skipped``      — PR sans `mergedAt` ou sans branche de tete exploitable
    """
    number = pr.get("number")
    head = (pr.get("headRefName") or "").strip()
    merged_at_raw = pr.get("mergedAt")

    base = {"number": number, "head": head, "merged_at": merged_at_raw,
            "title": pr.get("title", "")}

    if not head or not merged_at_raw:
        return {**base, "status": "skipped", "reason": "missing headRefName or mergedAt"}

    branch_ref = f"{remote}/{head}" if remote else head
    if not branch_exists(repo, branch_ref):
        return {**base, "status": "branch_gone", "branch_ref": branch_ref}

    merged_at = parse_ts(merged_at_raw)
    unreachable = commits_not_in_base(repo, base_ref, branch_ref)

    # Filtre 1 : seuls les commits DATES APRES le merge sont candidats.
    # Les originaux d'un squash sont inaccessibles par construction, pas orphelins.
    post_merge = [c for c in unreachable if parse_ts(c["committed_at"]) > merged_at]
    if not post_merge:
        return {**base, "status": "clean", "branch_ref": branch_ref,
                "unreachable_total": len(unreachable), "post_merge": 0}

    # Filtre 2 : le contenu a-t-il re-atterri par une autre route (cherry-pick) ?
    paths = files_touched(repo, [c["sha"] for c in post_merge])
    missing = content_missing_from_base(repo, base_ref, branch_ref, paths)
    if not missing:
        return {**base, "status": "clean", "branch_ref": branch_ref,
                "unreachable_total": len(unreachable), "post_merge": len(post_merge),
                "reason": "content already present in base (re-landed elsewhere)"}

    return {
        **base,
        "status": "orphan",
        "branch_ref": branch_ref,
        "base_ref": base_ref,
        "unreachable_total": len(unreachable),
        "post_merge": len(post_merge),
        "commits": post_merge,
        "paths": paths,
    }


def load_prs(args: argparse.Namespace) -> list[dict]:
    """Charge les PR mergees depuis un JSON local (`--from-json`) ou via `gh`."""
    if args.from_json:
        path = Path(args.from_json)
        if not path.is_file():
            raise GitError(f"--from-json: fichier introuvable: {path}")
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, list) else data.get("prs", [])

    cmd = [
        "gh", "pr", "list", "--state", "merged", "--limit", str(args.limit),
        "--json", "number,title,headRefName,mergedAt",
    ]
    if args.repo:
        cmd += ["--repo", args.repo]
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                          errors="replace")
    if proc.returncode != 0:
        raise GitError(f"gh pr list -> {proc.returncode}: {proc.stderr.strip()}")
    return json.loads(proc.stdout or "[]")


def filter_by_age(prs: list[dict], days: int, now: datetime | None = None) -> list[dict]:
    """Ne garde que les PR mergees dans la fenetre demandee (0 = sans limite)."""
    if days <= 0:
        return prs
    reference = now or datetime.now(timezone.utc)
    kept = []
    for pr in prs:
        raw = pr.get("mergedAt")
        if not raw:
            continue
        if (reference - parse_ts(raw)).days <= days:
            kept.append(pr)
    return kept


def format_report(results: list[dict]) -> str:
    """Rapport texte : les findings d'abord, puis un recapitulatif compte."""
    orphans = [r for r in results if r["status"] == "orphan"]
    gone = [r for r in results if r["status"] == "branch_gone"]
    lines: list[str] = []

    for r in orphans:
        lines.append(f"ORPHAN  PR #{r['number']}  {r['head']}")
        lines.append(f"        merge: {r['merged_at']}   |  {r['title'][:70]}")
        for c in r["commits"]:
            lines.append(f"        + {c['sha'][:9]}  {c['committed_at']}  {c['subject'][:60]}")
        for p in r["paths"]:
            lines.append(f"          ~ {p}")
        lines.append(
            "        verifier : git diff {base} {branch} -- {paths}".format(
                base=r.get("base_ref", "origin/main"),
                branch=r["branch_ref"],
                paths=" ".join(r["paths"][:3]),
            )
        )
        lines.append("")

    lines.append(
        "Analysees: {total} | orphelines: {o} | propres: {c} | branche supprimee: {g} | ignorees: {s}".format(
            total=len(results),
            o=len(orphans),
            c=sum(1 for r in results if r["status"] == "clean"),
            g=len(gone),
            s=sum(1 for r in results if r["status"] == "skipped"),
        )
    )
    if gone:
        lines.append(
            "Note: {n} PR ont une branche supprimee — le travail poste-merge y serait "
            "indetectable (raison du 'JAMAIS --delete-branch').".format(n=len(gone))
        )
    return "\n".join(lines)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo-path", default=".", help="racine du depot git (defaut: .)")
    parser.add_argument("--base-ref", default="origin/main", help="ref de base (defaut: origin/main)")
    parser.add_argument("--remote", default="origin",
                        help="remote portant les branches de tete ('' pour des refs locales)")
    parser.add_argument("--days", type=int, default=14,
                        help="fenetre d'anciennete des merges, en jours (0 = sans limite)")
    parser.add_argument("--limit", type=int, default=100, help="nombre de PR demandees a gh")
    parser.add_argument("--repo", default=None, help="slug owner/name passe a gh")
    parser.add_argument("--from-json", default=None,
                        help="lire les PR depuis un JSON local au lieu d'appeler gh")
    parser.add_argument("--json-out", default=None, help="ecrire le resultat complet en JSON")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 si au moins un orphelin (defaut: advisory, exit 0)")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    repo = Path(args.repo_path).resolve()

    try:
        if not (repo / ".git").exists() and not (repo / ".git").is_file():
            run_git(repo, "rev-parse", "--git-dir")
        prs = filter_by_age(load_prs(args), args.days)
        results = [analyse_pr(repo, pr, args.base_ref, args.remote) for pr in prs]
    except GitError as exc:
        print(f"ERREUR: {exc}", file=sys.stderr)
        return 2
    except json.JSONDecodeError as exc:
        print(f"ERREUR: JSON illisible: {exc}", file=sys.stderr)
        return 2

    print(format_report(results))

    if args.json_out:
        try:
            Path(args.json_out).write_text(
                json.dumps({"results": results}, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
        except OSError as exc:
            print(f"ERREUR: --json-out non ecrivable: {exc}", file=sys.stderr)
            return 2

    orphans = [r for r in results if r["status"] == "orphan"]
    return 1 if (orphans and args.strict) else 0


if __name__ == "__main__":
    sys.exit(main())
