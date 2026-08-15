#!/usr/bin/env python3
"""check_orphan_merged_pr.py — detecte les PR dont le contenu n'a jamais atteint main.

Classe de defaut visee (#10981) : une PR est mergee avec ``base != main`` (dans
une jambe de stack). Son contenu n'atteint ``main`` QUE si la jambe y arrive
ensuite. Un squash-merge de la jambe produit un commit neuf sur ``main`` et ne
rend PAS la branche ancetre de main : tout ce qui atterrit ensuite sur la
branche est mort-ne. Sequence reelle du 2026-08-14 (orphelin #10972, site casse
en prod) :

    16:23:30  advisory sur #10972 : base=feature/c10923-quarto-normalize,
              open_prs_to_main=1 -> « stack legitime »       <-- VRAI a cet instant
    16:41:15  #10965 (cette base -> main) mergee en --squash
    16:41:39  #10972 mergee DANS cette base, 24 s plus tard  <-- orphelin cree

L'advisory (base_not_main.py) ne mesure qu'au moment ``pull_request`` ; le
verdict « stack legitime » devient faux 18 minutes plus tard sans re-declencher
l'advisory. Ce detecteur est POST-MERGE : il re-examine chaque PR MERGED dont
``baseRefName != main`` et verifie que son ``mergeCommit`` est ancetre de
``origin/main``. C'est le controle que l'advisory deleguait a l'humain
(« verifier au moment du merge ») sans que rien ne l'execute.

Trois filtres anti-faux-positifs :

1. **mergeCommit ancetre de main** -> propre : le contenu est arrive (jambe
   mergee en --merge preserve-SHA, ou contenu porte directement).
2. **Jambe en vol** : une PR OUVERTE de la base vers ``main`` existe -> le
   contenu va arriver, ce n'est pas un orphelin (verdict stable, pas de course).
3. **Contenu re-atterri** : les fichiers de la PR sont deja presents a
   l'identique sur ``main`` (cherry-pick / re-PR) -> pas un orphelin.

Un finding est donc : *PR MERGED, base != main, mergeCommit non-ancetre de
main, aucune PR ouverte de la base vers main, et le contenu manque encore a
main*. L'orphelinage est un etat STABLE une fois avere : un balayage quotidien
suffit (latence J+1 acceptable, l'issue le dit explicitement).

Usage :
    py scripts/audit/check_orphan_merged_pr.py --days 14
    py scripts/audit/check_orphan_merged_pr.py --from-json prs.json --repo-path <repo>
    py scripts/audit/check_orphan_merged_pr.py --days 30 --strict
    py scripts/audit/check_orphan_merged_pr.py --days 7 --json-out out.json --apply

Exit codes :
    0 — advisory par defaut : n'echoue jamais, meme avec des findings
    1 — findings ET `--strict`
    2 — erreur d'execution (git absent, depot invalide, JSON illisible)
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

LABEL_NAME = "orphaned-delivery"
LABEL_COLOR = "b60205"  # dark red — "le contenu de cette PR n'a jamais atteint main"
LABEL_DESC = "PR mergee dont le mergeCommit n'est pas ancetre de main : contenu orphelin (#10981)"

MARKER_START = "<!-- ORPHANED-DELIVERY:START -->"
MARKER_END = "<!-- ORPHANED-DELIVERY:END -->"


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
    """Parse un horodatage ISO 8601 (gh mergedAt) en datetime aware."""
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    parsed = datetime.fromisoformat(text)
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed


def commit_exists(repo: Path, commit: str) -> bool:
    """Vrai si le commit existe localement (objet git present)."""
    proc = subprocess.run(
        ["git", "-C", str(repo), "cat-file", "-e", f"{commit}^{{commit}}"],
        capture_output=True,
        text=True,
    )
    return proc.returncode == 0


def is_ancestor(repo: Path, commit: str, base_ref: str) -> bool:
    """Vrai si `commit` est ancetre (ou egal) de `base_ref`."""
    proc = subprocess.run(
        ["git", "-C", str(repo), "merge-base", "--is-ancestor", commit, base_ref],
        capture_output=True,
        text=True,
    )
    if proc.returncode == 0:
        return True
    if proc.returncode == 1:
        return False
    raise GitError(f"git merge-base --is-ancestor -> {proc.returncode}: {proc.stderr.strip()}")


def content_missing_from_base(
    repo: Path, base_ref: str, merge_commit: str, paths: list[str]
) -> bool:
    """Vrai si les chemins donnes different encore entre base et mergeCommit.

    Diff deux-points volontairement : on compare les arbres tels qu'ils sont
    aujourd'hui. Un diff trois-points reintroduirait le contenu de la jambe
    deja squashe et rendrait tout orphelin suspect.
    """
    if not paths:
        return False
    proc = subprocess.run(
        ["git", "-C", str(repo), "diff", "--quiet", base_ref, merge_commit, "--", *paths],
        capture_output=True,
        text=True,
    )
    if proc.returncode == 0:
        return False  # identique -> le contenu est deja dans la base
    if proc.returncode == 1:
        return True  # differe -> contenu absent de la base
    raise GitError(f"git diff --quiet -> {proc.returncode}: {proc.stderr.strip()}")


def open_prs_to_main(repo: str, base: str) -> int:
    """PRs ouvertes dont la tete est `base` et qui visent `main` (le stack)."""
    proc = subprocess.run(
        ["gh", "pr", "list", "--repo", repo, "--state", "open",
         "--search", f'head:"{base}" base:main', "--json", "number"],
        capture_output=True, text=True, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh pr list -> {proc.returncode}: {proc.stderr.strip() or proc.stdout.strip()}"
        )
    data = json.loads(proc.stdout or "[]")
    return len(data)


def analyse_pr(repo: Path, pr: dict, base_ref: str, repo_slug: str) -> dict:
    """Analyse une PR mergee. Rend un dict de resultat avec `status` explicite.

    Statuts :
      ``orphan``      — mergeCommit non-ancetre de main, jambe morte, contenu absent (finding)
      ``clean``       — ancetre de main, ou contenu deja present (re-atterri)
      ``in_flight``   — jambe encore ouverte vers main (stack legitime en vol)
      ``skipped``     — base == main, ou mergeCommit manquant / introuvable
    """
    number = pr.get("number")
    base = (pr.get("baseRefName") or "").strip()
    head = (pr.get("headRefName") or "").strip()
    merged_at = pr.get("mergedAt")
    merge_commit = (pr.get("mergeCommit") or {}).get("oid") if isinstance(
        pr.get("mergeCommit"), dict) else None
    title = pr.get("title", "")

    result = {"number": number, "head": head, "base": base, "merged_at": merged_at,
              "title": title}

    if not base or base == "main":
        return {**result, "status": "skipped", "reason": "base is main"}
    if not merge_commit:
        return {**result, "status": "skipped", "reason": "no mergeCommit"}
    if not commit_exists(repo, merge_commit):
        return {**result, "status": "skipped", "reason": f"mergeCommit {merge_commit[:9]} unreachable locally"}

    # Filtre 1 : ancetre de main -> le contenu est arrive.
    if is_ancestor(repo, merge_commit, base_ref):
        return {**result, "status": "clean", "reason": "mergeCommit is ancestor of base"}

    # Filtre 2 : jambe encore ouverte vers main -> le contenu va arriver.
    if repo_slug:
        inflight = open_prs_to_main(repo_slug, base)
        if inflight > 0:
            return {**result, "status": "in_flight", "open_prs_to_main": inflight,
                    "reason": f"base '{base}' still has {inflight} open PR(s) towards main"}

    # Filtre 3 : le contenu a-t-il re-atterri par une autre route (cherry-pick) ?
    paths = [f.get("path") for f in (pr.get("files") or []) if f.get("path")]
    missing = content_missing_from_base(repo, base_ref, merge_commit, paths)
    if not missing:
        return {**result, "status": "clean", "merge_commit": merge_commit,
                "paths": paths, "reason": "content already present in base (re-landed)"}

    return {**result, "status": "orphan", "merge_commit": merge_commit,
            "paths": paths,
            "recovery": f"git merge origin/{head}"}


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
        "--json", "number,title,baseRefName,headRefName,mergedAt,mergeCommit,files",
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
    inflight = [r for r in results if r["status"] == "in_flight"]
    lines: list[str] = []

    for r in orphans:
        lines.append(f"ORPHAN  PR #{r['number']}  base={r['base']}  head={r['head']}")
        lines.append(f"        merge: {r['merged_at']}  mergeCommit={r['merge_commit'][:12]}  |  {r['title'][:70]}")
        for p in r.get("paths", [])[:5]:
            lines.append(f"          ~ {p}")
        lines.append(f"        recuperation : {r.get('recovery', '')}")
        lines.append("")

    lines.append(
        "Analysees: {total} | orphelins: {o} | en vol: {f} | propres: {c} | ignorees: {s}".format(
            total=len(results),
            o=len(orphans),
            f=len(inflight),
            c=sum(1 for r in results if r["status"] == "clean"),
            s=sum(1 for r in results if r["status"] == "skipped"),
        )
    )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# gh wiring for --apply (label + comment), mirrors scripts/base_not_main.py
# ---------------------------------------------------------------------------

def _gh_json(args: list[str]) -> object:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True,
                          check=False, encoding="utf-8")
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def ensure_label(repo: str) -> None:
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


def build_comment(r: dict) -> str:
    return "\n".join([
        MARKER_START,
        "## Contenu orphelin — mergeCommit jamais arrive sur `main` (#10981)",
        "",
        f"Cette PR a ete mergee dans `{r['base']}` (base != `main`), et son "
        f"`mergeCommit` **{r['merge_commit'][:12]}** n'est **pas ancetre de "
        f"`main`** : le contenu (`{r['title']}`) n'a jamais ete porte sur la "
        f"branche principale. Recuperation proposee : "
        f"`{r.get('recovery', '')}` puis PR de la base vers `main`.",
        MARKER_END,
    ])


def apply_findings(repo: str, orphans: list[dict], dry_run: bool) -> None:
    """Label + commentaire marker-guarde (upsert, pas de spam quotidien)."""
    if not orphans:
        return
    if not dry_run:
        ensure_label(repo)
    for r in orphans:
        number = r["number"]
        if dry_run:
            print(f"[orphan-apply] #{number} label={LABEL_NAME} (dry-run)")
            continue
        body = build_comment(r)
        cid = existing_comment(repo, number)
        if cid is not None:
            update_comment(repo, cid, body)
            print(f"[orphan-apply] #{number} comment updated ({cid})")
        else:
            post_comment(repo, number, body)
            print(f"[orphan-apply] #{number} comment posted")
        subprocess.run(
            ["gh", "pr", "edit", str(number), "--repo", repo, "--add-label", LABEL_NAME],
            capture_output=True, text=True, check=False, encoding="utf-8",
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo-path", default=".", help="racine du depot git (defaut: .)")
    parser.add_argument("--base-ref", default="origin/main", help="ref de base (defaut: origin/main)")
    parser.add_argument("--days", type=int, default=14,
                        help="fenetre d'anciennete des merges, en jours (0 = sans limite)")
    parser.add_argument("--limit", type=int, default=200, help="nombre de PR demandees a gh")
    parser.add_argument("--repo", default=None, help="slug owner/name passe a gh")
    parser.add_argument("--from-json", default=None,
                        help="lire les PR depuis un JSON local au lieu d'appeler gh")
    parser.add_argument("--json-out", default=None, help="ecrire le resultat complet en JSON")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 si au moins un orphelin (defaut: advisory, exit 0)")
    parser.add_argument("--apply", action="store_true",
                        help="label orphaned-delivery + commentaire sur les PR orphelines")
    parser.add_argument("--dry-run", action="store_true",
                        help="avec --apply : loguer sans appliquer")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    repo = Path(args.repo_path).resolve()

    try:
        if not (repo / ".git").exists() and not (repo / ".git").is_file():
            run_git(repo, "rev-parse", "--git-dir")
        repo_slug = args.repo or (subprocess.run(
            ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
            capture_output=True, text=True, encoding="utf-8").stdout.strip()
            or "jsboige/CoursIA")
        prs = filter_by_age(load_prs(args), args.days)
        results = [analyse_pr(repo, pr, args.base_ref, repo_slug) for pr in prs]
    except GitError as exc:
        print(f"ERREUR: {exc}", file=sys.stderr)
        return 2
    except json.JSONDecodeError as exc:
        print(f"ERREUR: JSON illisible: {exc}", file=sys.stderr)
        return 2
    except RuntimeError as exc:
        print(f"ERREUR: {exc}", file=sys.stderr)
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
    if args.apply:
        try:
            apply_findings(repo_slug, orphans, args.dry_run)
        except RuntimeError as exc:
            print(f"ERREUR: {exc}", file=sys.stderr)
            return 2

    return 1 if (orphans and args.strict) else 0


if __name__ == "__main__":
    sys.exit(main())
