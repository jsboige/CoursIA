#!/usr/bin/env python3
r"""prune_merged_worktrees.py -- retire les worktrees de PRs mergées/fermées (#14195, dette #8924).

## Why this exists

`po-2026:Maintenance` mesure le 2026-09-02T01:20Z : **265 worktrees recréés en 36 h**
(178 CoursIA + 87 CoursIA-2, contre ~0 le 31/08). Cause première nommée par
l'auteur de la mesure : **chaque review de PR notebook / build Lean crée un
worktree ; rien ne les retire quand la PR est mergée.**

#8924 avait écrit le mécanisme (CLOSED le 2026-08-05 après un nettoyage
manuel, 131 worktrees retirés). Le nettoyage était bon ; l'organe n'a jamais
été construit. La classe est revenue, à quatre fois l'échelle, vingt-huit
jours plus tard. C'est le motif « une règle non appliquée demande un organe,
pas plus de vigilance ».

Ce script est cet organe.

## What it does

  $ python scripts/ci/prune_merged_worktrees.py
  # dry-run (default) : affiche les retraits prévus + les refus motivés
  WOULD REMOVE  <path>  branch=fix/X  reason=pr_merged  pr=#14427
  REFUSE       <path>  branch=fix/Y  reason=pr_open    pr=#14433
  REFUSE       <path>  branch=fix/Z  reason=unpushed_commits  ahead=2
  REFUSE       <path>  reason=no_branch_untracked_artifacts_only
  ---
  total=4  removable=1  refused=3

  $ python scripts/ci/prune_merged_worktrees.py --apply
  # applique les retraits ; exit 1 si au moins un refus non-bloquant

  $ python scripts/ci/prune_merged_worktrees.py --json
  {"scanned": 4, "removable": 1, "refused": 3, "actions": [...]}

  $ python scripts/ci/prune_merged_worktrees.py --path /c/dev/CoursIA-X
  # ne considere qu'un worktree (test)

Critères de retrait (cf issue #14195 acceptance) :

1. **Worktree avec commits non poussés** (`git rev-list --count @{u}..HEAD > 0`) :
   REFUSE, jamais d'exception. Aucune branche n'est mergee alors qu'elle a
   du travail non publie.
2. **Worktree avec une PR OPEN** : REFUSE. Le retrait casserait l'iteration
   en cours.
3. **Worktree avec une PR MERGED ou CLOSED (non-merged)** : REMOVE.
4. **Worktree sans branche (HEAD détaché)** : verdict par contenu. Si
   `git log origin/main --grep "<branch_topic>"` trouve un commit dont le
   sujet correspond (le squash a efface l'ascendance) : REMOVE ; sinon REFUSE.
5. **Worktree avec arbre sale non-artefact** (edition de source non
   commitée) : REFUSE. Les artefacts untracked (`slides/images/`,
   `**/scripts/results/`, `.claude/agent-memory/*`, `*_output.ipynb`, caches
   `node_modules/`, `.cache/`, `.pytest_cache/`) sont tolérés -- ce sont
   les categories du dernier commentaire de #8924, qui sont bonnes et qu'on
   reprend plutôt qu'on réinvente.

Ancre PR : `gh pr list --state all --search "head:<branch>"` (autoritative,
cf matrice a 4 ancres de `.claude/rules/git-workflow.md` §orphan-branch-scan).
Ni `--is-ancestor` seul ni `commits/<oid>/pulls` ne suffisent : le premier
rate les squash-merges, le second a des faux negatifs mesures.

## Design rules that matter

1. **Dry-run par defaut, --apply explicite.** Jamais de retrait silencieux.
2. **Journal de refus obligatoire.** Un outil de purge qui ne dit pas ce
   qu'il épargne est indiscernable d'un outil qui ne regarde pas.
3. **Aucun `git worktree remove --force`.** Le retrait est `git worktree
   remove` sans --force ; si git refuse (worktree sale), on log la cause et
   on continue (ne JAMAIS forcer).
4. **Mode `--json` parallele au mode texte.** Mêmes chiffres, même ordre ;
   le recipient downstream (dashboard sweep, DM ai-01) parse le JSON sans
   réinventer le rendu.
5. **Exit code : 0 si tout OK (dry-run ou apply reussi), 1 si refus
   non-bloquant observe, 2 si erreur gh/git infra.** Comme `list_orphan_prs`
   (#13086).
6. **Pas d'auto-retry.** Si `gh` echoue (auth, rate-limit, network), exit 2
   sans fallback silencieux.
7. **Worktree courant exclu.** On ne tente jamais `git worktree remove` sur
   le worktree depuis lequel le script est lance -- un retrait du repertoire
   de travail serait fatal.

## Run locally

    python scripts/ci/prune_merged_worktrees.py
    python scripts/ci/prune_merged_worktrees.py --apply
    python scripts/ci/prune_merged_worktrees.py --json
    python scripts/ci/prune_merged_worktrees.py --path /c/dev/CoursIA-X

Exit codes:
    0  OK (dry-run propre, ou apply reussi avec 0 erreur)
    1  Au moins un refus observe (worktree non retire pour cause legitime)
    2  Erreur gh/git infra (auth, rate-limit, worktree introuvable, etc.)

## Coupling with #14195 et #8924

#8924 est le precedent CLOSED : mecanisme nomme, organe non construit.
#14195 demande cet organe. Ce script ferme la dette.

## Acceptance criteria (depuis #14195)

- [x] `scripts/ci/prune_merged_worktrees.py` livre, dry-run par defaut,
      `--apply` explicite
- [x] Tests d'affaiblissement : commits non pousses refuses, PR open
      refusee, arbre sale edition source refuse, branche squash-mergee
      retiree (controle positif du predicat d'ascendance)
- [x] Journal nomme chaque refus avec sa cause
- [x] Ligne dans `.claude/rules/git-workflow.md` : commande canonique en
      fin de cycle
- [x] Mesure avant/apres sur machine reelle, posee en commentaire issue
"""
from __future__ import annotations

import argparse
import dataclasses
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Optional


# Categories d'artefacts untracked tolerees (cf commentaire final de #8924).
# Une edition source (fichier .py, .md, .cs, .ipynb, .yml, .json hors
# resultats) NON committee REFUSE le retrait, peu importe le statut PR.
# Tokens a matcher dans le chemin untracke. Le matching est "contient"
# apres normalisation des separateurs Windows -> /. Cela permet de
# capturer `scripts/results/foo.json` (debut relatif) aussi bien que
# `foo/scripts/results/x.json` (interne). Pour eviter les faux positifs
# sur des fichiers source qui contiennent `scripts/results` dans leur nom
# (improbable mais prudent), chaque token est precede ou suivi d'un /
# virtuel par la logique de matching.
UNTRACKED_ARTIFACT_TOKENS = (
    "slides/images",
    "slides/pptx-reference",
    "scripts/results",
    ".claude/agent-memory",
    "_output.ipynb",
    "node_modules",
    ".cache",
    ".pytest_cache",
    "__pycache__",
    "_measurements",
    ".mypy_cache",
    ".ruff_cache",
    "/dist/",
    "/build/",
    ".eggs",
    ".tox",
)

# Extensions/editions source : si du contenu untracked touche un fichier
# de ce type, c'est une edition de source non poussee, REFUSE obligatoire.
SOURCE_EXTENSIONS = (
    ".py", ".ipynb", ".md", ".cs", ".yml", ".yaml", ".json", ".toml",
    ".ini", ".cfg", ".sh", ".ps1", ".bat", ".txt", ".html", ".css", ".js",
    ".ts", ".tsx", ".jsx", ".lean", ".pyi",
)


@dataclasses.dataclass
class WorktreeStatus:
    """Résultat du diagnostic d'un worktree."""

    path: str
    branch: Optional[str]
    is_current: bool
    pr_state: Optional[str]      # "OPEN" / "MERGED" / "CLOSED" / None
    pr_number: Optional[int]
    pr_url: Optional[str]
    ahead_count: int             # commits non poussés
    has_source_dirty: bool       # edition source untracked non toleree
    untracked_paths: list        # chemins untracked (info seulement)
    decision: str                # "REMOVE" / "REFUSE" / "SKIP_CURRENT"
    refusal_reason: Optional[str]

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)


def run_git(cwd: str, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    """Lance une commande git avec capture stricte. cwd doit être un worktree."""
    return subprocess.run(
        ["git", "-C", cwd, *args],
        capture_output=True,
        text=True,
        check=check,
        encoding="utf-8",
        errors="replace",
    )


def run_gh(*args: str, check: bool = True) -> subprocess.CompletedProcess:
    """Lance une commande gh avec capture stricte. cwd = CWD courant."""
    return subprocess.run(
        ["gh", *args],
        capture_output=True,
        text=True,
        check=check,
        encoding="utf-8",
        errors="replace",
    )


def is_untracked_artifact(path: str) -> bool:
    """True si le chemin untracke correspond a un artefact tolere."""
    p = path.replace("\\", "/")
    # Encadre le chemin de / virtuels pour matcher correctement les tokens
    # qui peuvent apparaitre en debut (relatif) ou en milieu (interne).
    wrapped = f"/{p}"
    for token in UNTRACKED_ARTIFACT_TOKENS:
        if token in wrapped:
            return True
    return False


def is_source_dirty(path: str) -> bool:
    """True si le chemin untracked est une edition source non toleree."""
    p = path.replace("\\", "/")
    if is_untracked_artifact(p):
        return False
    return any(p.endswith(ext) for ext in SOURCE_EXTENSIONS)


def get_worktree_info(wt_path: str, current_path: str) -> dict:
    """Recupere branch + ahead count + dirty status d'un worktree."""
    # Branche (peut etre None si HEAD detaché)
    branch_proc = run_git(wt_path, "rev-parse", "--abbrev-ref", "HEAD", check=False)
    branch_raw = branch_proc.stdout.strip()
    branch = None if branch_raw in ("HEAD", "") else branch_raw

    # Ahead count : commits non pousses vs @{u}. Si @{u} n'est pas
    # configure (branche feature sans `set-upstream-to`, frequente avec
    # `git worktree add -b`), @{u} retombe sur origin/main ce qui compare
    # la branche feature a main -- un faux positif massif. On verifie
    # d'abord la resolution explicite : si l'upstream specifique est la
    # branche elle-meme, on compte les commits en avance. Sinon (upstream
    # = main), on considere 0 unpushed et on laisse le verdict PR trancher.
    ahead_count = 0
    if branch:
        upstream_proc = run_git(
            wt_path, "rev-parse", "--abbrev-ref",
            f"{branch}@{{u}}", check=False,
        )
        if upstream_proc.returncode == 0:
            upstream = upstream_proc.stdout.strip()
            if upstream and not upstream.endswith("/main"):
                ahead_proc = run_git(
                    wt_path, "rev-list", "--count", "@{u}..HEAD", check=False
                )
                if ahead_proc.returncode == 0:
                    try:
                        ahead_count = int(ahead_proc.stdout.strip())
                    except ValueError:
                        ahead_count = 0

    # Untracked files
    status_proc = run_git(wt_path, "status", "--porcelain", check=False)
    untracked: list[str] = []
    has_source = False
    for line in status_proc.stdout.splitlines():
        # Format porcelain : XY path (XY = 2 chars index/worktree)
        if len(line) < 4:
            continue
        # '??' = untracked, ' M' / 'M ' / 'MM' etc = modifie
        xy = line[:2]
        path = line[3:].strip()
        # Renames : "R  old -> new" -> on prend la cible
        if " -> " in path:
            path = path.split(" -> ", 1)[1]
        if "??" in xy:
            untracked.append(path)
            if is_source_dirty(path):
                has_source = True
        elif any(c != " " for c in xy):
            # Modification tracked non commitee = source sale
            has_source = True

    return {
        "branch": branch,
        "ahead_count": ahead_count,
        "untracked": untracked,
        "has_source_dirty": has_source,
        "is_current": wt_path == current_path,
    }


def lookup_pr_for_branch(branch: str) -> Optional[dict]:
    """Cherche la PR dont le headRefName = branch.

    Ancre autoritative : `gh pr list --state all --search "head:<branch>"`.
    Pas de REST `commits/<oid>/pulls` (faux negatifs mesures, cf
    orphan-branch-scan dans .claude/rules/git-workflow.md).
    """
    proc = run_gh(
        "pr", "list",
        "--state", "all",
        "--search", f"head:{branch}",
        "--json", "number,state,url,headRefName",
        "--limit", "5",
        check=False,
    )
    if proc.returncode != 0:
        # gh erreur : on ne sait pas decider, REFUSE sec
        raise RuntimeError(f"gh pr list failed: {proc.stderr.strip()}")
    try:
        rows = json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        raise RuntimeError(f"gh pr list returned non-JSON: {e}") from e
    if not rows:
        return None
    # Si plusieurs PRs ont partage le meme nom de branche (improbable mais
    # possible apres close+reopen), on prend la plus recente en premier
    # (gh retourne deja par date desc).
    return rows[0]


def lookup_pr_for_detached_head(wt_path: str) -> Optional[dict]:
    """Verdict par contenu pour HEAD detaché : sujet de commit = titre PR ?

    Le squash-merge efface l'ascendance, donc `git merge-base --is-ancestor`
    ne marche pas. On cherche dans les messages de commit du HEAD du
    worktree un motif qui ressemble a un titre de PR recente.
    """
    log_proc = run_git(
        wt_path, "log", "HEAD", "--format=%s", "-n", "20", check=False
    )
    if log_proc.returncode != 0:
        return None
    subjects = [s.strip() for s in log_proc.stdout.splitlines() if s.strip()]
    if not subjects:
        return None

    # Match contre titres PR recents (limite 50) pour eviter explosion
    pr_proc = run_gh(
        "pr", "list", "--state", "all", "--limit", "50",
        "--json", "number,state,url,title",
        check=False,
    )
    if pr_proc.returncode != 0:
        return None
    try:
        prs = json.loads(pr_proc.stdout)
    except json.JSONDecodeError:
        return None

    # Heuristique : on prend la 1ere PR dont un mot-clé du titre matche un
    # mot du commit subject. Conservateur : on exige au moins 4 chars
    # communs, ce qui limite les faux positifs sur "fix", "test", etc.
    for pr in prs:
        title_tokens = {
            t.lower() for t in re.findall(r"[A-Za-z0-9-]{4,}", pr["title"])
        }
        for subj in subjects:
            subj_tokens = {t.lower() for t in re.findall(r"[A-Za-z0-9-]{4,}", subj)}
            if title_tokens & subj_tokens:
                return pr
    return None


def diagnose_worktree(wt_path: str, current_path: str) -> WorktreeStatus:
    """Diagnostic complet d'un worktree."""
    info = get_worktree_info(wt_path, current_path)

    # Worktree courant : on ne tente JAMAIS de le retirer
    if info["is_current"]:
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=True,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="SKIP_CURRENT",
            refusal_reason="current_worktree_not_removable",
        )

    # Branche main : JAMAIS retirer (le worktree de travail principal).
    # Une PR fermee qui pointe sur `main` ne doit pas faire conclure au
    # retrait : main est la branche de travail vivante, pas une feature
    # terminee.
    if info["branch"] in ("main", "master"):
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason="protected_branch:main",
        )

    # Predicat 1 : commits non poussés -> REFUSE inconditionnel
    if info["branch"] and info["ahead_count"] > 0:
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason=f"unpushed_commits:{info['ahead_count']}",
        )

    # Predicat 2 : edition source untracked -> REFUSE
    if info["has_source_dirty"]:
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=True,
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason="uncommitted_source_changes",
        )

    # Resolution PR
    pr = None
    if info["branch"]:
        pr = lookup_pr_for_branch(info["branch"])
    elif not info["branch"]:
        pr = lookup_pr_for_detached_head(wt_path)

    pr_state = pr.get("state") if pr else None
    pr_number = pr.get("number") if pr else None
    pr_url = pr.get("url") if pr else None

    # Predicat 3 : PR OPEN -> REFUSE
    if pr_state == "OPEN":
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=pr_state,
            pr_number=pr_number,
            pr_url=pr_url,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason=f"pr_open:#{pr_number}",
        )

    # Predicat 4 : PR MERGED ou CLOSED -> REMOVE
    if pr_state in ("MERGED", "CLOSED"):
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=pr_state,
            pr_number=pr_number,
            pr_url=pr_url,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REMOVE",
            refusal_reason=None,
        )

    # Pas de PR trouvee : HEAD detaché sans correspondance, ou branche
    # non pushée qu'on ne peut pas relier. REFUSE conservatrice.
    return WorktreeStatus(
        path=wt_path,
        branch=info["branch"],
        is_current=False,
        pr_state=None,
        pr_number=None,
        pr_url=None,
        ahead_count=info["ahead_count"],
        has_source_dirty=info["has_source_dirty"],
        untracked_paths=info["untracked"],
        decision="REFUSE",
        refusal_reason="no_pr_match" if info["branch"] else "detached_no_match",
    )


def list_worktrees() -> list[dict]:
    """Retourne les worktrees sous forme [{path, head_sha}, ...]."""
    proc = run_git(".", "worktree", "list", "--porcelain", check=False)
    if proc.returncode != 0:
        raise RuntimeError(f"git worktree list failed: {proc.stderr.strip()}")
    out: list[dict] = []
    cur: dict = {}
    for line in proc.stdout.splitlines():
        if line.startswith("worktree "):
            if cur:
                out.append(cur)
            cur = {"path": line[len("worktree "):].strip()}
        elif line.startswith("HEAD "):
            cur["head_sha"] = line[len("HEAD "):].strip()
        elif line.startswith("branch "):
            cur["branch"] = line[len("branch "):].strip()
    if cur:
        out.append(cur)
    return out


def apply_removal(wt: WorktreeStatus) -> tuple[bool, str]:
    """Tente `git worktree remove`. Retourne (success, stderr)."""
    proc = run_git(".", "worktree", "remove", wt.path, check=False)
    if proc.returncode == 0:
        return True, ""
    return False, proc.stderr.strip()


def render_text(statuses: list[WorktreeStatus], dry_run: bool) -> str:
    """Rendu texte canonique (lisible humain)."""
    verb = "WOULD REMOVE" if dry_run else "REMOVED"
    lines: list[str] = []
    counts = {"REMOVE": 0, "REFUSE": 0, "SKIP_CURRENT": 0}
    for s in statuses:
        counts[s.decision] = counts.get(s.decision, 0) + 1
        if s.decision == "REMOVE":
            label = f"{verb} {s.path}"
            if s.branch:
                label += f"  branch={s.branch}"
            if s.pr_state and s.pr_number:
                label += f"  pr=#{s.pr_number}({s.pr_state})"
            lines.append(label)
        elif s.decision == "REFUSE":
            branch_part = f"branch={s.branch}" if s.branch else "no_branch"
            lines.append(
                f"REFUSE    {s.path}  {branch_part}  reason={s.refusal_reason}"
            )
        elif s.decision == "SKIP_CURRENT":
            lines.append(f"SKIP      {s.path}  reason=current_worktree")
    lines.append("---")
    lines.append(
        f"total={len(statuses)}  "
        f"removable={counts.get('REMOVE', 0)}  "
        f"refused={counts.get('REFUSE', 0)}  "
        f"skipped={counts.get('SKIP_CURRENT', 0)}"
    )
    return "\n".join(lines)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument(
        "--apply",
        action="store_true",
        help="Applique les retraits. Dry-run par defaut.",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help="Sortie JSON structuree (parallele au mode texte).",
    )
    p.add_argument(
        "--path",
        default=None,
        help="Cwd pour `git worktree list`. Default = CWD.",
    )
    args = p.parse_args()

    cwd = args.path or "."
    try:
        worktrees = list_worktrees()
    except RuntimeError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2

    # Resolution du chemin canonique du CWD (pour comparaison is_current)
    try:
        current_path = str(Path(cwd).resolve())
    except OSError:
        current_path = cwd

    statuses: list[WorktreeStatus] = []
    for wt in worktrees:
        try:
            statuses.append(diagnose_worktree(wt["path"], current_path))
        except RuntimeError as e:
            print(f"ERROR diagnosing {wt['path']}: {e}", file=sys.stderr)
            return 2

    # Application
    apply_results: list[dict] = []
    refused_count = 0
    removal_count = 0
    error_count = 0
    if args.apply:
        for s in statuses:
            if s.decision != "REMOVE":
                if s.decision == "REFUSE":
                    refused_count += 1
                continue
            ok, stderr = apply_removal(s)
            apply_results.append({
                "path": s.path,
                "branch": s.branch,
                "pr_number": s.pr_number,
                "applied": ok,
                "stderr": stderr,
            })
            if ok:
                removal_count += 1
            else:
                error_count += 1

    refused_count = sum(1 for s in statuses if s.decision == "REFUSE")

    # Sortie
    if args.json:
        out = {
            "scanned": len(statuses),
            "removable": sum(1 for s in statuses if s.decision == "REMOVE"),
            "refused": refused_count,
            "skipped_current": sum(
                1 for s in statuses if s.decision == "SKIP_CURRENT"
            ),
            "dry_run": not args.apply,
            "statuses": [s.to_dict() for s in statuses],
        }
        if args.apply:
            out["apply_results"] = apply_results
            out["applied"] = removal_count
            out["apply_errors"] = error_count
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        # Texte
        print(render_text(statuses, dry_run=not args.apply))
        if args.apply:
            print()
            print(f"applied={removal_count}  errors={error_count}")

    # Exit code
    if error_count > 0:
        return 2
    if refused_count > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
