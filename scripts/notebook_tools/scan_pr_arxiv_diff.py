#!/usr/bin/env python3
"""Extraire les IDs arXiv ajoutes par chaque PR listee dans #11168.

Approche : pour chaque PR, on prend son SHA de merge sur origin/main,
on extrait les fichiers .ipynb modifies (added / modified) par son diff
contre le parent du merge, et on scanne les cellules markdown ajoutees.

Sortie : un CSV avec PR_number, IDs_covered (separes par virgule).
"""
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ARXIV_RE = re.compile(r"\barXiv:\s*(\d{4}\.\d{4,5})\b")
# Le préfixe d'archive fait partie de l'ID legacy (bare 7 chiffres = 400 API,
# #14435 rem. 3) — la capture l'inclut quand il est présent.
ARXIV_RE_LEGACY = re.compile(r"\barXiv:\s*((?:[a-z\-]+(?:\.[A-Z]{2})?/)?\d{7})\b")


def run(cmd, cwd=None):
    """Execute git command, return stdout."""
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    if r.returncode != 0:
        raise RuntimeError(f"git failed: {' '.join(cmd)}\n{r.stderr}")
    return r.stdout


def get_pr_info(pr_number, repo_root):
    """Fichiers touches et SHA de merge d'une PR via `gh pr view`.

    Retourne (files, merge_sha, src) ou (None, None, erreur).
    """
    out = run(["gh", "pr", "view", str(pr_number), "--json",
               "files,mergeCommit"], cwd=repo_root)
    data = json.loads(out)
    files = [f["path"] for f in data.get("files", []) if f["path"].endswith(".ipynb")]
    mc = data.get("mergeCommit") or {}
    sha = mc.get("oid")
    if not sha:
        return files, None, "no-merge-commit"
    return files, sha, "gh-pr-view"


def get_ids_in_files_at_sha(files, sha, repo_root):
    """Scan repo-wide : retourne l'ensemble des IDs arXiv dans les fichiers
    donnes au SHA donne.

    Pour CoursIA, les fichiers sont dans MyIA.AI.Notebooks/ et le scan
    exclut _archives/, .ipynb_checkpoints/, .lake/packages/ -- ici on
    prend les fichiers specifies directement, pas le scan repo-wide.
    """
    ids = set()
    for fp in files:
        try:
            content = run(["git", "show", f"{sha}:{fp}"], cwd=repo_root)
        except RuntimeError:
            continue
        ids.update(extract_arxiv_from_text(content))
    return ids


def extract_arxiv_from_file_at_sha(repo_root, file_path, sha):
    """Lire le notebook a un SHA donne et extraire les IDs arXiv."""
    try:
        content = run(["git", "show", f"{sha}:{file_path}"], cwd=repo_root)
    except RuntimeError:
        return set()
    return extract_arxiv_from_text(content)


def extract_arxiv_from_text(text):
    """Extraire les IDs arXiv d'un texte (notebook JSON sérialisé ou markdown)."""
    ids = set()
    for m in ARXIV_RE.finditer(text):
        ids.add(m.group(1))
    for m in ARXIV_RE_LEGACY.finditer(text):
        aid = m.group(1)
        if len(aid.rsplit("/", 1)[-1]) == 7:
            ids.add(aid)
    return ids


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".", help="Racine du repo CoursIA")
    ap.add_argument("--prs", required=True,
                    help="Liste de PRs separees par des virgules")
    ap.add_argument("--out", default=None, help="Fichier CSV de sortie")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    prs = [int(p) for p in args.prs.split(",") if p.strip()]
    results = []
    for pr in prs:
        files, merge_sha, src = get_pr_info(pr, repo)
        if not files:
            print(f"[pr {pr}] aucun .ipynb touche")
            results.append({"pr": pr, "files": [], "ids_covered": [], "src": src})
            continue
        if not merge_sha:
            print(f"[pr {pr}] pas de merge commit")
            results.append({"pr": pr, "files": files, "ids_covered": [], "src": src})
            continue
        # Couverture : tous les IDs arXiv actuellement presents dans les
        # fichiers touches par la PR. Une PR qui corrige des attributions
        # couvre tous les IDs du notebook, meme ceux qui n'ont pas change.
        ids_covered = get_ids_in_files_at_sha(files, merge_sha, repo)
        results.append({
            "pr": pr,
            "files": files,
            "ids_covered": sorted(ids_covered),
            "src": src,
            "merge_sha": merge_sha,
        })
        print(f"[pr {pr}] {len(files)} fichiers, {len(ids_covered)} IDs couverts (src={src})")
    # Sortie
    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(results, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"[scan-pr-diff] -> {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
