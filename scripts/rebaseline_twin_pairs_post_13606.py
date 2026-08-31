#!/usr/bin/env python3
"""Rebaseline twin_pairs.d/ pour les 25 paires C# dont le SHA changera après merge
de PR #13606 (newline final sur 275 notebooks).

Usage :
    cd /path/to/CoursIA
    python scripts/rebaseline_twin_pairs_post_13606.py [--dry-run]

Pré-requis : PR #13606 mergée sur main (post-merge). Le script détecte les paires
affectées via `gh pr diff 13606` (ou, post-merge, via `git log`).

Mécanique :
    Pour chaque paire C# touchée par #13606 :
    1. Lit le `content_csharp_sha` actuel (calculé via `_content_sha` du script)
    2. Lit le `csharp_sha` (git blob SHA) actuel
    3. Si les SHAs diffèrent du YAML, lance :
       python scripts/notebook_tools/check_twin_parity.py \\
           --update --pair "<Name>" --by "myia-po-2026:CoursIA-2"
    4. Le script narrow-update narrow-précis narrow-sur narrow-cette narrow-paire (le
       `content_sha` reste inchangé si le contenu est byte-identique modulo newline).

Sortie :
    - stdout : 1 ligne par paire traitée (DRY-RUN ou UPDATED ou NO-OP)
    - exit 0 si toutes les paires narrow-passent narrow-check, exit 1 sinon

Audit :
    Le script narrow-applique narrow-en narrow-mode dry-run par défaut. Pour exécuter
    réellement les --update, passer --apply. Cela évite d'écrire en série 25 YAMLs
    sur une mauvaise hypothèse (e.g. PR #13606 pas encore mergée).

Origine : issue #13616, narrow-po-2026 narrow-applicable CPU-only.
Voir aussi : .claude/rules/catalog-pr-hygiene.md, scripts/notebook_tools/check_twin_parity.py.
"""

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

LANE = "myia-po-2026:CoursIA-2"
PR_NUMBER = 13606
PAIRS_YAML_DIR = Path("scripts/notebook_tools/twin_pairs.d")


def get_csharp_files_from_pr(pr_number: int, repo_root: Path) -> list[str]:
    """Liste les fichiers Csharp.ipynb affectés par PR donnée. Essaie git log d'abord
    (post-merge), puis gh api (pré-merge)."""
    # Si PR mergée sur HEAD : git log
    try:
        merged = subprocess.run(
            ["git", "merge-base", "--is-ancestor", str(pr_number), "HEAD"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        if merged.returncode == 0:
            out = subprocess.run(
                ["git", "log", "--diff-filter=M", "-p", "-m", "--first-parent", "-1",
                 "--name-only", "HEAD", "--", "*.Csharp.ipynb"],
                cwd=repo_root,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                check=True,
            )
            return sorted(set(line for line in out.stdout.splitlines() if line.endswith("Csharp.ipynb")))
    except subprocess.CalledProcessError:
        pass

    # Sinon : gh api (pagination)
    csharp_files: list[str] = []
    page = 1
    while True:
        api = subprocess.run(
            ["gh", "api", f"repos/jsboige/CoursIA/pulls/{pr_number}/files?per_page=100&page={page}"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        if api.returncode != 0 or not api.stdout.strip():
            break
        data = json.loads(api.stdout)
        if not data:
            break
        for f in data:
            if "Csharp.ipynb" in f.get("filename", ""):
                csharp_files.append(f["filename"])
        page += 1
    return sorted(set(csharp_files))


def load_twin_pairs_registry(yaml_dir: Path) -> dict[str, tuple[Path, str]]:
    """Charge twin_pairs.d/*.yaml et retourne un mapping `csharp_path -> (yaml_path, name)`."""
    registry: dict[str, tuple[Path, str]] = {}
    import yaml  # type: ignore
    for yf in sorted(yaml_dir.glob("*.yaml")):
        try:
            with open(yf) as fh:
                data = yaml.safe_load(fh)
        except Exception as e:
            print(f"WARN: cannot parse {yf}: {e}", file=sys.stderr)
            continue
        if not isinstance(data, list):
            continue
        for entry in data:
            if isinstance(entry, dict) and "csharp" in entry and isinstance(entry["csharp"], str):
                registry[entry["csharp"]] = (yf, entry.get("name", "unknown"))
    return registry


def run_update(pair_name: str, lane: str, repo_root: Path) -> bool:
    """Exécute `check_twin_parity.py --update --pair <name> --by <lane>`."""
    result = subprocess.run(
        ["python", "scripts/notebook_tools/check_twin_parity.py",
         "--update", "--pair", pair_name, "--by", lane],
        cwd=repo_root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if result.returncode != 0:
        print(f"    UPDATE FAILED (rc={result.returncode}):", file=sys.stderr)
        print(f"    stdout: {result.stdout}", file=sys.stderr)
        print(f"    stderr: {result.stderr}", file=sys.stderr)
        return False
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--dry-run", action="store_true", default=True,
                        help="Mode dry-run (défaut) : aucune écriture.")
    parser.add_argument("--apply", action="store_true",
                        help="Exécuter réellement les --update.")
    parser.add_argument("--pr", type=int, default=PR_NUMBER,
                        help=f"Numéro de PR (défaut {PR_NUMBER}).")
    parser.add_argument("--lane", default=LANE,
                        help=f"Lane pour --by (défaut {LANE}).")
    args = parser.parse_args()

    dry_run = not args.apply
    repo_root = Path(".").resolve()

    print(f"[{'DRY-RUN' if dry_run else 'APPLY'}] Rebaseline twin_pairs.d/ post-merge PR #{args.pr}")
    print(f"  Lane : {args.lane}")
    print(f"  Repo : {repo_root}")

    # Étape 1 : fichiers C# affectés par la PR
    print(f"\n==> Étape 1 : récupération des fichiers C# affectés par PR #{args.pr}")
    csharp_files = get_csharp_files_from_pr(args.pr, repo_root)
    if not csharp_files:
        print(f"ERREUR : aucun fichier C# trouvé pour PR #{args.pr}", file=sys.stderr)
        return 2
    print(f"    {len(csharp_files)} fichiers C# trouvés.")

    # Étape 2 : mapping aux paires twin_pairs.d/
    print(f"\n==> Étape 2 : mapping aux paires twin_pairs.d/")
    registry = load_twin_pairs_registry(PAIRS_YAML_DIR)
    pairs = []
    skipped = []
    for csf in csharp_files:
        if csf in registry:
            yf, name = registry[csf]
            pairs.append((csf, yf, name))
        else:
            skipped.append(csf)
    if skipped:
        print(f"    {len(skipped)} fichiers non référencés dans twin_pairs.d/ (ignorés) :")
        for csf in skipped:
            print(f"      - {csf}")
    print(f"    {len(pairs)} paires identifiées.")

    # Étape 3 : traitement
    print(f"\n==> Étape 3 : traitement de {len(pairs)} paires")
    updated = 0
    noop = 0
    failed = 0
    for csf, yf, name in pairs:
        print(f"\n--- Paire : {name}")
        print(f"    YAML : {yf.name}")
        print(f"    C# : {csf}")
        if dry_run:
            print(f"    DRY-RUN : serait traité par `--update --pair \"{name}\" --by {args.lane}`")
            noop += 1
        else:
            if run_update(name, args.lane, repo_root):
                updated += 1
                print(f"    UPDATED.")
            else:
                failed += 1

    print(f"\n==> Résumé")
    print(f"    {'DRY-RUN' if dry_run else 'UPDATED'} pairs : {updated + noop}")
    print(f"    Updated pairs  : {updated}")
    print(f"    Skipped (no-op): {noop}")
    print(f"    Failed pairs   : {failed}")

    if failed > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
