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
    1. Liste les fichiers C# affectés par la PR (post-merge : `git show
       --first-parent --name-only --format= <merge_sha>` ; pre-merge ou
       fallback : `gh api /files` paginé). La fast-path `git show
       --first-parent` capture TOUS les fichiers de la branche fusionnée,
       ce qui couvre **les trois modes de merge** : squash (1 parent,
       `--first-parent` no-op), merge-commit (2 parents, le combined-diff
       par défaut peut être vide — `--first-parent` suit la branche PR) et
       rebase (1 parent, les fichiers sont déjà dans la branche rebasée).
       La version antérieure utilisait `--first-parent -1` qui ratait les
       fichiers antérieurs au dernier commit de la PR. Si la fast-path
       rend vide malgré tout (corner case), on retombe sur le fallback
       `gh api /files` paginé plutôt que retourner [] (qui mènerait à
       l'exit 2 « aucun fichier C# trouvé » avec perte de signal).
    2. Mappe chaque fichier C# à sa paire dans `twin_pairs.d/*.yaml`.
    3. Skip si la paire est **déjà alignée** : `csharp_sha` YAML == blob SHA
       actuel du fichier (`git hash-object`). Évite une re-touch qui pollue
       le diff git sans valeur ajoutée.
    4. Pour les paires non-alignées, lance :
       python scripts/notebook_tools/check_twin_parity.py \\
           --update --pair "<Name>" --by "myia-po-2026:CoursIA-2"

Sortie :
    - stdout : 1 ligne par paire traitée (ALREADY ALIGNED, DRY-RUN, UPDATED,
      NO-OP, ou FAILED).
    - exit 0 si toutes les paires passent le check de parité, exit 1 sinon.

Audit :
    Le script s'exécute en mode dry-run par défaut. Pour appliquer réellement
    les --update, passer --apply. Cela évite d'écrire en série 25 YAMLs
    sur une mauvaise hypothèse (e.g. PR #13606 pas encore mergée).

Origine : issue #13616, lane myia-po-2026:CoursIA-2, livraison CPU-only.
Voir aussi : .claude/rules/catalog-pr-hygiene.md, scripts/notebook_tools/check_twin_parity.py.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

LANE = "myia-po-2026:CoursIA-2"
PR_NUMBER = 13606
PAIRS_YAML_DIR = Path("scripts/notebook_tools/twin_pairs.d")


def get_csharp_files_from_pr(pr_number: int, repo_root: Path) -> list[str]:
    """Liste les fichiers ``*.Csharp.ipynb`` affectés par PR donnée.

    Stratégie : on dérive toujours le SHA source (merge_commit_sha si mergée,
    sinon head.sha) via gh api, puis on l'utilise comme ancêtre valide pour
    git merge-base. Cela évite la fast-path cassée qui passait le numéro de
    PR brut à git — git attend un objet (SHA/ref), pas un entier.

    Justification : la branche git-log d'origine utilisait
    ``git merge-base --is-ancestor <pr_number> HEAD`` qui échoue toujours
    (rc=128, ``fatal: Not a valid object name <pr_number>``). Le code mort
    retombait sur gh api, qui marche, mais le chemin rapide n'était jamais
    emprunté et le pattern était réutilisable par erreur ailleurs. Refactor :
    passer par gh api systématiquement pour résoudre l'objet SHA.

    Pré-requis : gh CLI authentifié (compte lecture des pulls).
    """
    # Étape 1 : résoudre le SHA source de la PR (merge_commit_sha post-merge,
    # head.sha pré-merge). gh api garantit l'objet SHA.
    pr_meta = subprocess.run(
        ["gh", "api", f"repos/jsboige/CoursIA/pulls/{pr_number}"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if pr_meta.returncode != 0 or not pr_meta.stdout.strip():
        print(f"WARN: gh api pull/{pr_number} indisponible (rc={pr_meta.returncode}), "
              f"fallback direct sur /files",
              file=sys.stderr)
    else:
        try:
            pr_data = json.loads(pr_meta.stdout)
        except json.JSONDecodeError as e:
            print(f"WARN: réponse gh api pull/{pr_number} non-JSON ({e}), fallback direct",
                  file=sys.stderr)
        else:
            source_sha = pr_data.get("merge_commit_sha") or pr_data.get("head", {}).get("sha")
            if source_sha and isinstance(source_sha, str) and len(source_sha) >= 7:
                # Étape 2 : vérifier que ce SHA est ancêtre de HEAD (post-merge)
                merged = subprocess.run(
                    ["git", "merge-base", "--is-ancestor", source_sha, "HEAD"],
                    cwd=repo_root,
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                )
                if merged.returncode == 0:
                    # PR mergée : extraire les fichiers C# touchés par le merge commit.
                    # Stratégie : `git show --first-parent --name-only --format=
                    # <merge_sha>` liste TOUS les fichiers de la branche fusionnée
                    # (first-parent suit la branche mergée, qui contient les
                    # commits PR). Le `--first-parent` est **obligatoire** pour les
                    # merge-commits (parents=2) : sans lui, git show rend un
                    # combined-diff par défaut, qui peut être vide pour un merge
                    # pur (sans résolution conflictuelle) — mesuré en review #13859.
                    # En squash ou rebase, le merge commit a 1 parent, et le
                    # `--first-parent` est un no-op (la branche = le commit).
                    out = subprocess.run(
                        ["git", "show", "--first-parent", "--name-only", "--format=",
                         source_sha, "--", "*.Csharp.ipynb"],
                        cwd=repo_root,
                        capture_output=True,
                        text=True,
                        encoding="utf-8",
                        errors="replace",
                        check=True,
                    )
                    files = sorted(set(line for line in out.stdout.splitlines()
                                       if line.endswith("Csharp.ipynb")))
                    # Robustesse : si la fast-path rend vide (corner case
                    # théorique, e.g. merge commit bizarre), on RETOMBE sur le
                    # fallback gh api /files plutôt que retourner [] et risquer
                    # l'exit 2 « aucun fichier C# trouvé » avec perte de signal.
                    if files:
                        return files
                    print(f"WARN: git show first-parent a rendu vide pour {source_sha}, "
                          f"fallback gh api /files",
                          file=sys.stderr)

    # Fallback : gh api /files (pagination). Aussi chemin nominal quand la PR
    # n'est pas encore mergée (pre-merge).
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


def get_yaml_csharp_sha(yaml_path: Path, csharp_rel: str) -> str | None:
    """Lit le `csharp_sha` (git blob SHA) enregistré pour une paire dans twin_pairs.d/.

    Retourne le SHA ou None si non trouvé / structure inattendue.
    """
    import yaml  # type: ignore
    try:
        with open(yaml_path) as fh:
            data = yaml.safe_load(fh)
    except Exception:
        return None
    if not isinstance(data, list):
        return None
    for entry in data:
        if (isinstance(entry, dict)
                and entry.get("csharp") == csharp_rel
                and isinstance(entry.get("csharp_sha"), str)):
            return entry["csharp_sha"]
    return None


def get_current_blob_sha(csharp_rel: str, repo_root: Path) -> str | None:
    """Calcule le SHA git blob actuel du fichier C# (`git hash-object <path>`).

    Le SHA retourné est ce que `check_twin_parity.py` utilise pour `csharp_sha`.
    Retourne None si le fichier n'existe pas ou git échoue.
    """
    out = subprocess.run(
        ["git", "hash-object", csharp_rel],
        cwd=repo_root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if out.returncode != 0:
        return None
    return out.stdout.strip() or None


def is_already_rebaselined(yaml_path: Path, csharp_rel: str, repo_root: Path) -> bool:
    """Vrai si le `csharp_sha` YAML correspond au blob SHA actuel du fichier.

    Évite la re-touch d'une paire déjà alignée (le `check_twin_parity.py --update`
    ré-écrirait le YAML même quand la valeur est déjà bonne, ce qui pollue le diff).
    """
    yaml_sha = get_yaml_csharp_sha(yaml_path, csharp_rel)
    if yaml_sha is None:
        return False
    current_sha = get_current_blob_sha(csharp_rel, repo_root)
    if current_sha is None:
        return False
    return yaml_sha == current_sha


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
    parser.add_argument("--dry-run", action="store_true", default=False,
                        help="Mode dry-run : aucune écriture (no-op si --apply).")
    parser.add_argument("--apply", action="store_true",
                        help="Exécuter réellement les --update (prime sur --dry-run).")
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
    already_aligned = 0
    for csf, yf, name in pairs:
        print(f"\n--- Paire : {name}")
        print(f"    YAML : {yf.name}")
        print(f"    C# : {csf}")
        # Skip si déjà-rebaseliné : csharp_sha YAML == blob SHA actuel.
        # Évite une re-touch qui pollue le diff git sans valeur ajoutée.
        if is_already_rebaselined(yf, csf, repo_root):
            print(f"    ALREADY ALIGNED : csharp_sha YAML = blob SHA actuel → skip")
            already_aligned += 1
            continue
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
    print(f"    Updated pairs         : {updated}")
    print(f"    Skipped (no-op)       : {noop}")
    print(f"    Already aligned (skip): {already_aligned}")
    print(f"    Failed pairs          : {failed}")

    if failed > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
