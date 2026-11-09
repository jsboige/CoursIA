#!/usr/bin/env python3
"""Generateur de carte de revue editoriale (acceptance 2 de #11259).

Agrege les faits mesurables d'une PR de revue en une carte au format canonique
docs/notebook-metadata/EDITORIAL_REVIEW_CARD.md et emet l'entree YAML
correspondante du registre docs/notebook-metadata/editorial-review-registry.md.

Le validateur scripts/audit/check_editorial_review.py verifie la coherence du
registre ; il ne PRODUIT rien. Ce generateur comble ce manque : il prend les
faits verifiables (etat de la PR, cellules touchees, commit de merge) et les
rend dans la forme attendue, sans inventer de constat.

Principes (calques sur check_editorial_review.py) :
  - aucun constat fabrique : les champs non mesurables restent des marqueurs
    explicites a remplir par le reviewer ;
  - refus (exit 1) si la PR n'est pas MERGED, si elle ne touche pas le
    notebook, ou si reviewer == owner_logique (regle de curation §3.1 #4) ;
  - les runners gh/git sont injectables -> les tests tournent hors reseau.

Run:
    python scripts/audit/build_editorial_review_card.py \\
        --notebook MyIA.AI.Notebooks/Sudoku/Sudoku-12-Z3-CSharp.ipynb \\
        --pr 7801 --reviewer jsboigeEpita --scope factual --owner po-2023 \\
        --date 2026-07-22 --card-out card.md --yaml-out entry.yaml

See also:
    docs/notebook-metadata/EDITORIAL_REVIEW_CARD.md (format canonique)
    docs/notebook-metadata/editorial-review-registry.md (schema YAML)
    scripts/audit/check_editorial_review.py (validateur croise)
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

REVIEW_SCOPES = ("typo", "pedagogie", "factual", "substance", "full")
PROMOTING_SCOPES = ("factual", "substance", "full")


def run_gh(args: list[str], repo: str) -> str:
    """Execute une sous-commande gh et rend sa sortie, ou leve RuntimeError."""
    out = subprocess.run(
        ["gh", *args, "--repo", repo], capture_output=True, text=True, timeout=60
    )
    if out.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} -> {out.stderr.strip()}")
    return out.stdout


def run_git(args: list[str]) -> str:
    """Execute une sous-commande git et rend sa sortie, ou leve RuntimeError."""
    out = subprocess.run(["git", *args], capture_output=True, text=True, timeout=60)
    if out.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} -> {out.stderr.strip()}")
    return out.stdout


def pr_facts(pr: int, repo: str, gh=run_gh) -> dict:
    """Faits mesures d'une PR de revue (etat, merge, fichiers, auteur)."""
    raw = gh(
        [
            "pr", "view", str(pr), "--json",
            "number,title,state,mergedAt,author,files,mergeCommit",
        ],
        repo,
    )
    return json.loads(raw)


def merge_commit(pr: int, git=run_git) -> str | None:
    """SHA court du commit de merge portant #NNNN (cf carte §Preuves).

    Rend None si aucun commit ne porte la reference : la carte porte alors un
    marqueur a remplir, jamais un SHA invente.
    """
    out = git(["log", "--all", "--format=%h", "-n", "1", f"--grep=#{pr}"])
    sha = out.strip().splitlines()[0] if out.strip() else None
    return sha[:7] if sha else None


def touched_cells(files: list[dict], notebook: str) -> dict:
    """Le notebook est-il touche par la PR, et avec combien de lignes modifiees."""
    for f in files:
        if f.get("path") == notebook:
            return {
                "touched": True,
                "additions": f.get("additions", 0),
                "deletions": f.get("deletions", 0),
            }
    return {"touched": False, "additions": 0, "deletions": 0}


def refused_reason(facts: dict, notebook: str, reviewer: str, owner: str) -> str | None:
    """Motif de refus, ou None si la carte peut etre produite (§3.1).

    Trois refus durs : PR non mergée, PR ne touchant pas le notebook,
    auto-review (reviewer == owner_logique).
    """
    if facts.get("state") != "MERGED":
        return f"PR_NOT_MERGED: state={facts.get('state')}"
    if not touched_cells(facts.get("files", []), notebook)["touched"]:
        return f"PR_DOES_NOT_TOUCH_NOTEBOOK: {notebook}"
    if reviewer and owner and reviewer == owner:
        return f"AUTO_REVIEW: reviewer={reviewer} == owner_logique={owner}"
    return None


def render_card(
    notebook: str,
    title: str,
    owner: str,
    reviewer: str,
    scope: str,
    pr: int,
    sha: str | None,
    additions: int,
    deletions: int,
    notes: str,
    last_exec: str = "<YYYY-MM-DD>",
) -> str:
    """Carte au format EDITORIAL_REVIEW_CARD.md.

    Les constats et la verification croisee restent des marqueurs a remplir :
    le generateur ne fabrique pas un constat qu'il n'a pas mesure.
    """
    if scope not in REVIEW_SCOPES:
        raise ValueError(f"scope invalide: {scope!r}")
    boxes = "\n".join(
        f"- [{'x' if s == scope else ' '}] **{s}**" for s in REVIEW_SCOPES
    )
    promote = "x" if scope in PROMOTING_SCOPES else " "
    sha_display = sha or "<introuvable — verifier git log --grep>"
    return f"""## Identification du notebook

- **Chemin relatif** : `{notebook}`
- **Titre** : `{title}`
- **Owner logique** : `{owner}`
- **Derniere execution verifiee** : `{last_exec}`

## Portee de la revue

{boxes}

## Constats

1. `<A REMPLIR par le reviewer — constat factuel verifiable>`
2. `<A REMPLIR>`

## Verdict

- [{promote}] **PROMOTE** — la revue justifie `editorial_reviewed_by = "{reviewer}"` et promeut `BETA -> FINAL`
- [ ] **DO_NOT_PROMOTE**
- [ ] **DEFER**

## Preuves (G.1 obligatoires)

- **PR de revue** : `#{pr}`
- **Commit de merge** : `{sha_display}`
- **Diff excerpt** : `+{additions}/-{deletions}` sur le notebook (extrait a coller)
- **Verification croisee** : `<A REMPLIR — comment la correction a ete verifiee>`

## Signature du reviewer

- **Reviewer** : `{reviewer}`
- **Date de revue** : `<YYYY-MM-DD>`
- **Notes** : `{notes[:200]}`
"""


def render_yaml_entry(
    notebook: str, reviewer: str, scope: str, pr: int, date: str, notes: str
) -> str:
    """Entree du registre au schema de editorial-review-registry.md §2."""
    if scope not in REVIEW_SCOPES:
        raise ValueError(f"scope invalide: {scope!r}")
    return (
        f"- notebook_path: {notebook}\n"
        f"  reviewer: {reviewer}\n"
        f"  review_date: {date}\n"
        f'  evidence_pr: "#{pr}"\n'
        f"  review_scope: {scope}\n"
        f'  notes: "{notes[:200]}"\n'
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generateur de carte de revue editoriale (acceptance 2 de #11259)"
    )
    parser.add_argument("--notebook", required=True, help="chemin relatif du notebook")
    parser.add_argument("--pr", required=True, type=int, help="numero de PR de revue")
    parser.add_argument("--reviewer", required=True, help="login GitHub du reviewer")
    parser.add_argument(
        "--scope", required=True, choices=REVIEW_SCOPES, help="profondeur de la revue"
    )
    parser.add_argument("--owner", default="", help="owner_logique du notebook")
    parser.add_argument("--date", required=True, help="date de revue ISO 8601")
    parser.add_argument("--notes", default="", help="note libre (max 200 chars)")
    parser.add_argument("--repo", default="jsboige/CoursIA", help="depot GitHub")
    parser.add_argument("--card-out", help="fichier de sortie de la carte")
    parser.add_argument("--yaml-out", help="fichier de sortie de l'entree YAML")
    args = parser.parse_args(argv)

    facts = pr_facts(args.pr, args.repo)
    reason = refused_reason(facts, args.notebook, args.reviewer, args.owner)
    if reason:
        print(f"REFUS: {reason}", file=sys.stderr)
        return 1

    touched = touched_cells(facts["files"], args.notebook)
    sha = merge_commit(args.pr)
    card = render_card(
        args.notebook, facts.get("title", ""), args.owner, args.reviewer,
        args.scope, args.pr, sha, touched["additions"], touched["deletions"],
        args.notes,
    )
    entry = render_yaml_entry(
        args.notebook, args.reviewer, args.scope, args.pr, args.date, args.notes
    )

    if args.card_out:
        Path(args.card_out).write_text(card, encoding="utf-8")
    else:
        print(card)
    if args.yaml_out:
        Path(args.yaml_out).write_text(entry, encoding="utf-8")
    else:
        print("--- entree registre ---")
        print(entry)
    return 0


if __name__ == "__main__":
    sys.exit(main())
