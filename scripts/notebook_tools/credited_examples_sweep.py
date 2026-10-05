#!/usr/bin/env python3
r"""credited_examples_sweep.py -- pose POST-MORTEM du label `credited-examples-lost`.

## Pourquoi (#19101)

`exercises-advisory.yml` porte une branche « exemples credites » posee par
#18761, mais **dormante** : elle exige `--base` ET `--pr-body-file`. Sous
`schedule` -- le seul declencheur qui subsiste apres la tranche 1 de #12817 --
il n'y a pas de contexte PR, donc pas de body, donc pas de `--base` : le diff
des exemples credites n'etait **jamais** mesure et le label ne pouvait pas
etre pose.

Ce balayage le reveille **sans reintroduire `pull_request`** sur ce workflow
(interdit : le clone par PR etait la motivation de #12817). Il tourne apres
coup : il liste les PRs MERGEES de la fenetre et rejoue, pour chacune, le diff
avec SA base et SON body -- c'est l'option 1 de #19101.

## Portee honnete

Post-mortem : il detecte les pertes **passees**, il ne protege pas le merge.
C'est le compromis assume de l'option 1 ; l'option 2 (un declencheur PR leger)
reste ouverte et n'est pas traitee ici.

Deux limites de la mesure, nommees plutot que tues :

  - la version HEAD est lue dans l'**arbre de travail** (defaut de
    `check_notebooks`), donc une PR dont un carnet a ete re-touche par une PR
    ulterieure est mesuree contre l'etat courant, pas contre son propre head.
    Le chiffre reste une borne basse exploitable ; il n'est pas presente comme
    « exactement l'apport de cette PR ».
  - quand `headRefOid` n'est plus atteignable (ref supprimee au merge), le
    merge-base est indisponible : la PR est alors mesuree **contre sa base
    declaree** et le repli est imprime en `[WARN]`, jamais silencieux.

## Usage

    python scripts/notebook_tools/credited_examples_sweep.py --hours 24
    python scripts/notebook_tools/credited_examples_sweep.py --hours 24 --apply

Sans `--apply`, rien n'est pose : le rapport dit ce qui **serait** labellise.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import subprocess
import sys
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from check_pr_exercises import LABEL_NAME, check_notebooks  # noqa: E402

REPO_DEFAULT = "jsboige/CoursIA"
LABEL_CREDITED_LOST = "credited-examples-lost"

# Le plafond de l'API de recherche. Un lot qui l'atteint n'est pas un compte :
# c'est le plafond, et il cache les plus anciens (#19209, meme classe). Une
# fenetre qui sature est une erreur, jamais un corpus tronque qui a l'air
# complet.
SEARCH_RESULT_CAP = 1000


def _run(argv: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(
        argv, capture_output=True, text=True, encoding="utf-8",
        errors="replace", check=False, **kw,
    )


def _gh_json(argv: list[str]) -> object:
    proc = _run(["gh", *argv])
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh failed ({proc.returncode}): "
            f"{proc.stderr.strip() or proc.stdout.strip()}"
        )
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def merged_prs(repo: str, since: dt.datetime, run=_gh_json) -> list[dict]:
    """PRs mergees depuis `since`, avec leurs fichiers et leurs deux refs.

    Leve si le lot atteint le plafond de l'API de recherche : un corpus
    tronque se lirait comme un corpus complet, et les PRs perdues sont les
    plus anciennes de la fenetre.
    """
    stamp = since.strftime("%Y-%m-%dT%H:%M:%SZ")
    rows = run([
        "pr", "list", "--repo", repo, "--state", "merged",
        "--limit", str(SEARCH_RESULT_CAP),
        "--search", f"merged:>={stamp}",
        "--json", "number,baseRefOid,headRefOid,files,mergedAt",
    ]) or []
    if len(rows) >= SEARCH_RESULT_CAP:
        raise RuntimeError(
            f"la fenetre depuis {stamp} rend {len(rows)} PRs, au plafond de "
            f"l'API de recherche ({SEARCH_RESULT_CAP}) : le corpus serait "
            "tronque par les plus anciennes. Reduire --hours."
        )
    return rows


def _ipynb_by_change(pr: dict) -> tuple[list[str], list[str], list[str]]:
    """`(modifies, ajoutes, renommes)` parmi les `.ipynb` de la PR.

    Deux exclusions et une separation, toutes structurelles. Toutes viennent
    d'un `git show <base>:<chemin>` qui sort en **128** parce que le carnet
    n'est pas a ce chemin dans la base -- ce qui n'est PAS une erreur de
    mesure, mais ne veut pas dire la meme chose selon le cas :

      - `DELETED` : supprime, plus rien a compter (meme regle que le
        `--diff-filter=d` du workflow) ;
      - `ADDED` : neuf, donc **rien a perdre** par construction. Mesure du
        2026-10-05 : 6 des 6 « erreurs de diff » du corpus de 24 h venaient de
        la (#18968, #19037, #19020, #19007, #18986) ;
      - `RENAMED` : la version de base existe **sous un autre chemin**, que
        `gh pr view --json files` n'expose pas ici (`previousFilename` absent).
        On ne peut donc pas la comparer -- et contrairement a `ADDED`, un
        renommage **peut** perdre des exemples. On le declare NON MESURE.

    Pourquoi separer plutot que compter en erreur : `credited_diff_errors > 0`
    **bloque** la pose du label (#18761). Une erreur structurelle sur un carnet
    empechait donc la mesure reelle des carnets modifies de la meme PR -- un
    faux positif d'erreur produisait un faux zero de pertes.
    """
    modified, added, renamed = [], [], []
    for f in (pr.get("files") or []):
        path = f.get("path") or ""
        if not path.endswith(".ipynb"):
            continue
        change = f.get("changeType") or "MODIFIED"
        if change == "DELETED":
            continue
        if change == "ADDED":
            added.append(path)
        elif change == "RENAMED":
            renamed.append(path)
        else:
            modified.append(path)
    return modified, added, renamed


def ipynb_paths(pr: dict) -> list[str]:
    """Chemins `.ipynb` **modifies** par la PR (cf. `_ipynb_by_change`)."""
    return _ipynb_by_change(pr)[0]


def merge_base(repo_dir: Path, base_ref: str, head_ref: str) -> str | None:
    """`git merge-base` des deux refs, ou None si l'une n'est pas atteignable.

    Pour une PR deja mergee et squash-mergee, `headRefOid` peut avoir disparu
    du depot (ref supprimee). On rend None et l'appelant NOMME le repli --
    jamais un diff silencieusement mesure contre la mauvaise base.
    """
    proc = _run(["git", "-C", str(repo_dir), "merge-base", base_ref, head_ref])
    if proc.returncode != 0:
        return None
    return proc.stdout.strip() or None


def pr_body(repo: str, number: int, run=_gh_json) -> str:
    payload = run(["pr", "view", str(number), "--repo", repo, "--json", "body"])
    return ((payload or {}).get("body") or "") if isinstance(payload, dict) else ""


def sweep(repo: str, repo_dir: Path, hours: int, now: dt.datetime,
          *, fetch_merged=merged_prs, fetch_body=pr_body,
          base_of=merge_base, check=check_notebooks) -> tuple[list[dict], list[str]]:
    """Rejoue le diff des exemples credites pour chaque PR mergee de la fenetre.

    Rend `(lignes, erreurs)`. Une ligne porte, par PR : le nombre de pertes non
    exemptees et si le label serait pose. Un diff en erreur n'est JAMAIS
    presente comme un zero mesure (#18761) : il est compte a part.
    """
    since = now - dt.timedelta(hours=hours)
    rows: list[dict] = []
    errors: list[str] = []
    for pr in fetch_merged(repo, since):
        number = pr.get("number")
        paths, added, renamed = _ipynb_by_change(pr)
        if not paths and not added and not renamed:
            continue
        if not paths:
            # PR sans carnet mesurable : rien a perdre (ajouts) ou rien de
            # comparable (renommages). On la NOMME plutot que de la faire
            # disparaitre du rapport.
            rows.append({
                "number": number,
                "notebooks": 0,
                "added_notebooks": len(added),
                "renamed_notebooks": len(renamed),
                "credited_lost_unexempted": 0,
                "credited_diff_errors": 0,
                "would_label": False,
                "paths": [],
            })
            continue
        base_ref = pr.get("baseRefOid") or ""
        head_ref = pr.get("headRefOid") or ""
        base = base_of(repo_dir, base_ref, head_ref) if base_ref and head_ref else None
        if base is None:
            # Repli nomme : on mesure contre la ref de base declaree, sans
            # merge-base. Le chiffre reste exploitable, sa provenance est dite.
            errors.append(
                f"#{number}: merge-base indisponible pour "
                f"{base_ref[:8]}...{head_ref[:8]} -- diff mesure contre la base declaree"
            )
            base = base_ref
        try:
            body = fetch_body(repo, number)
        except RuntimeError as exc:
            errors.append(f"#{number}: body illisible ({exc})")
            continue
        result = check([Path(p) for p in paths], base_ref=base, pr_body=body)
        summary = result.as_payload().get("summary", {})
        lost = int(summary.get("credited_lost_unexempted", 0) or 0)
        diff_errors = int(summary.get("credited_diff_errors", 0) or 0)
        rows.append({
            "number": number,
            "notebooks": len(paths),
            "added_notebooks": len(added),
            "renamed_notebooks": len(renamed),
            "credited_lost_unexempted": lost,
            "credited_diff_errors": diff_errors,
            # #18761 : le label ne se pose QUE si tous les diffs ont reussi.
            "would_label": lost > 0 and diff_errors == 0,
            "paths": paths,
        })
    return rows, errors


def apply_label(repo: str, number: int, run=_run) -> bool:
    """Pose le label sur la PR (idempotent cote GitHub). Rend True si pose."""
    proc = run([
        "gh", "pr", "edit", str(number), "--repo", repo,
        "--add-label", LABEL_CREDITED_LOST,
    ])
    return proc.returncode == 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=REPO_DEFAULT)
    ap.add_argument("--repo-dir", default=".")
    ap.add_argument("--hours", type=int, default=24)
    ap.add_argument("--apply", action="store_true",
                    help="poser reellement le label (defaut: rapport seul)")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)

    now = dt.datetime.now(dt.timezone.utc)
    try:
        rows, errors = sweep(args.repo, Path(args.repo_dir), args.hours, now)
    except RuntimeError as exc:
        print(f"credited_examples_sweep: {exc}", file=sys.stderr)
        return 2

    labelled: list[int] = []
    if args.apply:
        for row in rows:
            if row["would_label"] and apply_label(args.repo, row["number"]):
                labelled.append(row["number"])

    if args.json:
        json.dump({"prs": rows, "errors": errors, "labelled": labelled},
                  sys.stdout, ensure_ascii=False)
        print()
        return 0

    print(f"Fenetre : {args.hours} h -- {len(rows)} PR(s) mergee(s) touchant un .ipynb")
    for row in rows:
        mark = "LABEL" if row["would_label"] else "  -  "
        added = row.get("added_notebooks", 0)
        renamed = row.get("renamed_notebooks", 0)
        suffix = ""
        if added:
            suffix += f" (+{added} neuf(s), rien a perdre)"
        if renamed:
            suffix += f" ({renamed} renomme(s), NON MESURE(S) : base a un autre chemin)"
        print(f"  [{mark}] #{row['number']}: {row['notebooks']} carnet(s) modifie(s), "
              f"pertes non exemptees={row['credited_lost_unexempted']}, "
              f"erreurs de diff={row['credited_diff_errors']}{suffix}")
    for err in errors:
        print(f"  [WARN] {err}", file=sys.stderr)
    total_lost = sum(r["credited_lost_unexempted"] for r in rows if r["would_label"])
    total_err = sum(r["credited_diff_errors"] for r in rows)
    print(f"RESULT: {len(labelled) if args.apply else sum(1 for r in rows if r['would_label'])} "
          f"PR(s) a labelliser, {total_lost} perte(s) non exemptee(s), "
          f"{total_err} erreur(s) de diff, {len(errors)} repli(s) nomme(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
