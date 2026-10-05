#!/usr/bin/env python3
r"""credited_examples_sweep.py -- pose POST-MORTEM du label `credited-examples-lost`.

## Pourquoi (#19101)

`exercises-advisory.yml` porte une branche « exemples credites » posee par
#18761, mais **dormante** : elle exige `--base` ET `--pr-body-file`. Sous
`schedule` -- le seul declencheur qui subsiste apres la tranche 1 de #12817 --
il n'y a pas de contexte PR, donc pas de body, donc pas de `--base` : le diff
des exemples credites n'etait **jamais** mesure et le label ne pouvait pas etre
pose.

Ce balayage le reveille **sans reintroduire `pull_request`** sur ce workflow
(interdit : le clone par PR etait la motivation de #12817). Il tourne apres
coup : il liste les PRs MERGEES de la fenetre et rejoue, pour chacune, le diff
avec SA base et SON body -- c'est l'option 1 de #19101.

## Deux sources de verite, chacune du bon cote (review 04:53Z)

- **`changeType` n'existe pas dans `gh pr list --json files`** (mesure gh
  2.83.2 : cette forme ne rend que `{additions, deletions, path}`). Le
  classifieur ADDED/DELETED/RENAMED se nourrit donc de **GraphQL**
  (`pullRequest.files.nodes { path changeType }`), pagine au curseur. Un
  carnet supprime (#19040 a supprime GameTheory-18d) fait sinon planter le
  balayage en `FileNotFoundError` : le repli « tout MODIFIED » de la premiere
  version classait tout en modifie.
- **le cote « apres » est la tete de la PR, pas l'arbre de travail** :
  `check_notebooks` recoit `head_ref=headRefOid`, et le commit est amene
  localement s'il manque (PR squash-mergee : l'objet n'est pas dans `main`).
  Un commit de tete inatteignable est **nomme**, jamais remplace par l'etat
  du jour.

## Portee honnete

Post-mortem : il detecte les pertes **passees**, il ne protege pas le merge.
C'est le compromis assume de l'option 1 ; l'option 2 (un declencheur PR leger)
reste ouverte et n'est pas traitee ici.

Quand `headRefOid` n'est plus atteignable (ref supprimee au merge), le
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

# La liste des fichiers d'une PR AVEC leur nature de changement. Cette
# information n'existe pas dans `gh pr list --json files` (review 04:53Z,
# mesure gh 2.83.2) : elle est lue par GraphQL, page par 100.
GRAPHQL_FILES = """query($owner: String!, $name: String!, $num: Int!, $cursor: String) {
  repository(owner: $owner, name: $name) {
    pullRequest(number: $num) {
      files(first: 100, after: $cursor) {
        nodes { path changeType }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}"""


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
    """PRs mergees depuis `since`, avec leurs deux refs -- PAS leurs fichiers.

    La forme `gh pr list --json files` ne rend pas `changeType` : les fichiers
    (et leur nature) sont lus par `pr_files`, par PR, en GraphQL. Leve si le
    lot atteint le plafond de l'API de recherche : un corpus tronque se
    lirait comme un corpus complet.
    """
    stamp = since.strftime("%Y-%m-%dT%H:%M:%SZ")
    rows = run([
        "pr", "list", "--repo", repo, "--state", "merged",
        "--limit", str(SEARCH_RESULT_CAP),
        "--search", f"merged:>={stamp}",
        "--json", "number,baseRefOid,headRefOid,mergedAt",
    ]) or []
    if len(rows) >= SEARCH_RESULT_CAP:
        raise RuntimeError(
            f"la fenetre depuis {stamp} rend {len(rows)} PRs, au plafond de "
            f"l'API de recherche ({SEARCH_RESULT_CAP}) : le corpus serait "
            "tronque par les plus anciennes. Reduire --hours."
        )
    return rows


def pr_files(repo: str, number: int, run=_gh_json) -> list[dict]:
    """Fichiers de la PR avec `changeType`, par GraphQL, pagine au curseur.

    `gh pr view --json files` (REST/CLI) ne rend que des decomptes : la nature
    du changement n'existe que cote GraphQL. Pages de 100, boucle sur
    `pageInfo.endCursor` -- une PR de carnet peut deplacer plus de 100 fichiers
    (mesure : #19040 en deplace 2876+214 lignes sur plusieurs carnets).
    """
    owner, name = repo.split("/", 1)
    nodes: list[dict] = []
    cursor = None
    while True:
        payload = run([
            "api", "graphql", "-f", f"query={GRAPHQL_FILES}",
            "-F", f"owner={owner}", "-F", f"name={name}",
            "-F", f"num={number}",
        ] + (["-f", f"cursor={cursor}"] if cursor else []))
        conn = (payload or {}).get("data", {}).get("repository", {}) \
                               .get("pullRequest", {}).get("files", {})
        nodes.extend(conn.get("nodes") or [])
        page = conn.get("pageInfo") or {}
        if not page.get("hasNextPage"):
            return nodes
        cursor = page.get("endCursor")


def _ipynb_by_change(files: list[dict]) -> tuple[list[str], list[str], list[str]]:
    """`(modifies, ajoutes, renommes)` parmi les `.ipynb` de la PR.

    Deux exclusions et une separation, toutes structurelles, toutes lues de
    `changeType` (GraphQL) :

      - `DELETED` : supprime, plus rien a compter (meme regle que le
        `--diff-filter=d` du workflow). C'est le cas qui FAIT PLANTER le
        balayage quand on le croit modifie : `git show <base>:<chemin>` puis
        l'ouverture du carnet levait `FileNotFoundError` sur GameTheory-18d
        (supprime par #19040) ;
      - `ADDED` : neuf, donc **rien a perdre** par construction ;
      - `RENAMED` : la version de base existe **sous un autre chemin**, que
        cette source n'expose pas (`previousFilename` absent du jeu GraphQL
        demande ici). On ne peut donc pas la comparer -- et contrairement a
        `ADDED`, un renommage **peut** perdre des exemples. NON MESURE.

    Pourquoi separer plutot que compter en erreur : `credited_diff_errors > 0`
    **bloque** la pose du label (#18761). Une erreur structurelle sur un carnet
    empechait donc la mesure reelle des carnets modifies de la meme PR -- un
    faux positif d'erreur produisait un faux zero de pertes.
    """
    modified, added, renamed = [], [], []
    for f in (files or []):
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


def ipynb_paths(files: list[dict]) -> list[str]:
    """Chemins `.ipynb` **modifies** par la PR (cf. `_ipynb_by_change`)."""
    return _ipynb_by_change(files)[0]


def merge_base(repo_dir: Path, base_ref: str, head_ref: str) -> str | None:
    """`git merge-base` des deux refs, ou None si l'une n'est pas atteignable.

    Pour une PR deja mergeee et squash-mergee, `headRefOid` peut avoir disparu
    du depot (ref supprimee). On rend None et l'appelant NOMME le repli --
    jamais un diff silencieusement mesure contre la mauvaise base.
    """
    proc = _run(["git", "-C", str(repo_dir), "merge-base", base_ref, head_ref])
    if proc.returncode != 0:
        return None
    return proc.stdout.strip() or None


def ensure_commit(repo_dir: Path, sha: str, run=_run) -> bool:
    """Ameine localement le commit de tete s'il manque, puis confirme.

    Une PR squash-mergee n'est pas un ancetre de `main` : son `headRefOid`
    n'est pas dans un clone frais. GitHub autorise le fetch d'un SHA atteignable
    depuis une ref de PR (`git fetch origin <sha>`). Rend False si le commit
    reste inatteignable -- l'appelant NOMME l'echec, il ne mesure pas contre
    un autre arbre.
    """
    probe = ["git", "-C", str(repo_dir), "cat-file", "-e", f"{sha}^{{commit}}"]
    if run(probe).returncode == 0:
        return True
    run(["git", "-C", str(repo_dir), "fetch", "--quiet", "origin", sha])
    return run(probe).returncode == 0


def pr_body(repo: str, number: int, run=_gh_json) -> str:
    payload = run(["pr", "view", str(number), "--repo", repo, "--json", "body"])
    return ((payload or {}).get("body") or "") if isinstance(payload, dict) else ""


def sweep(repo: str, repo_dir: Path, hours: int, now: dt.datetime,
          *, fetch_merged=merged_prs, fetch_files=pr_files,
          fetch_body=pr_body, base_of=merge_base, ensure=ensure_commit,
          check=check_notebooks) -> tuple[list[dict], list[str]]:
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
        try:
            files = fetch_files(repo, number)
        except RuntimeError as exc:
            errors.append(f"#{number}: fichiers illisibles ({exc})")
            continue
        paths, added, renamed = _ipynb_by_change(files)
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
        if not base_ref or not head_ref:
            errors.append(f"#{number}: refs absentes (base={base_ref!r}, head={head_ref!r})")
            continue
        if not ensure(repo_dir, head_ref):
            errors.append(
                f"#{number}: commit de tete {head_ref[:8]} inatteignable -- "
                "PR ecartee, pas mesuree contre l'arbre du jour"
            )
            continue
        base = base_of(repo_dir, base_ref, head_ref)
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
        result = check([Path(p) for p in paths], base_ref=base,
                       head_ref=head_ref, pr_body=body)
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
