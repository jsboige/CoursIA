"""Construit le manifeste de preservation des branches distantes (issue #14238).

Lecture seule par defaut : l'organe NE SUPPRIME JAMAIS une branche. Il produit
la preuve qui conditionne toute suppression ulterieure (protocole de
`docs/reference/branch-cleanup-manifest.README.md`).

Les classes, par ordre de contraigance decroissante :

| Classe | Signification | Sortie |
|---|---|---|
| A | une PR OUVERTE sur la branche | garder |
| B | une PR MERGEE sur la branche (contenu livre sur main) | candidat |
| C | uniquement des PRs FERMEES sans merge | candidat, lecture L576 requise |
| D | aucune PR, mais la tete est un ancetre de `main` | candidat |
| E | aucune PR, tete absente de `main` | candidat, lecture L576 requise |

Une branche peut porter PLUSIEURS PRs (nom reutilise dans le temps). La classe
est celle de l'etat le plus contraignant : OPEN > MERGED > CLOSED. Une branche
qui a eu une PR fermee puis une PR mergee reste B : son contenu EST sur main.

Usage :
    python scripts/ci/build_branch_cleanup_manifest.py --out <fichier.tsv>
    python scripts/ci/build_branch_cleanup_manifest.py --out <fichier.tsv.gz> --gzip
"""
from __future__ import annotations

import argparse
import gzip
import json
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

# OPEN bat MERGED bat CLOSED : la classe retenue est la plus contraignante.
RANG = {"OPEN": 0, "MERGED": 1, "CLOSED": 2}
CLASSE = {"OPEN": "A", "MERGED": "B", "CLOSED": "C"}
COLONNES = ("branch", "sha", "class", "pr_number", "pr_state", "note")


def sh(args, cwd=None, check=True):
    p = subprocess.run(args, cwd=cwd, capture_output=True, text=True, encoding="utf-8")
    if check and p.returncode != 0:
        sys.exit(f"ECHEC {args[0]} (rc={p.returncode}) : {(p.stderr or '')[-400:]}")
    return p.stdout or ""


def branches_distantes(repo: Path) -> dict[str, str]:
    distant = {}
    for ligne in sh(["git", "ls-remote", "--heads", "origin"], cwd=str(repo)).splitlines():
        sha, ref = ligne.split("\t")
        distant[ref[len("refs/heads/"):]] = sha
    return distant


def etats_par_branche(repo: Path) -> dict[str, list[dict]]:
    """Toutes les PRs du depot, indexees sur `headRefName`.

    `gh pr list --state all` rapporte l'etat `MERGED` pour une PR mergee et
    `CLOSED` pour une PR fermee sans merge : la distinction est portee par la
    source, pas deduite. Sans elle, une PR mergee passerait pour une PR
    fermee sans merge et le manifeste classerait B comme C.

    On conserve aussi le `headRefOid` (la tete de la branche AU MOMENT de la
    PR) : c'est lui qui rattache une PR a l'etat courant de la branche. Un
    nom de branche est reutilisable, et une PR fermee sans merge ne dit rien
    de la tete qui a pu naitre apres elle.

    `mergeCommit.oid` et `baseRefName` sont conserves pour la preuve de
    contenu : une PR peut etre mergee dans une base PILOTE (une branche de
    travail), auquel cas son contenu n'est pas sur `main` -- et la classe B
    ne doit pas couvrir ce cas.
    """
    brut = sh([
        "gh", "pr", "list", "--repo", "jsboige/CoursIA", "--state", "all",
        "--limit", "30000", "--json",
        "headRefName,number,state,headRefOid,baseRefName,mergeCommit",
    ], cwd=str(repo))
    documents = json.loads(brut)
    par_branche = defaultdict(list)
    for pr in documents:
        oid = ((pr.get("mergeCommit") or {}).get("oid") or "").lower()
        par_branche[pr["headRefName"]].append({
            "state": pr["state"],
            "number": pr["number"],
            "oid": (pr.get("headRefOid") or "").lower(),
            "base": pr.get("baseRefName") or "",
            "merge_oid": oid,
        })
    return par_branche


def commits_de_main(repo: Path, main: str) -> set[str]:
    """L'ensemble des commits de la branche principale.

    Un commit de fusion y figure <=> le contenu de la PR est sur `main`.
    Un test d'appartenance suffit : mesurer `merge-base --is-ancestor`
    branche par branche serait 2 930 appels de processus.
    """
    sortie = sh(["git", "rev-list", main], cwd=str(repo))
    return set(sortie.split())


def tete_sur_main(repo: Path, sha: str, main: str) -> bool | None:
    """La tete de branche est-elle un ancetre de `main` ?

    Trois issues, trois reponses : True (contenu integre), False (absent de
    `main`), None (objet absent du clone local -> INCONNU). Un inconnu ne
    vaut jamais False : il doit etre signale, pas presume effacable.
    """
    p = subprocess.run(["git", "merge-base", "--is-ancestor", sha, main],
                       cwd=str(repo), capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    if p.returncode == 0:
        return True
    if p.returncode == 1:
        return False
    return None


def main() -> int:
    parseur = argparse.ArgumentParser(description=__doc__)
    parseur.add_argument("--repo", default=str(Path(__file__).resolve().parents[2]))
    parseur.add_argument("--out", required=True, help="fichier TSV a ecrire")
    parseur.add_argument("--gzip", action="store_true", help="compresser la sortie")
    parseur.add_argument("--main", default="origin/main")
    args = parseur.parse_args()

    repo = Path(args.repo)
    distant = branches_distantes(repo)
    par_branche = etats_par_branche(repo)
    commits_main = commits_de_main(repo, args.main)

    classes: dict[str, tuple] = {}
    inconnus: list[str] = []
    for nom, sha in distant.items():
        prs = par_branche.get(nom) or []
        # La PR qui decrit la TETE COURANTE est celle dont le headRefOid vaut
        # la tete distante. Les autres PRs du meme nom decrivent un etat
        # passe : elles ne disent rien de ce qui serait supprime.
        tete = sha.lower()
        candidates = [p for p in prs if p["oid"] == tete]
        if not candidates:
            # Aucune PR ne porte la tete actuelle : soit la branche a avance
            # depuis sa derniere PR, soit aucune PR ne l'a recouverte.
            # Une PR OUVERTE reste bloquante (travail en cours) meme si la
            # tete a bouge depuis.
            ouvertes = [p for p in prs if p["state"] == "OPEN"]
            if ouvertes:
                candidates = [min(ouvertes, key=lambda p: p["number"])]
        if candidates:
            retenue = min(candidates, key=lambda p: (RANG[p["state"]], p["number"]))
            classes[nom] = (CLASSE[retenue["state"]], prs, sha, retenue, "")
            continue
        # Aucune PR exploitable : le statut devient une MESURE du contenu.
        sur_main = tete_sur_main(repo, sha, args.main)
        if sur_main is True:
            classes[nom] = ("D", prs, sha, None, "ancestor_of_main")
            continue
        if sur_main is None:
            inconnus.append(nom)
            classes[nom] = ("E", prs, sha, None, "head_absent_du_clone")
            continue
        classes[nom] = ("E", prs, sha, None, "not_ancestor_of_main")

    # Preuve de contenu pour les classes C et E : la tete est-elle un ancetre
    # de `main` ? Un « oui » dit que le contenu EST sur main ; un « non » dit
    # qu'il pourrait ne l'etre pas -- et le verdict de suppression change.
    for nom, entree in list(classes.items()):
        classe, prs, sha, retenue, contenu = entree
        if classe not in ("C", "E") or contenu:
            continue
        sur_main = tete_sur_main(repo, sha, args.main)
        if sur_main is True:
            classes[nom] = (classe, prs, sha, retenue, "ancestor_of_main")
        elif sur_main is None:
            classes[nom] = (classe, prs, sha, retenue, "head_absent_du_clone")
        else:
            classes[nom] = (classe, prs, sha, retenue, "not_ancestor_of_main")

    lignes = []
    repliables = 0
    for nom in sorted(classes):
        classe, prs, sha, retenue, contenu = classes[nom]
        etats = Counter(p["state"] for p in prs)
        if classe == "E":
            etat, numero = "NONE", "-"
            note = "orphan_no_pr"
        elif classe == "D":
            etat, numero = "NONE", "-"
            note = "ancestor_of_main"
        else:
            etat, numero = retenue["state"], retenue["number"]
            note = "+".join(f"{k.lower()}:{v}" for k, v in sorted(etats.items()))
            note += {"A": ";keep_open_pr", "B": ";merged", "C": ";closed_unmerged"}[classe]
        if classe in ("C", "E"):
            note += ";" + contenu
            # Une PR MERGEE sur une TETE ANCIENNE de la branche ne prouve rien
            # sur les commits posterieurs : elle est notee, pas comptee comme
            # livraison. C'est ce qui distingue « contenu livre » de
            # « branche avec des commits jamais fusionnes ».
            if etats.get("MERGED"):
                note += ";merged_at_older_head"
        if classe == "B":
            # Preuve EXACTE du contenu livre : le commit de fusion de la PR
            # est-il un commit de `main` ? Une PR mergee dans une base
            # PILOTE a un commit de fusion, mais ce commit n'est pas dans
            # `main` : son contenu n'est donc PAS livre par ce merge.
            oid = retenue.get("merge_oid") or ""
            if oid and oid in commits_main:
                note += ";content_on_main"
                repliables += 1
            elif oid:
                note += f";merged_into_pilot_base:{retenue.get('base') or '?'}"
            else:
                note += ";merge_commit_unknown"
        lignes.append(f"{nom}\t{sha}\t{classe}\t{numero}\t{etat}\t{note}")

    sortie = Path(args.out)
    sortie.parent.mkdir(parents=True, exist_ok=True)
    corps = "\t".join(COLONNES) + "\n" + "\n".join(lignes) + "\n"
    if args.gzip:
        with gzip.open(sortie, "wt", encoding="utf-8", newline="\n") as fh:
            fh.write(corps)
    else:
        sortie.write_text(corps, encoding="utf-8", newline="\n")

    compteur = Counter(c[0] for c in classes.values())
    print(f"remote : {len(distant)} branches")
    for classe in "ABCDE":
        if compteur.get(classe):
            print(f"  classe {classe} : {compteur[classe]}")
    if inconnus:
        print(f"  dont tete absente du clone (INCONNU, jamais presume effacable) : {len(inconnus)}")
    contenu = Counter(c[4] for c in classes.values() if c[0] in ("C", "E"))
    for jeton, nb in sorted(contenu.items(), key=lambda kv: -kv[1]):
        print(f"  contenu {jeton} : {nb}")
    print(f"manifeste ecrit : {sortie}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
