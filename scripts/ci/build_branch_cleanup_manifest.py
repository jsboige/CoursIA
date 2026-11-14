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
| P | la BRANCHE PAR DEFAUT du depot | garder, jamais candidate |

Une branche peut porter PLUSIEURS PRs (nom reutilise dans le temps). La classe
est celle de l'etat le plus contraignant : OPEN > MERGED > CLOSED. Une branche
qui a eu une PR fermee puis une PR mergee reste B : son contenu EST sur main.
En revanche, une PR **ouverte** l'emporte toujours, meme si sa tete est
ancienne : c'est un travail vivant sur ce nom de branche, et une PR mergee
qui porterait la tete courante ne peut pas le faire disparaitre.

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

# La branche par defaut n'est JAMAIS un candidat : la supprimer, meme
# « trivially ancetre de main », detruirait le depot. Elle porte donc sa
# propre classe P, hors de l'ensemble des candidats.
CLASSE_PROTEGEE = "P"
CLASSES_CANDIDATES = ("B", "C", "D", "E")
CLASSES_NON_CANDIDATES = ("A", CLASSE_PROTEGEE)

# Plafond de la liste de PRs de `gh pr list` (voir `etats_par_branche`). Un
# depot qui l'atteindrait rendrait une liste TRONQUEE sans avertissement :
# la garde en bas de la fonction echoue alors plutot que de construire un
# manifeste incomplet (fail-open).
PLAFOND_PRS = 30000


def sh(args, cwd=None, check=True):
    p = subprocess.run(args, cwd=cwd, capture_output=True, text=True, encoding="utf-8")
    if check and p.returncode != 0:
        sys.exit(f"ECHEC {args[0]} (rc={p.returncode}) : {(p.stderr or '')[-400:]}")
    return p.stdout or ""


def branches_distantes(repo: Path, remote: str = "origin") -> dict[str, str]:
    distant = {}
    for ligne in sh(["git", "ls-remote", "--heads", remote], cwd=str(repo)).splitlines():
        sha, ref = ligne.split("\t")
        distant[ref[len("refs/heads/"):]] = sha
    return distant


def repli_branche_par_defaut(main_ref: str) -> str:
    """Le nom de branche deduit de `main_ref` (`origin/main` -> `main`).

    Repli employe quand ni le remote ni le clone local ne nomment la branche
    par defaut.
    """
    for prefixe in ("refs/remotes/", "refs/heads/"):
        if main_ref.startswith(prefixe):
            main_ref = main_ref[len(prefixe):]
            break
    # `origin/main` -> `main` : le premier segment est le nom du remote.
    return main_ref.split("/", 1)[1] if "/" in main_ref else main_ref


def branche_par_defaut_distant(repo: Path, remote: str) -> str:
    """La branche par defaut, lue sur le remote lui-meme.

    `git ls-remote --symref <remote> HEAD` repond une ligne
    `ref: refs/heads/<branche>` suivie de la tete. C'est la source
    autoritative : elle repond meme quand le clone local n'a pas de
    `refs/remotes/<remote>/HEAD`.
    """
    p = subprocess.run(
        ["git", "ls-remote", "--symref", remote, "HEAD"],
        cwd=str(repo), capture_output=True, text=True, encoding="utf-8",
        errors="replace")
    for ligne in (p.stdout or "").splitlines():
        # La ligne reelle est `ref: refs/heads/<branche>\tHEAD` : le nom de
        # la branche s'arrete a la tabulation.
        ref = ligne.split("\t", 1)[0].strip()
        if ref.startswith("ref: "):
            ref = ref[len("ref: "):].strip()
        if ref.startswith("refs/heads/"):
            return ref[len("refs/heads/"):]
    return ""


def branche_par_defaut(repo: Path, main_ref: str, remote: str = "origin") -> str:
    """Le nom de la branche par defaut du depot.

    Trois sources, dans cet ordre :

    1. `git ls-remote --symref <remote> HEAD` -- le remote nomme lui-meme
       sa branche par defaut ;
    2. `git symbolic-ref refs/remotes/<remote>/HEAD` -- la reference
       symbolique locale. Le prefixe a retirer est
       `refs/remotes/<remote>/` : le nom du remote fait partie du ref, et
       le conserver produirait `origin/main` au lieu de `main` -- c'est-a-dire
       un nom qui ne correspond a aucune branche du lot ;
    3. a defaut, le nom de `main_ref` deduit de sa forme habituelle
       (`origin/main` -> `main`).

    Cette branche ne doit JAMAIS entrer dans le lot de suppression : elle
    est trivially un ancetre de `main`, et le classifieur la retiendrait donc
    comme candidate alors que la supprimer detruit le depot.
    """
    nom = branche_par_defaut_distant(repo, remote)
    if nom:
        return nom
    prefixe = f"refs/remotes/{remote}/"
    p = subprocess.run(
        ["git", "symbolic-ref", "--quiet", f"refs/remotes/{remote}/HEAD"],
        cwd=str(repo), capture_output=True, text=True, encoding="utf-8",
        errors="replace")
    sortie = (p.stdout or "").strip()
    if p.returncode == 0 and sortie.startswith(prefixe):
        return sortie[len(prefixe):]
    return repli_branche_par_defaut(main_ref)


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
        "--limit", str(PLAFOND_PRS), "--json",
        "headRefName,number,state,headRefOid,baseRefName,mergeCommit",
    ], cwd=str(repo))
    documents = json.loads(brut)
    if len(documents) >= PLAFOND_PRS:
        sys.exit(
            f"ECHEC : {len(documents)} PRs, plafond --limit {PLAFOND_PRS} "
            "atteint : la liste est TRONQUEE et le manifeste serait incomplet "
            "(fail-open). Lever le plafond ou paginer, puis re-excuter.")
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


def classe_branche(nom: str, sha: str, prs: list[dict], defaut: str,
                   mesure_contenu) -> tuple[str, dict | None, str]:
    """La classe d'UNE branche, et sa preuve.

    Fonction **pure** : tout ce qu'elle decide est decide ici, et les tests
    peuvent l'exercer sans reseau ni jeton. C'est la fonction que `main()`
    appelle, et elle n'a pas de version parallele : un test qui la
    n'exercerait pas laisserait la decision de suppression hors de portee.

    `mesure_contenu` est un callable sans argument rendu True / False /
    None -- None signifiant « tete absente du clone », donc inconnu.

    Retourne `(classe, retenue, note)`.
    """
    # La branche par defaut est PROTEGEE : elle ne peut ni etre candidate,
    # ni etre mesuree comme telle. Sans cette exclusion, elle tombait en D
    # (ancetre de `main` -- trivial), et un passage automatise aurait tente
    # de supprimer le depot.
    if nom == defaut:
        return (CLASSE_PROTEGEE, None, "branche_par_defaut")

    # La PR qui decrit la TETE COURANTE est celle dont le headRefOid vaut
    # la tete distante. Les autres PRs du meme nom decrivent un etat
    # passe : elles ne disent rien de ce qui serait supprime.
    tete = sha.lower()
    candidates = [p for p in prs if p["oid"] == tete]
    # Le verrou OUVERT porte sur TOUTES les PRs de la branche, et non sur
    # le seul repli. Une PR ouverte dont la tete a bouge represente un
    # travail VIVANT sur ce nom de branche : si une PR mergee porte la
    # tete courante, elle ne peut pas faire disparaitre le verrou, sinon
    # un passage automatise supprimerait une branche sur laquelle une PR
    # ouverte existe encore.
    ouvertes = [p for p in prs if p["state"] == "OPEN"]
    if ouvertes:
        candidates = candidates + ouvertes
    if candidates:
        retenue = min(candidates, key=lambda p: (RANG[p["state"]], p["number"]))
        return (CLASSE[retenue["state"]], retenue, "")

    # Aucune PR exploitable : le statut devient une MESURE du contenu.
    sur_main = mesure_contenu()
    if sur_main is True:
        return ("D", None, "ancestor_of_main")
    if sur_main is None:
        return ("E", None, "head_absent_du_clone")
    return ("E", None, "not_ancestor_of_main")


def main() -> int:
    parseur = argparse.ArgumentParser(description=__doc__)
    parseur.add_argument("--repo", default=str(Path(__file__).resolve().parents[2]))
    parseur.add_argument("--out", required=True, help="fichier TSV a ecrire")
    parseur.add_argument("--gzip", action="store_true", help="compresser la sortie")
    parseur.add_argument("--main", default="origin/main")
    parseur.add_argument("--remote", default="origin")
    args = parseur.parse_args()

    repo = Path(args.repo)
    distant = branches_distantes(repo, args.remote)
    par_branche = etats_par_branche(repo)
    commits_main = commits_de_main(repo, args.main)
    defaut = branche_par_defaut(repo, args.main, args.remote)

    classes: dict[str, tuple] = {}
    inconnus: list[str] = []
    for nom, sha in distant.items():
        prs = par_branche.get(nom) or []
        mesure = (lambda s: (lambda: tete_sur_main(repo, s, args.main)))(sha)
        classe, retenue, note = classe_branche(nom, sha, prs, defaut, mesure)
        classes[nom] = (classe, prs, sha, retenue, note)
        if note == "head_absent_du_clone":
            inconnus.append(nom)

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
    # Ordonne par SHA (pas par nom) : c'est le contrat du README (« ordonnee
    # par SHA pour faciliter les diffs entre passes successives ») et l'ordre
    # que `sort -c` sur la colonne 2 re-verifie. Le nom fait le tie-break.
    for nom in sorted(classes, key=lambda n: (classes[n][2], n)):
        classe, prs, sha, retenue, contenu = classes[nom]
        etats = Counter(p["state"] for p in prs)
        if classe == "E":
            etat, numero = "NONE", "-"
            note = "orphan_no_pr"
        elif classe == "D":
            etat, numero = "NONE", "-"
            note = "ancestor_of_main"
        elif classe == CLASSE_PROTEGEE:
            etat, numero = "NONE", "-"
            note = "branche_par_defaut;jamais_candidate"
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
    for classe in ("A", "B", "C", "D", "E", CLASSE_PROTEGEE):
        if compteur.get(classe):
            print(f"  classe {classe} : {compteur[classe]}")
    if repliables:
        print(f"  classe B repliables (contenu prouve sur main) : {repliables}")
    if compteur.get(CLASSE_PROTEGEE):
        print(f"  branche par defaut protegee : {defaut}")
    if inconnus:
        print(f"  dont tete absente du clone (INCONNU, jamais presume effacable) : {len(inconnus)}")
    contenu = Counter(c[4] for c in classes.values() if c[0] in ("C", "E"))
    for jeton, nb in sorted(contenu.items(), key=lambda kv: -kv[1]):
        print(f"  contenu {jeton} : {nb}")
    print(f"manifeste ecrit : {sortie}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
