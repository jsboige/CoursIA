#!/usr/bin/env python3
"""Registre anti-entropie (#23175) — l'instrument de resultat des issues
qui gardent le depot digérable.

Le mandat, verbatim de l'issue :

> « ... un registre des issues qui doivent etre visitées plus souvent
> (reorganisation, consolidation, reecriture des readme, densite etc.),
> celles qui luttent contre l'entropie et gardent le depot digeable ...
> je pense que tu dois pouvoir identifier toutes ces issues de
> consolidation qui n'avancent pas »

Ce que l'organe fait, et rien de plus :

  * chaque entree du registre porte un **instrument de resultat** : une
    commande, et la valeur que cette commande rend ;
  * l'organe **execute** l'instrument, lit la valeur du jour ;
  * il publie sur l'issue un commentaire **balise** `ANTI-ENTROPY-REGISTER`
    qui porte la valeur du jour, la valeur de reference (celle d'il y a
    sept jours), et le **verdict** : `AVANCE`, `STAGNE` ou `RECULE` ;
  * il ecrit un **etat** local (les verdicts) que le budget de creation
    (#23174) lit comme **cliquet** : quand l'entree « padding et nommage »
    recule, un carnet neuf qui ajouterait un nom non conforme est retenu.

Le progres se lit a la **valeur**, jamais au nombre de PRs qui citent
l'issue : c'est la demande expresse de l'issue, et la raison pour laquelle
le registre porte un instrument et non un compteur de PRs.

La **reference** (la valeur d'il y a sept jours) est lue dans le
**dernier commentaire** publie sur l'issue : il est durable, il est partage
par la flotte, et il a ete mesure par le meme organe — la comparaison est
donc homogene. Au premier passage d'une entree sans reference, le verdict
est `PREMIERE MESURE` : il ne dit rien, il constate qu'il n'y a pas encore
de reference.

Usage :

    python scripts/coordination/anti_entropy_register.py --dry-run
    python scripts/coordination/anti_entropy_register.py
    python scripts/coordination/anti_entropy_register.py --issue 5081 --json
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

RACINE = pathlib.Path(__file__).resolve().parent.parent.parent
if str(RACINE) not in sys.path:
    sys.path.insert(0, str(RACINE))

REPO = "jsboige/CoursIA"

# Le marqueur du commentaire publie. Il est dans un HTML comment : il
# disparait a la lecture, et il se retrouve par une recherche exacte.
MARQUEUR = "ANTI-ENTROPY-REGISTER"

# Le compte sous lequel l'organe publie. Le trousseau `gh` de la machine
# est partage et le compte actif bascule : une ecriture faite sous le
# mauvais compte n'est plus levable par le coordinateur. L'organe
# refuse donc de publier si l'identite n'est pas etablie.
COMPTE_EPINGLE = "jsboige"

# L'etat local des verdicts (lu par le budget de creation, cf #23174).
ENV_ETAT = "COURSIA_ANTI_ENTROPY_FILE"

VERDICTS = ("AVANCE", "STAGNE", "RECULE", "PREMIERE MESURE",
            "INSTRUMENT ILLEGIBLE")

# Le fichier d'etat, par defaut sous LOCALAPPDATA (le meme perimetre que
# l'etat du budget de creation).
def chemin_etat_defaut() -> pathlib.Path:
    base = os.environ.get("LOCALAPPDATA") or str(pathlib.Path.home())
    return pathlib.Path(base) / "CoursIA" / "anti_entropy_register.json"


# ---------------------------------------------------------------------------
# Le registre
# ---------------------------------------------------------------------------

@dataclasses.dataclass(frozen=True)
class Reference:
    """La valeur de reference : celle d'il y a sept jours.

    `instrument` est l'IDENTITE de l'instrument qui a produit la valeur.
    Sans elle, une reference n'est pas comparable a la valeur du jour : deux
    instruments qui ne sont pas le meme ne produisent pas la meme grandeur
    (cf `comparables` et `identite_instrument`).
    """

    valeur: float
    mesure_le: str
    source: str = ""
    instrument: str = ""


@dataclasses.dataclass(frozen=True)
class Entree:
    """Une entree du registre : une issue, un instrument, un sens, une cible.

    `extraction` dit comment lire la valeur dans la sortie de l'instrument :

      * `("chemin", "a.b.c")` — un chemin dans un JSON ;
      * `("lignes",)` — le nombre de lignes non vides ;
      * `("somme_listes", ("a.b", "c.d"))` — la somme des longueurs de deux
        listes d'un JSON.
    """

    cle: str
    issue: int
    titre: str
    commande: tuple[str, ...]
    extraction: tuple
    sens: str                 # "descend" (moins c'est mieux) ou "ascend"
    cible: float = 0.0
    reference: Reference | None = None
    note: str = ""
    # Le sous-arbre dont le contenu l'instrument LIT dans l'arbre local.
    # Vide = l'instrument ne lit que la revision qu'il nomme (un builtin
    # git comme `git ls-tree`) : il n'y a alors rien a verifier. Voir
    # `arbre_aligne`.
    arbre: str = ""
    # Les points HISTORIQUES de la serie, anterieurs a la reference courante.
    #
    # Ils ne portent PAS d'identite d'instrument : l'organe la derive
    # lui-meme, a la DATE du point (`identite_instrument(..., au=...)`).
    # C'est ce qui rend la serie cumulative sans la faire mentir : une
    # valeur datee du 2026-10-21 est attribu a l'instrument qui etait
    # alors dans l'arbre, pas a celui d'aujourd'hui.
    #
    # Chaque point porte sa SOURCE (le fil ou la publication qui l'a
    # produit) : une valeur sans source est une valeur inventee.
    historique: tuple[Reference, ...] = ()


# Le registre, version 1 (les trois cas cites par l'issue).
#
# Chaque entree a un instrument REEL, deja dans le depot : l'issue demande
# « une commande, et la valeur que cette commande rend ».
REGISTRE: tuple[Entree, ...] = (
    Entree(
        cle="padding-nommage",
        issue=5081,
        titre="Padding et nommage — carnets au nom non conforme",
        commande=(sys.executable, "scripts/notebook_tools/inventory_notebook_names.py",
                  "--json", "--base", "origin/main"),
        extraction=("chemin", "by_classification.ambigu"),
        sens="descend",
        cible=0.0,
        # La reference REBASEE sur l'instrument courant, mesuree sur un
        # checkout ALIGNE sur la revision nommee.
        #
        # Pourquoi ce rebasage : la reference d'origine (776, mesuree le
        # 2026-10-21) a ete produite par l'AVANT dernier instrument. Le
        # correctif #23193 (d818b008b) a change ce que l'instrument compte
        # : sur le meme arbre, l'ancien instrument rend 776 et le nouveau
        # 44. Comparer 44 a 776, c'est fabriquer un AVANCE (ou un RECULE)
        # qui ne dit rien du depot -- c'est ce qui produisait le verdict
        # « AVANCE » affiche sur l'entree « padding et nommage » au lieu
        # du RECULE attendu, et le cliquet du budget de creation
        # (#23174) s'ouvrait a contresens sur cette base.
        #
        # Pourquoi 38 et non 44 (mesure du 2026-10-31, meme `origin/main`
        # = 6135a06, deux checkouts, instrument d818b008b) : l'instrument
        # prend sa LISTE de carnets dans la revision nommee (`git ls-tree`)
        # mais lit le CONTENU de chaque carnet dans l'ARBRE LOCAL
        # (`open(path)`). Les deux ne concordent que si le checkout EST
        # sur la revision nommee. Sur un checkout aligne (worktree sur
        # 6135a06) l'instrument rend **38** ; sur un checkout en retard
        # (clone principal a d9aee247) il rend **44** : l'ecart est
        # exactement la serie Wavelet renommee par 6135a06 -- son nom
        # nouveau est dans la liste (prise sur la revision), son contenu
        # est absent du checkout (nom ancien), donc le kernel n'est pas lu
        # et le carnet compte `ambigu`. La valeur mesuree dependait donc
        # du CHECKOUT, sans que rien ne le dise.
        #
        # La reference retenue est donc 38 : c'est la valeur de l'arbre
        # que l'instrument nomme (`origin/main` a 6135a06), mesuree dans
        # les conditions ou l'instrument mesure ce qu'il dit mesurer. Le
        # garde `arbre_aligne` refuse desormais la mesure quand le
        # checkout n'est pas sur la revision nommee -- sinon on publierait
        # un melange de deux arbres sous un verdict unique.
        #
        # Apres ce rebasage, la comparaison est « valeur du jour » contre
        # « valeur du jour du rebasage » : elle est STAGNE, ce qui est
        # exact. Elle redeviendra une comparaison de sept jours le
        # 2026-11-06, quand une publication portant l'identite de
        # l'instrument aura sept jours : la reference sera alors relue
        # dans le commentaire publie, avec l'identite a cote de la valeur.
        reference=Reference(38.0, "2026-10-31", "issue #23175",
                            instrument=("scripts/notebook_tools/"
                                        "inventory_notebook_names.py"
                                        "@d818b008b5558d9a755c81d3d05e29ac23a9f823")),
        # Les points anterieurs de la serie, avec leur SOURCE. L'identite
        # de l'instrument n'est PAS declaree ici : l'organe la derive a
        # la date du point. C'est ce qui permet de lire la serie de
        # l'instrument d'avant #23193 — celle-la meme qui vaut
        # « RECULE » (776 -> 813 -> 840).
        historique=(
            Reference(776.0, "2026-10-21",
                      "issue #23175, reference inscrite dans le corps",
                      instrument=("scripts/notebook_tools/"
                                  "inventory_notebook_names.py"
                                  "@4ee8a58dfee62fc7e8cc3bff3329c17493822c01")),
            Reference(840.0, "2026-10-30",
                      "issue #23175, commentaire de mesure du "
                      "2026-10-30T23:46Z (lane myia-po-2028:CoursIA-2)",
                      instrument=("scripts/notebook_tools/"
                                  "inventory_notebook_names.py"
                                  "@4ee8a58dfee62fc7e8cc3bff3329c17493822c01")),
        ),
        note="`ambigu` = nom non parsé ou kernel non verifie.",
        # L'instrument prend sa LISTE de carnets dans `origin/main` et lit
        # le CONTENU de chaque carnet dans l'ARBRE LOCAL : le rayon a
        # verifier est donc celui des carnets.
        arbre="MyIA.AI.Notebooks",
    ),
    Entree(
        cle="catalogue-fraicheur",
        issue=5081,
        titre="Catalogue — fraicheur de la derniere regeneration sur main",
        commande=("git", "log", "-1", "--format=%ct", "--grep",
                  "scheduled auto-regenerate", "origin/main"),
        extraction=("age_jours",),
        sens="descend",
        cible=0.0,
        note="Age en jours du dernier commit de regeneration du catalogue "
             "sur main. L'issue nomme « l'age de la PR longue dure "
             "chore(catalog): scheduled auto-regenerate » et conclut que "
             "« le goulot est le merge du coordinateur, pas "
             "l'automatisation » : cet age mesure les DEUX (cron arrete ET "
             "PR non mergee), et c'est le second que le coordinateur "
             "pilote. Un complement possible : l'ecart entre le catalogue "
             "publie et l'arbre (`check_catalog_freshness.py --json`).",
    ),
    Entree(
        cle="dynamics-escalier",
        issue=20381,
        titre="GameTheory/Dynamics — carnets materialises de l'escalier 01-08",
        commande=("git", "ls-tree", "-r", "--name-only", "origin/main", "--",
                  "MyIA.AI.Notebooks/GameTheory/Dynamics/"),
        extraction=("lignes", ".ipynb"),
        sens="ascend",
        cible=11.0,
        note="Le carnet est la valeur : l'escalier doit se materialiser. "
             "Cible 11 = les 8 marches de l'escalier (01 a 08) + les deux "
             "jumeaux qui ne comptent pas comme marche (01 C#, 05 Lean) + "
             "le carnet 09 greffe apres GT-03 — le perimetre annonce par "
             "#20381 (« 11 carnets + README »). La mesure ne compte que "
             "les FICHIERS `.ipynb` : la cible est en carnets, et un README "
             "de plus ne doit pas faire bouger l'escalier. Mesure au "
             "2026-10-28 : 1 (seul `Dynamics-09` etait alors present ; la "
             "descente T3 #20374 n'avait pas ete mergee).",
    ),
)


# ---------------------------------------------------------------------------
# L'instrument
# ---------------------------------------------------------------------------

def _run(cmd: tuple[str, ...] | list[str], timeout: int = 600) -> tuple[int, str, str]:
    """Execute l'instrument. Rend `(code, stdout, stderr)`."""
    try:
        out = subprocess.run(list(cmd), capture_output=True, text=True,
                             encoding="utf-8", timeout=timeout, cwd=str(RACINE),
                             check=False)
    except Exception as exc:  # noqa: BLE001 - un instrument muet = pas de valeur
        return 2, "", f"{type(exc).__name__}: {exc}"
    return out.returncode, out.stdout or "", out.stderr or ""


def _chemin(obj, chemin: str):
    """Lit un chemin `a.b.c` dans un JSON. Raise KeyError si absent."""
    cur = obj
    for part in chemin.split("."):
        cur = cur[part]
    return cur


# ---------------------------------------------------------------------------
# L'identite de l'instrument
# ---------------------------------------------------------------------------
#
# Deux valeurs ne sont comparables que si le MEME instrument les a
# produites. Or un instrument change : #23193 (d818b008b) a corrige
# `inventory_notebook_names.py`, et sur le meme arbre l'ancien instrument
# rend 776 la ou le nouveau rend 44. Comparer les deux, c'est fabriquer un
# verdict qui ne dit rien du depot -- et un verdict fabrique est pire
# qu'une absence de verdict, parce qu'il est lu comme une mesure.
#
# L'identite d'un instrument est donc la grandeur qui change quand
# l'instrument change :
#
#   * un instrument qui est un SCRIPT du depot : `<chemin>@<sha du dernier
#     commit qui a touche ce script>` -- le sha est precisement la
#     grandeur qui bouge a chaque correction de l'instrument ;
#   * un instrument qui est une COMMANDE git (`git log`, `git ls-tree`) :
#     la commande elle-meme. Elle n'a pas de version, elle est stable par
#     construction, et c'est ce qui la rend comparable d'une publication a
#     l'autre.
#
# Une identite qu'on ne sait pas etablir vaut "" : elle ne veut pas dire
# « identique », elle veut dire « inconnue » -- et une reference d'identite
# inconnue n'est PAS comparable (cf `comparables`).

def _script_de_la_commande(commande) -> str:
    """Le script du depot que la commande appelle, ou "" si elle n'en appelle pas."""
    for mot in commande:
        mot = str(mot)
        if mot.endswith((".py", ".sh")) and "/" in mot:
            return mot
    return ""


def identite_instrument(commande) -> str:
    """L'identite de l'instrument que la commande constitue.

    Une commande git a une identite stable (la commande). Une commande
    qui appelle un script du depot a pour identite le script et le sha du
    dernier commit qui l'a touche -- c'est la grandeur qui change quand
    l'instrument change. Si le sha ne peut pas etre etabli, l'identite
    est inconnue (""), jamais « identique ».
    """
    return _identite(commande, None)


def identite_instrument_a(commande, au: str) -> str:
    """L'identite de l'instrument **tel qu'il etait a la date** `au`.

    C'est ce qui rend la serie lisible : une valeur mesuree le 2026-10-21
    appartient a l'instrument de cette date-la, pas a celui d'aujourd'hui.
    Sans elle, la serie historique disparaitrait — et avec elle, la seule
    comparaison qui dise si le chantier recule.

    La resolution est au JOUR : `--before=<date>` prend le dernier commit
    anterieur a minuit. Une mesure faite en fin de journee apres un
    commit de la journee est donc attribuee a l'instrument d'avant ce
    commit — c'est le cas de la mesure du 2026-10-30T23:46Z, faite
    volontairement avec l'instrument anterieur a #23193. Le point declare
    porte alors son identite, et l'ecart entre les deux est visible.
    """
    return _identite(commande, au)


def _identite(commande, au: str | None) -> str:
    """Le coeur de l'identite : le sha du dernier commit qui a touche le
    script de l'instrument, avant la date `au` si elle est donnee."""
    script = _script_de_la_commande(commande)
    if not script:
        return "git:" + " ".join(str(m) for m in commande)
    for ref in ("origin/main", "HEAD"):
        if au:
            cmd = ("git", "log", "-1", "--format=%H", f"--before={au}",
                   ref, "--", script)
        else:
            cmd = ("git", "log", "-1", "--format=%H", ref, "--", script)
        code, out, _ = _run(cmd)
        sha = out.strip()
        if code == 0 and sha:
            return f"{script}@{sha}"
    return ""


def comparables(identite: str, identite_reference: str) -> bool:
    """Deux valeurs sont-elles produites par le meme instrument ?

    Le principe : on ne presume **jamais** la comparabilite. Une identite
    inconnue (l'un des deux cotes vide) n'est pas une identite : elle ne
    permet pas de comparer, donc elle ne vaut pas comparaison.
    """
    return bool(identite) and bool(identite_reference) and identite == identite_reference


# ---------------------------------------------------------------------------
# La serie a instrument constant
# ---------------------------------------------------------------------------
#
# Le controle positif de l'issue exige que le padding rende « RECULE » a la
# mesure. Depuis le merge de #23193 (l'instrument corrige), la valeur du jour
# et la reference ne viennent plus du meme instrument : comparer les deux
# fabriquerait un verdict, et le controle ne testerait plus ce qu'il croit
# testerer.
#
# Refuser la comparaison transverse (fait par `comparables`) suffit a ne plus
# mentir, mais cela laisse le lecteur sans la MESURE qui compte : le
# chantier recule-t-il, lui ? Cette question a une reponse, et elle se lit
# dans la serie **a instrument constant** : le groupe des valeurs produites
# par un meme instrument, dans leur ordre chronologique.
#
# Pour l'entree « padding et nommage », ce groupe est celui de l'instrument
# d'avant #23193 : 776 (2026-10-21) -> 813 (2026-10-28) -> 840 (2026-10-30).
# Il rend RECULE (+64 en neuf jours) — le controle positif est donc
# VIVANT : il s'exerce sur des mesures reelles, et non sur des constantes
# ecrites en dur dans un test.
#
# L'identite d'un point est celle de l'instrument TEL QU'IL ETAIT a la date
# du point (`identite_instrument(..., au=...)`) : sans cela, une valeur du
# 2026-10-21 serait attribuee a l'instrument d'aujourd'hui, et la serie
# historique disparaitrait.

def _valeur_publiee(body: str, cle: str) -> float | None:
    """La valeur du jour d'une publication balisee, pour l'entree `cle`.

    La colonne `valeur` du tableau de la publication. Une cellule qui n'est
    pas un nombre (un tiret, une mention) donne `None` : une absence de
    valeur n'est pas une valeur.
    """
    for ligne in (body or "").splitlines():
        m = _LIGNE_TABLE.match(ligne)
        if not m or m.group("cle") != cle:
            continue
        cellules = [c.strip() for c in ligne.strip().strip("|").split("|")]
        if len(cellules) < 3:
            return None
        brut = cellules[2].replace(",", ".").strip()
        try:
            return float(brut)
        except ValueError:
            return None
    return None


def points_publies(issue: int, cle: str) -> list[tuple[str, float, str, str]]:
    """Les points `(date, valeur, source, instrument)` de chaque publication.

    Les publications sont lues dans l'ordre chronologique. L'identite de
    l'instrument est celle portee par le tableau de la publication depuis le
    rebasage du 2026-10-30 ; avant elle, elle est vide et sera derivee a la
    date de la publication (cf `serie_par_instrument`).
    """
    points: list[tuple[str, float, str, str]] = []
    for commentaire in _commentaires_marques(issue):
        corps = commentaire.get("body") or ""
        valeur = _valeur_publiee(corps, cle)
        if valeur is None:
            continue
        ident = identite_du_commentaire(corps, cle)
        source = (f"publication balisee du {commentaire.get('created_at') or '?'}"
                  + (f" (instrument `{ident}`)" if ident else ""))
        points.append((commentaire.get("created_at") or "", valeur, source, ident))
    return points


def serie_par_instrument(commande, sens: str,
                         points: list[tuple[str, float, str, str]]
                         ) -> list[dict]:
    """Regroupe les points par l'instrument qui les a produits.

    Chaque point est un quadruplet `(date, valeur, source, instrument)`.
    L'instrument **declare** est utilise quand il est connu (c'est la
    version de l'instrument avec laquelle la valeur a ete MESUREE) ; sinon
    l'identite est derivee a la date du point. Un point dont l'identite ne
    peut pas etre etablie est **laisse de cote** (il ne se compare a rien).

    Chaque groupe porte sa TENDANCE : le verdict entre sa premiere et sa
    derniere valeur. Deux valeurs du meme groupe sont, par construction,
    produites par le meme instrument — c'est la seule comparaison qui se
    defend.
    """
    groupes: dict[str, list[dict]] = {}
    for date, valeur, source, declaree in points:
        identite = declaree or identite_instrument_a(commande, date)
        if not identite:
            continue
        groupes.setdefault(identite, []).append(
            {"date": date, "valeur": valeur, "source": source})
    sortie: list[dict] = []
    for identite, lot in groupes.items():
        lot.sort(key=lambda p: (p["date"], p["valeur"]))
        # Deux publications du meme jour et de meme valeur sont le MEME
        # point : il en faut une seule, sinon la serie compte des
        # repetitions comme des etapes.
        dedupes: list[dict] = []
        for p in lot:
            if dedupes and dedupes[-1]["date"][:10] == p["date"][:10] \
                    and dedupes[-1]["valeur"] == p["valeur"]:
                continue
            dedupes.append(p)
        lot = dedupes
        if len(lot) >= 2:
            # `verdict(valeur, reference)` : la valeur du jour est la
            # DERNIERE de la serie, la reference en est la PREMIERE. Inverser
            # les deux inverserait la tendance — c'est ce qui faisait
            # rendre « AVANCE » a une serie qui recule.
            tendance = verdict(lot[-1]["valeur"], lot[0]["valeur"], sens)
        else:
            tendance = "PREMIERE MESURE"
        sortie.append({"instrument": identite, "points": lot,
                        "tendance": tendance})
    sortie.sort(key=lambda g: g["points"][0]["date"])
    return sortie


def _ref_de_la_commande(commande) -> str:
    """La revision que la commande nomme (l'argument apres `--base`)."""
    args = [str(m) for m in commande]
    for i, mot in enumerate(args):
        if mot == "--base" and i + 1 < len(args):
            return args[i + 1]
    return ""


def arbre_aligne(commande, rayon: str = "") -> tuple[bool, str]:
    """L'arbre mesure est-il celui que l'instrument nomme ?

    Un instrument qui appelle un SCRIPT du depot peut lire le CONTENU de
    ses fichiers dans l'ARBRE LOCAL, alors que sa LISTE de fichiers vient
    de la revision nommee. Les deux ne concordent que si l'arbre local
    porte le MEME contenu que la revision, dans le rayon que l'instrument
    lit.

    Le rayon est declare par l'entree (`Entree.arbre`) : c'est le
    sous-arbre dont le contenu l'instrument lit. Un instrument qui ne lit
    que la revision qu'il nomme (un builtin git comme `git ls-tree`)
    declare un rayon vide : il n'y a alors rien a verifier.

    La verification compare la revision nommee a l'ARBRE LOCAL
    (`git diff <ref> -- <rayon>` compare une revision a l'arbre de
    travail, commits non compris) : c'est exactement ce que l'instrument
    lit. Comparer les SHA de HEAD et de la revision serait trop grossier
    — une branche de travail qui ne touche que des scripts diverge
    aussi, alors que les carnets qu'elle mesure sont identiques.

    Mesure (2026-10-31, meme `origin/main` = 6135a06, deux checkouts) :
    un checkout aligne rend **38** carnets `ambigu`, un checkout en retard
    (main a d9aee247) en rend **44** : l'ecart est exactement la serie
    Wavelet renommee par 6135a06 — son nom nouveau est dans la liste
    (prise sur la revision), son contenu absent du checkout (nom ancien),
    donc le kernel n'est pas lu et le carnet compte `ambigu`. La valeur
    de l'instrument dependait donc du checkout, sans que rien ne le
    dise.
    """
    ref = _ref_de_la_commande(commande)
    if not ref or not rayon:
        return True, ""
    code, out, _ = _run(("git", "diff", "--name-only", ref, "--", rayon))
    if code != 0:
        return False, f"la revision nommee `{ref}` n'est pas lisible"
    divergents = [l.strip() for l in out.splitlines() if l.strip()]
    if not divergents:
        return True, (f"l arbre local porte le meme contenu que `{ref}` "
                      f"sur `{rayon}`")
    return False, (
        f"l arbre local ne porte pas le contenu de `{ref}` sur `{rayon}` "
        f"({len(divergents)} fichier(s) divergent, dont "
        f"`{divergents[0]}`) : l'instrument prend sa liste dans `{ref}` et "
        f"lit son contenu dans l'arbre local — les deux ne concordent "
        f"pas, et la valeur mesuree n'est pas celle de l'arbre nomme")


def identite_du_commentaire(body: str, cle: str) -> str:
    """L'identite de l'instrument, d'apres un commentaire publie.

    Deux sources, dans cet ordre :

      * la colonne `instrument` du tableau — elle est portee par les
        publications qui suivent le rebasage du 2026-10-30 ;
      * a defaut, la ligne de detail, qui porte la commande : pour une
        commande git elle suffit (l'identite EST la commande) ; pour un
        script elle ne suffit PAS (le sha du script n'y est pas), et
        l'identite reste inconnue — donc non comparable.
    """
    for ligne in (body or "").splitlines():
        m = _LIGNE_TABLE.match(ligne)
        if not m or m.group("cle") != cle:
            continue
        cellules = [c.strip() for c in ligne.strip().strip("|").split("|")]
        if len(cellules) >= 7 and cellules[6] and cellules[6] != "—":
            return cellules[6]
        break
    for ligne in (body or "").splitlines():
        if not ligne.startswith(f"- `{cle}`"):
            continue
        for bout in re.findall(r"`([^`]+)`", ligne):
            if bout == cle:
                continue
            if bout.startswith("git "):
                return "git:" + bout
            if _script_de_la_commande(bout.split()):
                return ""
        return ""
    return ""


def extraire(sortie: str, spec: tuple, maintenant: dt.datetime | None = None):
    """La valeur de l'instrument, lue par sa specification.

      * `("lignes",)` — le nombre de lignes non vides ;
      * `("lignes", ".ipynb")` — idem, **filtre par suffixe** : seules les
        lignes qui se terminent par ce suffixe comptent ;
      * `("chemin", "a.b.c")` — un chemin dans un JSON ;
      * `("somme_listes", ("a.b", "c.d"))` — la somme des longueurs de deux
        listes d'un JSON ;
      * `("age_jours",)` — l'age en jours d'un timestamp epoch (la sortie
        est un nombre de secondes depuis l'epoch).
    """
    kind = spec[0]
    if kind == "lignes":
        suffixe = spec[1] if len(spec) > 1 else ""
        return float(sum(1 for ln in sortie.splitlines()
                          if ln.strip() and ln.strip().endswith(suffixe)))
    if kind == "age_jours":
        # La valeur est POSITIVE : le nombre de jours ecoules depuis le
        # timestamp. Un timestamp dans le futur (horloge de la machine
        # en avance) rendrait un age negatif, et un age negatif signifie
        # « plus recent que maintenant » — ce qui n'est pas un ecart de
        # mesure. On borne a zero.
        epoch = float(sortie.strip().splitlines()[0])
        now = maintenant or dt.datetime.now(dt.UTC)
        age = (now.timestamp() - epoch) / 86400.0
        # Arrondi a deux decimales (environ 21 minutes) : la valeur doit
        # faire un aller-retour EXACT entre la mesure et le commentaire
        # publie, parce que la detection de « la valeur a bouge » relit la
        # valeur dans le commentaire et la compare a la mesure du jour. Un
        # affichage a 14 decimales serait relu different.
        return round(max(0.0, age), 2)
    data = json.loads(sortie)
    if kind == "chemin":
        return float(_chemin(data, spec[1]))
    if kind == "somme_listes":
        total = 0
        for chemin in spec[1]:
            valeur = _chemin(data, chemin)
            total += len(valeur) if isinstance(valeur, list) else float(valeur)
        return float(total)
    raise ValueError(f"specification d'extraction inconnue : {spec!r}")


def mesurer(entree: Entree,
             maintenant: dt.datetime | None = None) -> tuple[float | None, str, str]:
    """Execute l'instrument de l'entree. Rend `(valeur, erreur, note)`.

    Une valeur absente n'est PAS un zero : c'est une **mesure non faite**,
    et elle est rendue telle quelle (l'issue demande un instrument de
    resultat, pas un silence).

    Le **code de sortie** ne decide pas de la validite de la mesure :
    plusieurs organes du depot rendent `1` quand l'ecart constate est
    REEL (`scripts/ci/check_catalog_freshness.py` sort 1 des qu'il y a
    une divergence — c'est sa maniere de dire « l'ecart existe »). Ce qui
    decide, c'est l'**extraction** : si la valeur se lit, la mesure est
    faite, et le code de sortie est note.
    """
    code, stdout, stderr = _run(entree.commande)
    if code != 0 and not stdout.strip():
        # Un instrument qui ECHOUE et ne dit rien n'a pas mesure : sa
        # sortie vide ne vaut pas un zero (il rendrait « 0 » la valeur
        # d'une panne). C'est la distinction entre « l'ecart constate »
        # (rc != 0, sortie exploitable) et « l'instrument est tombe ».
        detail = (stderr.strip().splitlines() or [""])[-1][:300]
        motif = f"instrument rc={code} : {detail}" if detail else \
            f"instrument rc={code} : aucune sortie"
        return None, motif, ""
    try:
        valeur = extraire(stdout, entree.extraction, maintenant=maintenant)
    except Exception as exc:  # noqa: BLE001 - extraction illisible = pas de valeur
        detail = (stderr.strip().splitlines() or [""])[-1][:300]
        if code != 0 and detail:
            return None, f"instrument rc={code} : {detail}", ""
        return None, f"extraction illisible : {type(exc).__name__}: {exc}", ""
    note = "" if code == 0 else f"instrument rc={code} : ecart constate"
    return valeur, "", note


# ---------------------------------------------------------------------------
# Le verdict
# ---------------------------------------------------------------------------

def verdict(valeur: float | None, reference: float | None, sens: str) -> str:
    """Le verdict, en fonction pure — elle se teste sans reseau.

    `sens` = le sens du progres :

      * `descend` — moins c'est mieux (le padding doit baisser) ;
      * `ascend`  — plus c'est mieux (l'escalier doit se materialiser).

    `AVANCE` : la valeur se rapproche de la cible. `STAGNE` : elle ne bouge
    pas. `RECULE` : elle s'en eloigne. Sans reference, `PREMIERE MESURE` :
    l'organe constate qu'il n'a pas encore de point de comparaison.

    **Une valeur absente n'est pas une valeur** : l'instrument a ete muet
    (absent, casse, sortie illisible), et la mesure n'a pas ete faite. Le
    verdict est alors `INSTRUMENT ILLEGIBLE` — jamais une comparaison, et
    surtout jamais un `None` compare a une reference (le `TypeError` que
    cela produisait cassait le cycle entier au premier instrument muet,
    alors qu'une reference existe presque toujours : c'est le cas de
    `padding-nommage`, dont la reference de repli est portee par l'issue).
    """
    if valeur is None:
        return "INSTRUMENT ILLEGIBLE"
    if reference is None:
        return "PREMIERE MESURE"
    if sens == "descend":
        if valeur < reference:
            return "AVANCE"
        if valeur > reference:
            return "RECULE"
        return "STAGNE"
    if sens == "ascend":
        if valeur > reference:
            return "AVANCE"
        if valeur < reference:
            return "RECULE"
        return "STAGNE"
    raise ValueError(f"sens inconnu : {sens!r}")


def vers_cible(valeur: float, reference: float, cible: float,
               sens: str = "descend") -> bool:
    """La valeur se rapproche-t-elle de la cible ? (controle negatif)

    Le sens n'entre pas dans le calcul : la distance a la cible se compare
    dans les deux sens. C'est ce qui rend le controle negatif valable pour
    les deux familles d'entrees.
    """
    return abs(cible - valeur) < abs(cible - reference)


# ---------------------------------------------------------------------------
# La reference : le dernier commentaire publie
# ---------------------------------------------------------------------------

_LIGNE_TABLE = re.compile(r"^\|\s*`(?P<cle>[^`]+)`\s*\|", re.MULTILINE)


def _pages_json(sortie: str) -> list:
    """Les valeurs JSON d'une sortie `gh api --paginate`.

    `--paginate` **concatene les pages**, et le `--jq` est applique a
    CHACUNE d'elles : la sortie porte donc **un tableau JSON par page**,
    pas un tableau unique. Un `json.loads` de la sortie entiere echoue
    des la deuxieme page — et l'except rendait `[]` en silence, ce qui
    effacait silencieusement tout l'historique des references.

    Le contournement mesure : `--slurp` est **incompatible avec `--jq`**
    dans `gh` (message « the `--slurp` option is not supported with
    `--jq` or `--template` », gh 2.83.2). On lit donc la sortie comme un
    flux de documents JSON : `raw_decode` enchaîne les valeurs sans
    dependre du decoupage en lignes, et tolere aussi bien un objet par
    ligne (selection `.[] | ...`) qu'un tableau par page.
    """
    valeurs: list = []
    decodeur = json.JSONDecoder()
    texte = sortie or ""
    index = 0
    longueur = len(texte)
    while index < longueur:
        while index < longueur and texte[index].isspace():
            index += 1
        if index >= longueur:
            break
        try:
            valeur, index = decodeur.raw_decode(texte, index)
        except ValueError:
            # Queue illisible : on s'arrete sur ce qui est deja lu.
            break
        if isinstance(valeur, list):
            valeurs.extend(valeur)
        else:
            valeurs.append(valeur)
    return valeurs


def _commentaires_marques(issue: int) -> list[dict]:
    """Les commentaires `ANTI-ENTROPY-REGISTER` de l'issue, du plus ancien
    au plus recent. Vide si l'issue n'en porte pas ou si la lecture echoue.

    La lecture **pagine** et aplatit les pages : une issue de plus de
    trente commentaires porte ses publications au-dela de la premiere
    page, et une lecture limitee a la premiere page perdrait les
    references les plus anciennes — c'est-a-dire l'historique dont la
    reference de sept jours est tiree.
    """
    try:
        raw = subprocess.run(
            ["gh", "api", f"repos/{REPO}/issues/{issue}/comments",
             "--paginate", "--jq", (f".[] | select(.body | contains(\"{MARQUEUR}\")) | "
             "{created_at, body}")],
            capture_output=True, text=True, encoding="utf-8", timeout=120,
            check=False)
    except Exception:  # noqa: BLE001 - reseau muet = pas de reference
        return []
    if raw.returncode != 0:
        return []
    data = [c for c in _pages_json(raw.stdout) if isinstance(c, dict)]
    # Le `--jq` filtre deja cote serveur ; on re-filtre ici pour que la
    # fonction tienne sa promesse meme si la requete change de forme
    # (une page sans marqueur ne doit rien.contribuer).
    marques = [c for c in data if MARQUEUR in (c.get("body") or "")]
    return sorted(marques, key=lambda c: c.get("created_at") or "")


def lire_reference(issue: int, cle: str,
                   now: dt.datetime | None = None) -> Reference | None:
    """La reference de l'entree : la valeur mesuree **il y a sept jours**.

    L'issue demande « la valeur actuelle, la valeur 7 jours plus tot ». La
    reference se lit donc dans l'**historique des publications**, et non
    dans la derniere : une publication declenchee par un changement de
    valeur peut dater de la veille, et s'y fier daterait la reference d'un
    jour faux — le verdict `RECULE`/`AVANCE` porterait alors sur un
    intervalle de 24 h au lieu de 7 jours.

    Regle : on retient la publication la plus recente **dotee d'au moins
    sept jours**. Tant qu'aucune publication n'a cet age, la fonction ne
    rend RIEN : l'appelant garde alors la reference de l'issue (la
    valeur mesuree il y a sept jours, publiee dans l'issue elle-meme).

    Le repli sur « la plus ancienne publication » serait tentant, et
    faux : il remplacerait la reference de sept jours par une valeur de
    la veille, et le verdict porterait sur un intervalle d'un jour au
    lieu de sept. L'intervalle de mesure fait partie de la mesure.

    La valeur se lit dans la colonne `valeur` du commentaire ; la date est
    celle de la PUBLICATION (la colonne `reference` du commentaire, elle,
    date la reference de la reference).

    Un commentaire absent ou illisible donne `None` — c'est une absence de
    MESURE, pas une reference nulle.
    """
    commentaires = _commentaires_marques(issue)
    if not commentaires:
        return None
    reference = now or dt.datetime.now(dt.UTC)
    # L'eligibilite se joue sur le JOUR, pas sur l'horodatage : avec une
    # cadence quotidienne, un decalage de quelques minutes ferait basculer
    # la reference d'un jour, en silence.
    seuil = (reference - dt.timedelta(days=7)).date()
    eligible = [d for d in commentaires
                if (_date_iso(d.get("created_at")) or reference).date() <= seuil]
    if not eligible:
        return None
    choisi = eligible[-1]
    body = choisi.get("body") or ""
    for ligne in body.splitlines():
        m = _LIGNE_TABLE.match(ligne)
        if not m or m.group("cle") != cle:
            continue
        cellules = [c.strip() for c in ligne.strip().strip("|").split("|")]
        if len(cellules) < 3:
            continue
        try:
            valeur = float(cellules[2].replace(",", ".").split()[0])
        except Exception:  # noqa: BLE001 - valeur illisible
            continue
        date = (choisi.get("created_at") or "")[:10]
        return Reference(valeur, date, "commentaire publie",
                         instrument=identite_du_commentaire(body, cle))
    return None


def _date_iso(texte: str | None) -> dt.datetime | None:
    """Un timestamp GitHub (`2026-10-28T20:00:00Z`) en datetime UTC."""
    if not texte:
        return None
    try:
        return dt.datetime.fromisoformat(texte.replace("Z", "+00:00"))
    except Exception:  # noqa: BLE001 - date illisible
        return None


def dernier_commentaire_issue(issue: int) -> dict | None:
    """Le dernier commentaire `ANTI-ENTROPY-REGISTER` de l'issue (brut)."""
    commentaires = _commentaires_marques(issue)
    return commentaires[-1] if commentaires else None


def _commande_affichee(commande) -> str:
    """La commande telle qu'elle est affichee dans le commentaire publie.

    L'instrument s'execute avec `sys.executable` (l'interpreteur qui
    tourne), mais le commentaire est **public** : y afficher le chemin
    absolu de l'interpreteur publie une empreinte de la machine
    (`C:\\Python314\\python.exe`). On affiche donc `python`.
    """
    mots = []
    for mot in commande:
        mot = str(mot)
        if mot == sys.executable:
            mot = "python"
        mots.append(mot)
    return " ".join(mots)


def commentaire_du_jour(entrees: list[dict], mesure_le: str) -> str:
    """Le corps du commentaire balise.

    Le format est impose par l'issue : **valeur actuelle**, **valeur 7
    jours plus tot**, et **verdict**. Le marqueur est un HTML comment :
    il se retrouve par une recherche exacte, et il ne pollue pas la lecture.
    """
    lignes = [
        f"<!-- {MARQUEUR} -->",
        "",
        "**Registre anti-entropie — mesure du " + mesure_le + "**",
        "",
        "| entree | issue | valeur | reference (7 j) | sens | verdict | instrument |",
        "|---|---|---:|---:|---|---|---|",
    ]
    for e in entrees:
        if e.get("erreur"):
            ref = "—"
        elif e.get("reference") is None:
            ref = "— (pas de reference)"
        elif e.get("comparaison_suspendue"):
            ref = (f"{_fmt(e['reference']['valeur'])} "
                   f"(rebascage {e['reference']['mesure_le']})")
        else:
            ref = f"{_fmt(e['reference']['valeur'])} ({e['reference']['mesure_le']})"
        lignes.append(
            f"| `{e['cle']}` | #{e['issue']} | {_fmt(e.get('valeur'))} | {ref} "
            f"| {e.get('sens')} | **{e.get('verdict')}** | "
            f"{e.get('instrument') or '—'} |")
    lignes += ["", "Instrument, sens et cible de chaque entree :", ""]
    for e in entrees:
        detail = (f"- `{e['cle']}` (#{e['issue']}) — {e['titre']} : "
                  f"`{_commande_affichee(e['commande'])}`")
        detail += f" — sens {e.get('sens')}, cible {_fmt(e.get('cible'))}"
        if e.get("instrument"):
            detail += f" — instrument `{e['instrument']}`"
        if e.get("alignement"):
            detail += f" — arbre : {e['alignement']}"
        if e.get("fenetre"):
            detail += f" — **{e['fenetre']}**"
        if e.get("erreur"):
            detail += f" — **INSTRUMENT ILLEGIBLE** : {e['erreur']}"
        elif e.get("non_comparable"):
            detail += f" — **comparaison refusee** : {e['non_comparable']}"
        elif e.get("note"):
            detail += f" — {e['note']}"
        lignes.append(detail)
    # La SERIE a instrument constant : elle porte la reponse a la question
    # que le verdict de sept jours ne peut plus poser — « le chantier
    # recule-t-il ? ». Elle est ce qui rend le controle positif de l'issue
    # VIF : il s'exerce sur des mesures reelles, groupees par l'instrument
    # qui les a produites, et non sur des constantes ecrites en dur.
    if any(e.get("serie") for e in entrees):
        lignes += ["", "**Serie a instrument constant** — chaque groupe est "
                  "l'ensemble des valeurs produites par le MEME instrument ; "
                  "a instrument constant, la valeur se compare.", "",
                  "| entree | instrument | points | tendance |",
                  "|---|---|---|---|"]
        for e in entrees:
            for groupe in e.get("serie") or []:
                points = " → ".join(
                    f"{_fmt(p['valeur'])} ({p['date'][:10]})"
                    for p in groupe["points"])
                lignes.append(
                    f"| `{e['cle']}` | `{groupe['instrument']}` | {points} "
                    f"| **{groupe['tendance']}** |")
    lignes += [
        "",
        ("Le progres se lit a la **valeur** de l'instrument, jamais au nombre "
        "de PRs qui citent l'issue."),
        "",
        ("L'**identite de l'instrument** est portee avec la valeur : deux "
        "valeurs ne sont comparables que si le meme instrument les a "
        "produites. Une reference produite par un autre instrument est "
        "refusee — le verdict affiche alors `INSTRUMENT ILLEGIBLE` plutot "
        "que de comparer des grandeurs qui ne se mesurent pas l'une comme "
        "l'autre."),
        "",
        ("La **serie a instrument constant** est publiee en regard : c'est la "
         "seule comparaison qui se defend quand l'instrument a change. "
         "Elle porte la tendance de chaque groupe — c'est la que se lit "
         "le controle positif de l'issue (le padding rend `RECULE` a "
         "instrument constant)."),
        "",
        ("L'**arbre mesure** est nomme avec la valeur : un instrument qui "
         "prend sa liste de fichiers dans une revision et lit leur contenu "
         "dans l'arbre local ne mesure l'arbre nomme que si le checkout EST "
         "sur cette revision. Sinon la mesure est refusee (`INSTRUMENT "
         "ILLEGIBLE`) — un melange de deux arbres ne porte pas de verdict."),
    ]
    return "\n".join(lignes) + "\n"


def _fmt(valeur) -> str:
    if valeur is None:
        return "—"
    if isinstance(valeur, float) and valeur.is_integer():
        return str(int(valeur))
    return str(valeur)


# ---------------------------------------------------------------------------
# La publication
# ---------------------------------------------------------------------------

def due_pour_publier(dernier: dict | None, entrees: list[dict], now: dt.datetime,
                      jours_fraicheur: float = 1.0) -> tuple[bool, str]:
    """Faut-il publier ?

    Le mandat dit « l'organe publie son commentaire a chaque cycle, et les
    verdicts `STAGNE` et `RECULE` sont servis ou dispatches nomment dans le
    cycle qui les lit ». Un registre qui ne se republie que tous les sept
    jours masquerait un `RECULE` pendant une semaine : le verdict serait
    lu dans un cycle qui ne l'a pas observe.

    D'ou la regle : on publie au plus une fois par jour et par issue, et
    des que la valeur a bouge. Ce qui rend la publication idempotente
    dans la journee (deux passages du meme cycle ne commentent pas deux
    fois) tout en gardant le verdict lisible le jour ou il apparait.
    """
    if not dernier:
        return True, "premiere publication"
    try:
        date = dt.datetime.fromisoformat(
            dernier.get("created_at") or "")
    except Exception:  # noqa: BLE001 - date illisible = on republie
        return True, "date du dernier commentaire illisible"
    age = (now - date).total_seconds() / 86400.0
    if age >= jours_fraicheur:
        return True, f"dernier commentaire vieux de {age:.2f} j"
    # La valeur a-t-elle bouge depuis le dernier commentaire ?
    for e in entrees:
        ligne = _valeur_du_commentaire(dernier.get("body") or "", e["cle"])
        if ligne is None:
            return True, f"valeur de `{e['cle']}` absente du dernier commentaire"
        if e.get("valeur") is not None and abs(ligne - e["valeur"]) > 1e-9:
            return True, f"valeur de `{e['cle']}` changee ({_fmt(ligne)} -> {_fmt(e['valeur'])})"
    return False, f"rien n'a bouge et le dernier commentaire a {age:.2f} j"


def _valeur_du_commentaire(body: str, cle: str) -> float | None:
    for ligne in body.splitlines():
        m = _LIGNE_TABLE.match(ligne)
        if not m or m.group("cle") != cle:
            continue
        cellules = [c.strip() for c in ligne.strip().strip("|").split("|")]
        if len(cellules) < 3:
            return None
        try:
            return float(cellules[2].replace(",", ".").split()[0])
        except Exception:  # noqa: BLE001
            return None
    return None


def publier(issue: int, corps: str, dry_run: bool = False) -> bool:
    """Poste le commentaire balise sur l'issue. Rend `True` si poste.

    Deux garde-fous de publication, tous deux issus d'incidents mesures :

      * **l'identite est epinglee** (`GH_TOKEN` sous le compte `jsboige`) :
        le trousseau `gh` de la machine est partage et le compte actif
        bascule ; une ecriture faite sous le mauvais compte n'est plus
        levable par le coordinateur. Si l'identite ne peut pas etre
        etablie (ni jeton resolvable, ni compte actif verifie), l'organe
        **refuse** de publier : il prefere un cycle sans publication a une
        publication sous une identite inconnue.
      * **le corps vient d'un fichier** (`--body-file`), jamais de `-f
        body=@fichier` : le prefixe `@` n'est expandu que par `-F`, et
        l'echec est SILENCIEUX (le corps atterrit litteral). Le fichier est
        un **temporaire** : un nom fixe laisse des debris quand `TEMP` est
        absent, et se fait ecraser par une execution concurrente.
    """
    if dry_run:
        return False
    token = _token_gh()
    env = dict(os.environ)
    if token:
        env["GH_TOKEN"] = token
    elif _compte_actif_gh() != COMPTE_EPINGLE:
        # L'identite n'est PAS etablie : le trousseau `gh` de la machine
        # est partage et le compte actif bascule. Publier sous une identite
        # non verifiee, c'est publier sous le mauvais compte -- et une
        # reserve levee par le mauvais compte n'est pas leveable par le
        # coordinateur. On refuse (fail-CLOSED) plutot que publier muet.
        print(f"IDENTITE NON EPINGLEE : ni jeton '{COMPTE_EPINGLE}' ni "
              f"compte actif '{COMPTE_EPINGLE}' -- publication refusee.",
              file=sys.stderr)
        return False
    # Le payload est un fichier TEMPORAIRE : un nom fixe dans `TEMP` laisse
    # des debris quand `TEMP` est absent (Linux), et se fait ecraser par
    # une execution concurrente (organe cron + relance manuelle) entre
    # l'ecriture et le POST.
    fd, chemin = tempfile.mkstemp(prefix="anti_entropy_", suffix=".md")
    payload = pathlib.Path(chemin)
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as fh:
            fh.write(corps)
        out = subprocess.run(["gh", "issue", "comment", str(issue), "--repo", REPO,
                              "--body-file", str(payload)],
                             capture_output=True, text=True, encoding="utf-8",
                             timeout=120, check=False, env=env)
    except Exception:  # noqa: BLE001 - l'ecriture du payload a echoue
        return False
    finally:
        try:
            payload.unlink(missing_ok=True)
        except Exception:  # noqa: BLE001, S110 - le fichier temporaire reste, sans consequence
            pass
    if out.returncode != 0:
        return False
    return _verifier_publication(issue, corps,
                                 _identifiant_commentaire(out.stdout))


def _identifiant_commentaire(sortie: str) -> int | None:
    """L'identifiant du commentaire publie, lu dans la sortie du POST.

    `gh issue comment` rend l'URL du commentaire qu'il vient de creer :
    `https://github.com/<repo>/issues/<n>#issuecomment-<id>`. Cet
    identifiant permet une relecture **exacte** du commentaire publie,
    sans parcourir le fil — donc sans dependre du nombre de commentaires
    de l'issue. `None` quand la sortie ne porte pas d'URL : la relecture
    retombe alors sur la lecture paginee du fil.
    """
    trouve = re.search(r"issuecomment-(\d+)", sortie or "")
    if not trouve:
        return None
    return int(trouve.group(1))


def _token_gh() -> str:
    """Le jeton `gh` du compte de la flotte, ou vide si introuvable."""
    try:
        raw = subprocess.run(["gh", "auth", "token", "--user", COMPTE_EPINGLE],
                             capture_output=True, text=True, encoding="utf-8",
                             timeout=60, check=False)
    except Exception:  # noqa: BLE001 - pas de jeton = on verifie l'identite autrement
        return ""
    if raw.returncode != 0:
        return ""
    return (raw.stdout or "").strip()


def _compte_actif_gh() -> str:
    """Le compte `gh` actif, ou vide si la lecture echoue.

    C'est le **repli** de l'identite : quand le jeton du compte de la
    flotte n'est pas resolvable, on verifie que le compte actif EST ce
    compte. Une identite non verifiable ne publie rien.
    """
    try:
        raw = subprocess.run(["gh", "api", "user", "--jq", ".login"],
                             capture_output=True, text=True, encoding="utf-8",
                             timeout=60, check=False)
    except Exception:  # noqa: BLE001 - identite illisible
        return ""
    if raw.returncode != 0:
        return ""
    return (raw.stdout or "").strip()


def _verifier_publication(issue: int, corps: str,
                          identifiant: int | None = None) -> bool:
    """Relire le corps PUBLIE et verifier deux predicats.

    1. **longueur** : un corps < 100 caracteres apres une publication depuis
       un fichier = le piege `-f body=@` a tire ;
    2. **structure** : le corps publie ne doit pas parser en objet JSON
       portant une cle `body` — c'est le payload JSON complet passe comme
       corps, et la garde de longueur est structurellement aveugle a ce cas.

    La relecture se fait **par identifiant de commentaire** quand on le
    sait : `gh issue comment` rend l'URL du commentaire publie, qui porte
    son `id`. Relire exactement CE commentaire dispense de parcourir le
    fil et rend la relecture insensible au volume de commentaires de
    l'issue.

    **Sans identifiant**, on retombe sur une lecture du fil, et cette
    lecture **pagine** : `.[-10:]` sans `--paginate` selectionne les dix
    derniers elements de la **premiere page** — sur une issue de plus de
    trente commentaires, notre publication recente n'y est pas, et une
    publication reelle est declaree en echec. On collecte donc toutes les
    pages avant de selectionner.

    Dans les deux cas, on cherche le commentaire **balise** et non « le
    dernier commentaire » : le fil est actif et plusieurs lanes y
    ecrivent, donc un commentaire tiers arrive entre le POST et la
    relecture. Lire `last` produirait un faux echec — et un cliquet
    avance sur une publication reelle mais non verifiee.
    """
    if identifiant is not None:
        return _verifier_par_identifiant(identifiant, corps)
    try:
        raw = subprocess.run(
            ["gh", "api", f"repos/{REPO}/issues/{issue}/comments",
             "--paginate", "--jq", ".[-10:] | map({body, created_at})"],
            capture_output=True, text=True, encoding="utf-8", timeout=120,
            check=False)
    except Exception:  # noqa: BLE001 - relecture impossible = publie quand meme
        print("RELECTURE IMPOSSIBLE : publication non verifiee", file=sys.stderr)
        return True
    if raw.returncode != 0:
        print("RELECTURE IMPOSSIBLE : publication non verifiee", file=sys.stderr)
        return True
    commentaires = _pages_json(raw.stdout)
    if not commentaires:
        print("RELECTURE ILLISIBLE : publication non verifiee", file=sys.stderr)
        return True
    marques = [c for c in commentaires
               if isinstance(c, dict) and MARQUEUR in (c.get("body") or "")]
    if not marques:
        return False
    publie = marques[-1].get("body") or ""
    return _corps_conforme(publie, corps)


def _verifier_par_identifiant(identifiant: int, corps: str) -> bool:
    """Relire le commentaire PUBLIE par son identifiant exact.

    C'est la voie sans pagination : on lit le commentaire que le POST a
    designe, pas « les derniers commentaires de l'issue ». Un fil de plus
    de trente commentaires, ou un commentaire tiers intercale entre le
    POST et la relecture, ne peuvent plus faire echouer une publication
    reelle.
    """
    try:
        raw = subprocess.run(
            ["gh", "api", f"repos/{REPO}/issues/comments/{identifiant}",
             "--jq", "{body, created_at}"],
            capture_output=True, text=True, encoding="utf-8", timeout=120,
            check=False)
    except Exception:  # noqa: BLE001 - relecture impossible = publie quand meme
        print("RELECTURE IMPOSSIBLE : publication non verifiee", file=sys.stderr)
        return True
    if raw.returncode != 0:
        print("RELECTURE IMPOSSIBLE : publication non verifiee", file=sys.stderr)
        return True
    commentaires = _pages_json(raw.stdout)
    if not commentaires:
        print("RELECTURE ILLISIBLE : publication non verifiee", file=sys.stderr)
        return True
    publie = commentaires[-1].get("body") or ""
    return _corps_conforme(publie, corps)


def _corps_conforme(publie: str, corps: str) -> bool:
    """Le corps publie est-il bien le notre, et conforme aux deux
    predicats de transport (longueur, structure JSON) ?"""
    if publie.strip() != corps.strip():
        return False
    if len(publie) < 100:
        return False
    try:
        parse = json.loads(publie)
    except Exception:
        parse = None
    if isinstance(parse, dict) and isinstance(parse.get("body"), str):
        return False
    return True


# ---------------------------------------------------------------------------
# L'etat (lu par le cliquet du budget de creation)
# ---------------------------------------------------------------------------

def ecrire_etat(etat: dict, chemin: str | None = None) -> pathlib.Path:
    p = pathlib.Path(chemin or os.environ.get(ENV_ETAT, "") or chemin_etat_defaut())
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(etat, ensure_ascii=False, indent=2) + "\n",
                 encoding="utf-8")
    return p


def _chemin_etat(chemin: str | None = None) -> pathlib.Path:
    """Le chemin de l'etat SANS l'ecrire.

    Un `--dry-run` qui ecrit l'etat a un effet de bord mesurable : l'etat
    est l'ENTREE du cliquet du budget de creation (#23174), et l'ecrire
    c'est activer ou desactiver la retenue, sans que le lecteur sache qu'il
    a agi. Le dry-run mesure et affiche ; il n'ecrit rien.
    """
    return pathlib.Path(chemin or os.environ.get(ENV_ETAT, "") or chemin_etat_defaut())


def lire_etat(chemin: str | None = None) -> dict:
    p = pathlib.Path(chemin or os.environ.get(ENV_ETAT, "") or chemin_etat_defaut())
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except Exception:  # noqa: BLE001 - etat illisible = pas de cliquet
        return {}
    return data if isinstance(data, dict) else {}


# ---------------------------------------------------------------------------
# Le cycle
# ---------------------------------------------------------------------------

def mesurer_tout(registre: tuple[Entree, ...] = REGISTRE,
                 issue_filtre: int | None = None,
                 now: dt.datetime | None = None) -> list[dict]:
    """Mesure toutes les entrees, avec leur reference et leur verdict.

    `now` est l'instant de la mesure : il sert a choisir la reference
    (la publication dotee d'au moins sept jours). Le caller doit passer
    le MEME instant que celui qu'il affiche dans le commentaire — sinon
    la reference annoncee et la reference appliquee divergent.
    """
    reference = now or dt.datetime.now(dt.UTC)
    out = []
    for entree in registre:
        if issue_filtre and entree.issue != issue_filtre:
            continue
        valeur, erreur, note = mesurer(entree, maintenant=reference)
        identite = identite_instrument(entree.commande)
        aligne, motif_alignement = arbre_aligne(entree.commande, entree.arbre)
        ref = lire_reference(entree.issue, entree.cle, now=reference)
        origine_reference = "publication" if ref is not None else ""
        non_comparable = ""
        if not aligne:
            # La mesure ne mesure pas l'arbre qu'elle nomme : elle est
            # refusee, reference comprise. Une valeur publiee dans ces
            # conditions decrirait un melange de deux arbres.
            non_comparable = f"mesure refusee : {motif_alignement}"
            ref = None
        elif ref is not None and not comparables(identite, ref.instrument):
            # La reference vient d'une publication qui n'a pas ete mesuree
            # par l'instrument courant : la comparer fabriquerait un verdict
            # qui ne dit rien du depot. Elle est refusee, et le motif est
            # nomme -- un refus sans motif se lit comme une panne.
            non_comparable = (
                f"reference transverse refusee : la reference "
                f"{ref.valeur:g} (mesuree le {ref.mesure_le}) a ete "
                f"produite par `{ref.instrument or 'instrument d identite inconnue'}`, "
                f"l instrument courant est `{identite or 'instrument d identite inconnue'}`")
            ref = None
        if ref is None and aligne and entree.reference is not None:
            if comparables(identite, entree.reference.instrument):
                ref = entree.reference
                origine_reference = "rebase"
            elif not non_comparable:
                non_comparable = (
                    f"reference de repli incompatible : la reference "
                    f"{entree.reference.valeur:g} (mesuree le "
                    f"{entree.reference.mesure_le}) a ete produite par "
                    f"`{entree.reference.instrument or 'instrument d identite inconnue'}`, "
                    f"l instrument courant est `{identite or 'instrument d identite inconnue'}`")
        # La FENETRE de comparaison est un element de la mesure : pendant
        # la fenetre de rebasage, la reference n'est pas une publication de
        # sept jours, et le verdict porte sur un intervalle plus court. Un
        # lecteur qui ne le voit pas lit « STAGNE » comme « le chantier
        # n'a pas bouge depuis sept jours » -- c'est exactement le faux
        # « AVANCE » qu'on a corrige. Le marqueur est donc porte par la
        # mesure, la publication et l'etat ecrit.
        fenetre = ""
        comparaison_suspendue = False
        if ref is not None:
            if origine_reference == "rebase":
                ouverture = (dt.date.fromisoformat(ref.mesure_le)
                             + dt.timedelta(days=7)).isoformat()
                comparaison_suspendue = True
                fenetre = (f"comparaison de 7 j SUSPENDUE : reference de "
                           f"rebasage ({ref.mesure_le}, meme instrument, "
                           f"mesuree le jour du rebasage) ; elle s'ouvre le "
                           f"{ouverture}")
            else:
                fenetre = (f"comparaison de 7 j active (reference publiee "
                           f"le {ref.mesure_le})")
        # La SERIE a instrument constant : les points anterieurs declares
        # (avec leur source), les publications, et la mesure du jour. Elle
        # repond a la question que le verdict de sept jours ne peut plus
        # poser — « le chantier recule-t-il ? » — et elle est ce qui rend
        # le controle positif de l'issue VIF : il s'exerce sur des
        # mesures reelles, groupees par l'instrument qui les a produites.
        points_serie = [(h.mesure_le, h.valeur, h.source, h.instrument)
                        for h in entree.historique]
        if entree.reference is not None:
            points_serie.append((entree.reference.mesure_le,
                                 entree.reference.valeur,
                                 f"reference portee par l'entree "
                                 f"({entree.reference.source})",
                                 entree.reference.instrument))
        points_serie.extend(points_publies(entree.issue, entree.cle))
        if valeur is not None and aligne and not erreur:
            # Seule une mesure ACCEPTEE entre dans la serie : une mesure
            # refusee (arbre divergent, instrument muet) ne decrit rien et
            # ne se compare a rien.
            points_serie.append((reference.date().isoformat(), valeur,
                                 "mesure du jour", identite))
        serie = serie_par_instrument(entree.commande, entree.sens,
                                     points_serie)
        if valeur is None:
            verdict_final = "INSTRUMENT ILLEGIBLE"
        elif ref is None:
            verdict_final = ("INSTRUMENT ILLEGIBLE" if non_comparable
                             else "PREMIERE MESURE")
        else:
            verdict_final = verdict(valeur, ref.valeur, entree.sens)
        out.append({
            "cle": entree.cle,
            "issue": entree.issue,
            "titre": entree.titre,
            "commande": list(entree.commande),
            "sens": entree.sens,
            "cible": entree.cible,
            "valeur": valeur,
            "erreur": erreur,
            "note_mesure": note,
            "instrument": identite,
            "alignement": motif_alignement,
            "non_comparable": non_comparable,
            "fenetre": fenetre,
            "comparaison_suspendue": comparaison_suspendue,
            "reference": ({"valeur": ref.valeur,
                           "mesure_le": ref.mesure_le,
                           "source": ref.source,
                           "instrument": ref.instrument}
                          if ref else None),
            "serie": serie,
            "verdict": verdict_final,
        })
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Registre anti-entropie")
    ap.add_argument("--dry-run", action="store_true",
                    help="mesurer et afficher sans publier ni ecrire l'etat")
    ap.add_argument("--issue", type=int, default=None,
                    help="ne mesurer que cette issue")
    ap.add_argument("--json", default=None, help="ecrire le rapport JSON ici")
    ap.add_argument("--etat", default=None, help="chemin du fichier d'etat")
    args = ap.parse_args(argv)

    now = dt.datetime.now(dt.UTC)
    mesure_le = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    entrees = mesurer_tout(issue_filtre=args.issue, now=now)

    par_issue: dict[int, list[dict]] = {}
    for e in entrees:
        par_issue.setdefault(e["issue"], []).append(e)

    publies = []
    echecs = []
    for issue, lot in sorted(par_issue.items()):
        dernier = dernier_commentaire_issue(issue)
        due, motif = due_pour_publier(dernier, lot, now)
        corps = commentaire_du_jour(lot, mesure_le)
        poste = False
        echec = False
        if due:
            poste = publier(issue, corps, dry_run=args.dry_run)
            # Un echec de publication n'est pas « rien a publier » : la
            # chaine des references se lit dans les commentaires publies,
            # et une publication qui echoue en silence fait perdre la
            # fenetre de sept jours SANS que personne ne le voie.
            echec = not poste and not args.dry_run
            if echec:
                echecs.append(issue)
        publies.append({"issue": issue, "poste": poste, "echec": echec,
                        "motif": motif})

    etat = {
        "mesure_le": mesure_le,
        "entrees": {e["cle"]: {"issue": e["issue"], "valeur": e["valeur"],
                               "verdict": e["verdict"],
                               "instrument": e.get("instrument"),
                               "erreur": e["erreur"],
                               # La fenetre de comparaison, avec son motif :
                               # un lecteur de l'etat doit voir si la
                               # comparaison de sept jours est ACTIVE ou
                               # SUSPENDUE (fenetre de rebasage). Sans ce
                               # marqueur, « aucune retention » se lit
                               # comme « le chantier s'est ameneliore ».
                               "fenetre": e.get("fenetre"),
                               "comparaison_suspendue": e.get(
                                   "comparaison_suspendue", False),
                               "reference": e.get("reference")}
                    for e in entrees},
    }
    chemin = ecrire_etat(etat, args.etat) if not args.dry_run else _chemin_etat(args.etat)

    for e in entrees:
        print(f"{e['cle']:<22} #{e['issue']:<6} valeur="
              f"{_fmt(e.get('valeur')):>6}  reference="
              f"{_fmt((e.get('reference') or {}).get('valeur')):>6}  "
              f"verdict={e['verdict']}"
              + (f"  ERREUR: {e['erreur']}" if e.get("erreur") else ""))
    for p in publies:
        if p["poste"]:
            etat_publication = "commentaire publie"
        elif p.get("echec"):
            etat_publication = f"ECHEC de publication — {p['motif']}"
        elif args.dry_run:
            etat_publication = "publie (dry-run)"
        else:
            etat_publication = f"pas de publication — {p['motif']}"
        print(f"issue #{p['issue']} : {etat_publication}")
    print(f"etat ecrit : {chemin}" if not args.dry_run
          else f"etat NON ecrit (dry-run) : {chemin}")

    if args.json:
        pathlib.Path(args.json).write_text(
            json.dumps({"mesure_le": mesure_le, "entrees": entrees,
                        "publications": publies}, ensure_ascii=False,
                       indent=2, default=str) + "\n", encoding="utf-8")
    # Un echec de publication est un ECHEC du cycle : la reference se lit
    # dans les commentaires publies, et une publication qui echoue en
    # silence fait perdre la fenetre de sept jours sans que personne ne le
    # voie. L'etat reste ecrit (le verdict est mesure, independamment de
    # la publication) — mais le code de sortie le dit.
    if echecs:
        print(f"ECHEC de publication sur {len(echecs)} issue(s) : "
              f"{', '.join('#' + str(i) for i in echecs)}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
