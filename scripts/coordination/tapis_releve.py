#!/usr/bin/env python3
"""LE RELEVE persistant par issue : la preuve qu'un fil a ete lu ENTIEREMENT.

Mandat du coordinateur (19/11/2026, DM `coord2108-picker-decision`) :
« Couverture : enregistrer date, version du fil lu et verdict apres lecture
integrale ; sans preuve = inconnu. » et, dans le meme arbitrage :
« Une livraison enfant date son parent, pas son frere ; elle ne vaut lecture
d'aucun fil. »

Deux etats, deux sections, jamais confondus :

- la **cle de service** (`coordination.tapis_cle`) est datee par une
  **livraison** : elle classe le tirage ;
- le **releve** est date par une **lecture** : il prouve qu'un fil a ete lu
  entierement, et avec quel verdict.

Une livraison ne vaut jamais lecture : un `[DELIVERED]` ne cree aucun releve,
et un releve ne date aucune cle. Un releve absent vaut **INCONNU**
(fail-CLOSED) : ni « lu », ni « non lu ».

La section `service` porte, elle, la **livraison confirmee par son diff** :
la date de creation de la PR dont le diff couvre le perimetre declare. C'est
la « derniere PR **pertinente** » du mandat, et elle ne remplace la cle
candidate (`tapis_cle`) que lorsqu'elle existe : le classement lit
**confirme > candidat > creation**, dans cet ordre.

Le store est local a la machine (LOCALAPPDATA), comme l'etat d'ancre
(`coordination.tapis_etat`) : l'etat d'un tirage n'a rien de versionnable
dans le depot. Un store absent ou illisible vaut **INCONNU** pour tout.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

from coordination.tapis_marqueurs import evenements

ENV_RELEVE = "COURSIA_TAPIS_RELEVE_DIR"

#: Le verdict d'un fil lu et servable.
SERVIABLE = "SERVIABLE"

#: Les deux sections du store.
RELEVE = "releve"
SERVICE = "service"


def chemin_releve() -> Path:
    """Le store du releve (LOCALAPPDATA par defaut)."""
    base = os.environ.get(ENV_RELEVE) or os.environ.get("LOCALAPPDATA")
    racine = Path(base) if base else Path.home() / ".coursia"
    return racine / "CoursIA" / "tapis_releve" / "releve.json"


def _vide() -> dict:
    return {RELEVE: {}, SERVICE: {}}


def empreinte(commentaires: list[dict] | None) -> str:
    """L'empreinte du fil : elle change des que le fil change.

    Elle porte le **dernier** commentaire (identifiant, date, queue du corps) :
    un fil qui ne recoit rien garde la meme empreinte, un fil qui avance
    change.
    """
    liste = list(commentaires or [])
    if not liste:
        return "00000000"
    dernier = liste[-1]
    graine = "%s|%s|%s" % (
        dernier.get("id") or dernier.get("databaseId") or "",
        dernier.get("createdAt") or dernier.get("created_at") or "",
        (dernier.get("body") or "")[-400:])
    return hashlib.sha1(graine.encode("utf-8")).hexdigest()[:8]


def version_fil(commentaires: list[dict] | None) -> str:
    """La version du fil lu : `c<nb de commentaires>@<empreinte>`."""
    liste = list(commentaires or [])
    return "c%d@%s" % (len(liste), empreinte(liste))


def lire() -> dict:
    """Le store normalise ; absent ou illisible = inconnu (fail-CLOSED)."""
    etat = _vide()
    try:
        brut = json.loads(chemin_releve().read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return etat
    if not isinstance(brut, dict):
        return etat
    for section in (RELEVE, SERVICE):
        bloc = brut.get(section)
        if isinstance(bloc, dict):
            etat[section] = {k: v for k, v in bloc.items() if isinstance(v, dict)}
    return etat


def ecrire(etat: dict) -> Path:
    """Persiste le store (une ecriture atomique)."""
    chemin = chemin_releve()
    chemin.parent.mkdir(parents=True, exist_ok=True)
    corps = {section: {str(k): v for k, v in (etat.get(section) or {}).items()}
             for section in (RELEVE, SERVICE)}
    tmp = chemin.with_suffix(".tmp")
    tmp.write_text(json.dumps(corps, ensure_ascii=False, indent=1) + "\n",
                   encoding="utf-8")
    tmp.replace(chemin)
    return chemin


def enregistrer(numero: int, version: str, verdict: str, lane: str = "",
                lu_le: str = "") -> dict:
    """Enregistre le releve d'un fil lu integralement (date, version, verdict)."""
    etat = lire()
    entree = {"version": version, "empreinte": version.split("@")[-1],
              "verdict": verdict, "lane": lane}
    if lu_le:
        entree["lu_le"] = lu_le
    etat[RELEVE][str(int(numero))] = entree
    ecrire(etat)
    return entree


def enregistrer_service(numero: int, date: str, origine: str, pr: int) -> dict:
    """Enregistre la livraison CONFIRMEE par le diff (la cle de service)."""
    etat = lire()
    entree = {"date": date, "origine": origine, "pr": int(pr)}
    etat[SERVICE][str(int(numero))] = entree
    ecrire(etat)
    return entree


def service_connue() -> dict:
    """Les livraisons confirmees par le diff, par numero d'issue."""
    sortie = {}
    for cle, entree in (lire()[SERVICE] or {}).items():
        date = (entree or {}).get("date")
        if not date:
            continue
        try:
            numero = int(cle)
        except (TypeError, ValueError):
            continue
        sortie[numero] = (date, (entree or {}).get("origine") or "diff")
    return sortie


def relever(numero: int) -> dict | None:
    """Le releve d'un issue, ou None (inconnu)."""
    return lire()[RELEVE].get(str(int(numero)))


def service(numero: int) -> dict | None:
    """La livraison confirmee par le diff d'un issue, ou None."""
    return lire()[SERVICE].get(str(int(numero)))


def connu(numero: int) -> bool:
    """Le fil de cet issue a-t-il ete lu integralement, au moins une fois ?"""
    return relever(numero) is not None


def pr_livree(comments: list[dict] | None) -> int | None:
    """La PR designee par le dernier marqueur [DELIVERED] du fil.

    L'import de `tapis_diff` est **local** : ce module tire `gh_bulk`, qui
    tire `tapis_cle`, qui tire ce module -- un import au niveau du module
    fermerait la boucle.
    """
    from coordination.tapis_diff import pr_designee
    livres = [e for e in evenements(comments or []) if e.marque == "DELIVERED"]
    if not livres:
        return None
    return pr_designee("[%s] %s" % (livres[-1].marque, livres[-1].reste))


def noter(numero: int, fil: list[dict] | None, code: str | None,
          lane: str = "", par_pr: dict | None = None) -> dict | None:
    """Enregistre le releve d'un fil lu, et la livraison qu'il confirme.

    Le releve porte la version du fil lu et le verdict. La livraison
    **confirmee par le diff** (verdict `LIVREE`) porte, elle, la date de
    creation de la PR designee : c'est elle qui est **pertinente** pour le
    classement (arbitrage du 19/11). Une livraison qui n'est pas confirmee
    n'est pas enregistree : le candidat, lui, reste dans `tapis_cle`.
    """
    version = version_fil(fil)
    enregistrer(numero, version, code or SERVIABLE, lane)
    if code != "LIVREE":
        return None
    num = pr_livree(fil or [])
    pr = (par_pr or {}).get(num or -1)
    if pr is None or not pr.get("created_at"):
        return None
    return enregistrer_service(numero, pr["created_at"],
                               "PR #%s (diff couvre)" % num, num)


def etat(releves: dict, numero: int) -> dict:
    """Le releve d'un grain : connu (version + verdict) ou inconnu."""
    r = releves.get(str(numero)) or {}
    return {"connu": bool(r), "version": r.get("version"),
            "verdict": r.get("verdict"), "lu_le": r.get("lu_le")}


def servable(numero: int, empreinte_courante: str) -> bool:
    """Le releve tient-il encore ?

    Oui si le fil a ete lu, si le verdict etait SERVIABLE, et si le fil n'a pas
    bouge depuis : l'empreinte du fil actuel est celle du releve. Un fil qui a
    change rend le releve caduc -- l'issue redevient INCONNUE.
    """
    r = relever(numero)
    if not r:
        return False
    if r.get("verdict") != SERVIABLE:
        return False
    return bool(empreinte_courante) and r.get("empreinte") == empreinte_courante
