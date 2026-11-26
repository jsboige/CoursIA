#!/usr/bin/env python3
"""Mesure du critere de succes du plan « CI a deux etages » (#25510).

Le body de #25510 pose l'indicateur qui decide de la bascule P4 : « la plupart
des PRs approuvees mergent **dans les 24 h** qui suivent l'APPROVE. Indicateur :
la part mergee sous 24 h, et le p90. »

Aucun organe ne le mesurait. Les releves periodiques de #22937 mesurent la
file, les ordonnanceurs, le parc et les durees de run, et disent explicitement
ne pas mesurer « le debit de merges » ; `measure_ci_two_tier.py` mesure le cout
des runs, pas le delai de merge. Ce module produit la mesure manquante.

Le point de depart est l'APPROVE du coordinateur **a la tete exacte** : c'est
la regle de merge du depot (l'approbation de `myia-ai-01` porte sur la tete que
`merge_ready.py` fusionne, une approbation posee sur une tete anterieure ne
l'autorise pas). Une PR dont la seule approbation porte sur une tete
anterieure, ou qui n'a aucune approbation du coordinateur (fusion admin d'une
PR etudiante, fusion par un autre compte), est **comptee a part** : elle sort
du denominateur, elle n'est jamais comptee comme « lente ».

Usage :

    python scripts/ci/measure_approve_to_merge.py --depuis 2026-11-19
    python scripts/ci/measure_approve_to_merge.py --heures 168 --json --out .tmp/a2m.json
    python scripts/ci/measure_approve_to_merge.py --approuveur myia-ai-01 --max-prs 400
    python scripts/ci/measure_approve_to_merge.py --max-pages 20 --json

Lectures honnetes que le rapport porte lui-meme :

- la fenetre se lit sur `merged_at` (pas `updated_at`) ;
- `--max-prs` borne le nombre de PRs dont les revues sont lues ; si la fenetre
  en contient davantage, le champ `tronquee` le dit et `inspectees` donne le
  compte reellement mesure -- une part calculee sur un echantillon tronque
  n'est pas la part de la fenetre ;
- sans aucune PR a tete exacte, la part vaut `null`, jamais 0 % : il n'y a pas
  de denominateur, et 0 % se lirait comme « aucune fusion rapide » ;
- la mesure des **fusionnees** ne voit pas une PR approuvee qui attend encore :
  la section « ouvertes approuvees » (sauf `--sans-ouvertes`) compte celles
  dont l'approbation a la tete exacte attend depuis plus que le seuil ;
- une approbation soumise **apres** la fusion sort du denominateur : elle ne
  peut pas etre la cause de la fusion, et le delai serait negatif -- un delai
  negatif compte « sous 24 h » gonflerait la part qu'on cherche a mesurer ;
- une approbation que l'approbateur fait suivre d'un `CHANGES_REQUESTED` sur
  la **meme tete** n'est plus en force : la PR fusionnee sort du denominateur
  (`approbation_retiree`), et une PR ouverte ainsi retiree n'attend pas un
  merge. Cote ouvert, la population est celle que la recherche GitHub liste
  sous `review:approved` (derniere decision de review) : ce filtre omet deja
  ces PRs, et la regle tient aussi sans lui ;
- les revues se lisent **page par page** : une page unique peut omettre
  l'approbation recente d'une PR tres commentee, et la PR serait alors classee
  « tete anterieure » a tort ;
- chaque lecture a un plafond de pages (`MAX_PAGES`, `--max-pages`). Atteint sur
  une page **pleine**, il laisse la lecture sans preuve d'avoir tout vu : la
  fenetre est alors declaree incomplete (`fenetre_complete: false`, et
  `tronquee: true`), et une PR dont les revues ne sont pas lues en entier sort
  du denominateur sous `revues_incompletes` -- jamais classee « tete
  anterieure » ou « sans approbation » sur un prefixe.

Lecture seule : aucune ecriture dans le depot, aucun secret (le jeton est lu
par ``gh auth token`` au premier appel, et n'est jamais imprime).
"""
from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone

REPO = "jsboige/CoursIA"
PAR_PAGE = 100
SEUIL_HEURES = 24.0
APPROUVEUR = "myia-ai-01"
MAX_PR_READ = 400
MAX_PAGES = 10
MAX_OPEN_READ = 60

_TOKEN: str | None = None


def jeton() -> str:
    """Jeton du compte de service, lu au premier appel (le module reste importable)."""
    global _TOKEN
    if _TOKEN is None:
        sortie = subprocess.run(
            ["gh", "auth", "token", "--user", "jsboige"],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=True,
        )
        _TOKEN = sortie.stdout.strip()
    return _TOKEN


def api(chemin: str, essais: int = 4):
    requete = urllib.request.Request(
        f"https://api.github.com{chemin}",
        headers={
            "Authorization": f"Bearer {jeton()}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "coursia-approve-to-merge-measure",
        },
    )
    pause = 3
    for tentative in range(essais):
        try:
            with urllib.request.urlopen(requete, timeout=90) as reponse:
                return json.loads(reponse.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            if exc.code in (403, 429) and tentative < essais - 1:
                time.sleep(pause)
                pause *= 2
                continue
            raise
    raise RuntimeError(chemin)


def parse_ts(valeur: str | None) -> datetime | None:
    """Horodatage ISO 8601 de l'API, toujours en UTC (suffixe `Z` ou offset)."""
    if not valeur:
        return None
    texte = valeur.strip()
    if texte.endswith("Z"):
        texte = texte[:-1] + "+00:00"
    moment = datetime.fromisoformat(texte)
    if moment.tzinfo is None:
        moment = moment.replace(tzinfo=timezone.utc)
    return moment.astimezone(timezone.utc)


def fusionnees(depuis: datetime, jusqu_a: datetime,
               max_pages: int = MAX_PAGES) -> tuple[list[dict], bool]:
    """PRs fusionnees dont `merged_at` tombe dans la fenetre, de la plus recente a la plus ancienne.

    Rend aussi la preuve que la fenetre a ete lue en entier. Elle manque dans un
    seul cas : le plafond `max_pages` est atteint sur une page pleine dont la
    plus ancienne `updated_at` reste dans la fenetre -- des fusions plus
    anciennes peuvent alors exister au-dela. La liste rendue n'est dans ce cas
    qu'un prefixe de la population, et `complete` vaut `False`.
    """
    trouvees: list[dict] = []
    complete = False
    for page in range(1, max_pages + 1):
        lot = api(
            f"/repos/{REPO}/pulls?state=closed&sort=updated&direction=desc"
            f"&per_page={PAR_PAGE}&page={page}")
        if not lot:
            complete = True
            break
        for pr in lot:
            fusionnee_le = parse_ts(pr.get("merged_at"))
            if fusionnee_le is None:
                continue
            if depuis <= fusionnee_le <= jusqu_a:
                trouvees.append(pr)
        # `updated_at` decroit le long des pages : la page suivante est plus ancienne.
        plus_ancienne = parse_ts(lot[-1].get("updated_at"))
        if plus_ancienne is not None and plus_ancienne < depuis:
            # Une fusion de la fenetre est mise a jour au plus tard a sa fusion :
            # rien d'elle ne peut se trouver sur une page plus ancienne.
            complete = True
            break
        if len(lot) < PAR_PAGE:
            complete = True
            break
    trouvees.sort(key=lambda pr: parse_ts(pr["merged_at"]), reverse=True)
    return trouvees, complete


def revues(numero: int, max_pages: int = MAX_PAGES) -> tuple[list[dict], bool]:
    """Toutes les revues d'une PR, page par page, et la preuve qu'elles ont ete lues en entier.

    Une page unique ne suffit pas : sur une PR tres commentee, l'approbation
    recente tombe sur une page suivante, et le classement conclurait alors
    « tete anterieure » ou « sans approbation » sur une PR pourtant approuvee a
    la tete exacte. La lecture suit les pages jusqu'a une page courte.

    La preuve manque quand le plafond `max_pages` est atteint sur une page
    pleine : les revues des pages suivantes n'ont pas ete lues, et elles
    peuvent porter l'approbation qui decide du classement. Rendues dans ce cas,
    elles ne sont qu'un prefixe, et `complete` vaut `False`.
    """
    lues: list[dict] = []
    for page in range(1, max_pages + 1):
        lot = api(f"/repos/{REPO}/pulls/{numero}/reviews"
                  f"?per_page={PAR_PAGE}&page={page}")
        if not lot:
            return lues, True
        lues.extend(lot)
        if len(lot) < PAR_PAGE:
            return lues, True
    return lues, False


def approbations(revues_lues: list[dict], approbateur: str) -> list[dict]:
    """Revues APPROVED de l'approbateur, dans l'ordre de soumission."""
    retenues = [
        revue for revue in revues_lues
        if str(revue.get("state", "")).upper() == "APPROVED"
        and (revue.get("user") or {}).get("login") == approbateur
        and parse_ts(revue.get("submitted_at")) is not None
    ]
    retenues.sort(key=lambda revue: parse_ts(revue["submitted_at"]))
    return retenues


def approbation_tete(revues_lues: list[dict], tete: str, approbateur: str,
                     avant: datetime | None = None) -> dict | None:
    """Derniere approbation de l'approbateur **en force** sur cette tete, ou None.

    `avant` borne la lecture a l'instant qu'elle ne peut pas depasser, celui de
    la fusion quand il s'agit d'une PR fusionnee : une approbation soumise
    **apres** la fusion ne peut pas en etre la cause, et n'a donc aucun delai a
    donner.

    Une approbation cesse d'etre en force quand l'approbateur demande lui-meme
    des changements sur la meme tete : la decision de review redevient
    « changements demandes », et la fusion n'attend plus le meme geste.
    Retenir l'approbation d'avant ce retrait daterait le point de depart d'un
    moment que la fusion ne suivait pas.
    """
    sur_la_tete = [
        revue for revue in revues_lues
        if revue.get("commit_id") == tete
        and (revue.get("user") or {}).get("login") == approbateur
        and parse_ts(revue.get("submitted_at")) is not None
    ]
    if avant is not None:
        sur_la_tete = [revue for revue in sur_la_tete
                       if parse_ts(revue["submitted_at"]) <= avant]
    sur_la_tete.sort(key=lambda revue: parse_ts(revue["submitted_at"]))
    en_force: dict | None = None
    for revue in sur_la_tete:
        etat = str(revue.get("state", "")).upper()
        if etat == "APPROVED":
            en_force = revue
        elif etat == "CHANGES_REQUESTED":
            en_force = None
    return en_force


def _classe_sans_approbation_en_force(revues_lues: list[dict], tete: str,
                                      approbateur: str) -> str:
    """Classe d'une PR dont aucune approbation n'est en force a sa tete.

    Trois cas seuls, et ils ne se confondent pas : l'approbateur a approuve
    cette tete puis l'a reprise (`approbation_retiree`) ; il n'a approuve
    qu'une tete anterieure (`tete_anterieure`) ; il n'a rien approuve du tout
    (`sans_approbation`).
    """
    if any(revue.get("commit_id") == tete for revue in approbations(revues_lues, approbateur)):
        return "approbation_retiree"
    return "tete_anterieure" if approbations(revues_lues, approbateur) else "sans_approbation"


def classer(pr: dict, revues_lues: list[dict], approbateur: str,
            revues_completes: bool = True) -> dict:
    """Classe une PR fusionnee : tete exacte, tete anterieure, sans approbation, ou revues incompletes.

    Sur des revues lues en prefixe (`revues_completes` faux), aucun classement
    n'est sur : ceux qui annoncent l'absence d'une approbation a la tete
    (« tete anterieure », « sans approbation ») seraient faux si les pages non
    lues en portaient une. La PR sort du denominateur sans etre classee.
    """
    if not revues_completes:
        return {"numero": pr["number"], "classe": "revues_incompletes", "heures": None}
    tete = (pr.get("head") or {}).get("sha") or ""
    fusionnee_le = parse_ts(pr.get("merged_at"))
    sur_la_tete = approbation_tete(revues_lues, tete, approbateur, avant=fusionnee_le)
    if sur_la_tete is not None:
        approuvee_le = parse_ts(sur_la_tete["submitted_at"])
        return {
            "numero": pr["number"],
            "classe": "tete_exacte",
            "heures": (fusionnee_le - approuvee_le).total_seconds() / 3600.0,
        }
    if approbation_tete(revues_lues, tete, approbateur) is not None:
        # Approbation en force sur cette tete, mais apres la fusion : la fusion
        # n'en est pas la consequence, et le delai serait negatif.
        return {"numero": pr["number"], "classe": "approbation_apres_fusion",
                "heures": None}
    return {"numero": pr["number"],
            "classe": _classe_sans_approbation_en_force(revues_lues, tete, approbateur),
            "heures": None}


def percentile(valeurs: list[float], p: float) -> float | None:
    """Percentile par rang le plus proche (pas d'interpolation : les valeurs sont des durees)."""
    if not valeurs:
        return None
    triees = sorted(valeurs)
    rang = max(1, math.ceil(p / 100.0 * len(triees)))
    return triees[rang - 1]


def resume(lignes: list[dict], seuil: float = SEUIL_HEURES) -> dict:
    """Agrege les lignes classees. Une part sans denominateur vaut None, jamais 0 %."""
    tete = [ligne["heures"] for ligne in lignes if ligne["classe"] == "tete_exacte"]
    sous_le_seuil = [heures for heures in tete if heures <= seuil]
    return {
        "tete_exacte": {
            "n": len(tete),
            "sous_le_seuil": len(sous_le_seuil),
            "part_sous_le_seuil": (len(sous_le_seuil) / len(tete)) if tete else None,
            "p50_heures": percentile(tete, 50),
            "p90_heures": percentile(tete, 90),
            "min_heures": min(tete) if tete else None,
            "max_heures": max(tete) if tete else None,
        },
        "tete_anterieure": sum(1 for ligne in lignes if ligne["classe"] == "tete_anterieure"),
        "approbation_retiree": sum(1 for ligne in lignes
                                   if ligne["classe"] == "approbation_retiree"),
        "approbation_apres_fusion": sum(1 for ligne in lignes
                                        if ligne["classe"] == "approbation_apres_fusion"),
        "revues_incompletes": sum(1 for ligne in lignes
                                  if ligne["classe"] == "revues_incompletes"),
        "sans_approbation": sum(1 for ligne in lignes if ligne["classe"] == "sans_approbation"),
    }


def ouvertes_approuvees(jusqu_a: datetime, approbateur: str = APPROUVEUR,
                        seuil: float = SEUIL_HEURES, max_ouvertes: int = MAX_OPEN_READ,
                        max_pages: int = MAX_PAGES) -> dict:
    """Cote censure du releve : les PRs ouvertes qu'une approbation attend.

    Une PR approuvee qui n'est pas encore fusionnee n'entre dans aucun
    denominateur de la mesure des fusionnees : un releve qui ne lirait que les
    merges serait bon par omission -- il suffirait de ne jamais fusionner les
    PRs lentes. Ici, la population est celle des PRs ouvertes approuvees
    (`review:approved`), et l'age se lit depuis l'approbation **a la tete
    exacte** : une approbation suivie d'un push est perimee, elle n'attend rien.

    Deux lectures honnetes que ce cote porte :

    - la population est celle que la **recherche GitHub** liste sous
      `review:approved`, c'est-a-dire la derniere decision de review. GitHub
      en detient la semantique ; `trouvees` est son `total_count`, et
      `tronquee` dit que seules `max_ouvertes` ont ete inspectees. Une PR dont
      l'approbateur a redemande des changements n'y figure pas -- et la regle
      de `approbation_tete` la retirerait de toute facon, donc l'accord des
      deux se mesure, il ne se suppose pas ;
    - une PR lue en entier dont l'approbation a la tete a ete reprise est
      comptee `approbation_retiree` : elle n'attend pas un merge.
    """
    cherche = api(f"/search/issues?q=repo:{REPO}+is:pr+is:open+review:approved"
                  f"&per_page={PAR_PAGE}")
    numeros = [item["number"] for item in cherche.get("items", [])][:max_ouvertes]
    lignes: list[dict] = []
    for numero in numeros:
        pr = api(f"/repos/{REPO}/pulls/{numero}")
        revues_lues, completes = revues(numero, max_pages)
        if not completes:
            lignes.append({"numero": numero, "classe": "revues_incompletes", "heures": None})
            continue
        tete = (pr.get("head") or {}).get("sha") or ""
        sur_la_tete = approbation_tete(revues_lues, tete, approbateur)
        if sur_la_tete is None:
            lignes.append({"numero": numero, "heures": None,
                           "classe": _classe_sans_approbation_en_force(
                               revues_lues, tete, approbateur)})
            continue
        approuvee_le = parse_ts(sur_la_tete["submitted_at"])
        lignes.append({"numero": numero, "classe": "tete_exacte",
                       "heures": (jusqu_a - approuvee_le).total_seconds() / 3600.0})
    ages = [ligne["heures"] for ligne in lignes if ligne["classe"] == "tete_exacte"]
    au_dela = sorted((ligne for ligne in lignes
                      if ligne["classe"] == "tete_exacte" and ligne["heures"] > seuil),
                     key=lambda ligne: ligne["heures"], reverse=True)
    return {
        "trouvees": cherche.get("total_count", len(numeros)),
        "inspectees": len(numeros),
        "tronquee": cherche.get("total_count", 0) > len(numeros),
        "revues_incompletes": sum(1 for ligne in lignes
                                  if ligne["classe"] == "revues_incompletes"),
        "approbations_retirees": sum(1 for ligne in lignes
                                     if ligne["classe"] == "approbation_retiree"),
        "a_la_tete_exacte": len(ages),
        "au_dela_du_seuil": len(au_dela),
        "plus_ancienne_heures": max(ages) if ages else None,
        "au_dela": au_dela,
    }


def mesurer(depuis: datetime, jusqu_a: datetime, approbateur: str = APPROUVEUR,
            max_prs: int = MAX_PR_READ, avec_ouvertes: bool = True,
            max_ouvertes: int = MAX_OPEN_READ, max_pages: int = MAX_PAGES) -> dict:
    """Mesure bornee : liste les PRs fusionnees de la fenetre, lit leurs revues, classe."""
    pool, fenetre_complete = fusionnees(depuis, jusqu_a, max_pages)
    inspectees = pool[:max_prs]
    lignes = []
    for pr in inspectees:
        revues_lues, completes = revues(pr["number"], max_pages)
        lignes.append(classer(pr, revues_lues, approbateur, revues_completes=completes))
    agregat = resume(lignes)
    rapport = {
        "fenetre": {"depuis": depuis.isoformat().replace("+00:00", "Z"),
                    "jusqu_a": jusqu_a.isoformat().replace("+00:00", "Z")},
        "approuveur": approbateur,
        "seuil_heures": SEUIL_HEURES,
        # Borne basse quand `fenetre_complete` est faux : la liste lue est un prefixe.
        "fusionnees_dans_la_fenetre": len(pool),
        "fenetre_complete": fenetre_complete,
        "inspectees": len(inspectees),
        "tronquee": len(pool) > len(inspectees) or not fenetre_complete,
        **agregat,
        "lignes": lignes,
    }
    if avec_ouvertes:
        rapport["ouvertes_approuvees"] = ouvertes_approuvees(
            jusqu_a, approbateur, SEUIL_HEURES, max_ouvertes, max_pages)
    return rapport


def _heures(valeur: float | None) -> str:
    return "-" if valeur is None else f"{valeur:.2f} h"


def _causes_troncature(rapport: dict) -> list[str]:
    """Raisons pour lesquelles la part ne vaut pas pour la fenetre entiere."""
    causes: list[str] = []
    if not rapport["fenetre_complete"]:
        causes.append("plafond de pages atteint sur une page pleine,"
                      " la fenetre n'est pas lue en entier")
    if rapport["fusionnees_dans_la_fenetre"] > rapport["inspectees"]:
        causes.append("--max-prs atteint, la part ne vaut que pour l'echantillon")
    return causes


def formater(rapport: dict) -> str:
    """Rendu lisible : les nombres d'abord, la lecture ensuite."""
    bloc = rapport["tete_exacte"]
    part = bloc["part_sous_le_seuil"]
    part_txt = "n/a (aucune PR a tete exacte)" if part is None else f"{part * 100:.1f} %"
    causes = _causes_troncature(rapport)
    lignes = [
        f"Fenetre {rapport['fenetre']['depuis']} -> {rapport['fenetre']['jusqu_a']}"
        f" (merged_at), approbateur {rapport['approuveur']},"
        f" seuil {rapport['seuil_heures']:.0f} h",
        f"Fusionnees dans la fenetre : {rapport['fusionnees_dans_la_fenetre']}"
        + ("" if rapport["fenetre_complete"] else " (borne basse)")
        + f" | inspectees : {rapport['inspectees']}"
        + ("  [TRONQUEE : " + " ; ".join(causes) + "]" if causes else ""),
        f"Tete exacte : {bloc['n']} PRs | sous le seuil : {bloc['sous_le_seuil']}"
        f" | part : {part_txt}",
        f"Delais tete exacte : p50 {_heures(bloc['p50_heures'])}"
        f" | p90 {_heures(bloc['p90_heures'])}"
        f" | min {_heures(bloc['min_heures'])} | max {_heures(bloc['max_heures'])}",
        f"Hors denominateur : {rapport['tete_anterieure']} approbation(s) sur tete anterieure"
        f" | {rapport['approbation_retiree']} reprise(s) sur la tete par l'approbateur"
        f" | {rapport['approbation_apres_fusion']} soumise(s) apres la fusion"
        f" | {rapport['sans_approbation']} sans approbation de l'approbateur"
        f" | {rapport['revues_incompletes']} a revues non lues en entier (plafond de pages)",
    ]
    ouvertes = rapport.get("ouvertes_approuvees")
    if ouvertes is not None:
        lignes.append(
            f"Ouvertes approuvees (cote censure) : {ouvertes['trouvees']} trouvees"
            f" | inspectees : {ouvertes['inspectees']}"
            + ("  [TRONQUEE]" if ouvertes["tronquee"] else "")
            + f" | a la tete exacte : {ouvertes['a_la_tete_exacte']}"
            + f" | {ouvertes['revues_incompletes']} revues non lues en entier"
            + f" | {ouvertes['approbations_retirees']} approbation(s) reprise(s)"
            + f" | au-dela du seuil : {ouvertes['au_dela_du_seuil']}"
            f" (la plus ancienne attend {_heures(ouvertes['plus_ancienne_heures'])})")
    return "\n".join(lignes)


def main(argv: list[str] | None = None) -> int:
    analyseur = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    analyseur.add_argument("--heures", type=float, default=168.0,
                           help="taille de la fenetre en heures avant maintenant (defaut 168 = 7 j)")
    analyseur.add_argument("--depuis", default="",
                           help="debut de fenetre ISO 8601 (prime sur --heures)")
    analyseur.add_argument("--approuveur", default=APPROUVEUR,
                           help="compte dont l'APPROVE definit le point de depart")
    analyseur.add_argument("--max-prs", type=int, default=MAX_PR_READ,
                           help="nombre de PRs dont les revues sont lues (borne la depense)")
    analyseur.add_argument("--max-ouvertes", type=int, default=MAX_OPEN_READ,
                           help="nombre de PRs ouvertes approuvees inspectees (cote censure)")
    analyseur.add_argument("--max-pages", type=int, default=MAX_PAGES,
                           help="plafond de pages de chaque lecture (100 lignes par page) ;"
                                " atteint sur une page pleine, il est dit dans le rapport")
    analyseur.add_argument("--sans-ouvertes", action="store_true",
                           help="ne pas mesurer les PRs ouvertes approuvees")
    analyseur.add_argument("--json", action="store_true", help="sortie machine")
    analyseur.add_argument("--out", default="", help="ecrit le JSON dans ce fichier")
    options = analyseur.parse_args(argv)
    if options.max_pages < 1:
        print("--max-pages doit valoir au moins 1", file=sys.stderr)
        return 2

    maintenant = datetime.now(timezone.utc)
    if options.depuis:
        # `parse_ts` reste stricte (une donnee d'API illisible ne passe pas pour
        # absente) ; seul l'argument de la ligne de commande a droit a un refus lisible.
        try:
            depuis = parse_ts(options.depuis)
        except ValueError:
            depuis = None
        if depuis is None:
            print(f"--depuis illisible : {options.depuis!r}", file=sys.stderr)
            return 2
    else:
        depuis = maintenant - timedelta(hours=options.heures)
    if depuis >= maintenant:
        print("fenetre vide : --depuis est dans le futur", file=sys.stderr)
        return 2

    rapport = mesurer(depuis, maintenant, options.approuveur, options.max_prs,
                      avec_ouvertes=not options.sans_ouvertes,
                      max_ouvertes=options.max_ouvertes, max_pages=options.max_pages)
    texte = json.dumps(rapport, indent=1, ensure_ascii=False)
    if options.out:
        with open(options.out, "w", encoding="utf-8", newline="\n") as flux:
            flux.write(texte + "\n")
    if options.json:
        print(texte)
    else:
        print(formater(rapport))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
