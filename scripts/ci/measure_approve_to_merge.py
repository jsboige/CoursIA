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
  dont l'approbation a la tete exacte attend depuis plus que le seuil.

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


def fusionnees(depuis: datetime, jusqu_a: datetime, max_pages: int = MAX_PAGES) -> list[dict]:
    """PRs fusionnees dont `merged_at` tombe dans la fenetre, de la plus recente a la plus ancienne."""
    trouvees: list[dict] = []
    for page in range(1, max_pages + 1):
        lot = api(
            f"/repos/{REPO}/pulls?state=closed&sort=updated&direction=desc"
            f"&per_page={PAR_PAGE}&page={page}")
        if not lot:
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
            break
        if len(lot) < PAR_PAGE:
            break
    trouvees.sort(key=lambda pr: parse_ts(pr["merged_at"]), reverse=True)
    return trouvees


def revues(numero: int) -> list[dict]:
    return api(f"/repos/{REPO}/pulls/{numero}/reviews?per_page={PAR_PAGE}")


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


def approbation_tete(revues_lues: list[dict], tete: str, approbateur: str) -> dict | None:
    """Derniere approbation de l'approbateur posee sur **cette** tete, ou None."""
    sur_la_tete = [
        revue for revue in approbations(revues_lues, approbateur)
        if revue.get("commit_id") == tete
    ]
    return sur_la_tete[-1] if sur_la_tete else None


def classer(pr: dict, revues_lues: list[dict], approbateur: str) -> dict:
    """Classe une PR fusionnee : tete exacte, tete anterieure, ou sans approbation."""
    tete = (pr.get("head") or {}).get("sha") or ""
    fusionnee_le = parse_ts(pr.get("merged_at"))
    sur_la_tete = approbation_tete(revues_lues, tete, approbateur)
    if sur_la_tete is not None:
        approuvee_le = parse_ts(sur_la_tete["submitted_at"])
        return {
            "numero": pr["number"],
            "classe": "tete_exacte",
            "heures": (fusionnee_le - approuvee_le).total_seconds() / 3600.0,
        }
    if approbations(revues_lues, approbateur):
        return {"numero": pr["number"], "classe": "tete_anterieure", "heures": None}
    return {"numero": pr["number"], "classe": "sans_approbation", "heures": None}


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
        "sans_approbation": sum(1 for ligne in lignes if ligne["classe"] == "sans_approbation"),
    }


def ouvertes_approuvees(jusqu_a: datetime, approbateur: str = APPROUVEUR,
                        seuil: float = SEUIL_HEURES, max_ouvertes: int = MAX_OPEN_READ) -> dict:
    """Cote censure du releve : les PRs ouvertes qu'une approbation attend.

    Une PR approuvee qui n'est pas encore fusionnee n'entre dans aucun
    denominateur de la mesure des fusionnees : un releve qui ne lirait que les
    merges serait bon par omission -- il suffirait de ne jamais fusionner les
    PRs lentes. Ici, la population est celle des PRs ouvertes approuvees
    (`review:approved`), et l'age se lit depuis l'approbation **a la tete
    exacte** : une approbation suivie d'un push est perimee, elle n'attend rien.
    """
    cherche = api(f"/search/issues?q=repo:{REPO}+is:pr+is:open+review:approved"
                  f"&per_page={PAR_PAGE}")
    numeros = [item["number"] for item in cherche.get("items", [])][:max_ouvertes]
    lignes: list[dict] = []
    for numero in numeros:
        pr = api(f"/repos/{REPO}/pulls/{numero}")
        revues_lues = revues(numero)
        sur_la_tete = approbation_tete(revues_lues, (pr.get("head") or {}).get("sha") or "",
                                       approbateur)
        if sur_la_tete is None:
            classe = "tete_anterieure" if approbations(revues_lues, approbateur) else "sans_approbation"
            lignes.append({"numero": numero, "classe": classe, "heures": None})
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
        "a_la_tete_exacte": len(ages),
        "au_dela_du_seuil": len(au_dela),
        "plus_ancienne_heures": max(ages) if ages else None,
        "au_dela": au_dela,
    }


def mesurer(depuis: datetime, jusqu_a: datetime, approbateur: str = APPROUVEUR,
            max_prs: int = MAX_PR_READ, avec_ouvertes: bool = True,
            max_ouvertes: int = MAX_OPEN_READ) -> dict:
    """Mesure bornee : liste les PRs fusionnees de la fenetre, lit leurs revues, classe."""
    pool = fusionnees(depuis, jusqu_a)
    inspectees = pool[:max_prs]
    lignes = [classer(pr, revues(pr["number"]), approbateur) for pr in inspectees]
    agregat = resume(lignes)
    rapport = {
        "fenetre": {"depuis": depuis.isoformat().replace("+00:00", "Z"),
                    "jusqu_a": jusqu_a.isoformat().replace("+00:00", "Z")},
        "approuveur": approbateur,
        "seuil_heures": SEUIL_HEURES,
        "fusionnees_dans_la_fenetre": len(pool),
        "inspectees": len(inspectees),
        "tronquee": len(pool) > len(inspectees),
        **agregat,
        "lignes": lignes,
    }
    if avec_ouvertes:
        rapport["ouvertes_approuvees"] = ouvertes_approuvees(
            jusqu_a, approbateur, SEUIL_HEURES, max_ouvertes)
    return rapport


def _heures(valeur: float | None) -> str:
    return "-" if valeur is None else f"{valeur:.2f} h"


def formater(rapport: dict) -> str:
    """Rendu lisible : les nombres d'abord, la lecture ensuite."""
    bloc = rapport["tete_exacte"]
    part = bloc["part_sous_le_seuil"]
    part_txt = "n/a (aucune PR a tete exacte)" if part is None else f"{part * 100:.1f} %"
    lignes = [
        f"Fenetre {rapport['fenetre']['depuis']} -> {rapport['fenetre']['jusqu_a']}"
        f" (merged_at), approbateur {rapport['approuveur']},"
        f" seuil {rapport['seuil_heures']:.0f} h",
        f"Fusionnees dans la fenetre : {rapport['fusionnees_dans_la_fenetre']}"
        f" | inspectees : {rapport['inspectees']}"
        + ("  [TRONQUEE : --max-prs atteint, la part ne vaut que pour l'echantillon]"
           if rapport["tronquee"] else ""),
        f"Tete exacte : {bloc['n']} PRs | sous le seuil : {bloc['sous_le_seuil']}"
        f" | part : {part_txt}",
        f"Delais tete exacte : p50 {_heures(bloc['p50_heures'])}"
        f" | p90 {_heures(bloc['p90_heures'])}"
        f" | min {_heures(bloc['min_heures'])} | max {_heures(bloc['max_heures'])}",
        f"Hors denominateur : {rapport['tete_anterieure']} approbation(s) sur tete anterieure"
        f" | {rapport['sans_approbation']} sans approbation de l'approbateur",
    ]
    ouvertes = rapport.get("ouvertes_approuvees")
    if ouvertes is not None:
        lignes.append(
            f"Ouvertes approuvees (cote censure) : {ouvertes['trouvees']} trouvees"
            f" | inspectees : {ouvertes['inspectees']}"
            + ("  [TRONQUEE]" if ouvertes["tronquee"] else "")
            + f" | a la tete exacte : {ouvertes['a_la_tete_exacte']}"
            f" | au-dela du seuil : {ouvertes['au_dela_du_seuil']}"
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
    analyseur.add_argument("--sans-ouvertes", action="store_true",
                           help="ne pas mesurer les PRs ouvertes approuvees")
    analyseur.add_argument("--json", action="store_true", help="sortie machine")
    analyseur.add_argument("--out", default="", help="ecrit le JSON dans ce fichier")
    options = analyseur.parse_args(argv)

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
                      max_ouvertes=options.max_ouvertes)
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
