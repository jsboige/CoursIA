"""Ce que le tapis rapide SERT a une lane : grains, procedure, sortie (#26926).

Seam d'extraction de `tapis_rapide.py` (plafond de lignes) : ce module porte
la forme du service -- la commande a lancer avant d'editer, la procedure d'un
conteneur, la lecture de secours sur le cache quand le reseau tombe, et la
sortie texte. Aucune decision d'ecart ici ; aucun processus lance.

Mesure fondatrice (#26926, 16/11) : un conteneur servi avec `check_lane_claim.py N`
sans `--paths` etait refuse des que d'autres lanes y tenaient des claims bornes
(6 sur #19297), et la lecture incomplete renvoyait vers le tapis lourd (240 s).
"""
from __future__ import annotations

from pathlib import Path

from coordination import gh_bulk, gh_cache_fichier, tapis_recul, tapis_sature

VERIF = "python scripts/check_lane_claim.py {n} --lane {lane}"
VERIF_CONTENEUR = VERIF + " --paths <vos chemins>"
# Au-dela, une lecture de secours est trop vieille pour proposer quoi que ce soit.
SECOURS_MAX_S = 12 * 3600
SANS_SECOURS = ("Rien n'est servi. Ne tirez pas le tapis lourd : portez vos PRs ouvertes "
                "au merge, traitez la file du coordinateur, puis re-tirez ce tapis.")
PROCEDURE = (
    "conteneur : lisez le fil entier (gh issue view {n} --comments), prenez l'etape "
    "suivante non faite HORS des chemins occupes ci-dessous, verifiez avec la commande "
    "--paths, puis posez [CLAIMED] lane {lane} -- paths: <vos chemins>. Sans --paths, "
    "check_lane_claim refuse le conteneur entier des qu'une autre lane y tient un claim borne.")


def grain_servi(rang: int, e, lane: str, priorite: list[str],
                prs_par_issue: dict[int, list[dict]]) -> dict:
    """Un grain du rapport ; un conteneur porte sa procedure et ses occupations."""
    g = {"rang": rang, "numero": e.numero, "titre": e.titre, "famille": e.famille,
         "parent": e.parent, "conteneur": e.conteneur, "notes": e.notes,
         "consolidation": e.consolidation, "derniere_visite": e.derniere_visite,
         "visites": e.visites, "visites_total": e.visites_total,
         "priorite": priorite,
         "avant_d_editer": (VERIF_CONTENEUR if e.conteneur else VERIF).format(
             n=e.numero, lane=lane)}
    if e.conteneur:
        g["procedure"] = PROCEDURE.format(n=e.numero, lane=lane)
        g["chemins_occupes"] = [{"lane": autre, "paths": paths} for autre, paths in e.occupes]
        g["prs_ouvertes"] = sorted({pr["number"] for pr in prs_par_issue.get(e.numero, [])})
    return g


def lecture_de_secours(jours: int, exc: gh_bulk.LectureIncomplete,
                       dossier: Path | None = None) -> gh_bulk.Lecture | None:
    """La derniere lecture COMPLETE du cache machine, si elle a moins de 12 h.

    Une lecture incomplete ne sert rien (le pool serait faux) ; une lecture
    complete un peu vieille sert encore, puisque `check_lane_claim.py` reste
    l'autorite avant d'editer. Le motif de la panne est porte par `fetch_note`.
    """
    chemin = (dossier or gh_bulk.dossier_cache_defaut()) / f"lecture-{jours}j.json"
    brut = gh_cache_fichier.frais(chemin, SECOURS_MAX_S)
    if brut is None:
        return None
    try:
        brut["citations"] = {int(k): v for k, v in brut["citations"].items()}
        lecture = gh_bulk.Lecture(**{**brut, "depuis_cache": True})
    except (KeyError, TypeError, ValueError, AttributeError):
        return None
    lecture.fetch_note = (f"lecture reseau en echec ({exc.lecture}, page {exc.page} : "
                          f"{str(exc.cause)[:80]}) ; tirage sur la lecture complete du "
                          f"{lecture.lu_a or '?'}, verifiez chaque grain avant d'editer")
    return lecture


def _court(texte_: str, n: int) -> str:
    return texte_ if len(texte_) <= n else texte_[:n - 3] + "..."


def _lignes_grain(g: dict) -> list[str]:
    notes = f" | notes : {' ; '.join(g['notes'])}" if g["notes"] else ""
    lignes = [f"{g['rang']:2d}. #{g['numero']} {_court(g['titre'], 100)}"
              + (" [CONTENEUR]" if g["conteneur"] else ""),
              (f"    famille #{g['famille']} | priorite : {', '.join(g['priorite']) or 'neutre'}"
               f" | derniere visite : {(g['derniere_visite'] or 'jamais')[:10]}{notes}"),
              f"    avant d'editer : {g['avant_d_editer']}"]
    if g["conteneur"]:
        lignes.append(f"    {g['procedure']}")
        lignes += [f"    chemins occupes par {o['lane']} : {o['paths']}"
                   for o in g["chemins_occupes"]]
        if g["prs_ouvertes"]:
            prs = ", ".join(f"#{n}" for n in g["prs_ouvertes"][:12])
            suite = f" (+{len(g['prs_ouvertes']) - 12})" if len(g["prs_ouvertes"]) > 12 else ""
            lignes.append(f"    PRs ouvertes qui le citent (leurs fichiers sont occupes) : "
                          f"{prs}{suite}")
    return lignes


def texte(r: dict, source: str) -> str:
    """Sortie courte, en francais, derivee du rapport."""
    lu, age_h = r["lecture"], r["lecture"]["origin_main_age_h"]
    age = "inconnu" if age_h is None else (
        f"il y a {age_h} h" if age_h >= 0 else f"{-age_h} h apres la lecture rejouee")
    fetch = f" ; {lu['fetch_note']}" if lu.get("fetch_note") else ""
    lignes = [f"Tapis rapide -- lane {r['lane']} -- {r['maintenant']} -- source : {source}",
              (f"{lu['issues']} issues ouvertes, {lu['servables']} servables en "
               f"{lu['familles']} familles (feuilles {lu.get('servables_feuilles', '?')}, "
               f"conteneurs {lu.get('servables_conteneurs', '?')}) ; lecture "
               f"{lu['secondes']} s, {lu['appels']} appels, cache "
               f"{'oui' if lu['depuis_cache'] else 'non'} ; origin/main "
               f"local : dernier commit {age}{fetch}"),
              (f"\nVos PRs ouvertes ({len(r['vos_prs'])}) -- traitez d'abord leurs nits "
               "(reserves, rouge propre, conflit) ; une PR verte qui n'attend que la "
               "review ne se touche pas :")]
    lignes += [f"  #{p['numero']}  {p['age_j']} j  {_court(p['titre'], 90)}"
               for p in r["vos_prs"]]
    lignes.append(f"\nGrains ({len(r['grains'])}) -- les grains d'abord, les conteneurs "
                  "ensuite :")
    if not r["grains"]:
        lignes.append("  Pool vide : aucune issue servable pour cette lane apres les ecarts.")
    for g in r["grains"]:
        lignes += _lignes_grain(g)
    comptes = ", ".join(f"{code} {len(v)}" for code, v in r["ecartees"].items())
    total = sum(len(v) for v in r["ecartees"].values())
    lignes.append(f"\nEcartees sans sonde : {comptes} (total {total})")
    lignes += tapis_recul.lignes_recul(r.get("en_recul"))
    lignes += tapis_sature.lignes_urne(r.get("eteints") or [])
    rev = r.get("reverif_fils")
    if rev:
        jetes = ", ".join(f"{j['code']} #{j['numero']}" for j in rev["jetes"]) or "aucun"
        echecs = (f", {len(rev['echecs'])} fil(s) illisible(s) -- verdict sur fenetre"
                  if rev["echecs"] else "")
        borne = " ; borne d'appels atteinte" if rev["borne"] else ""
        lignes.append(f"Fils tronques re-decides sur fil complet : {rev['appels']} relu(s)"
                      f" en {rev['secondes']} s, jetes : {jetes}{echecs}{borne}")
    orig = r.get("origami_parking") or {}
    if orig.get("measured"):
        parcs = orig.get("parked") or []
        detail = ", ".join(f"#{n}" for n in parcs[:8]) if parcs else "aucun"
        suites = f" (+{len(parcs) - 8})" if len(parcs) > 8 else ""
        lignes.append(f"Parcage Origami : {len(parcs)} EPIC(s) en attente de depliage "
                      f"-- {detail}{suites}")
    else:
        lignes.append(f"Parcage Origami : NON MESURE ({orig.get('reason') or 'inconnu'})")
    return "\n".join(lignes)
