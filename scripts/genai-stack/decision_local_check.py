"""Verification locale du classement Decision Index (issue #21910, Pli 1 de #18204).

Ce que mesure ce script
-----------------------
Le Decision Index classe des « modeles de decision » : des modeles qui lisent un
etat et des questions typees (`choice`, `score`, `noul`) et rendent une probabilite
par option, sans generer de texte. L'EPIC #18204 demande, a son Pli 1, de
« rejouer 2 ou 3 tranches de benchmarks de l'index sur 3 modeles de la liste
courte, pour verifier que l'ordre du classement tient chez nous ».

Ce que fait ce script
---------------------
1. Il reconstruit une tranche de benchmarks **publics** dans le contrat servi par
   les modeles (question de type `choice`), a partir de jeux de donnees QCM
   publics.
2. Il sert les modeles **localement**, avec leur bibliotheque native (`jiwo`), sur
   la carte de la machine : aucune API distante, aucun degrade.
3. Il mesure l'exactitude, la calibration (ECE) et le score de Brier, puis
   **confronte l'ordre mesure a l'ordre publie par l'index**.

Ce que ce script ne fait pas, et pourquoi
------------------------------------------
Il ne rejoue pas les charges utiles de l'index : elles vivent dans un jeu de
donnees Hugging Face **non publie** (`multimodalart/decision-index-suite-0.3` :
401 / `RepositoryNotFoundError`, mesure du 2026-10-21) et le depot public du kit
n'en contient que des identifiants (`run_ids`, `group_ids`). La tranche est donc
**reconstruite**, pas reprise : la comparaison porte sur l'**ordre**, pas sur les
scores, et les trois jeux de donnees employes ne sont pas ceux du protocole de
l'index.

Prerequis
---------
Un interpreteur Python 3.12 (la bibliotheque `jiwo` exige `>=3.12,<3.13`) avec
`jiwo`, `torch` et `datasets` :

    pip install "jiwo @ git+https://github.com/jiwidi/jiwo" datasets

Utilisation
------------
    python scripts/genai-stack/decision_local_check.py \
        --model "eljiwo/jiwo-0.8b@v1" \
        --model "eljiwo/jiwo-0.8b@v2" \
        --model "eljiwo/jiwo-4b@v2#cpu:100" \
        --json scripts/results/decision_local_<date>.json

Syntaxe d'un modele : `depot[@revision][#device][:limite_par_jeu_de_donnees]`.
`v1` et `v2` sont des **tags** du depot (mesure : `list_repo_refs`, 2026-10-21) ;
`main` porte le meme contenu que le tag `v2`. La limite est le nombre d'items
par jeu de donnees pour ce modele (une limite plus petite sert les modeles trop
lourds pour la carte) ; le classement est calcule sur le sous-ensemble commun a
tous les modeles.

Un checkpoint deja telecharge peut etre servi sans requete au hub :
`--local depot@revision=chemin`. L'identite publiee reste celle du depot, seule
la source des poids change.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import random
import sys
import time
from pathlib import Path
from typing import Any, Iterable

# Les poids des modeles de decision sont stockes en Xet. Sur cette machine, le
# telechargement Xet echoue en silence : `snapshot_download` rend un repertoire
# sans les `.safetensors`, et le chargement du modele echoue ensuite sur le
# tokenizer. Le chemin classique (CDN) telecharge tout : on le force.
os.environ.setdefault("HF_HUB_DISABLE_XET", "1")

# ---- valeurs publiees, avec leur source (relues le 2026-10-21) --------------------

# Cartes modele eljiwo/jiwo-0.8b et eljiwo/jiwo-4b, section « Evaluation » ;
# README github.com/jiwidi/jiwo, section « Models ».
SOURCE_CARTES = "cartes modele eljiwo (section Evaluation) et README jiwidi/jiwo, relus le 2026-10-21"

# Score public de l'edition 0.3 de l'index, tel que repris par les cartes modele.
INDEX_PUBLIC_0_3 = {
    "eljiwo/jiwo-0.8b@v1": 28.72,
    "eljiwo/jiwo-0.8b@v2": 29.58,
    "eljiwo/jiwo-4b@v1": 45.76,
    "eljiwo/jiwo-4b@v2": 46.06,
}

# « Three public datasets never used in training (accuracy) ». Les jeux de donnees
# ne sont pas nommes par les cartes : ces nombres servent de repere de plausibilite,
# pas de reproduction.
TROIS_JEUX_PUBLIES = {
    "eljiwo/jiwo-0.8b@v1": 54.6,
    "eljiwo/jiwo-0.8b@v2": 61.3,
    "eljiwo/jiwo-4b@v1": 66.3,
    "eljiwo/jiwo-4b@v2": 67.8,
}

# « Area skill x100 » publie par les cartes modele. L'ordre des cinq aires est
# celui de la carte : knowledge / language / retrieval and classification /
# tools / arts. La colonne v1 de la carte est celle de l'edition 0.2.1.
AIRES_PUBLIEES = {
    "eljiwo/jiwo-0.8b@v2": {"knowledge": 10.9, "language": 36.1,
                            "retrieval_and_classification": 44.2, "tools": 40.3, "arts": 12.2},
    "eljiwo/jiwo-0.8b@v1": {"knowledge": 10.3, "language": 32.3,
                            "retrieval_and_classification": 44.5, "tools": 38.0, "arts": 11.2},
}

# Controle publie par les cartes : le modele **non entraine** (Qwen3.5-0.8B sans
# entrainement de decision) plafonne a 6.99 sur l'edition 0.2.1, dans le meme
# serveur et la meme calibration. C'est le plancher de ce que vaut un modele de
# decision : le hasard du QCM a 4 options vaut 25.
BASE_NON_ENTRAINEE_0_2_1 = 6.99

# « Seven more public datasets from new domains, never used in training (accuracy) »,
# publie pour v2 seul. Les jeux ne sont pas nommes.
SEPT_JEUX_PUBLIES = {"eljiwo/jiwo-0.8b@v2": 59.6}

# Aire de competence a laquelle chaque jeu de la tranche reconstruite se rattache.
# Le classement des games publics de l'index ne se decompose pas par aire, mais la
# carte publie les aires : la forme du profil (knowledge faible, language et
# retrieval-and-classification eleves) est un second axe de verification, distinct
# de l'ordre.
AIRE_DES_JEUX = {
    "arc_easy": "knowledge",
    "openbookqa": "knowledge",
    "commonsense_qa": "language",
}

# ---- les jeux de donnees publics de la tranche reconstruite ----------------------

# Chaque entree : (identifiant, jeu HF, configuration, coupe, colonne question).
# Les trois portent la meme forme (choix + cle de reponse), ce qui permet de les
# traiter de facon identique.
DATASETS = {
    "arc_easy": ("allenai/ai2_arc", "ARC-Easy", "test", "question"),
    "openbookqa": ("allenai/openbookqa", "main", "test", "question_stem"),
    "commonsense_qa": ("tau/commonsense_qa", None, "validation", "question"),
}

LETTRES = "abcdefghijklmnopqrstuvwxyz"


# ---- lecture des jeux de donnees --------------------------------------------------

def load_items(nom: str, limite: int, graine: int) -> list[dict[str, Any]]:
    """Charge un jeu QCM public et rend une liste d'items deterministes.

    Chaque item porte : `id`, `dataset`, `question`, `options` (liste de textes) et
    `reponse` (index de la bonne option). L'ordre est trie par identifiant puis
    melee avec une graine fixe : la tranche est donc reproductible.
    """
    from datasets import load_dataset

    depot, config, coupe, colonne = DATASETS[nom]
    if config is None:
        brut = load_dataset(depot, split=coupe)
    else:
        brut = load_dataset(depot, config, split=coupe)

    items: list[dict[str, Any]] = []
    for ligne in brut:
        choix = ligne["choices"]
        textes = list(choix["text"])
        etiquettes = list(choix["label"])
        if ligne["answerKey"] not in etiquettes:
            continue
        reponse = etiquettes.index(ligne["answerKey"])
        items.append({
            "id": f"{nom}:{ligne.get('id', len(items))}",
            "dataset": nom,
            "question": ligne[colonne],
            "options": textes,
            "reponse": reponse,
        })

    items.sort(key=lambda item: item["id"])
    random.Random(graine).shuffle(items)
    return items[:limite]


def empreinte(items: Iterable[dict[str, Any]]) -> str:
    """sha256 de la tranche : elle identifie le sous-ensemble evalue."""
    charge = json.dumps(
        [{"id": i["id"], "options": i["options"], "reponse": i["reponse"]} for i in items],
        ensure_ascii=False, sort_keys=True,
    )
    return hashlib.sha256(charge.encode("utf-8")).hexdigest()


# ---- contrat servi ---------------------------------------------------------------

def contrat(item: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    """Rend l'etat et la question `choice` correspondant a un item QCM.

    L'etat porte l'enonce, la question porte les options : c'est la lecture
    naturelle du contrat `choice` (un etat, des options nommees, une reponse).
    Les cles d'option sont des lettres minuscules : la bibliotheque les affiche
    telles quelles, sans les mettre entre guillemets comme une reponse.
    """
    options = item["options"]
    criteres = {LETTRES[i]: texte for i, texte in enumerate(options)}
    question = {
        "type": "choice",
        "instructions": "Which option is the correct answer?",
        "criteria": criteres,
    }
    return item["question"], {"q": question}


# ---- metriques -------------------------------------------------------------------

def brier(probabilites: dict[str, float], reponse: int, nb_options: int) -> float:
    """Score de Brier multiclasse : somme des (p_k - y_k)^2."""
    total = 0.0
    for index in range(nb_options):
        cible = 1.0 if index == reponse else 0.0
        p = probabilites.get(LETTRES[index], 0.0)
        total += (p - cible) ** 2
    return total


def ece(confiances: list[float], exactitudes: list[float], bins: int = 10) -> float | None:
    """Erreur de calibration attendue (10 bins, ponderation par le nombre d'items)."""
    if not confiances:
        return None
    total = 0.0
    for index in range(bins):
        bas, haut = index / bins, (index + 1) / bins
        Inside = [
            (c, a) for c, a in zip(confiances, exactitudes)
            if (c >= bas and c < haut) or (index == bins - 1 and c == 1.0)
        ]
        if not Inside:
            continue
        moyenne_conf = sum(c for c, _ in Inside) / len(Inside)
        moyenne_acc = sum(a for _, a in Inside) / len(Inside)
        total += len(Inside) / len(confiances) * abs(moyenne_conf - moyenne_acc)
    return total


def agrege(lignes: list[dict[str, Any]]) -> dict[str, Any]:
    """Agrege les lignes d'items en metriques globales."""
    if not lignes:
        return {"items": 0}
    confiances = [ligne["confiance"] for ligne in lignes]
    exactitudes = [1.0 if ligne["correct"] else 0.0 for ligne in lignes]
    return {
        "items": len(lignes),
        "exactitude": sum(exactitudes) / len(exactitudes),
        "confiance_moyenne": sum(confiances) / len(confiances),
        "ece": ece(confiances, exactitudes),
        "brier": sum(ligne["brier"] for ligne in lignes) / len(lignes),
    }


# ---- evaluation d'un modele ------------------------------------------------------

def parse_modele(spec: str, device_defaut: str, limite_defaut: int) -> dict[str, Any]:
    """Parse `depot[@revision][#device][:limite]`."""
    reste = spec
    limite = limite_defaut
    if ":" in reste:
        reste, _, texte = reste.rpartition(":")
        limite = int(texte)
    device = device_defaut
    if "#" in reste:
        reste, _, texte = reste.partition("#")
        device = texte
    revision = None
    if "@" in reste:
        reste, _, texte = reste.partition("@")
        revision = texte
    # `v1` et `v2` sont des tags du depot (mesure : list_repo_refs le 2026-10-21) ;
    # `main` pointe sur le meme commit que le tag `v2`.
    return {"id": f"{reste}@{revision or 'v2'}", "spec": spec, "depot": reste,
            "revision": revision, "device": device, "limite": limite}


def charge_modele(modele: dict[str, Any], tentatives: int = 4) -> Any:
    """Charge le checkpoint localement, en reessayant les pannes de reseau du hub.

    La connexion au hub est instable sur cette machine (coupure TCP 10054 au
    milieu du telechargement). Le checkpoint n'est donc charge qu'apres une
    serie de tentatives espacees.
    """
    from jiwo.model import DecisionModel

    source = modele.get("chemin_local") or modele["depot"]
    derniere: Exception | None = None
    for essai in range(tentatives):
        try:
            return DecisionModel.from_pretrained(
                source, revision=modele["revision"], device=modele["device"]
            )
        except Exception as problem:  # reseau ou disque : on reessaye
            derniere = problem
            del problem
            if essai + 1 < tentatives:
                time.sleep(5 * (essai + 1))
    raise RuntimeError(
        f"chargement impossible de {modele['id']} apres {tentatives} tentatives : {derniere}"
    )


def evalue_modele(modele: dict[str, Any], tranches: dict[str, list[dict[str, Any]]],
                  max_length: int) -> dict[str, Any]:
    """Sert le modele localement et evalue sa tranche."""
    import torch

    depart = time.perf_counter()
    chargeur = charge_modele(modele)
    chargement_s = time.perf_counter() - depart
    if modele["device"].startswith("cuda") and torch.cuda.is_available():
        torch.cuda.reset_peak_memory_stats()

    lignes: list[dict[str, Any]] = []
    par_dataset: dict[str, dict[str, Any]] = {}
    for nom, items in tranches.items():
        sous = items[: modele["limite"]]
        lignes_locales: list[dict[str, Any]] = []
        for item in sous:
            etat, questions = contrat(item)
            reponse = chargeur.decide(etat, questions, max_length=max_length)
            reponse = dict(reponse)
            reponse = reponse["answers"]["q"] if "answers" in reponse else reponse
            choisit = reponse["choice"]
            probabilites = reponse["probabilities"]
            lignes_locales.append({
                # le jeu se lit dans le prefixe de l'identifiant : le grain de
                # l'item est reproduit sans le doublon
                "id": item["id"],
                "correct": choisit == LETTRES[item["reponse"]],
                "p_gold": float(probabilites.get(LETTRES[item["reponse"]], 0.0)),
                "confiance": float(reponse.get("confidence", 0.0)),
                "brier": brier(probabilites, item["reponse"], len(item["options"])),
                "nb_options": len(item["options"]),
            })
        par_dataset[nom] = agrege(lignes_locales)
        lignes.extend(lignes_locales)

    return {
        "id": modele["id"],
        "depot": modele["depot"],
        "revision": modele["revision"] or "main (v2)",
        "device": modele["device"],
        "limite_par_jeu": modele["limite"],
        "chargement_s": round(chargement_s, 1),
        "evaluation_s": round(time.perf_counter() - depart - chargement_s, 1),
        "vram_peak_go": round(torch.cuda.max_memory_allocated() / 2**30, 2)
        if (modele["device"].startswith("cuda") and torch.cuda.is_available()) else None,
        "par_jeu": par_dataset,
        "global": agrege(lignes),
        "items": lignes,
    }


# ---- classement -------------------------------------------------------------------

def compare_classements(mesures: dict[str, dict[str, Any]],
                        lignes_par_modele: dict[str, list[dict[str, Any]]]) -> dict[str, Any]:
    """Compare l'ordre mesure (sous-ensemble commun) a l'ordre publie par l'index."""
    communs: set[str] | None = None
    for lignes in lignes_par_modele.values():
        ids = {ligne["id"] for ligne in lignes}
        communs = ids if communs is None else (communs & ids)
    communs = communs or set()

    sur_commun: dict[str, dict[str, Any]] = {}
    for identifiant, lignes in lignes_par_modele.items():
        filtrees = [ligne for ligne in lignes if ligne["id"] in communs]
        sur_commun[identifiant] = agrege(filtrees)

    mesure = sorted(
        ({"id": i, "exactitude": m["exactitude"], "items": m["items"]}
         for i, m in sur_commun.items() if m["items"]),
        key=lambda d: (-d["exactitude"], d["id"]),
    )
    publie = sorted(
        ({"id": i, "score_index_public_0_3": s} for i, s in INDEX_PUBLIC_0_3.items()
         if i in sur_commun),
        key=lambda d: (-d["score_index_public_0_3"], d["id"]),
    )
    rang_mesure = {d["id"]: i for i, d in enumerate(mesure)}
    rang_publie = {d["id"]: i for i, d in enumerate(publie)}

    paires = []
    for identifiant in sorted(rang_mesure):
        if identifiant in rang_publie:
            paires.append({
                "id": identifiant,
                "rang_mesure": rang_mesure[identifiant],
                "rang_publie": rang_publie[identifiant],
                "concordant": rang_mesure[identifiant] == rang_publie[identifiant],
            })

    return {
        "sous_ensemble_commun": len(communs),
        "classement_mesure": mesure,
        "classement_publie": publie,
        "paires": paires,
        "ordre_identique": bool(paires) and all(p["concordant"] for p in paires),
        "note": "L'ordre publie est celui du score public de l'edition 0.3 de l'index "
                "(source : cartes modele eljiwo). L'ordre mesure porte sur la tranche "
                "reconstruite : la comparaison porte sur l'ordre, pas sur les scores.",
    }


def compare_aires(resultats: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """Compare la forme du profil mesure par aire de competence a la forme publiee.

    Les cartes modele publient un score d'aire (« area skill x100 ») : le modele
    est fort en « retrieval and classification », faible en « knowledge ». Les
    valeurs mesurees ici sont des **exactitudes**, pas des scores d'aire : la
    comparaison porte donc sur la **forme** (l'aire la plus faible et l'aire la
    plus forte), pas sur les nombres.
    """
    profil: dict[str, Any] = {}
    conformites: list[dict[str, Any]] = []
    for identifiant, resultat in resultats.items():
        par_aire: dict[str, list[dict[str, Any]]] = {}
        for nom, stats in resultat["par_jeu"].items():
            aire = AIRE_DES_JEUX.get(nom)
            if aire and stats.get("items"):
                par_aire.setdefault(aire, []).append(stats)
        mesure: dict[str, Any] = {}
        for aire, liste in par_aire.items():
            items = sum(entree["items"] for entree in liste)
            mesure[aire] = {
                "exactitude": round(
                    sum(entree["exactitude"] * entree["items"] for entree in liste) / items, 4),
                "items": items,
            }
        publie_complet = AIRES_PUBLIEES.get(identifiant, {})
        publie = {aire: publie_complet[aire] for aire in mesure if aire in publie_complet}
        profil[identifiant] = {
            "mesure": mesure,
            "publie_complet": publie_complet,
            "publie_sur_aires_mesurees": publie,
        }

        if mesure and publie:
            faible = min(mesure, key=lambda a: mesure[a]["exactitude"])
            forte = max(mesure, key=lambda a: mesure[a]["exactitude"])
            faible_pub = min(publie, key=lambda a: publie[a])
            forte_pub = max(publie, key=lambda a: publie[a])
            ecart = mesure[forte]["exactitude"] - mesure[faible]["exactitude"]
            if ecart <= 0:
                # ex aequo : la tranche ne separe pas les deux aires, l'ordre
                # publie n'est ni confirme ni infirme
                verdict = "indetermine"
            elif faible == faible_pub and forte == forte_pub:
                verdict = "conforme"
            else:
                verdict = "non conforme"
            conformites.append({
                "id": identifiant,
                "aire_la_plus_faible_mesuree": faible,
                "aire_la_plus_faible_publiee": faible_pub,
                "aire_la_plus_forte_mesuree": forte,
                "aire_la_plus_forte_publiee": forte_pub,
                "ecart_exactitudes": round(ecart, 4),
                "verdict": verdict,
                "note": "La comparaison porte sur les aires couvertes par la tranche "
                        "reconstruite (knowledge, language) : les autres aires publiees "
                        "n'ont pas de jeu equivalent ici.",
            })

    return {
        "par_modele": profil,
        "formes": conformites,
        "note": "Les scores d'aire publies (skill x100 sur l'edition 0.3 pour v2, "
                "0.2.1 pour v1) ne sont pas des exactitudes : la comparaison porte "
                "sur la forme du profil, pas sur les valeurs.",
    }


# ---- main ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parseur = argparse.ArgumentParser(
        description="Verification locale du classement Decision Index (modeles servis localement)."
    )
    parseur.add_argument("--model", action="append", default=[], metavar="SPEC",
                          help="depot[@revision][#device][:limite_par_jeu] (repetable)")
    parseur.add_argument("--datasets", default=",".join(DATASETS),
                          help="jeux de donnees de la tranche, separes par des virgules")
    parseur.add_argument("--limit", type=int, default=300,
                          help="items par jeu de donnees (limite par defaut de chaque modele)")
    parseur.add_argument("--seed", type=int, default=42, help="graine du melange deterministe")
    parseur.add_argument("--device", default="cuda", help="device par defaut des modeles")
    parseur.add_argument("--max-length", type=int, default=8192,
                          help="longueur maximale de prompt en jetons")
    parseur.add_argument("--json", default=None, help="fichier de sortie JSON")
    parseur.add_argument("--local", action="append", default=[], metavar="ID=CHEMIN",
                          help="checkpoint local deja telecharge, sous la forme "
                               "depot@revision=chemin (le chemin est lu sur le disque, "
                               "aucune requete au hub)")
    args = parseur.parse_args(argv)

    locaux: dict[str, str] = {}
    for entree in args.local:
        identifiant, _, chemin = entree.partition("=")
        if not identifiant or not chemin:
            parseur.error(f"--local mal forme : {entree!r} (attendu depot@revision=chemin)")
        locaux[identifiant.strip()] = chemin.strip()

    if not args.model:
        parseur.error("au moins un --model est requis")

    try:
        import jiwo
        import torch
    except ImportError as problem:
        print(f"dependance manquante : {problem}. Installer jiwo (Python 3.12) et torch.",
              file=sys.stderr)
        return 2

    noms = [n.strip() for n in args.datasets.split(",") if n.strip()]
    inconnus = [n for n in noms if n not in DATASETS]
    if inconnus:
        print(f"jeux de donnees inconnus : {inconnus}", file=sys.stderr)
        return 2

    tranches: dict[str, list[dict[str, Any]]] = {}
    for nom in noms:
        tranches[nom] = load_items(nom, args.limit, args.seed)
        print(f"tranche {nom} : {len(tranches[nom])} items")

    modeles = [parse_modele(spec, args.device, args.limit) for spec in args.model]
    for modele in modeles:
        modele["chemin_local"] = locaux.get(modele["id"])
    resultats: dict[str, dict[str, Any]] = {}
    lignes_par_modele: dict[str, list[dict[str, Any]]] = {}
    for modele in modeles:
        print(f"\n== {modele['id']} (device {modele['device']}, limite {modele['limite']}/jeu)")
        resultat = evalue_modele(modele, tranches, args.max_length)
        resultats[modele["id"]] = resultat
        lignes_par_modele[modele["id"]] = resultat["items"]
        print(f"   exactitude globale : {resultat['global'].get('exactitude', 0):.4f} "
              f"sur {resultat['global'].get('items', 0)} items "
              f"({resultat['evaluation_s']} s)")

    classement = compare_classements(resultats, lignes_par_modele)
    aires = compare_aires(resultats)

    environnement = {
        "python": sys.version.split()[0],
        "torch": torch.__version__,
        "jiwo": getattr(jiwo, "__version__", "inconnu"),
        "cuda_disponible": bool(torch.cuda.is_available()),
        "gpu": torch.cuda.get_device_name(0) if torch.cuda.is_available() else None,
        "vram_go": round(torch.cuda.get_device_properties(0).total_memory / 2**30, 2)
        if torch.cuda.is_available() else None,
    }

    agregat = {
        "genere_le": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        "issue": "#21910 (Pli 1 de #18204)",
        "environnement": environnement,
        "tranche": {
            "jeux": {nom: {"items": len(items), "sha256": empreinte(items)}
                     for nom, items in tranches.items()},
            "graine": args.seed,
            "reconstruction": "Tranche RECONSTRUITE depuis des jeux de donnees QCM publics : "
                              "les charges utiles de l'index sont dans un jeu de donnees non publie "
                              "(multimodalart/decision-index-suite-0.3, 401 mesure le 2026-10-21).",
        },
        "modeles": {
            identifiant: {k: v for k, v in resultat.items() if k != "items"}
            for identifiant, resultat in resultats.items()
        },
        "classement": classement,
        "profil_aires": aires,
        "reference_publiee": {
            "source": SOURCE_CARTES,
            "index_public_0_3": INDEX_PUBLIC_0_3,
            "trois_jeux_publies_non_nommes": TROIS_JEUX_PUBLIES,
            "sept_jeux_publies_non_nommes": SEPT_JEUX_PUBLIES,
            "aires_par_modele": AIRES_PUBLIEES,
            "base_non_entrainee_0_2_1": BASE_NON_ENTRAINEE_0_2_1,
            "avertissement": "Les « trois jeux de donnees » et les « sept jeux de donnees » "
                             "ne sont pas nommes par les cartes : ces accuracies servent de "
                             "repere de plausibilite, pas de reproduction.",
        },
        "items": {identifiant: resultat["items"] for identifiant, resultat in resultats.items()},
        "limites": [
            "La tranche est reconstruite, pas reprise de l'index : la comparaison porte sur "
            "l'ordre, pas sur les scores.",
            "Les modeles sont servis par leur bibliotheque native, sur la carte de la machine ; "
            "un modele trop lourd pour la carte tourne sur CPU (float32), pas en version quantifiee.",
            "Les accuracies publiees par les cartes modele portent sur des jeux de donnees non "
            "nommes : elles ne sont pas des valeurs a reproduire ici.",
        ],
    }

    if args.json:
        chemin = Path(args.json)
        chemin.parent.mkdir(parents=True, exist_ok=True)
        chemin.write_text(json.dumps(agregat, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"\nagregat ecrit : {chemin}")

    print("\nclassement mesure (sous-ensemble commun) :")
    for entree in classement["classement_mesure"]:
        print(f"   {entree['exactitude']:.4f}  {entree['id']}  ({entree['items']} items)")
    print("classement publie (index 0.3, public) :")
    for entree in classement["classement_publie"]:
        print(f"   {entree['score_index_public_0_3']:.2f}  {entree['id']}")
    print(f"ordre identique : {classement['ordre_identique']}")

    print("\nprofil par aire (forme comparee au profil publie) :")
    for entree in aires["formes"]:
        print(f"   {entree['id']} : mesure {entree['aire_la_plus_faible_mesuree']} < "
              f"{entree['aire_la_plus_forte_mesuree']} (ecart {entree['ecart_exactitudes']}) ; "
              f"publie {entree['aire_la_plus_faible_publiee']} < {entree['aire_la_plus_forte_publiee']} "
              f"-> {entree['verdict']}")
    print("\nplausibilite (exactitude mesuree vs accuracies publiees, jeux non nommes) :")
    for identifiant, resultat in resultats.items():
        mesure = resultat["global"].get("exactitude")
        repere = TROIS_JEUX_PUBLIES.get(identifiant)
        if mesure is not None and repere is not None:
            print(f"   {identifiant} : mesure {mesure * 100:.1f}% ; publie {repere}% (trois jeux non nommes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
