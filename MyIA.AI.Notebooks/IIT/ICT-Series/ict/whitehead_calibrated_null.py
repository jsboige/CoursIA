"""Case 28b -- portee exacte et null calibre de l'instrument relationnel de la case 28.

Le scelle `docs/ict/whitehead-calibrated-null-pre-enregistrement.md` fixe, AVANT
toute mesure a `n >= 6`, les theoremes de lecture T1-T4, les questions Q1-Q5 et la
regle de verdict. Ce banc ne fait que les executer : il enumere des relations
symetriques irreflexives, appelle `whitehead_extensive_connection.assess` (jamais
reimplemente) et agrege.

Ce que la case 28b ajoute a la case 28 :

  * un recensement EXHAUSTIF a `n = 6` (32 768 relations), qui remplace celui de
    `n <= 5` et separe les theoremes des hypotheses que la taille du recensement
    n'exercait pas ;
  * la portee exacte de l'instrument et son plafond, avec leurs certificats ;
  * le null exact (loi uniforme et courbe de densite en fractions exactes) et le
    seuil calibre `k*` qui s'en derive, la ou la case 28 avait fixe 12 et 14 sans
    connaitre la portee ;
  * un transfert et un balayage sur graines fraiches, disjointes de toutes celles
    que la case 28 emploie.

Aucune bande du scelle n'est recalibree ici : le module mesure, il ne choisit pas.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path

from . import whitehead_extensive_connection as wec

# --------------------------------------------------------------------------- #
# Constantes scellees
# --------------------------------------------------------------------------- #

CASE = "28b"
ORGAN = "ict/whitehead_extensive_connection.py"
SEAL = "docs/ict/whitehead-calibrated-null-pre-enregistrement.md"
RESULTS = Path(__file__).resolve().parent / "results" / "whitehead_calibrated_null_results.json"

SIZE = 6
REACH = (2, 3, 8, 9, 11, 15, 16, 17, 18)
THEOREMS_OF_READING = (12, 20)
UNCONDITIONAL_FALSE = (9,)
CEILING = 8
EXCLUSIVE_PAIR = (3, 17)

DENSITY_GRID = tuple(F(k, 20) for k in range(21))
SAMPLED_GRID = (F(149, 1000), F(299, 1000), F(699, 1000), F(849, 1000))
CORE_LEVEL = F(9, 10)
CONFIDENCE = F(95, 100)

TRANSFER_SIZE = 8
TRANSFER_SEEDS = (101, 202, 303, 404, 505)
TRANSFER_CONTROL_SEEDS = (111, 222, 333)
SWEEP_SEEDS = (611, 722, 833, 944, 1055)
SWEEP_DENSITIES = (F(3, 20), F(3, 10), F(7, 10))
EXPLORATORY_DENSITY = F(17, 20)

PUBLISHED_SEEDS = (0, 1, 7, 42, 99)
PUBLISHED_CONTROL_SEEDS = (11, 22, 33)
PUBLISHED_SWEEP_SEEDS = (500, 501, 507, 542, 599)
PUBLISHED_CORE = (2, 9, 11, 15)

# Temoins scelles (section 3 du scelle) : listes d'adjacence explicites, evaluees
# par leur nom et non par leur position dans l'enumeration.
WITNESS_W = (
    ("a", (1, 2, 3, 4, 5)),
    ("b", (0, 2, 3, 4, 5)),
    ("c", (0, 1, 3, 4)),
    ("d", (0, 1, 2, 4, 5)),
    ("e", (0, 1, 2, 3)),
    ("f", (0, 1, 3)),
)
WITNESS_G = (
    ("a", (1, 2)),
    ("b", (0, 2)),
    ("c", (0, 1)),
    ("d", (4,)),
    ("e", (3,)),
    ("f", ()),
)

PORTEE_LEGS = (
    "Q1a_portee_egale_a_R",
    "Q1b_theoremes_de_lecture",
    "Q1c_plafond_8_atteint",
    "Q1d_exclusion_A3_A17",
    "Q1e_temoins_conformes",
    "Q4a_portee_independante_de_la_densite",
    "Q4b_A9_fausse_a_toute_densite",
    "Q4c_bord_complet",
    "Q3b_transfert_dans_la_portee",
    "Q5d_balayage_dans_la_portee",
)
NULL_LEGS = (
    "Q2a_q_exactes",
    "Q2b_noyau",
    "Q2c_k_etoile",
    "Q3a_transfert_frequences",
    "Q3c_transfert_K",
    "Q5a_balayage_3_20",
    "Q5b_balayage_3_10",
    "Q5c_balayage_7_10",
)


# --------------------------------------------------------------------------- #
# Construction de relations
# --------------------------------------------------------------------------- #


def _edges(size):
    """Aretes dans l'ordre canonique du recensement de la case 28."""
    return [(first, second) for first in range(size) for second in range(first + 1, size)]


def relation_from_mask(size, mask, key=None):
    """Relation symetrique irreflexive dont le masque d'aretes est `mask`."""
    edges = _edges(size)
    adjacency = [[] for _ in range(size)]
    for position, (first, second) in enumerate(edges):
        if mask >> position & 1:
            adjacency[first].append(second)
            adjacency[second].append(first)
    names = [f"n{index}" for index in range(size)]
    return wec.Relational(key or f"E{mask}", "recensement", names, adjacency, regular=False)


def relation_from_witness(rows, key):
    """Relation dont on donne la liste d'adjacence nommee."""
    names = [name for name, _neighbours in rows]
    adjacency = [list(neighbours) for _name, neighbours in rows]
    return wec.Relational(key, "temoin", names, adjacency, regular=False)


def complete_relation(size):
    """Graphe complet : le bord dense de la courbe."""
    names = [f"k{index}" for index in range(size)]
    adjacency = [[other for other in range(size) if other != first] for first in range(size)]
    return wec.Relational(f"K{size}", "complet", names, adjacency, regular=False)


def _statuses(substrate):
    statuses, _details = wec.assess(substrate, want_witness=False)
    return statuses


# --------------------------------------------------------------------------- #
# Q1 / Q4 -- recensement exhaustif et portee
# --------------------------------------------------------------------------- #


def _mask_report(mask, edges, failures):
    presents = ["{0}-{1}".format(*edges[position])
                for position in range(len(edges)) if mask >> position & 1]
    return {"masque": mask, "aretes": len(presents), "liste": presents,
            "violations": list(failures)}


def census(size=SIZE):
    """Recensement exhaustif : toutes les relations symetriques irreflexives."""
    edges = _edges(size)
    count_edges = len(edges)
    total = 1 << count_edges
    numbers = len(wec.ASSUMPTIONS)
    violations = {number: 0 for number in wec.ASSUMPTIONS}
    hits = {number: [0] * (count_edges + 1) for number in wec.ASSUMPTIONS}
    k_histogram = [0] * (numbers + 1)
    k_by_edges = [[0] * (numbers + 1) for _ in range(count_edges + 1)]
    status_union = {number: set() for number in wec.ASSUMPTIONS}
    outside = []
    exclusive = 0
    undecided = 0
    ceiling = 0
    at_ceiling = []

    for mask in range(total):
        statuses = _statuses(relation_from_mask(size, mask))
        failures = wec._failures(statuses)
        degree = bin(mask).count("1")
        count = len(failures)
        k_histogram[count] += 1
        k_by_edges[degree][count] += 1
        ceiling = max(ceiling, count)
        if count == CEILING and len(at_ceiling) < 8:
            at_ceiling.append(_mask_report(mask, edges, failures))
        for number in failures:
            violations[number] += 1
            hits[number][degree] += 1
        indeterminate = False
        for number in wec.ASSUMPTIONS:
            status_union[number].add(statuses[number])
            if statuses[number] in ("partiel", "instable"):
                indeterminate = True
        if indeterminate:
            undecided += 1
        stray = [number for number in failures if number not in REACH]
        if stray:
            outside.append({"masque": mask, "hors_portee": stray})
        if 3 in failures and 17 in failures:
            exclusive += 1

    return {
        "taille": size,
        "aretes_possibles": count_edges,
        "relations": total,
        "violations_observees": {str(number): violations[number] for number in wec.ASSUMPTIONS},
        "portee_observee": sorted(number for number in wec.ASSUMPTIONS if violations[number]),
        "jamais_violees": sorted(number for number in wec.ASSUMPTIONS if not violations[number]),
        "relations_hors_portee": len(outside),
        "hors_portee_exemples": outside[:8],
        "plafond": ceiling,
        "plafond_atteint": bool(at_ceiling),
        "relations_au_plafond": k_histogram[CEILING] if CEILING < len(k_histogram) else 0,
        "au_plafond": at_ceiling,
        "relations_A3_et_A17": exclusive,
        "relations_indecises": undecided,
        "statuts_vus": {str(number): sorted(status_union[number]) for number in wec.ASSUMPTIONS},
        "histogramme_K": {str(count): value for count, value in enumerate(k_histogram) if value},
        "hits_par_arete": {str(number): hits[number] for number in wec.ASSUMPTIONS},
        "K_par_arete": k_by_edges,
    }


def lemmas(report):
    """Les theoremes de lecture, verifies mecaniquement par le recensement."""
    violations = report["violations_observees"]
    total = report["relations"]
    count_edges = report["aretes_possibles"]
    complete = all(report["hits_par_arete"]["9"][degree] == comb(count_edges, degree)
                   for degree in range(count_edges + 1))
    return {
        "T1_A12_jamais_violee": violations[str(THEOREMS_OF_READING[0])] == 0,
        "T2_A20_jamais_violee": violations[str(THEOREMS_OF_READING[1])] == 0,
        "T3_A9_toujours_violee": violations[str(UNCONDITIONAL_FALSE[0])] == total,
        "T3_A9_compte_par_arete": complete,
        "T4_A3_et_A17_exclusives": report["relations_A3_et_A17"] == 0,
        "portee_egale_a_R": report["portee_observee"] == sorted(REACH),
        "plafond_egal_a_huit": report["plafond"] == CEILING,
        "plafond_atteint": report["plafond_atteint"],
        "aucune_violation_hors_portee": report["relations_hors_portee"] == 0,
    }


def exact_curve(report):
    """q_i(d) exact : loi de Bernoulli sur les aretes, en fractions."""
    hits = report["hits_par_arete"]
    count_edges = report["aretes_possibles"]
    table = {}
    for density in list(DENSITY_GRID) + list(SAMPLED_GRID):
        weights = [density ** degree * (1 - density) ** (count_edges - degree)
                   for degree in range(count_edges + 1)]
        q = {}
        for number in wec.ASSUMPTIONS:
            violated = sum(F(hits[str(number)][degree]) * weights[degree]
                           for degree in range(count_edges + 1))
            q[str(number)] = 1 - violated
        table[str(density)] = q
    return table


# --------------------------------------------------------------------------- #
# Q2 -- null exact et seuil calibre
# --------------------------------------------------------------------------- #


def calibration(report):
    """Loi uniforme : probabilites exactes, noyau et seuil calibre."""
    total = report["relations"]
    probabilities = {number: F(report["violations_observees"][str(number)], total)
                     for number in wec.ASSUMPTIONS}
    core = sorted(number for number in wec.ASSUMPTIONS
                  if probabilities[number] >= CORE_LEVEL)
    distribution = [0] * (len(wec.ASSUMPTIONS) + 1)
    for key, value in report["histogramme_K"].items():
        distribution[int(key)] = value
    at_least = {k: F(sum(distribution[k:]), total)
                for k in range(1, len(distribution))}
    k_star = 0
    for k in sorted(at_least):
        if at_least[k] >= CONFIDENCE:
            k_star = k
    return {
        "loi": "uniforme sur les relations symetriques irreflexives",
        "probabilite_violation": {str(number): probabilities[number]
                                  for number in wec.ASSUMPTIONS},
        "q_exactes": {str(number): 1 - probabilities[number]
                      for number in (9, 12, 20)},
        "noyau_dixieme": core,
        "noyau_inclus_dans_portee": all(number in REACH for number in core),
        "noyau_contient_le_publie": all(number in core for number in PUBLISHED_CORE),
        "k_etoile": k_star,
        "P_K_superieur_ou_egal": {str(k): at_least[k] for k in sorted(at_least)},
    }


# --------------------------------------------------------------------------- #
# Temoins et bord complet
# --------------------------------------------------------------------------- #


def _witness_report(key, rows, clause, expected):
    substrate = relation_from_witness(rows, key)
    statuses = _statuses(substrate)
    failures = wec._failures(statuses)
    if clause == "equal":
        conforme = failures == sorted(expected)
    else:
        conforme = all(number in failures for number in expected)
    return {
        "clause": clause,
        "attendu": list(expected),
        "aretes": sum(len(neighbours) for _name, neighbours in rows) // 2,
        "violations": failures,
        "conforme": conforme,
        "A3_vraie": statuses[3] == "true",
        "statuts": {str(number): statuses[number] for number in wec.ASSUMPTIONS},
    }


def witnesses():
    """Les deux temoins scelles, evalues par leur nom."""
    return {
        "W": _witness_report("W", WITNESS_W, "superset", (2, 8, 9, 11, 17, 18)),
        "G": _witness_report("G", WITNESS_G, "equal", (2, 3, 8, 9, 11, 15, 16, 18)),
    }


def complete_edge(size=SIZE):
    """Le bord dense : graphe complet a `n` regions."""
    statuses = _statuses(complete_relation(size))
    return {
        "taille": size,
        "violations": wec._failures(statuses),
        "statuts": {str(number): statuses[number] for number in wec.ASSUMPTIONS},
    }


# --------------------------------------------------------------------------- #
# Q3 / Q5 -- transfert et balayage sur graines fraiches
# --------------------------------------------------------------------------- #


def _runs(seeds, density, size):
    runs = {}
    for seed in seeds:
        statuses = _statuses(wec.random_substrate(seed, density, size=size))
        runs[str(seed)] = wec._failures(statuses)
    return runs


def transfer():
    """Transfert n = 6 -> n = 8, densite 1/2, graines fraiches et controles.

    Le scelle compte huit relations : cinq graines de test et trois controles.
    """
    runs = _runs(TRANSFER_SEEDS, wec.NULL_DENSITY, TRANSFER_SIZE)
    controls = _runs(TRANSFER_CONTROL_SEEDS, wec.NULL_DENSITY, TRANSFER_SIZE)
    sets = [set(runs[str(seed)]) for seed in TRANSFER_SEEDS]
    sets += [set(controls[str(seed)]) for seed in TRANSFER_CONTROL_SEEDS]
    return {
        "taille": TRANSFER_SIZE,
        "densite": str(wec.NULL_DENSITY),
        "graines": runs,
        "controles": controls,
        "relations": len(sets),
        "comptes": {
            "A2": sum(2 in item for item in sets),
            "A9": sum(9 in item for item in sets),
            "A11": sum(11 in item for item in sets),
            "A15": sum(15 in item for item in sets),
        },
        "portee_respectee": sum(all(number in REACH for number in item) for item in sets),
        "K_superieur_ou_egal_3": sum(len(item) >= 3 for item in sets),
        "K_minimum": min(len(item) for item in sets),
        "K_maximum": max(len(item) for item in sets),
    }


def sweep():
    """Balayage a n = 8 sur graines fraiches ; la densite 17/20 est hors verdict."""
    out = {}
    for density in list(SWEEP_DENSITIES) + [EXPLORATORY_DENSITY]:
        runs = _runs(SWEEP_SEEDS, density, TRANSFER_SIZE)
        sets = [set(runs[str(seed)]) for seed in SWEEP_SEEDS]
        out[str(density)] = {
            "hors_verdict": density == EXPLORATORY_DENSITY,
            "graines": runs,
            "comptes": {str(number): sum(number in item for item in sets)
                        for number in (2, 3, 8, 9, 11, 15, 16, 17, 18)},
            "portee_respectee": sum(all(number in REACH for number in item) for item in sets),
            "K_maximum": max(len(item) for item in sets),
            "K_minimum": min(len(item) for item in sets),
        }
    return out


# --------------------------------------------------------------------------- #
# Regle de verdict
# --------------------------------------------------------------------------- #


def legs(report):
    """Les clauses scellees, une par une, sur les mesures."""
    census_report = report["census"]
    calibration_report = report["calibration"]
    transfer_report = report["transfert"]
    sweep_report = report["balayage"]
    witness_report = report["temoin"]
    complete = report["bord_complet"]
    counts = transfer_report["comptes"]
    flagged = complete["violations"]
    three = sweep_report[str(SWEEP_DENSITIES[0])]
    three_tenths = sweep_report[str(SWEEP_DENSITIES[1])]
    seven_tenths = sweep_report[str(SWEEP_DENSITIES[2])]
    return {
        "Q1a_portee_egale_a_R": census_report["portee_observee"] == sorted(REACH),
        "Q1b_theoremes_de_lecture": (
            census_report["violations_observees"]["12"] == 0
            and census_report["violations_observees"]["20"] == 0
            and census_report["violations_observees"]["9"] == census_report["relations"]),
        "Q1c_plafond_8_atteint": (census_report["plafond"] == CEILING
                                  and census_report["plafond_atteint"]),
        "Q1d_exclusion_A3_A17": census_report["relations_A3_et_A17"] == 0,
        "Q1e_temoins_conformes": (witness_report["W"]["conforme"]
                                  and witness_report["G"]["conforme"]
                                  and witness_report["W"]["A3_vraie"]),
        "Q2a_q_exactes": (calibration_report["q_exactes"]["9"] == 0
                          and calibration_report["q_exactes"]["12"] == 1
                          and calibration_report["q_exactes"]["20"] == 1),
        "Q2b_noyau": (calibration_report["noyau_inclus_dans_portee"]
                      and calibration_report["noyau_contient_le_publie"]),
        "Q2c_k_etoile": calibration_report["k_etoile"] in (3, 4),
        "Q3a_transfert_frequences": (counts["A9"] == transfer_report["relations"]
                                     and counts["A15"] >= 7
                                     and counts["A2"] >= 6
                                     and counts["A11"] >= 5),
        "Q3b_transfert_dans_la_portee": (
            transfer_report["portee_respectee"] == transfer_report["relations"]),
        "Q3c_transfert_K": (transfer_report["K_superieur_ou_egal_3"] >= 6
                            and transfer_report["K_minimum"] <= 4),
        "Q4a_portee_independante_de_la_densite": census_report["relations_hors_portee"] == 0,
        "Q4b_A9_fausse_a_toute_densite": all(
            report["courbe"][str(density)]["9"] == 0 for density in DENSITY_GRID),
        "Q4c_bord_complet": (
            all(number in flagged for number in (2, 3, 8, 9, 18))
            and complete["statuts"]["11"] == "true"
            and complete["statuts"]["15"] == "true"
            and complete["statuts"]["17"] == "true"
            and complete["statuts"]["16"] == "false"),
        "Q5a_balayage_3_20": all(
            three["comptes"][str(number)] == len(SWEEP_SEEDS) for number in (2, 9, 15)),
        "Q5b_balayage_3_10": all(
            three_tenths["comptes"][str(number)] == len(SWEEP_SEEDS) for number in (2, 9, 15)),
        "Q5c_balayage_7_10": (
            all(seven_tenths["comptes"][str(number)] == len(SWEEP_SEEDS)
                for number in (9, 11, 15))
            and seven_tenths["comptes"]["18"] >= 3),
        "Q5d_balayage_dans_la_portee": all(
            sweep_report[str(density)]["portee_respectee"] == len(SWEEP_SEEDS)
            and sweep_report[str(density)]["comptes"]["9"] == len(SWEEP_SEEDS)
            and sweep_report[str(density)]["K_maximum"] <= CEILING
            for density in SWEEP_DENSITIES),
    }


def verdict(report):
    """Le verdict borne, par la regle scellee (section 5 du scelle)."""
    table = report["questions"]
    lemmas_ok = all(report["lemmes"].values())
    portee_broken = [key for key in PORTEE_LEGS if not table[key]]
    null_broken = [key for key in NULL_LEGS if not table[key]]
    if not lemmas_ok:
        portee = "REFUTE"
    elif portee_broken:
        portee = "PARTIEL"
    else:
        portee = "SUPPORTED"
    if len(null_broken) >= 2:
        null = "REFUTE"
    elif null_broken:
        null = "PARTIEL"
    else:
        null = "SUPPORTED"
    undecided = report["census"]["relations_indecises"]
    if undecided * 100 > report["census"]["relations"]:
        combined = "NON_CONCLUSIF_INSTRUMENT"
    elif "REFUTE" in (portee, null):
        combined = "REFUTE"
    elif portee == "SUPPORTED" and null == "SUPPORTED":
        combined = "SUPPORTED"
    else:
        combined = "PARTIEL"
    return portee, null, combined


def _summary(report):
    table = report["questions"]
    calibration_report = report["calibration"]
    return {
        "verdict": report["verdict"],
        "verdict_portee": report["verdict_portee"],
        "verdict_null": report["verdict_null"],
        "clauses_fausses": sorted(key for key, value in table.items() if not value),
        "portee_observee": report["census"]["portee_observee"],
        "plafond": report["census"]["plafond"],
        "k_etoile": calibration_report["k_etoile"],
        "noyau_dixieme": calibration_report["noyau_dixieme"],
        "seuils_case_28_retires": [wec.P6_MIN_VIOLATIONS, wec.CONTROL_MIN_VIOLATIONS],
        "census_case_28": {"taille_max": 5, "relations": 1099},
    }


# --------------------------------------------------------------------------- #
# Assemblage
# --------------------------------------------------------------------------- #


def constants():
    """Les valeurs scellees, dans l'artefact, pour qu'il se lise seul."""
    return {
        "taille_recensement": SIZE,
        "portee_attendue": list(REACH),
        "theoremes_de_lecture": list(THEOREMS_OF_READING),
        "fausse_inconditionnellement": list(UNCONDITIONAL_FALSE),
        "plafond": CEILING,
        "paire_exclusive": list(EXCLUSIVE_PAIR),
        "grille_densite": [str(density) for density in DENSITY_GRID],
        "grille_echantillonnee": [str(density) for density in SAMPLED_GRID],
        "niveau_noyau": str(CORE_LEVEL),
        "confiance": str(CONFIDENCE),
        "transfert": {"taille": TRANSFER_SIZE, "graines": list(TRANSFER_SEEDS),
                      "controles": list(TRANSFER_CONTROL_SEEDS)},
        "balayage": {"graines": list(SWEEP_SEEDS),
                     "densites": [str(density) for density in SWEEP_DENSITIES],
                     "hors_verdict": str(EXPLORATORY_DENSITY)},
        "graines_publiees": {"test": list(PUBLISHED_SEEDS),
                             "controle": list(PUBLISHED_CONTROL_SEEDS),
                             "balayage": list(PUBLISHED_SWEEP_SEEDS)},
        "noyau_publie": list(PUBLISHED_CORE),
    }


def run_all(size=SIZE):
    """Le banc complet : recensement, null, courbe, temoins, transfert, balayage."""
    census_report = census(size)
    report = {
        "case": CASE,
        "organe": ORGAN,
        "scelle": SEAL,
        "constants": constants(),
        "lemmes": lemmas(census_report),
        "census": census_report,
        "calibration": calibration(census_report),
        "courbe": exact_curve(census_report),
        "temoin": witnesses(),
        "bord_complet": complete_edge(size),
        "transfert": transfer(),
        "balayage": sweep(),
    }
    report["questions"] = legs(report)
    portee, null, combined = verdict(report)
    report["verdict_portee"] = portee
    report["verdict_null"] = null
    report["verdict"] = combined
    report["summary"] = _summary(report)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Case 28b : portee exacte et null calibre de l'instrument relationnel")
    parser.add_argument("--out", default=str(RESULTS))
    parser.add_argument("--size", type=int, default=SIZE)
    args = parser.parse_args(argv)
    report = run_all(size=args.size)
    path = Path(args.out)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(report, indent=2, sort_keys=True, default=wec._json_default) + "\n"
    path.write_text(payload, encoding="utf-8")
    print("ecrit : {0} ({1} octets)".format(path, len(payload)))
    print("portee : {0}".format(report["census"]["portee_observee"]))
    print("plafond : {0} (atteint : {1})".format(
        report["census"]["plafond"], report["census"]["plafond_atteint"]))
    print("k* : {0}".format(report["calibration"]["k_etoile"]))
    print("verdict : {0} / portee {1} / null {2}".format(
        report["verdict"], report["verdict_portee"], report["verdict_null"]))
    broken = report["summary"]["clauses_fausses"]
    print("clauses fausses : {0}".format(broken if broken else "aucune"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
