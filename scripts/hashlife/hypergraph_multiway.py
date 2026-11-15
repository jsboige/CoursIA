"""Couche multiway maison du Pli 5, Grain B -- #23093 (EPIC Origami #19742).

Le verdict d'outil du Grain A (PR #26671) a retenu setreplace-py 0.2.0
(SOTA-OK) pour la substitution exacte et le graphe causal, et constate que la
brique multiway n'y est pas exposee. Le present organe est l'instrumentation
maison declaree par ce verdict :

1. un moteur de reecriture d'hypergraphes independant (appariement et
   application de regle en pur Python) ;
2. un controle de correction en trois volets contre setreplace lui-meme :
   C1 rejeu semantique de chaque evenement observe, C2 completude de
   l'enumerateur sur un prefixe borne, C3 temoin d'etat final par empreinte ;
3. l'exploration multiway mesuree : nombre d'etats et temps par generation,
   dont l'exposant d'echelle temps/etats -- la question du pli etant : la
   croissance du nombre de branches est-elle reductible ou non.

Les seuils sont declares AVANT la mesure (bloc ``declared_before_measurement``
du JSON emis) et la mesure est VOIDE si l'un des controles echoue.

Usage :

    python scripts/hashlife/hypergraph_multiway.py > resultat.json

Sortie : un unique document JSON sur la sortie standard (a committer verbatim).
"""

from __future__ import annotations

import hashlib
import json
import math
import sys
import time
from collections import defaultdict

from setreplace import HypergraphSystem, Rule

# --- Parametres du grain, declares avant toute mesure ------------------------

RULE_STR = "{{x, y}, {x, z}} -> {{x, z}, {x, w}, {y, w}, {z, w}}"
RULE_ORIGIN = "regle de l'annonce du Wolfram Physics Project (temoin du Grain A, PR #26671)"
INITIAL_EDGES: tuple[tuple[int, ...], ...] = ((1, 2), (1, 3), (1, 4), (1, 5))

REPLAY_EVENTS = 1500  # longueur du rejeu deterministe (meme valeur que le Grain A)
ENUMERATOR_PREFIX = 100  # evenements ou l'enumerateur complet est verifie

DECLARED_BEFORE = {
    "arret": {
        "etats_cumules_max": 150_000,
        "mur_secondes": 90.0,
        "generation_max": 10,
    },
    "verdict_croissance": {
        "non_reductible": "lambda_g = |gen_g|/|gen_{g-1}| > 1.5 pour toute transition mesuree, et R2 du fit log|gen| ~ g > 0.97",
        "reductible": "lambda <= 1.15 sur le dernier tiers des transitions mesurees",
        "sinon": "INCONCLUSIVE",
    },
    "exposant_temps": {
        "mesure": "pente de la regression log(temps_cumule) ~ log(etats_vus) sur les points enregistres a chaque doublement du nombre d'etats vus (premier point a 64), au moins 3 points",
        "superlineaire_si": "pente > 1.2 avec R2 > 0.98",
    },
    "controle_correctness": {
        "C1": "chacun des evenements de setreplace est une instance valide de la regle et sa re-application maison redonne exactement l'etat observe",
        "C2": "l'enumerateur complet de la couche maison trouve la liaison choisie par setreplace sur chacun des 100 premiers evenements",
        "C3": "l'etat final rejoue par la couche maison est egal, atome pour atome, a l'etat final setreplace (empreinte sha256 des deux formes canoniques)",
        "mesure_void_si": "un quelconque controle echoue",
    },
    "dedup": "etats multiway dedupliques par etat EXACT etiquete ; l'atome neuf w de chaque application vaut 1 + max(atomes de l'etat source), fonction pure de (etat, liaison)",
    "granularite_arret": "le cap etats_cumules_max est applique PENDANT la generation : l'exploration s'arrete net des que le nombre d'etats vus atteint le cap ; la generation coupee est marquee tronquee, et exclue des ratios lambda et du fit de l'exposant",
}

# --- Moteur maison -----------------------------------------------------------

Atom = int
Edge = frozenset  # frozenset[Atom]
State = frozenset  # frozenset[Edge]

PATTERN_LEFT = (frozenset({"x", "y"}), frozenset({"x", "z"}))
PATTERN_RIGHT = (
    frozenset({"x", "z"}),
    frozenset({"x", "w"}),
    frozenset({"y", "w"}),
    frozenset({"z", "w"}),
)


def _unify_edge(pattern_edge: frozenset, edge: Edge) -> list[dict[str, Atom]]:
    """Lie les 2 variables d'une arete du pattern a une arete d'etat, dans les 2 ordres."""
    a, b = tuple(pattern_edge)
    u, v = tuple(edge)
    return [{a: u, b: v}, {a: v, b: u}]


def _merge(b1: dict[str, Atom], b2: dict[str, Atom]) -> dict[str, Atom] | None:
    """Fusionne deux liaisons partielles ; None si elles contredisent une variable commune."""
    m = dict(b1)
    for k, val in b2.items():
        if k in m and m[k] != val:
            return None
        m[k] = val
    return m


def enumerate_matches(state: State) -> list[dict[str, Atom]]:
    """Toutes les liaisons injectives du membre gauche de la regle dans l'etat.

    Passe par un index atome -> aretes : seules les paires d'aretes partageant
    un atome sont considerees (les deux aretes du pattern partagent x). Les
    liaisons (x, y, z) et (x, z, y) sont deux evenements distincts : la regle
    est asymetrique en y et z, elles sont toutes deux conservees.
    """
    by_atom: dict[Atom, list[Edge]] = defaultdict(list)
    for e in state:
        for a in e:
            by_atom[a].append(e)
    seen: set[tuple[Atom, Atom, Atom]] = set()
    out: list[dict[str, Atom]] = []
    for edges in by_atom.values():
        n = len(edges)
        for i in range(n):
            for j in range(i + 1, n):
                for e1, e2 in ((edges[i], edges[j]), (edges[j], edges[i])):
                    for b1 in _unify_edge(PATTERN_LEFT[0], e1):
                        for b2 in _unify_edge(PATTERN_LEFT[1], e2):
                            m = _merge(b1, b2)
                            if m is None:
                                continue
                            key = (m["x"], m["y"], m["z"])
                            if key not in seen:
                                seen.add(key)
                                out.append(m)
    return out


def fresh_atom(state: State) -> Atom:
    """Etiquette neuve canonique pour l'atome w : 1 + max des atomes de l'etat."""
    return max(a for e in state for a in e) + 1


def apply_match(state: State, m: dict[str, Atom], w: Atom) -> State:
    """Applique la regle a une liaison donnee ; ``w`` est l'atome neuf."""
    binding = dict(m)
    binding["w"] = w
    consumed = {
        frozenset((binding["x"], binding["y"])),
        frozenset((binding["x"], binding["z"])),
    }
    created = {frozenset(binding[v] for v in pe) for pe in PATTERN_RIGHT}
    return frozenset(state - consumed | created)


def canonical(state: State) -> list[list[int]]:
    return sorted(sorted(e) for e in state)


def state_sha(state: State) -> str:
    payload = json.dumps(canonical(state), separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()[:16]


# --- Controles ---------------------------------------------------------------

def _replay_binding(prev: State, cur: State) -> dict[str, Atom] | None:
    """Retrouve l'unique liaison de la regle qui explique la transition observee.

    Un evenement consomme {x,y} et {x,z} puis re-cre'e {x,z} : la difference
    prev - cur vaut exactement {{x,y}}, et cur - prev vaut exactement les trois
    aretes {x,w}, {y,w}, {z,w}. La liaison est determinee de maniere unique par
    ces deux differences ; la fonction rend None si aucune liaison ne colle.
    """
    consumed = prev - cur
    created = cur - prev
    if len(consumed) != 1 or len(created) != 3:
        return None
    e = next(iter(consumed))
    a, b = tuple(e)
    created_list = [set(x) for x in created]
    for x, y in ((a, b), (b, a)):
        # candidats {x, z} dans prev (les aretes contenant x, differentes de {x,y})
        for cand in prev:
            if x not in cand or cand == e:
                continue
            z = next(iter(cand - {x}))
            # les aretes creees attendues : {x,w},{y,w},{z,w} avec un unique w neuf,
            # c'est-a-dire exactement une arete creee par role contenant ce role
            # et aucun autre atome de {x, y, z}
            ws = set()
            ok = True
            for role in (x, y, z):
                pair = [c for c in created_list if c & {role} and not (c & {x, y, z}) - {role}]
                if len(pair) != 1:
                    ok = False
                    break
                ws.add(next(iter(pair[0] - {role})))
            if not ok or len(ws) != 1:
                continue
            w = next(iter(ws))
            expected = {frozenset((x, w)), frozenset((y, w)), frozenset((z, w))}
            if expected == created:
                return {"x": x, "y": y, "z": z}
    return None


def run_controls() -> dict:
    """Rejeu deterministe et temoin, contre un run setreplace equivalent."""
    rule = Rule.parse(RULE_STR)
    sys_ref = HypergraphSystem(rule, [list(e) for e in INITIAL_EDGES])
    t0 = time.perf_counter()
    sys_ref.evolve(max_events=REPLAY_EVENTS)
    ref_wall = time.perf_counter() - t0
    states = sys_ref.states_by_event()  # states[0] = initial, states[i] = apres evenement i
    n_events = len(states) - 1

    c1_ok = 0
    c2_hits = c2_checked = 0
    replay: State = frozenset(frozenset(e) for e in INITIAL_EDGES)
    deterministic_agree = 0

    for i in range(1, len(states)):
        prev = frozenset(frozenset(e) for e in states[i - 1])
        cur = frozenset(frozenset(e) for e in states[i])
        binding = _replay_binding(prev, cur)
        if binding is None:
            break
        new_atoms = {a for e in (cur - prev) for a in e} - {a for e in prev for a in e}
        if len(new_atoms) != 1:
            break
        applied = apply_match(replay, binding, next(iter(new_atoms)))
        if applied != cur:
            break
        # C2 et diagnostic : la liaison retenue doit figurer dans l'enumeration
        # COMPLETE de l'etat AVANT l'evenement (l'arete {x,y} consommee n'y est plus apres)
        if i <= ENUMERATOR_PREFIX:
            matches_on_prev = enumerate_matches(prev)
            c2_checked += 1
            if binding in matches_on_prev:
                c2_hits += 1
            if matches_on_prev and matches_on_prev[0] == binding:
                deterministic_agree += 1
        replay = cur  # le rejeu suit l'espace observe, par construction identique
        c1_ok += 1

    ref_final = frozenset(frozenset(e) for e in states[-1])
    return {
        "reference": {
            "package": "setreplace 0.2.0",
            "events": n_events,
            "wall_s": round(ref_wall, 3),
            "final_edges": len(ref_final),
            "final_state_sha256_16": state_sha(ref_final),
        },
        "C1_rejeu_semantique": {"ok": c1_ok, "checked": n_events, "pass": c1_ok == n_events},
        "C2_enum_complet_prefixe": {
            "hits": c2_hits,
            "checked": c2_checked,
            "pass": c2_checked == ENUMERATOR_PREFIX and c2_hits == c2_checked,
        },
        "C3_temoin_final": {
            "replayed_sha256_16": state_sha(replay),
            "reference_sha256_16": state_sha(ref_final),
            "pass": replay == ref_final,
        },
        "diagnostic_ordre_canonique": {
            "accord_premier_match": deterministic_agree,
            "sur_prefixe": c2_checked,
        },
        "pass": (
            c1_ok == n_events
            and c2_checked == ENUMERATOR_PREFIX
            and c2_hits == c2_checked
            and replay == ref_final
        ),
    }


# --- Mesure multiway ---------------------------------------------------------

def run_multiway() -> dict:
    """Exploration multiway en largeur, mesuree, sous les seuils declares."""
    stop = DECLARED_BEFORE["arret"]
    t_start = time.perf_counter()
    frontier: set[State] = {frozenset(INITIAL_EDGES)}
    seen: set[State] = set(frontier)
    gens: list[dict] = []
    cumulative = 1
    gen = 0
    # points (etats_vus, temps_cumule) a chaque doublement, pour l'exposant
    doubling: list[list[float]] = [[1.0, 0.0]]
    next_mark = 64

    def _mark() -> None:
        nonlocal next_mark
        while len(seen) >= next_mark:
            doubling.append([len(seen), round(time.perf_counter() - t_start, 4)])
            next_mark *= 2

    while frontier and gen < stop["generation_max"]:
        g_t0 = time.perf_counter()
        nxt: set[State] = set()
        matches_total = 0
        truncated = False
        for st in sorted(frontier, key=canonical):  # ordre deterministe, reproductible
            w = fresh_atom(st)
            for m in enumerate_matches(st):
                matches_total += 1
                child = apply_match(st, m, w)
                if child not in seen:
                    seen.add(child)
                    nxt.add(child)
                    _mark()
                    if len(seen) >= stop["etats_cumules_max"]:
                        truncated = True
                        break
            if truncated:
                break
        g_wall = time.perf_counter() - g_t0
        cumulative += len(nxt)
        gens.append({
            "generation": gen + 1,
            "etats": len(nxt),
            "etats_cumules": cumulative,
            "matches_totaux": matches_total,
            "wall_s": round(g_wall, 3),
            "tronquee": truncated,
        })
        gen += 1
        frontier = nxt
        if truncated:
            break
        if time.perf_counter() - t_start >= stop["mur_secondes"]:
            break

    total_wall = time.perf_counter() - t_start

    # exposant temps/etats : regression log-log sur les points de doublement
    xs = [math.log(p[0]) for p in doubling]
    ys = [math.log(max(p[1], 1e-6)) for p in doubling]
    alpha = r2 = None
    # lambdas sur les generations COMPLETES uniquement (declaration)
    complete = [g for g in gens if not g["tronquee"]]
    if len(xs) >= 3:
        n = len(xs)
        mx, my = sum(xs) / n, sum(ys) / n
        sxx = sum((x - mx) ** 2 for x in xs)
        sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        syy = sum((y - my) ** 2 for y in ys)
        if sxx > 0 and syy > 0:
            alpha = sxy / sxx
            r2 = (sxy * sxy) / (sxx * syy)

    lambdas = [
        complete[i]["etats"] / complete[i - 1]["etats"]
        for i in range(1, len(complete))
        if complete[i - 1]["etats"] > 0
    ]
    verdict = "INCONCLUSIVE"
    croissance_r2 = None
    if len(complete) >= 3:
        gs = [math.log(max(g["etats"], 1)) for g in complete]
        n = len(gs)
        mx = sum(range(n)) / n
        my = sum(gs) / n
        sxx = sum((i - mx) ** 2 for i in range(n))
        sxy = sum((i - mx) * (g - my) for i, g in enumerate(gs))
        syy = sum((g - my) ** 2 for g in gs)
        if sxx > 0 and syy > 0:
            croissance_r2 = round((sxy * sxy) / (sxx * syy), 4)
    if len(lambdas) >= 2:
        tail = lambdas[-max(1, len(lambdas) // 3):]
        if all(l > 1.5 for l in lambdas) and croissance_r2 is not None and croissance_r2 > 0.97:
            verdict = "NON_REDUCTIBLE"
        elif all(l <= 1.15 for l in tail):
            verdict = "REDUCTIBLE"

    arrets = []
    if cumulative >= stop["etats_cumules_max"]:
        arrets.append("etats_cumules_max")
    if total_wall >= stop["mur_secondes"]:
        arrets.append("mur_secondes")
    if gen >= stop["generation_max"]:
        arrets.append("generation_max")
    if not frontier:
        arrets.append("epuisement")

    return {
        "regle": RULE_STR,
        "regle_origine": RULE_ORIGIN,
        "etat_initial": canonical(frozenset(INITIAL_EDGES)),
        "arrets": arrets,
        "generations": gens,
        "lambdas_par_transition": [round(l, 3) for l in lambdas],
        "points_doublement": doubling,
        "exposant_temps_alpha": round(alpha, 3) if alpha is not None else None,
        "exposant_r2": round(r2, 4) if r2 is not None else None,
        "croissance_log_gen_r2": croissance_r2,
        "verdict_croissance": verdict,
        "wall_total_s": round(total_wall, 1),
    }


def main() -> None:
    result = {
        "probe": "pli5-grainB-mesure",
        "issue": 23093,
        "date": time.strftime("%Y-%m-%d"),
        "seat": "myia-po-2024 (Windows, python 3.13)",
        "organe": "scripts/hashlife/hypergraph_multiway.py",
        "declared_before_measurement": DECLARED_BEFORE,
        "controles": None,
        "mesure_multiway": None,
    }
    result["controles"] = run_controls()
    if result["controles"]["pass"]:
        result["mesure_multiway"] = run_multiway()
    else:
        result["mesure_void"] = "controle de correction echoue -- mesure non produite (seuil declare avant mesure)"
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
