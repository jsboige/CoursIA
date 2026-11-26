"""Structure causale du Pli 5, Grain C -- #23093 (EPIC Origami #19742).

Le Grain A (PR #26671) a retenu setreplace-py 0.2.0 (SOTA-OK) et constate
que le graphe causal y est natif (``causal_graph_edges()``). Le Grain B
(PR #26675) a mesure la proliferation multiway. Le present organe mesure la
structure causale du temoin (meme regle de l'annonce, meme etat initial
etoile, meme rejeu de 1500 evenements) et la CONFRONTE a la Definition 4 de
Gorard 2020 (copie archivee au gisement, chemin dans le doc de pont) :
un graphe causal est un DAG dont les sommets sont les evenements et dont
l'arete A->B existe ssi l'entree de B recouvre la sortie de A.

Controles declares AVANT la mesure :

- CC1 : le graphe causal natif est un DAG oriente vers l'avant (toute arete
  va d'un evenement anterieur vers un evenement posterieur, pas de boucle) ;
- CC2 : les sommets sont exactement les evenements (bijection avec 1..N, la
  convention de numerotation 0-/1-based est mesuree et documentee) ;
- CC3a : le graphe natif coïncide avec la relation JETON reconstruite
  independamment depuis le grand livre ``tokens()`` (pour chaque evenement,
  une arete depuis le createur de chacun de ses jetons d'entree) ;
- CC3b : la relation reconstruite depuis le SEUL diff d'etats (par
  contenus) en diverge, et TOUTE divergence est portee par un evenement
  AMBIGU : quand le membre gauche re-cree le membre droit {x,z}, deux
  applications distinctes de la regle peuvent produire le meme etat, et le
  diff ne determine alors pas laquelle a eu lieu.

CC3b est la decouverte du grain : la forme pragmatique de la Definition 4
(recouvrement entree/sortie) est vraie au niveau des objets (jetons), mais
n'est pas reconstruisible depuis les seuls etats -- le diff d'etat est une
projection perdante de l'evenement de reecriture.

Les metriques de structure (profondeur, largeurs de niveaux, degres) sont
descriptives : elles caracterisent la structure causale emergente du temoin,
aucun verdict n'en depend.

Usage :

    python scripts/hashlife/causal_structure.py > resultat.json

Sortie : un unique document JSON sur la sortie standard (a committer verbatim).
"""

from __future__ import annotations

import hashlib
import json
import sys
import time
from collections import defaultdict

from setreplace import HypergraphSystem, Rule

# --- Parametres du grain, declares avant toute mesure ------------------------

RULE_STR = "{{x, y}, {x, z}} -> {{x, z}, {x, w}, {y, w}, {z, w}}"
RULE_ORIGIN = "regle de l'annonce du Wolfram Physics Project (temoin des Grains A et B, PR #26671 / #26675)"
INITIAL_EDGES: tuple[tuple[int, ...], ...] = ((1, 2), (1, 3), (1, 4), (1, 5))

REPLAY_EVENTS = 1500  # meme temoin deterministe que les Grains A et B

DECLARED_BEFORE = {
    "controles": {
        "CC1_dag_avant": "toute arete native normalisee (a, b) verifie a < b strictement (un evenement ne peut dependre que d'un evenement anterieur) ; toute arete a >= b = echec",
        "CC2_sommets_evenements": "l'ensemble des sommets natifs est de cardinal N (nombre d'evenements) et forme un intervalle contigu ; la convention 0-based ou 1-based est mesuree et documentee",
        "CC3a_identite_jeton": "l'ensemble des aretes natives est EGAL a la relation reconstruite depuis le grand livre tokens() : pour chaque evenement b >= 1 et chaque jeton d'entree t de b dont le createur n'est pas la condition initiale, une arete (createur(t), b)",
        "CC3b_ambiguite_diff": "la relation par contenus (createur le plus recent du contenu consomme, reconstruite depuis les seuls diffs d'etats) diverge de la relation jeton ; la cause declaree est l'AMBIGUITE : quand le membre droit re-cree le membre gauche {x,z}, deux liaisons distinctes peuvent produire le MEME etat, le diff ne tranche pas, et l'erreur d'attribution se propage en aval. Controle : (1) compter les evenements ambigus (au moins deux liaisons valides) ; (2) verifier que la relation par contenus, les liaisons ambigues tranchees par le grand livre de jetons, coïncide EXACTEMENT avec la relation native ; (3) rapporter combien de fois la liaison choisie par le rejeu par diff differe de la vraie",
        "mesure_void_si": "CC1 ou CC2 echoue (le graphe natif ne serait alors pas le graphe causal de la Definition 4)",
    },
    "relation_jetons": "le paquet expose un grand livre : chaque jeton (arete-objet) porte ses atomes, son evenement createur et son evenement destructeur ; l'evenement 0 est la condition initiale (aucune arete causale n'en part) ; un jeton re-cree par le membre droit {x,z} est un NOUVEAU jeton (l'ancien est detruit)",
    "ambiguite_declaree": "quand un evenement consomme {x,y},{x,z} et que le membre droit re-cree {x,z}, une AUTRE paire d'aretes de l'etat precedent peut produire le MEME etat resultant (le {x,z} re-cree compense exactement) ; le diff d'etats (1 consommee, 3 creees) ne determine alors pas la liaison appliquee ; declare avant mesure d'apres la dissection des evenements 9-13 du present temoin",
    "structure_descriptive": "profondeur (plus long chemin), largeurs de niveaux, degres entrants/sortants, sources et puits -- aucune n'alimente un verdict ; elles caracterisent le temoin",
    "copie_couche_rejeu": "la reconstruction de liaison par differences d'etats est copiee depuis l'organe du Grain B (scripts/hashlife/hypergraph_multiway.py, PR #26675, pas encore sur main a la redaction) ; l'organe est autonome par rapport a main",
}

# --- Couche de rejeu par differences d'etats (copie Grain B) ------------------

Atom = int
Edge = frozenset  # frozenset[Atom]


def _replay_binding(prev: frozenset[Edge], cur: frozenset[Edge]) -> dict[str, Atom] | None:
    """Retrouve UNE liaison de la regle qui explique la transition observee.

    Un evenement consomme {x,y} et {x,z} puis re-cree {x,z} : la difference
    prev - cur vaut exactement {{x,y}}, et cur - prev vaut exactement les trois
    aretes {x,w}, {y,w}, {z,w}. La liaison est reconstruite depuis ces deux
    differences ; la fonction rend None si aucune liaison ne colle. Cette
    reconstruction est AMBIGUE sur les evenements ou deux applications
    distinctes produisent le meme etat (cf. declared_before.ambiguite_declaree).
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
                return {"x": x, "y": y, "z": z, "w": w}
    return None


def _new_atom(prev: frozenset[Edge], cur: frozenset[Edge]) -> Atom | None:
    new_atoms = {a for e in (cur - prev) for a in e} - {a for e in prev for a in e}
    return next(iter(new_atoms)) if len(new_atoms) == 1 else None


def valid_liaisons(prev: frozenset[Edge], cur: frozenset[Edge]) -> list[tuple[Atom, Atom, Atom]]:
    """Toutes les liaisons (x, y, z) du membre gauche sur prev qui produisent cur.

    w est fixe par l'atome neuf observe dans cur. Deux liaisons distinctes
    produisant le meme etat = evenement AMBIGU (cf. declaration).

    Verifie par equivalence de diffs (sans reconstruire l'etat resultant) :
    la liaison (x, y, z, w) produit cur ssi {x,y} et {x,z} sont dans prev et

        prev - cur == { {x,y} }            (seule arete reellement detruite)
        cur - prev == { {x,w},{y,w},{z,w} } (trois aretes reellement creees)

    puisque le membre droit re-cree {x,z}, invisible dans le diff.
    """
    w = _new_atom(prev, cur)
    if w is None:
        return []
    consumed_diff = prev - cur  # exactement 1 arete (garanti par _replay_binding)
    created_diff = cur - prev
    if len(consumed_diff) != 1 or len(created_diff) != 3:
        return []
    e = next(iter(consumed_diff))
    out: list[tuple[Atom, Atom, Atom]] = []
    for x in tuple(e):
        y = next(iter(e - {x}))
        # candidats {x, z} : aretes de prev contenant x, presentes aussi dans
        # cur (le membre droit les re-cree), differentes de l'arete detruite
        for cand in prev:
            if x not in cand or cand == e or cand not in cur:
                continue
            z = next(iter(cand - {x}))
            if {frozenset((x, w)), frozenset((y, w)), frozenset((z, w))} == created_diff:
                out.append((x, y, z))
    return out


def canonical(state: frozenset[Edge]) -> list[list[int]]:
    return sorted(sorted(e) for e in state)


def state_sha(state: frozenset[Edge]) -> str:
    payload = json.dumps(canonical(state), separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()[:16]


# --- Structure du DAG --------------------------------------------------------

def dag_structure(n_events: int, edges: set[tuple[int, int]]) -> dict:
    """Metriques descriptives du DAG (evenements numerotes 1..N, aretes a<b)."""
    indeg = defaultdict(int)
    outdeg = defaultdict(int)
    for a, b in edges:
        outdeg[a] += 1
        indeg[b] += 1
    depth = [0] * (n_events + 1)  # profondeur 0 = source
    # les aretes pointent vers l'avant : une passe croissante suffit
    for a, b in sorted(edges):
        if depth[b] < depth[a] + 1:
            depth[b] = depth[a] + 1
    level_width: dict[int, int] = defaultdict(int)
    for v in range(1, n_events + 1):
        level_width[depth[v]] += 1
    max_depth = max(depth[1:])
    sources = sum(1 for v in range(1, n_events + 1) if indeg[v] == 0)
    sinks = sum(1 for v in range(1, n_events + 1) if outdeg[v] == 0)
    in_vals = [indeg[v] for v in range(1, n_events + 1)]
    out_vals = [outdeg[v] for v in range(1, n_events + 1)]
    return {
        "sommets": n_events,
        "aretes": len(edges),
        "degre_sortant_moyen": round(len(edges) / n_events, 3),
        "sources_ind0": sources,
        "puits_out0": sinks,
        "degre_entrant_max": max(in_vals),
        "degre_sortant_max": max(out_vals),
        "profondeur_max": max_depth,
        "evenements_par_profondeur": max_depth + 1,
        "largeur_niveau_max": max(level_width.values()),
        "largeurs_par_niveau": [
            {"profondeur": d, "largeur": level_width[d]} for d in range(max_depth + 1)
        ],
        "ratio_evenements_profondeur": round(n_events / max_depth, 3) if max_depth else None,
    }


# --- Mesure -------------------------------------------------------------------

def main() -> None:
    t0 = time.perf_counter()
    rule = Rule.parse(RULE_STR)
    sys_ref = HypergraphSystem(rule, [list(e) for e in INITIAL_EDGES])
    sys_ref.evolve(max_events=REPLAY_EVENTS)
    states_raw = sys_ref.states_by_event()  # states[0] = initial, states[i] = apres evenement i
    n_events = len(states_raw) - 1
    states = [frozenset(frozenset(e) for e in st) for st in states_raw]

    native_raw = sys_ref.causal_graph_edges()
    vertices = sorted({v for e in native_raw for v in e})
    vmin, vmax, vcount = vertices[0], vertices[-1], len(vertices)
    contigu = vcount == vmax - vmin + 1
    offset = 1 - vmin
    native = {(a + offset, b + offset) for a, b in native_raw}
    convention = "1-based (sommets = numeros d'evenements)" if vmin == 1 else (
        "0-based (sommet v = evenement v+1)" if vmin == 0 else f"min={vmin}, decalage normalise"
    )

    cc1_forward = all(a < b for a, b in native)
    cc2_pass = contigu and vcount == n_events

    # CC3a : relation jeton reconstruite depuis le grand livre, sans passer par
    # causal_graph_edges
    events = sys_ref.events()
    tokens = sys_ref.tokens()
    tok_rel: set[tuple[int, int]] = set()
    for b, ev in enumerate(events):
        if b == 0:
            continue
        for t in ev.inputs:
            c = tokens[t].creator_event
            if c != 0:  # 0 = condition initiale
                tok_rel.add((c, b))

    # relation par contenus (diffs d'etats seuls), en deux resolutions de
    # l'ambiguite : la liaison telle que le rejeu par diff la choisit, et la
    # liaison vraie (celle dont les contenus consommes egalent les jetons
    # d'entree du grand livre)
    def _run_content(resolve_by_ledger: bool) -> tuple[set[tuple[int, int]], int, int, int]:
        rel: set[tuple[int, int]] = set()
        rec: dict[Edge, int | None] = {e: None for e in states[0]}
        n_ambiguous = 0
        n_pick_error = 0
        n_ok = 0
        for i in range(1, n_events + 1):
            prev, cur = states[i - 1], states[i]
            vl = valid_liaisons(prev, cur)
            if not vl:
                break
            picked = _replay_binding(prev, cur)
            if picked is None:
                break
            liaison = (picked["x"], picked["y"], picked["z"])
            if len(vl) >= 2:
                n_ambiguous += 1
                if resolve_by_ledger:
                    true_in = {frozenset(tokens[t].atoms) for t in events[i].inputs}
                    for x, y, z in vl:
                        if {frozenset((x, y)), frozenset((x, z))} == true_in:
                            liaison = (x, y, z)
                            break
            if liaison != (picked["x"], picked["y"], picked["z"]):
                n_pick_error += 1
            x, y, z = liaison
            w = _new_atom(prev, cur)
            consumed = {frozenset((x, y)), frozenset((x, z))}
            created = {
                frozenset((x, z)),
                frozenset((x, w)),
                frozenset((y, w)),
                frozenset((z, w)),
            }
            for c in consumed:
                a = rec.get(c)
                if a is not None:
                    rel.add((a, i))
            for c in consumed:
                if c not in created:
                    rec.pop(c, None)
            for c in created:
                rec[c] = i
            n_ok += 1
        return rel, n_ok, n_ambiguous, n_pick_error

    content_rel_diff, replay_ok, n_ambiguous, _ = _run_content(resolve_by_ledger=False)
    content_rel_resolved, _, _, n_pick_error = _run_content(resolve_by_ledger=True)

    tok_minus_diff = sorted(tok_rel - content_rel_diff)
    diff_minus_tok = sorted(content_rel_diff - tok_rel)
    resolved_exact = content_rel_resolved == tok_rel

    cc3 = {
        "CC3a_identite_jeton": {
            "aretes_native": len(native),
            "aretes_relation_jeton": len(tok_rel),
            "identite_exacte": native == tok_rel,
            "pass": native == tok_rel,
        },
        "CC3b_ambiguite_diff": {
            "aretes_jeton_non_contenu_diff": len(tok_minus_diff),
            "aretes_contenu_diff_non_jeton": len(diff_minus_tok),
            "evenements_ambigus": n_ambiguous,
            "erreurs_choix_du_rejeu_par_diff": n_pick_error,
            "relation_contenus_ambiguite_resolue_egale_native": resolved_exact,
            "aretes_relation_contenus_resolue": len(content_rel_resolved),
            "exemples_jetons_non_contenu_diff": tok_minus_diff[:3],
            "exemples_contenu_diff_non_jetons": diff_minus_tok[:3],
            "pass": resolved_exact,
        },
    }

    controles = {
        "reference": {
            "package": "setreplace 0.2.0",
            "events": n_events,
            "tokens": len(tokens),
            "final_state_sha256_16": state_sha(states[-1]),
            "rejeu_diff_ok": replay_ok == n_events,
        },
        "CC1_dag_avant": {
            "convention_numerotation": convention,
            "sommets_min": vmin,
            "sommets_max": vmax,
            "toutes_aretes_avant": cc1_forward,
            "pass": cc1_forward,
        },
        "CC2_sommets_evenements": {
            "sommets_distincts": vcount,
            "evenements": n_events,
            "intervalle_contigu": contigu,
            "pass": cc2_pass,
        },
        "CC3": cc3,
        "pass": cc1_forward and cc2_pass and cc3["CC3a_identite_jeton"]["pass"],
    }

    result = {
        "probe": "pli5-grainC-structure-causale",
        "issue": 23093,
        "date": time.strftime("%Y-%m-%d"),
        "seat": "myia-po-2024 (Windows, python 3.13)",
        "organe": "scripts/hashlife/causal_structure.py",
        "regle": RULE_STR,
        "regle_origine": RULE_ORIGIN,
        "etat_initial": canonical(frozenset(INITIAL_EDGES)),
        "declared_before_measurement": DECLARED_BEFORE,
        "controles": controles,
        "structure_causale": (
            dag_structure(n_events, native)
            if controles["pass"]
            else None
        ),
        "mesure_void_si_controles_echouent": controles["pass"] is False,
        "wall_s": round(time.perf_counter() - t0, 2),
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
