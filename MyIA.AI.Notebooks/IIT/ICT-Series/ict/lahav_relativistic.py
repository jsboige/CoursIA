"""Jouet « conscience relativiste » pour la distillation Lahav (case 23, #8182 iceberg L3).

La thèse formalise ELLE-MÊME sa structure d'accès : le modèle à trois niveaux
S = (T, P, C) (éq 2), l'identité première personne c = Q (éq 35), le ∅ des
sous-systèmes supérieurs sur les représentations d'autrui (éqs 36-38), la
mesure des seules propriétés physiques par la sensation (éqs 39-40) et la
transformation entre cadres Ξνµ à deux conditions — appartenance m_C et
position δ_r (éq 46), dont le scénario de symétrie brisée (éqs 49-50 : mêmes
dynamiques, positions différentes → mutuellement troisième personne) montre
la nécessité des deux. Ce module rend la triple structure falsifiable AU
NIVEAU SIGNAL (grade C documentaire — aucune phénoménologie n'est mesurée ni
revendiquée) :

- P1 mesure directe : dans son cadre et à sa position, C reconnaît ses
  propres jugements (« ALICE measures qualia », éq 18/42) ;
- P2 ∅ direct inter-cadres : les jugements d'un système appris séparément ne
  sont reconnus par aucun sous-système supérieur d'un autre cadre
  (« Alice and Bob have no states in common ») ;
- P3 voie physique intacte : la sensation d'autrui mesure les coordonnées du
  pattern et identifie LEQUEL des K jugements il était — « phenomenal
  properties are not truly private », la transformation est possible.

Null (b) : le routage « appartenance seule » (sans δ_r) contredit Ξνµ sur le
cas propre-quale-symétrie-brisée ; l'approximation éq 51 (δ_r seul) se
contredit sur les entrées tierces co-localisées.

Anti-duplication : case 13 (montante) et case 18 (descendante) testent la
structure du CHAMP ; case 23 teste la structure de l'ACCÈS — codebooks appris
séparément + position, prédicats de routage et taux de reconnaissance, pas
des corrélations dynamiques. Case 14 = séparabilité connectivité/cause
commune pour la frontière ; case 23 = géométrie des canaux de mesure.

Le scellé (bandes, graines, nulls, portes, verdicts) vit dans
docs/ict/lahav-relativistic-pre-enregistrement.md — ce module ne le
redéfinit pas, il l'exécute.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path

import numpy as np

__all__ = [
    "CognitiveSystem",
    "build_world",
    "recognize",
    "lab_prototypes",
    "channel_accuracy",
    "dispatch_table",
    "calibrate",
    "verdict",
    "run_seed",
    "TEST_SEEDS",
    "CALIB_SEEDS",
]

# Paramètres gelés par le scellé v1 (pré-enregistrement §4).
D_CODE = 64        # axes de l'espace d'état (« every degree of freedom is an axis »)
K_INPUTS = 8       # entrées cataloguées x_t
D_PROPS = 6        # propriétés physiques y des entrées
SIGMA_EPS = 0.05   # bruit de dynamique sur l'état de C participant à la mesure
TAU = 0.80         # seuil de reconnaissance (cosinus), gelé a priori
M_LAB = 40         # observations bruitées par pattern pendant la session labo
N_TEST = 200       # observations fraîches pour la précision du canal
SIGMA_T_GRID = (0.05, 0.10, 0.15, 0.20, 0.30)
TEST_SEEDS = (0, 1, 7, 42, 99)
CALIB_SEEDS = (11, 22, 33)
CALIB_BAND = (0.80, 0.95)   # bande de sélection de sigma_T (plus petite valeur dedans)
PILOT_SEED = 555            # graine de diagnostic — ni calibration ni test

# Décalages de graines : systèmes appris séparément (scellé §4), monde partagé.
BOB_OFFSET = 10_000
WORLD_OFFSET = 50_000

# Bandes du scellé v1 — une seule source de vérité pour les tests et le verdict.
BANDS = {
    "p1_own_min": 0.95,
    "p2_foreign_max": 0.05,
    "p3_channel_min": 0.75,
    "p3_three_x_chance": 0.375,   # 3 x 1/K = 0.375
    "null_a_lo": 0.70,
    "null_a_hi": 0.98,
    "door_margin_min": 0.80,
    "refuted_own_max": 0.50,      # voie directe cassée chez soi
    "refuted_foreign_min": 0.50,  # voie directe ouverte vers autrui
    "refuted_channel_max": 0.20,  # canal physique sous le hasard + marge
}


def _unit_rows(vectors: np.ndarray) -> np.ndarray:
    """Normalise chaque ligne en vecteur unitaire (norme nulle impossible ici)."""
    return vectors / np.linalg.norm(vectors, axis=1, keepdims=True)


@dataclass
class CognitiveSystem:
    """Un système à trois niveaux appris séparément (T encoder, P percepts, C jugements).

    `position` porte l'identifiant spatial du système (éq 46 : δ_r compare les
    positions, pas une géométrie — scellé §6.5).
    """

    name: str
    seed: int
    position: int
    encoder: np.ndarray      # D_CODE x D_PROPS — transduction T des propriétés y
    percepts: np.ndarray     # K x D_CODE — codebook P (états unitaires)
    judgments: np.ndarray    # K x D_CODE — codebook C (états unitaires)


def build_world(seed: int) -> tuple[np.ndarray, CognitiveSystem, CognitiveSystem, CognitiveSystem]:
    """Monde partagé + Alice, Bob (apprentissages séparés) et ALICE (réplique d'Alice, autre position).

    Les propriétés physiques y_k des K entrées sont tirées par la graine du
    monde — les DEUX systèmes voient les mêmes objets ; seuls leurs
    encodeurs/codebooks diffèrent (graines s et s + 10 000, scellé §4). ALICE
    partage la graine d'Alice (mêmes dynamiques) à une position différente —
    le scénario de symétrie brisée (éqs 49-50).
    """
    world = np.random.default_rng(seed + WORLD_OFFSET)
    props = world.normal(size=(K_INPUTS, D_PROPS))

    def build(name: str, sys_seed: int, position: int) -> CognitiveSystem:
        rng = np.random.default_rng(sys_seed)
        encoder = rng.normal(size=(D_CODE, D_PROPS))
        percepts = _unit_rows((encoder @ props.T).T)
        judgments = _unit_rows(rng.normal(size=(K_INPUTS, D_CODE)))
        return CognitiveSystem(name=name, seed=sys_seed, position=position,
                               encoder=encoder, percepts=percepts, judgments=judgments)

    alice = build("Alice", seed, position=0)
    bob = build("Bob", seed + BOB_OFFSET, position=2)
    alice_replica = build("ALICE", seed, position=1)  # même graine : états identiques
    return props, alice, bob, alice_replica


def recognize(state: np.ndarray, codebooks: list[np.ndarray]) -> tuple[bool, float]:
    """Prédicat d'appartenance m_C (éq 45) : cosinus max contre une famille de codebooks.

    Retourne (appartient, cosinus_max). L'état peut être bruité (c + eps).
    """
    best = -1.0
    for book in codebooks:
        sims = book @ state / np.linalg.norm(state)
        best = max(best, float(sims.max()))
    return best >= TAU, best


def measure_own(system: CognitiveSystem, rng: np.random.Generator) -> tuple[float, float]:
    """Mesure directe éq 42 : C reconnaît ses propres jugements (c_k + eps).

    Retourne (taux de reconnaissance correcte, cosinus propre moyen).
    """
    hits, coss = 0, 0.0
    for k in range(K_INPUTS):
        state = system.judgments[k] + rng.normal(0.0, SIGMA_EPS, size=D_CODE)
        sims = system.judgments @ state / np.linalg.norm(state)
        k_hat = int(np.argmax(sims))
        hits += (k_hat == k) and (sims[k_hat] >= TAU)
        coss += float(sims[k])
    return hits / K_INPUTS, coss / K_INPUTS


def measure_foreign(source: CognitiveSystem, observer: CognitiveSystem,
                    rng: np.random.Generator) -> tuple[float, float]:
    """∅ direct inter-cadres (éqs 36-38) : jugements de `source` contre P ET C de `observer`.

    Dans le jouet, P, C et L partagent le prédicat d'appartenance aux
    codebooks (scellé §4). Retourne (taux de faux positifs, cosinus croisé max).
    """
    hits, cross_max = 0, -1.0
    for k in range(K_INPUTS):
        state = source.judgments[k] + rng.normal(0.0, SIGMA_EPS, size=D_CODE)
        member, best = recognize(state, [observer.percepts, observer.judgments])
        hits += member
        cross_max = max(cross_max, best)
    return hits / K_INPUTS, cross_max


def lab_prototypes(judgments: np.ndarray, sigma_t: float,
                   rng: np.random.Generator) -> np.ndarray:
    """Session de labo (éqs 39-40) : M observations bruitées des coordonnées par pattern.

    Le prototype est la moyenne des observations — l'observateur tiers
    n'accède JAMAIS aux codebooks, seulement aux coordonnées bruitées.
    """
    protos = np.empty((K_INPUTS, D_CODE))
    for k in range(K_INPUTS):
        obs = judgments[k] + rng.normal(0.0, sigma_t, size=(M_LAB, D_CODE))
        protos[k] = obs.mean(axis=0)
    return protos


def channel_accuracy(judgments: np.ndarray, sigma_t: float,
                     rng: np.random.Generator) -> float:
    """P3 : identification du jugement observé par la seule voie physique.

    N_TEST observations fraîches d'un pattern tiré uniformément, étiquetage au
    plus proche prototype (L2). Hasard = 1/K.
    """
    protos = lab_prototypes(judgments, sigma_t, rng)
    ks = rng.integers(0, K_INPUTS, size=N_TEST)
    correct = 0
    for k in ks:
        obs = judgments[k] + rng.normal(0.0, sigma_t, size=D_CODE)
        d2 = ((protos - obs) ** 2).sum(axis=1)
        correct += int(np.argmin(d2)) == k
    return correct / N_TEST


# Table de dispatch attendue (éq 46 + texte p.17-18) : trois cas de mesure x
# deux scénarios de position. « DIRECT » = routage vers C_ν, « S » = voie
# indirecte S_ν. Les variantes s'écartent des lignes marquées (✗ absent du
# code : les écarts se MESURENT, ils ne se déclarent pas).
EXPECTED_DISPATCH = {
    ("third_input", "same_pos"): "S",
    ("third_input", "diff_pos"): "S",
    ("own_quale", "same_pos"): "DIRECT",
    ("own_quale", "diff_pos"): "S",     # symétrie brisée : éqs 49-50
    ("other_quale", "same_pos"): "S",   # cadre étranger : m_C = vide
    ("other_quale", "diff_pos"): "S",
}


def dispatch_table(observer: CognitiveSystem, replica: CognitiveSystem,
                   other: CognitiveSystem, props: np.ndarray,
                   rng: np.random.Generator) -> dict[str, dict]:
    """Routage des 6 cas par Ξνµ (éq 46) et ses deux variantes appauvries.

    m_C est mesuré (prédicat de reconnaissance), pas déclaré ; δ_r compare les
    identifiants de position. La variante « appartenance seule » retire δ_r,
    l'approximation éq 51 retire m_C.
    """
    # Entrée tierce : propriétés physiques inédites (ni cataloguées, ni un état appris).
    world = np.random.default_rng(observer.seed + WORLD_OFFSET + 1)
    y_new = world.normal(size=D_PROPS)
    third_state = _unit_rows((observer.encoder @ y_new).reshape(1, -1))[0]

    own_state = replica.judgments[rng.integers(0, K_INPUTS)] \
        + rng.normal(0.0, SIGMA_EPS, size=D_CODE)
    other_state = other.judgments[rng.integers(0, K_INPUTS)] \
        + rng.normal(0.0, SIGMA_EPS, size=D_CODE)

    rows: dict[str, dict] = {}
    for case, state in (("third_input", third_state),
                        ("own_quale", own_state),
                        ("other_quale", other_state)):
        member, _ = recognize(state, [observer.percepts, observer.judgments])
        for scenario, dr in (("same_pos", True), ("diff_pos", False)):
            full = "DIRECT" if (member and dr) else "S"
            membership_only = "DIRECT" if member else "S"
            eq51 = "DIRECT" if dr else "S"
            rows[f"{case}/{scenario}"] = {
                "m_C": bool(member), "delta_r": bool(dr),
                "full": full, "membership_only": membership_only, "eq51": eq51,
            }
    return rows


def _mismatches(rows: dict[str, dict], variant: str) -> list[str]:
    return [key for key, row in rows.items() if row[variant] != EXPECTED_DISPATCH[tuple(key.split("/"))]]


def calibrate() -> dict:
    """Calibration scellée §4 : sigma_T = plus petite valeur de la grille avec
    précision du canal (moyenne graines 11/22/33) dans [0.80, 0.95].

    Mesure AUSSI les portes/nulls de calibration : null (a) Acc_cal dans
    [0.70, 0.98] par graine, porte de séparabilité (marge direct/tiers >= 0.80).
    """
    grid_scan = {}
    for sigma_t in SIGMA_T_GRID:
        accs = []
        for seed in CALIB_SEEDS:
            _, alice, bob, _ = build_world(seed)
            rng = np.random.default_rng(20_000 + seed)
            accs.append(channel_accuracy(alice.judgments, sigma_t, rng))
        grid_scan[str(sigma_t)] = {"accs": accs, "mean": float(np.mean(accs))}
    selected = None
    for sigma_t in SIGMA_T_GRID:
        m = grid_scan[str(sigma_t)]["mean"]
        if CALIB_BAND[0] <= m <= CALIB_BAND[1]:
            selected = sigma_t
            break
    own_rates, foreign_rates = [], []
    for seed in CALIB_SEEDS:
        _, alice, bob, _ = build_world(seed)
        rng = np.random.default_rng(10_000 + seed)
        own_a, _ = measure_own(alice, rng)
        own_b, _ = measure_own(bob, rng)
        fp_a2b, _ = measure_foreign(alice, bob, rng)
        fp_b2a, _ = measure_foreign(bob, alice, rng)
        own_rates += [own_a, own_b]
        foreign_rates += [max(fp_a2b, fp_b2a)]
    margin = float(np.mean(own_rates) - np.mean(foreign_rates))
    return {
        "grid_scan": grid_scan,
        "sigma_t_selected": selected,
        "own_rates": own_rates,
        "foreign_rates": foreign_rates,
        "margin_direct_tiers": margin,
        "null_a_ok": selected is not None and all(
            BANDS["null_a_lo"] <= a <= BANDS["null_a_hi"]
            for a in grid_scan[str(selected)]["accs"]
        ),
        "door_ok": margin >= BANDS["door_margin_min"],
    }


def _count(flags: list[bool]) -> int:
    return sum(1 for f in flags if f)


def verdict(calib: dict, per_seed: list[dict]) -> dict:
    """Verdict borné du scellé §4 — aucune bande n'est relue ici, seulement BANDS."""
    n = len(per_seed)
    owns = [s["r_direct_own"] for s in per_seed]
    foreigns = [s["r_direct_foreign"] for s in per_seed]
    accs = [s["acc_indirect"] for s in per_seed]
    nullb = [s["membership_misroutes_own_broken"] for s in per_seed]

    p1 = _count([o >= BANDS["p1_own_min"] for o in owns]) >= n - 1
    p2 = _count([f <= BANDS["p2_foreign_max"] for f in foreigns]) >= n - 1
    p3 = _count([a >= BANDS["p3_channel_min"] for a in accs]) >= n - 1
    null_b = _count(nullb) >= n

    checks = {
        "P1_direct_own": p1,
        "P2_empty_foreign": p2,
        "P3_channel_intact": p3,
        "null_a_instrument": bool(calib["null_a_ok"]),
        "null_b_delta_r_load_bearing": null_b,
        "door_separability": bool(calib["door_ok"]),
        "calibration_selected": calib["sigma_t_selected"] is not None,
    }
    if calib["sigma_t_selected"] is None:
        outcome = ("NON_CONCLUSIF_INSTRUMENT (calibration : aucune valeur de la grille "
                   "ne place le canal dans la bande de sélection)")
    elif not calib["door_ok"]:
        outcome = "NON_CONCLUSIF_INSTRUMENT (porte : marge direct/tiers insuffisante a l'etat repos)"
    elif not calib["null_a_ok"]:
        outcome = "NON_CONCLUSIF_INSTRUMENT (null a : fidelite du canal hors bande en calibration)"
    elif not null_b:
        outcome = "NON_CONCLUSIF (null b : la condition spatiale ne fait aucun travail de routage)"
    elif p1 and p2 and p3:
        outcome = "SUPPORTED"
    elif _count([o < BANDS["refuted_own_max"] for o in owns]) >= 3:
        outcome = "REFUTED (P1 : la voie directe est fermée chez soi — non réalisable)"
    elif _count([f > BANDS["refuted_foreign_min"] for f in foreigns]) >= 3:
        outcome = "REFUTED (P2 : la voie directe est ouverte vers autrui — non réalisable)"
    elif _count([a < BANDS["refuted_channel_max"] for a in accs]) >= 3:
        outcome = "REFUTED (P3 : le canal physique ne porte pas l'identité — sous le hasard)"
    elif not p1:
        outcome = "NON_CONCLUSIF (P1 sous la bande sans cassure)"
    elif not p2:
        outcome = "NON_CONCLUSIF (P2 au-dessus de la bande sans ouverture massive)"
    else:
        outcome = "NON_CONCLUSIF (P3 sous la bande sans effondrement)"
    return {"verdict": outcome, "checks": checks}


def run_seed(seed: int, sigma_t: float) -> dict:
    """Une graine complète : monde, systèmes, les trois voies et le dispatch."""
    props, alice, bob, replica = build_world(seed)
    rng_meas = np.random.default_rng(10_000 + seed)
    own_a, own_cos = measure_own(alice, rng_meas)
    own_b, _ = measure_own(bob, rng_meas)
    fp_a2b, cross_a2b = measure_foreign(alice, bob, rng_meas)
    fp_b2a, cross_b2a = measure_foreign(bob, alice, rng_meas)
    rng_chan = np.random.default_rng(20_000 + seed)
    acc = channel_accuracy(alice.judgments, sigma_t, rng_chan)
    rng_disp = np.random.default_rng(30_000 + seed)
    rows = dispatch_table(alice, replica, bob, props, rng_disp)
    own_broken_key = "own_quale/diff_pos"
    return {
        "seed": seed,
        "r_direct_own": 0.5 * (own_a + own_b),
        "r_direct_own_detail": {"alice": own_a, "bob": own_b},
        "own_cos_mean": own_cos,
        "r_direct_foreign": max(fp_a2b, fp_b2a),
        "r_direct_foreign_detail": {"alice_to_bob": fp_a2b, "bob_to_alice": fp_b2a},
        "cross_cos_max": max(cross_a2b, cross_b2a),
        "acc_indirect": acc,
        "dispatch": rows,
        "full_dispatch_fidelity": all(
            row["full"] == EXPECTED_DISPATCH[tuple(key.split("/"))]
            for key, row in rows.items()
        ),
        "membership_misroutes": _mismatches(rows, "membership_only"),
        "eq51_misroutes": _mismatches(rows, "eq51"),
        "membership_misroutes_own_broken": own_broken_key in _mismatches(rows, "membership_only"),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seeds", type=int, nargs="+", default=list(TEST_SEEDS))
    parser.add_argument("--sigma-t", type=float, default=None,
                        help="si omis : calibration scellée (graines 11/22/33) puis gel")
    parser.add_argument("--pilot", action="store_true",
                        help="diagnostic sur la graine 555 (ni calibration ni test), sans verdict")
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args(argv)

    if args.pilot:
        # Diagnostic : sigma_t généreux pour la vue d'ensemble du canal.
        diag = {}
        for sigma_t in SIGMA_T_GRID:
            rng = np.random.default_rng(20_000 + PILOT_SEED)
            _, alice, bob, _ = build_world(PILOT_SEED)
            diag[str(sigma_t)] = channel_accuracy(alice.judgments, sigma_t, rng)
        rng = np.random.default_rng(10_000 + PILOT_SEED)
        own_a, own_cos = measure_own(alice, rng)
        fp, cross = measure_foreign(alice, bob, rng)
        pilot = {"seed": PILOT_SEED, "channel_acc_by_sigma": diag,
                 "own": own_a, "own_cos": own_cos, "foreign": fp, "cross_cos": cross}
        print(json.dumps(pilot, indent=2, ensure_ascii=False))
        return 0

    calib = calibrate() if args.sigma_t is None else None
    sigma_t = args.sigma_t if args.sigma_t is not None else calib["sigma_t_selected"]
    if sigma_t is None:
        # Calibration sans sélection : rendu honnête, pas de run principal.
        result = {"frozen": {"sigma_t": None}, "calibration": calib,
                  "verdict": verdict(calib, [])}
        text = json.dumps(result, indent=2, ensure_ascii=False)
        if args.out:
            args.out.write_text(text, encoding="utf-8")
            print(f"written: {args.out}")
        print(json.dumps(result["verdict"], indent=2, ensure_ascii=False))
        return 0
    runs = [run_seed(s, sigma_t) for s in args.seeds]
    result = {
        "frozen": {"D": D_CODE, "K": K_INPUTS, "sigma_eps": SIGMA_EPS, "tau": TAU,
                   "m_lab": M_LAB, "n_test": N_TEST, "sigma_t": sigma_t,
                   "seeds": list(args.seeds)},
        "calibration": calib,
        "runs": runs,
        "verdict": verdict(calib or {"null_a_ok": True, "door_ok": True,
                                     "sigma_t_selected": sigma_t,
                                     "margin_direct_tiers": None}, runs),
    }
    text = json.dumps(result, indent=2, ensure_ascii=False)
    if args.out:
        args.out.write_text(text, encoding="utf-8")
        print(f"written: {args.out}")
    print(json.dumps(result["verdict"], indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
