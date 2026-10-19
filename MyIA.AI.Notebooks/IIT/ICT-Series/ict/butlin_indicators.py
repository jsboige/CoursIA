"""Case 19 — le mot « using » de RPT-1 (veine #8182, Butlin et al. 2023, arXiv 2308.08708).

Exécution du pré-enregistrement ``docs/ict/butlin-indicators-pre-enregistrement.md``
(scellé AVANT ce banc — l'antériorité repose sur la relation de parenté des
commits, leçon case 8c). La thèse testée : décider qu'un système « utilise de
la récurrence algorithmique » au sens de l'indicateur RPT-1 est une question
**causale**, pas structurelle.

Le papier définit la récurrence algorithmique comme « the same operation is
applied repeatedly » (glossaire, l.2799-2802) et crédite explicitement le
mimique — « deep feedforward networks with weight-sharing display only
algorithmic recurrence » (l.783-786) — mais ne fournit **aucune procédure**
pour vérifier le mot *using* du libellé « RPT-1: Input modules using
algorithmic recurrence » (l.806). Le papier argue pourtant lui-même
causalement dans ses études de cas : le Perceiver est évalué par « only one
output module **acts on** information from the workspace » et « in practice
the system **must be reset** » (l.2366-2382) — un argument de dépendance
fonctionnelle.

Tâche (intégration temporelle non triviale)
-------------------------------------------
Séquence ``x_0 … x_7`` de ``T = 8`` symboles dans ``{0..7}`` (one-hot, ``K = 8``),
cible ``y = x_s`` avec ``s = x_7`` — le symbole à la position indiquée par le
dernier symbole. Aucune fonction du dernier symbole seul ne résout la tâche.

Trois architectures, un seul mécanisme (l'opération ``shift`` :
``m ← [x_t, m_0 … m_6]``) :

* **Real** — registre récurrent : ``m_t = shift(m_{t-1}, x_t)``, réponse
  ``m_T[T-1-s]``. L'opération ``shift`` est appliquée répétitivement sur *le
  même état* (boucle). Récurrence algorithmique **utilisée** : oui.
* **Twin** — chaîne déroulée : ``h_t = shift(h_{t-1}, x_t)`` sur ``T``
  variables distinctes, **mêmes poids** à chaque étage — le mimique exact de
  l.785-786. Implémentation numpy **indiscernable** de Real (le papier le dit
  lui-même, l.780-782) : la différence vit dans le **graphe déclaré**
  (self-loop sur un nœud vs chaîne de nœuds distincts à poids partagés).
  Récurrence algorithmique **utilisée** : oui (le papier le crédite).
* **Puppet** — indexation single-shot : la séquence entière est disponible
  d'un coup, réponse ``batch[s]`` — aucune opération répétée. En plus, le
  **même registre récurrent que Real** tourne sur les mêmes entrées et
  n'alimente que la **télémesure** (lue par rien). Récurrence algorithmique
  **utilisée** : non (le module existe et est calculé, mais n'est pas *used*).

Procédures d'inspection comparées (le banc les rend exécutables)
----------------------------------------------------------------
* **S1** (structurelle naïve) : « le graphe contient-il un cycle ? » ;
* **S2** (structurelle informée par le papier) : « cycle **ou** chaîne à
  poids partagés (une arête directe entre deux nœuds distincts portant
  l'opération ``shift`` **et** appartenant au même ensemble de poids) ? » ;
* **C** (causale) : lésion de chaque module candidat → porteur =
  ``argmax_λ Δ_λ`` ; verdict = ``iterative_reuse(porteur)`` (aucun porteur si
  ``max Δ < 0.5``). Modules : ``loop``/``chain`` (report coupé),
  ``selector`` (réponse constante), ``monitor`` (sham : télémesure constante,
  ne touche pas la sortie — **dormant par construction**, il valide le
  harnais de lésion, pas la sonde ; analogue de la porte plafond dormante de
  la case 16).

Prédictions scellées (graines test (0, 1, 7, 42, 99), N_TEST = 500 séquences
par graine ; bandes dérivées analytiquement — banc déterministe) :

* **P1** — comportement : ``acc(Real) = acc(Puppet) = acc(Twin) = 1.0``
  exactement, 5/5 graines (le behaviorisme ne discrimine pas) ;
* **P2** — S1 rend ``{oui, non, oui}`` contre vérité ``{oui, oui, non}`` :
  faux positif sur Puppet, faux négatif sur Twin → exact 1/3 ;
* **P3** — S2 rend ``{oui, oui, oui}`` : le faux positif Puppet survit à
  l'information du papier → exact 2/3 ;
* **P4** — C : Δ(porteur) ≥ 0.50 sur Real/Twin (valeur analytique attendue
  ≈ 1 − 0.234 = 0.766 : la réponse lésée reste correcte ssi ``s = 7`` ou
  ``x_s = 0``), Δ = 0 sur Puppet ; verdicts ``{oui, oui, non}`` → exact 3/3 ;
  sham ``Δ = 0`` exact sur 3/3 ;
* **P5** — stabilité : chaque mesure par graine, 5/5 conforme.

Portes instrumentales : ``acc(base) < 1.0`` ou sham ``|Δ| > 0.01`` sur ≥ 1
graine → ``NON_CONCLUSIF_INSTRUMENT``.

Verdicts bornés : **SUPPORTED** si P1 et P4 tiennent et qu'au moins une
procédure structurelle échoue (P2 ou P3 inexacte) ; **NOT_SUPPORTED** si P4
échoue ou si S1 et S2 sont exactes 3/3 (les procédures structurelles
suffiraient) ; **NON_CONCLUSIF_INSTRUMENT** sur porte.

Calibration sur graines disjointes (11, 22, 33) : vérifie les valeurs
analytiques (acc lésée ∈ [0.10, 0.35], sham nul, baselines parfaites) — aucun
paramètre n'est gelé (pas d'apprentissage) ; la valeur 0.234 est calculable.
Le bloc ``calibration`` de ``run_protocol()`` (donc du JSON committé) porte ce
run, rejouable depuis les graines seules.

References
----------
P. Butlin, R. Long, et al., « Consciousness in Artificial Intelligence:
Insights from the Science of Consciousness », arXiv 2308.08708 (2023).
Pré-enregistrement : ``docs/ict/butlin-indicators-pre-enregistrement.md``
(case 19 de ``docs/ict/dissociations-matrix.md``).
"""

from __future__ import annotations

import argparse
import json

import numpy as np

# --- Paramètres du jouet (scellés par le pré-enregistrement §4) ---
T_STEPS = 8          # longueur de séquence
K_SYMBOLS = 8        # taille de l'alphabet
N_TEST = 500         # séquences par graine
SEEDS_TEST = (0, 1, 7, 42, 99)
SEEDS_CALIB = (11, 22, 33)
BAND_COLLAPSE = 0.50   # Δ ≥ 0.50 = le porteur est identifié
BAND_INERT = 0.01      # |Δ| ≤ 0.01 = inertie (sham)
ACC_LESION_LO = 0.10   # fenêtre analytique de l'accuracy lésée (≈ 0.234)
ACC_LESION_HI = 0.35
# Valeur théorique de l'accuracy lésée : P(s = T-1) + P(s ≠ T-1) · P(x_s = 0)
# = 1/8 + 7/8 · 1/8 = 0.234375 (la réponse lésée est correcte ssi s = 7, ou x_s = 0).
ACC_LESION_THEORETICAL = 1 / K_SYMBOLS + (K_SYMBOLS - 1) / K_SYMBOLS * (1 / K_SYMBOLS)


def _shift(m: np.ndarray, x: np.ndarray) -> np.ndarray:
    """L'opération de mémoire : insère ``x`` en tête, décale le reste."""
    out = np.empty_like(m)
    out[0] = x
    out[1:] = m[:-1]
    return out


def _sample_sequences(seed: int, n: int) -> tuple[np.ndarray, np.ndarray]:
    """Séquences one-hot ``(n, T, K)`` et cibles ``y = x_s``, ``s = x_T``."""
    rng = np.random.default_rng(seed)
    syms = rng.integers(0, K_SYMBOLS, size=(n, T_STEPS))
    seqs = np.eye(K_SYMBOLS)[syms]
    targets = np.array([syms[i, syms[i, -1]] for i in range(n)])
    return seqs, targets


def _accuracy(forward, seqs: np.ndarray, targets: np.ndarray,
              lesion: str | None = None) -> float:
    preds = np.array([forward(seqs[i], lesion=lesion) for i in range(len(seqs))])
    return float(np.mean(preds == targets))


# --- Les trois architectures ---

def _read_answer(m: np.ndarray, s: int) -> int:
    """Lit la position ``s`` dans le registre final (``m[j] = x_{T-1-j}``)."""
    return int(np.argmax(m[T_STEPS - 1 - s]))


def forward_real(seq: np.ndarray, lesion: str | None = None) -> int:
    """Registre récurrent : la boucle porte la charge (self-loop sur ``m``)."""
    m = np.zeros((T_STEPS, K_SYMBOLS))
    for t in range(T_STEPS):
        prev = np.zeros_like(m) if lesion == "loop" else m
        m = _shift(prev, seq[t])
    s = int(np.argmax(seq[-1]))
    return _read_answer(m, s)


def forward_twin(seq: np.ndarray, lesion: str | None = None) -> int:
    """Chaîne déroulée à poids partagés — implémentation indiscernable de Real
    (l.780-782) ; la distinction vit dans le graphe déclaré."""
    h = np.zeros((T_STEPS, K_SYMBOLS))
    for t in range(T_STEPS):
        prev = np.zeros_like(h) if lesion == "chain" else h
        h = _shift(prev, seq[t])
    s = int(np.argmax(seq[-1]))
    return _read_answer(h, s)


def _decorative_register(seq: np.ndarray, lesion: str | None = None) -> np.ndarray:
    """Le registre récurrent du Puppet — calculé, sortie vers la télémétrie."""
    m = np.zeros((T_STEPS, K_SYMBOLS))
    for t in range(T_STEPS):
        prev = np.zeros_like(m) if lesion == "loop" else m
        m = _shift(prev, seq[t])
    return m


def forward_puppet(seq: np.ndarray, lesion: str | None = None) -> int:
    """Indexation single-shot du batch ; le registre récurrent ne sert qu'à la
    télémétrie (lue par rien) — présent mais inerte."""
    if lesion != "selector":
        _decorative_register(seq, lesion)   # tourne, n'alimente pas la réponse
    s = int(np.argmax(seq[-1]))
    if lesion == "selector":
        return 0
    return int(np.argmax(seq[s]))


# --- Graphes déclarés (les checklists structurelles opèrent ici) ---

def _twin_nodes_edges():
    nodes = {"input": "input"}
    weights = {}   # ensemble de poids par nœud ``shift`` : un seul, partagé
    edges = [("input", "h1")]
    for t in range(1, T_STEPS + 1):
        nodes[f"h{t}"] = "shift"
        weights[f"h{t}"] = "W_chain"
        if t > 1:
            edges.append((f"h{t - 1}", f"h{t}"))
    nodes["monitor"] = "id"
    nodes["output"] = "output"
    edges.append((f"h{T_STEPS}", "monitor"))
    edges.append((f"h{T_STEPS}", "output"))
    return nodes, edges, weights


_TWIN_NODES, _TWIN_EDGES, _TWIN_WEIGHTS = _twin_nodes_edges()

ARCHITECTURES = {
    "real": {
        "forward": forward_real,
        "nodes": {"input": "input", "loop": "shift", "monitor": "id",
                  "output": "output"},
        "edges": [("input", "loop"), ("loop", "loop"), ("loop", "monitor"),
                  ("loop", "output")],
        "weights": {"loop": "W_rec"},
        "modules": {
            "loop": {"iterative_reuse": True},
            "monitor": {"iterative_reuse": False},
        },
        "truth": True,
    },
    "twin": {
        "forward": forward_twin,
        "nodes": _TWIN_NODES,
        "edges": _TWIN_EDGES,
        "weights": _TWIN_WEIGHTS,
        "modules": {
            "chain": {"iterative_reuse": True},
            "monitor": {"iterative_reuse": False},
        },
        "truth": True,
    },
    "puppet": {
        "forward": forward_puppet,
        "nodes": {"input": "input", "loop": "shift", "monitor": "id",
                  "batch": "input", "selector": "index", "output": "output"},
        "edges": [("input", "loop"), ("loop", "loop"), ("loop", "monitor"),
                  ("batch", "selector"), ("selector", "output")],
        "weights": {"loop": "W_rec"},
        "modules": {
            "loop": {"iterative_reuse": True},
            "selector": {"iterative_reuse": False},
            "monitor": {"iterative_reuse": False},
        },
        "truth": False,
    },
}


# --- Les procédures d'inspection ---

def has_cycle(nodes: dict, edges: list) -> bool:
    """S1 — détection de cycle sur le graphe déclaré (DFS tricolore)."""
    adj = {n: [] for n in nodes}
    for a, b in edges:
        adj[a].append(b)
    state = {n: 0 for n in nodes}   # 0 = blanc, 1 = gris, 2 = noir

    def dfs(u: str) -> bool:
        state[u] = 1
        for v in adj[u]:
            if state[v] == 1:
                return True
            if state[v] == 0 and dfs(v):
                return True
        state[u] = 2
        return False

    return any(state[n] == 0 and dfs(n) for n in nodes)


def has_shared_weight_chain(nodes: dict, edges: list, weights: dict) -> bool:
    """S2 (volet partage) — une chaîne à poids partagés : une arête directe
    entre deux nœuds **distincts** portant l'opération ``shift`` **et**
    appartenant au même ensemble de poids (``weights`` : nœud -> ensemble).

    Deux nœuds ``shift`` disjoints, ou reliés mais de poids distincts, ne
    forment pas une chaîne à poids partagés. Une boucle (arête d'un nœud sur
    lui-même) relève de S1 (``has_cycle``), pas de ce prédicat.
    """
    return any(
        a != b
        and nodes.get(a) == "shift" and nodes.get(b) == "shift"
        and weights.get(a) is not None and weights.get(a) == weights.get(b)
        for a, b in edges
    )


def causal_probe(arch: dict, seqs: np.ndarray, targets: np.ndarray) -> dict:
    """C — lésion de chaque module candidat, identification du porteur."""
    base = _accuracy(arch["forward"], seqs, targets)
    deltas = {mod: base - _accuracy(arch["forward"], seqs, targets, lesion=mod)
              for mod in arch["modules"]}
    top = max(deltas.values()) if deltas else 0.0
    if top < BAND_COLLAPSE:
        return {"carrier": None, "verdict": False, "deltas": deltas}
    carrier = max(deltas, key=deltas.get)
    return {"carrier": carrier,
            "verdict": bool(arch["modules"][carrier]["iterative_reuse"]),
            "deltas": deltas}


# --- Calibration (graines disjointes, vérifie les valeurs analytiques) ---

def calibrate() -> dict:
    """Vérifie sur graines disjointes : baselines parfaites, Δ(porteur) dans la
    bande, accuracy lésée dans la fenêtre analytique, sham nul.

    Le dict rendu est le bloc ``calibration`` du JSON committé : il ne contient
    que des types JSON natifs (listes, pas de tuples) et des valeurs arrondies
    à 6 décimales, pour qu'une relecture depuis le JSON soit égale à ce run.
    """
    by_seed = []
    for s in SEEDS_CALIB:
        seqs, targets = _sample_sequences(s, N_TEST)
        row = {"seed": s}
        for name in ("real", "twin"):
            arch = ARCHITECTURES[name]
            mod = "loop" if name == "real" else "chain"
            acc_base = _accuracy(arch["forward"], seqs, targets)
            acc_les = _accuracy(arch["forward"], seqs, targets, lesion=mod)
            row[f"acc_base_{name}"] = round(acc_base, 6)
            row[f"acc_lesion_{name}"] = round(acc_les, 6)
            row[f"delta_{name}"] = round(acc_base - acc_les, 6)
        row["delta_sham"] = round(max(
            _accuracy(a["forward"], seqs, targets)
            - _accuracy(a["forward"], seqs, targets, lesion="monitor")
            for a in ARCHITECTURES.values()), 6)
        by_seed.append(row)
    ok = all(r["acc_base_real"] == 1.0 and r["acc_base_twin"] == 1.0
             and r["delta_real"] >= BAND_COLLAPSE and r["delta_twin"] >= BAND_COLLAPSE
             and ACC_LESION_LO <= r["acc_lesion_real"] <= ACC_LESION_HI
             and abs(r["delta_sham"]) <= BAND_INERT for r in by_seed)
    return {
        "seeds": list(SEEDS_CALIB),
        "n_test": N_TEST,
        "by_seed": by_seed,
        "acc_lesion_window": [ACC_LESION_LO, ACC_LESION_HI],
        "acc_lesion_theoretical": round(ACC_LESION_THEORETICAL, 6),
        "bands_ok": ok,
    }


# --- Run principal ---

def run_protocol() -> dict:
    """Run principal : graines test, procédures S1/S2/C, prédictions scellées."""
    truth = {name: a["truth"] for name, a in ARCHITECTURES.items()}
    s1 = {name: has_cycle(a["nodes"], a["edges"]) for name, a in ARCHITECTURES.items()}
    s2 = {name: (s1[name] or has_shared_weight_chain(a["nodes"], a["edges"], a["weights"]))
          for name, a in ARCHITECTURES.items()}
    s1_exact = sum(s1[n] == truth[n] for n in truth)
    s2_exact = sum(s2[n] == truth[n] for n in truth)

    by_seed = []
    for s in SEEDS_TEST:
        seqs, targets = _sample_sequences(s, N_TEST)
        row = {"seed": s, "baseline": {}, "probe": {}}
        for name, arch in ARCHITECTURES.items():
            row["baseline"][name] = _accuracy(arch["forward"], seqs, targets)
            row["probe"][name] = causal_probe(arch, seqs, targets)
        by_seed.append(row)

    # Portes instrumentales
    gate_baseline = any(row["baseline"][n] < 1.0
                        for row in by_seed for n in ARCHITECTURES)
    sham_max = max(abs(row["probe"][n]["deltas"]["monitor"])
                   for row in by_seed for n in ARCHITECTURES)
    gate_sham = sham_max > BAND_INERT

    # Prédictions
    p1 = not gate_baseline
    c_exact_by_seed = [sum(row["probe"][n]["verdict"] == truth[n]
                           for n in truth) for row in by_seed]
    p4 = all(c == len(truth) for c in c_exact_by_seed) and not gate_sham
    structural_fails = (s1_exact < len(truth)) or (s2_exact < len(truth))

    if gate_baseline or gate_sham:
        verdict = "NON_CONCLUSIF_INSTRUMENT"
    elif p4 and p1 and structural_fails:
        verdict = "SUPPORTED"
    else:
        verdict = "NOT_SUPPORTED"

    return {
        "case": "19-butlin-rpt1-using",
        "seeds": list(SEEDS_TEST),
        "n_test": N_TEST,
        "task": "y = x_s, s = x_T (T=8, K=8)",
        "truth": truth,
        "structural": {
            "s1_cycle": s1,
            "s2_cycle_or_shared": s2,
            "s1_exact": s1_exact,
            "s2_exact": s2_exact,
        },
        "baseline_acc_by_seed": [row["baseline"] for row in by_seed],
        "probe_by_seed": [
            {n: {"carrier": row["probe"][n]["carrier"],
                 "verdict": row["probe"][n]["verdict"],
                 "deltas": {k: round(v, 6)
                            for k, v in row["probe"][n]["deltas"].items()}}
             for n in ARCHITECTURES}
            for row in by_seed
        ],
        "c_exact_by_seed": c_exact_by_seed,
        "sham_max_abs_delta": round(sham_max, 6),
        "gate_baseline": gate_baseline,
        "gate_sham": gate_sham,
        "p1_baseline_perfect": bool(p1),
        "p2_s1_fails": bool(s1_exact < len(truth)),
        "p3_s2_fails": bool(s2_exact < len(truth)),
        "p4_causal_exact": bool(p4),
        "verdict": verdict,
        "bands": {"collapse": BAND_COLLAPSE, "inert": BAND_INERT,
                  "acc_lesion_window": [ACC_LESION_LO, ACC_LESION_HI]},
        # Ajouté en fin de dict : aucune autre clé ne change
        # (cf. test_artifact_is_run_protocol_output).
        "calibration": calibrate(),
    }


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Case 19 - RPT-1 'using' : structure vs cause (Butlin 2023)")
    ap.add_argument("--calibrate", action="store_true",
                    help="calibration sur graines disjointes (11/22/33)")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    args = ap.parse_args()
    out = calibrate() if args.calibrate else run_protocol()
    if args.json:
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        for key, val in out.items():
            print(f"{key}: {val}")


if __name__ == "__main__":
    main()