"""Jouet « boundary problem par obstruction de recollement » (case 14, #8182 iceberg L3 — Emilsson EM-field, seconde opérationnalisation).

Le boundary problem en une phrase : même en accordant qu'un substrat
physique porte de l'expérience, QU'EST-CE qui fixe la FRONTIÈRE de ce
porteur — pourquoi ces processeurs et pas ceux d'à côté, pourquoi ce
bout de champ et pas un bout plus grand ou plus petit ? La réponse
« EM-field topology » (Gómez-Emilsson & Percy 2023 : la topologie du
champ électromagnétique est le candidat naturel de frontière) est la
réponse PHYSIQUE ; la réponse fonctionnelle (la frontière suit la
structure de cause commune de l'information) est la réponse
INFORMATIONNELLE. Ce module rend leur DÉSACCORD falsifiable AU NIVEAU
SIGNAL (grade C documentaire — aucune phénoménologie n'est mesurée ni
revendiquée), par une observable distincte de la case 6.

Observable (lecture grothendieckienne) : une frontière candidate P
découpe le substrat en parties ; chaque partie produit une LECTURE
LOCALE de l'état global (moyenne de ses signaux). L'OBSTRUCTION AU
RECOLLEMENT de P est la divergence D(P) = E_t[std_p(lecture_p(t))] :
une frontière « juste » produit des lectures locales qui recollent
(D bas), une frontière qui coupe une structure de cause commune
produit des lectures qui divergent systématiquement (D haut). Le null
adversarial : médiane de D sur M partitions aléatoires APPARIÉES EN
TAILLES — toute élévation au-delà du hasard est imputable à
l'ALIGNEMENT de la frontière avec une cause locale, pas à sa taille.

Trois substrats (générateur factoriel gaussien, numpy only, CPU) —
f0 = broadcast (cause commune à tous les nœuds), f1 = cause locale
(sous-ensemble seulement), couplage W = topologie de champ à seuil :

- **S1 « topo coupe un broadcast »** : couplage concentré dans R
  (composantes {R, R^c} à seuil τ) MAIS signaux = broadcast pur
  (aucune cause locale). La topologie trace une frontière que la
  cause commune ne ratifie pas.
- **S2 « cause dispersée »** : champ uniformément connexe (UNE
  composante — la topologie ne trace RIEN) MAIS f1 charge un
  demi-ensemble dispersé H (nœuds pairs). La frontière fonctionnelle
  {H, H^c} est celle que le critère EM rejette (champ connecté).
- **S3 « CTRL aligné »** (contrôle positif) : couplage concentré
  dans R ET f1 charge exactement R — les deux critères s'accordent.

Prédictions verrouillées AVANT exécution (case 14 v1, 2026-09-17,
commentaire d'amendement c.5709451880 sur #8182) — l'instrument v1
(ρ*=0.6) a été invalidé par sa PROPRE première grille : marge de
seuil 1.7σ au plateau croisé (0.538), la règle fonctionnelle
s'effondrait en une composante sur 2/5 seeds (ratios `inf` = garde
de division, PAS une preuve de visibilité). Re-verrouillé v2 le
2026-09-17T06:55Z (c.5709502555) AVANT re-run : ρ*=0.75 (centre des
plateaux 0.538/0.891, marges ≈ 6σ/4σ) et ratio indéfini =
REJET_PROTOCOLE explicite, jamais compté comme pass (leçon case 6 :
un rejet > 0 seed invalide la prédiction). Prédictions P1-P4 et
bandes INCHANGÉES :

- **P1 (mécanique)** : D({tout}) = 0 EXACT pour tout substrat, tout
  seed — une partition à une partie n'a pas de couture.
- **P2 (S1)** : ratio(D_topo) = D(B_topo)/médiane D(aléatoire
  apparié) ∈ [0.75, 1.30] sur 5/5 seeds — une frontière topologique
  qui coupe un broadcast pur est INVISIBLE au recollement : le
  recollement ne la ratifie NI ne la punit. C'est la
  sous-détermination du boundary problem rendue quantitative :
  l'observable « recollement » ne peut pas arbitrer un
  sur-découpage du broadcast.
- **P3 (S2)** : ratio(D_func) ≥ 1.50 sur 5/5 seeds — la frontière
  DISPERSÉE alignée sur une cause locale est VISIBLE : le
  recollement punit la frontière que la connectivité de champ
  rejette. Si ratio ≈ 1 : NOT_SUPPORTED (le recollement suivrait
  alors la connectivité, pas la cause commune).
- **P4 (S3 CTRL)** : ratio(D_topo) ≥ 1.50 sur 5/5 seeds —
  l'instrument détecte bien une frontière alignée (cause +
  topologie d'accord).

Enseignements MÉCANIQUES (démontrables sans exécution) :
- partition à une partie : std sur un singleton = 0 exact, pour tout
  bruit, tout T.
- substrat à chargements échangeables (broadcast pur) : toute
  découpe de tailles données a la MÊME loi de divergence (les nœuds
  sont indiscernables en loi) — d'où P2 : le ratio tend vers 1 à
  T, M infinis, et l'écart fini n'est que bruit d'échantillon.

Anti-confusion vs voisines :
- **vs case 6** (#12179, `ict/kuramoto_boundary.py`, INCONCLUSIVE) :
  la case 6 mesurait la PORTÉE D'ENTRAÎNEMENT DE PHASE à travers la
  frontière (kick-propagation sur Kuramoto 2D, déficits
  vortex) ; la case 14 mesure la DIVERGENCE DES LECTURES LOCALES que
  la frontière induit (recollement, substrat factoriel). Observables
  et substrats distincts — l'INCONCLUSIVE de la case 6 (défauts
  instables, confound de gradient) n'est ni réutilisée ni corrigée
  ici ; les deux cases répondent de la même question famille par
  des voies indépendantes.
- **vs ICT-15d** : 15d teste l'OBSTRUCTION AU RECOLLEMENT de proxys
  sur corpus (EXISTENCE du glue) ; la case 14 fait du glue le
  CRITÈRE DE JUGEMENT d'une frontière candidate — le même mot
  « recollement » sert deux gestures : exister vs trancher.
- **vs case 13** (`combination_subjects.py`) : la case 13 teste le
  TRANSFERT DE PROPRIÉTÉ par la composition (le glue comme variable
  manipulée) ; la case 14 teste la DÉTERMINATION DE FRONTIÈRE (quelle
  partition est la bonne). Observable, substrat et question
  distincts, falsifiables indépendamment.

References
----------
Andrés Gómez Emilsson (Qualia Research Institute) & Chris Percy,
« Don't forget the boundary problem! How EM field topology can
address the overlooked cousin to the binding problem for
consciousness », Frontiers in Human Neuroscience 17:1233119 (2023),
DOI 10.3389/fnhum.2023.1233119 — citation vérifiée firsthand par la
case 6 (2026-08, 3 sources concordantes : Frontiers, PhilArchive,
APA PsycNet). Réservoir : K. Jaimungal — Theories of Everything,
iceberg L3 [#8182]. Vérifié firsthand 2026-09-17.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

__all__ = [
    "Substrate",
    "build_substrate",
    "simulate",
    "connected_components",
    "field_topology_boundary",
    "functional_boundary",
    "partition_reading_divergence",
    "matched_random_null",
    "boundary_case",
    "run_case14_protocol",
]

# Paramètres verrouillés AVANT exécution (case 14 v2, 2026-09-17,
# pré-enregistrés c.5709451880, re-verrouillés c.5709502555 après
# invalidation de la marge de seuil v1 par sa propre grille).
N_NODES = 12            # anneau de 12 nœuds (S1 : R de 4 + 8 ; S2/S3 : 6+6)
T_STEPS = 400           # pas de simulation par seed
SIGMA_NOISE = 0.35      # bruit iid par nœud
L0_BROADCAST = 1.0      # chargement f0 (tous les nœuds)
L1_LOCAL = 1.4          # chargement f1 (nœuds de la cause locale)
W_HIGH = 1.0            # couplage de champ intra-région
W_LOW = 0.35            # couplage de champ inter-régions
TAU_FIELD = 0.5         # seuil topologique (composantes connexes de W >= tau)
RHO_STAR = 0.75         # seuil fonctionnel (v2 : centre des plateaux 0.538/0.891)
M_NULL = 200            # partitions aléatoires appariées par null
SEEDS = (0, 1, 7, 42, 99)
# Bandes de verdict (pré-enregistrées) :
BAND_INVISIBLE = (0.75, 1.30)   # P2 : la frontière n'est NI ratifiée NI punie
MIN_VISIBLE = 1.50              # P3/P4 : la frontière est punie au-delà du hasard


@dataclass(frozen=True)
class Substrate:
    """Substrat factoriel + topologie de champ verrouillés par construction."""

    name: str
    W: np.ndarray            # (N, N) poids de couplage de champ
    L: np.ndarray            # (N, 2) chargements [f0, f1]
    local_set: tuple         # indices chargés sur f1 (témoin de construction)


def _ring_adjacency(n: int, region: tuple, w_in: float, w_cross: float) -> np.ndarray:
    """Anneau à n nœuds ; arêtes internes à `region` (et à son complément)
    de poids `w_in`, arêtes traversantes `w_cross`."""
    W = np.zeros((n, n))
    for i in range(n):
        j = (i + 1) % n
        cross = (i in region) != (j in region)
        w = w_cross if cross else w_in
        W[i, j] = w
        W[j, i] = w
    return W


def build_substrate(kind: str) -> Substrate:
    """Construit l'un des trois substrats verrouillés (S1/S2/S3)."""
    n = N_NODES
    L = np.zeros((n, 2))
    L[:, 0] = L0_BROADCAST
    if kind == "s1_topo_split_broadcast":
        # Couplage concentré dans R = {0,1,2,3} ; broadcast pur (f1 éteint).
        region = (0, 1, 2, 3)
        W = _ring_adjacency(n, region, W_HIGH, W_LOW)
        return Substrate(kind, W, L, local_set=())
    if kind == "s2_scattered_cause":
        # Champ uniforme (UNE composante) ; f1 sur les nœuds pairs dispersés.
        H = tuple(range(0, n, 2))
        W = _ring_adjacency(n, tuple(), W_HIGH, W_HIGH)
        L[list(H), 1] = L1_LOCAL
        return Substrate(kind, W, L, local_set=H)
    if kind == "s3_ctrl_aligned":
        # Couplage concentré dans R = {0..5} ET f1 charge exactement R.
        region = tuple(range(0, 6))
        W = _ring_adjacency(n, region, W_HIGH, W_LOW)
        L[list(region), 1] = L1_LOCAL
        return Substrate(kind, W, L, local_set=region)
    raise ValueError(f"kind inconnu : {kind!r}")


def simulate(substrate: Substrate, seed: int, t_steps: int = T_STEPS) -> np.ndarray:
    """Tire les facteurs et les signaux : X[t, i] = L_i · f(t) + eps_i(t)."""
    rng = np.random.default_rng(seed)
    f = rng.standard_normal((t_steps, 2))
    eps = rng.standard_normal((t_steps, substrate.L.shape[0])) * SIGMA_NOISE
    return f @ substrate.L.T + eps


def connected_components(adj: np.ndarray, threshold: float) -> list[list[int]]:
    """Composantes connexes du graphe des arêtes de poids >= threshold (BFS)."""
    n = adj.shape[0]
    seen = [False] * n
    comps: list[list[int]] = []
    for start in range(n):
        if seen[start]:
            continue
        comp: list[int] = []
        stack = [start]
        seen[start] = True
        while stack:
            u = stack.pop()
            comp.append(u)
            for v in np.flatnonzero(adj[u] >= threshold):
                if not seen[v]:
                    seen[v] = True
                    stack.append(int(v))
        comps.append(sorted(comp))
    return comps


def field_topology_boundary(substrate: Substrate) -> list[list[int]]:
    """Frontière EM-topologique : composantes connexes du champ à seuil tau."""
    return connected_components(substrate.W, TAU_FIELD)


def functional_boundary(X: np.ndarray) -> list[list[int]]:
    """Frontière fonctionnelle : composantes connexes de la corrélation
    empirique à seuil rho* (règle verrouillée, estimée sur données)."""
    corr = np.corrcoef(X, rowvar=False)
    return connected_components(corr, RHO_STAR)


def partition_reading_divergence(X: np.ndarray, parts: list[list[int]]) -> float:
    """D(P) = E_t[ std_p( lecture_p(t) )], lecture_p = moyenne des signaux
    de la partie. Une partie unique donne 0 exact."""
    if len(parts) <= 1:
        return 0.0
    readings = np.stack([X[:, p].mean(axis=1) for p in parts], axis=1)
    return float(np.std(readings, axis=1).mean())


def matched_random_null(X: np.ndarray, sizes: list[int], m_null: int,
                        seed: int) -> float:
    """Médiane de D sur des partitions aléatoires de MÊMES tailles."""
    n = X.shape[1]
    rng = np.random.default_rng(seed)
    divs = []
    for _ in range(m_null):
        perm = rng.permutation(n)
        parts: list[list[int]] = []
        pos = 0
        for s in sizes:
            parts.append(sorted(int(v) for v in perm[pos:pos + s]))
            pos += s
        divs.append(partition_reading_divergence(X, parts))
    return float(np.median(divs))


def boundary_case(kind: str, seed: int) -> dict:
    """Un substrat × un seed : frontières candidates, divergences, nulls, ratios."""
    sub = build_substrate(kind)
    X = simulate(sub, seed)
    p_topo = field_topology_boundary(sub)
    p_func = functional_boundary(X)
    d_topo = partition_reading_divergence(X, p_topo)
    d_func = partition_reading_divergence(X, p_func)
    null_topo = matched_random_null(X, [len(p) for p in p_topo], M_NULL, seed)
    null_func = matched_random_null(X, [len(p) for p in p_func], M_NULL, seed)
    def _ratio(d: float, null: float, parts: list[list[int]]):
        # v2 : une règle qui trace une seule composante est EFFONDRÉE —
        # ratio indéfini, jamais compté comme pass (c.5709502555).
        if len(parts) <= 1:
            return None
        return d / null if null > 0 else None

    return {
        "kind": kind,
        "seed": seed,
        "parts_topo": p_topo,
        "parts_func": p_func,
        "d_topo": d_topo,
        "d_func": d_func,
        "null_topo": null_topo,
        "null_func": null_func,
        "ratio_topo": _ratio(d_topo, null_topo, p_topo),
        "ratio_func": _ratio(d_func, null_func, p_func),
    }


def run_case14_protocol() -> dict:
    """Protocole complet : 3 substrats × 5 seeds, verdicts contre bandes
    pré-enregistrées."""
    out: dict = {"seeds": list(SEEDS), "cases": {}}
    cases = {
        "s1": ("s1_topo_split_broadcast", "ratio_topo"),
        "s2": ("s2_scattered_cause", "ratio_func"),
        "s3": ("s3_ctrl_aligned", "ratio_topo"),
    }
    for label, (kind, ratio_key) in cases.items():
        per_seed = [boundary_case(kind, s) for s in SEEDS]
        ratios = [c[ratio_key] for c in per_seed]
        rejets = [c["seed"] for c in per_seed if c[ratio_key] is None]
        if rejets:
            # v2 : un effondrement de règle invalide la prédiction —
            # jamais compté comme pass (leçon case 6 : 2/5 = INCONCLUSIVE).
            verdict = f"REJET_PROTOCOLE (règle effondrée : seeds {rejets})"
        elif label == "s1":
            lo, hi = BAND_INVISIBLE
            verdict = "INVISIBLE (dans la bande)" if all(
                lo <= r <= hi for r in ratios) else "HORS BANDE"
        else:
            verdict = "VISIBLE (>= min)" if all(
                r >= MIN_VISIBLE for r in ratios) else "SOUS LE MIN"
        valid = [r for r in ratios if r is not None]
        out["cases"][label] = {
            "kind": kind,
            "ratio_key": ratio_key,
            "ratios": ratios,
            "median": float(np.median(valid)) if valid else None,
            "verdict": verdict,
            "per_seed": per_seed,
        }
    return out
