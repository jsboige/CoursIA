"""Self-Location Lens (S-Lens) — bancs, oracles et métriques du POC #15481.

Le S-Lens est un **quatrième instrument** expérimental du toolkit ICT (#15475) :
il mesure si la représentation interne porte la *bonne référence* — position,
source ou relation de binding — nécessaire à la prédiction. Ce module est le
cœur **numpy-only** du POC (règle d'architecture de la série : torch reste
confiné aux scripts d'extraction/entraînement, cf. ``scripts/slens_poc.py``).

Ce qui vit ici est testable sans GPU :

* les **bancs synthétiques** (`copy_offset`, `variable_binding`) avec ground
  truth *exacte* et oracle de contrôle (le générateur est validé contre
  l'oracle, jamais l'inverse) ;
* la **distribution ground-truth** des positions de référence, exacte par
  construction ;
* le **probe linéaire** (ridge closed-form) et ses métriques held-out
  (R², RMSE, taux d'exactitude) — aucune métrique in-sample n'est présentée
  comme résultat ;
* les **contrôles** de localisation : shuffle, position absolue, contenu,
  cible aléatoire (ce dernier délégué au moteur commun
  :mod:`ict.causal_engine`) ;
* le **verdict de promotion** `PROMOTE / SPECIALIZED_ONLY / INCONCLUSIVE`.

Statut contractuel (honnêteté référentielle) : ``slens`` n'entre PAS dans
l'énumération ``INSTRUMENTS`` du contrat de trace v1 (``sae``, ``jlens``,
``jlens_trackp``). Le POC est expérimental — « no final notebook issue before
the promotion gate » (#15481). Les manifestes produits ici sont donc
**POC-locaux** (:func:`slens_manifest`) : ils portent les champs d'alignement
qui devront être respectés à la promotion, sans prétendre être validables par
:func:`ict.trace_contract.validate_manifest`. Ajouter ``slens`` au contrat
public est une étape *post-promotion*, pas un prérequis du POC.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping, Sequence

import numpy as np

__all__ = [
    "SLENS_CONTRACT_NOTE",
    "CopyOffsetConfig",
    "VarBindingConfig",
    "generate_copy_offset",
    "oracle_copy_offset",
    "generate_variable_binding",
    "oracle_variable_binding",
    "exact_position_distribution",
    "paired_by_offset",
    "paired_by_query",
    "ridge_probe",
    "probe_metrics",
    "self_location_table",
    "copy_success_by_position",
    "shuffle_control_scores",
    "location_causal_verdict",
    "promotion_verdict",
    "load_run",
    "run_metrics",
    "evidence_from_runs",
    "slens_manifest",
]

#: Note de contrat embarquée dans chaque manifeste POC.
SLENS_CONTRACT_NOTE = (
    "POC #15481 : instrument experimental hors enum du contrat v1 "
    "(sae|jlens|jlens_trackp). Manifeste POC-local, non validable par "
    "validate_manifest avant le gate de promotion."
)


# --------------------------------------------------------------------------- #
# Bancs synthetiques : ground truth EXACTE + oracle de controle
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class CopyOffsetConfig:
    """Banc ``copy_offset`` : l'offset est dans le contenu, la prediction
    exige de remonter a la bonne reference.

    Disposition (indices de sequence 0-based) ::

        [ v_0 ... v_{L-1} , OFF(k) , Q ]

    * valeurs : ids ``0..V-1`` (uniformes) ;
    * ``OFF(k)`` : id ``V + (k - 1)`` pour ``k`` dans ``1..L`` — l'offset est
      un **symbole de contenu**, il ne depend d'aucun encodage positionnel ;
    * ``Q`` : id ``V + L`` (marqueur de requete, position finale).

    Cible : ``v_{L-k}``. Position de reference (index de sequence) : ``L - k``.
    """

    seq_values: int = 12          # L : taille du bloc de valeurs
    n_symbols: int = 16           # V : taille du vocabulaire de valeurs
    min_offset: int = 1
    max_offset: int | None = None  # None -> L

    def __post_init__(self) -> None:
        if self.seq_values < 2:
            raise ValueError("seq_values doit valoir au moins 2")
        if self.n_symbols < 2:
            raise ValueError("n_symbols doit valoir au moins 2")
        hi = self.seq_values if self.max_offset is None else int(self.max_offset)
        if not (1 <= self.min_offset <= hi <= self.seq_values):
            raise ValueError(
                f"bornes d'offset invalides : {self.min_offset}..{hi} "
                f"pour seq_values={self.seq_values}"
            )

    @property
    def max_off(self) -> int:
        return self.seq_values if self.max_offset is None else int(self.max_offset)

    @property
    def query_id(self) -> int:
        return self.n_symbols + self.seq_values

    @property
    def n_tokens(self) -> int:
        """Taille de la sequence produite (bloc + OFF + Q)."""
        return self.seq_values + 2

    @property
    def vocab_size(self) -> int:
        return self.n_symbols + self.seq_values + 1


@dataclass(frozen=True)
class VarBindingConfig:
    """Second probleme de binding (gate de promotion) : variable -> valeur.

    Disposition ::

        [ x_0 a_0 x_1 a_1 ... x_{P-1} a_{P-1} , QB , x_q ]

    * variables : ids ``0..V_var-1`` ; valeurs : ids ``V_var..V_var+V_val-1`` ;
    * ``QB`` : marqueur de requete ``V_var + V_val`` ;
    * ``x_q`` : variable interrogee (tiree parmi celles du contexte, sans
      remise — la reponse existe toujours).

    Cible : la valeur liee a ``x_q``. Position de reference : l'index du
    couple ``(x_q, a)`` dans le contexte, soit ``2 * rank(x_q) + 1``.
    """

    n_pairs: int = 5              # P : nombre de liaisons dans le contexte
    n_vars: int = 8               # V_var
    n_vals: int = 8               # V_val

    def __post_init__(self) -> None:
        if self.n_pairs < 2:
            raise ValueError("n_pairs doit valoir au moins 2")
        if self.n_pairs > self.n_vars:
            raise ValueError("n_pairs ne peut exceder n_vars (liaisons distinctes)")
        if self.n_vars < 2 or self.n_vals < 2:
            raise ValueError("n_vars et n_vals doivent valoir au moins 2")

    @property
    def query_marker(self) -> int:
        return self.n_vars + self.n_vals

    @property
    def n_tokens(self) -> int:
        return 2 * self.n_pairs + 2

    @property
    def vocab_size(self) -> int:
        return self.n_vars + self.n_vals + 1


def generate_copy_offset(
    rng: np.random.Generator, n: int, cfg: CopyOffsetConfig = CopyOffsetConfig()
) -> dict[str, np.ndarray]:
    """Tire ``n`` exemples ``copy_offset`` avec cible et position exactes.

    Returns
    -------
    dict avec ``tokens`` (n, T) int64, ``target_value`` (n,), ``target_pos``
    (n,), ``offset`` (n,).
    """
    if n <= 0:
        raise ValueError("n doit etre strictement positif")
    L, V = cfg.seq_values, cfg.n_symbols
    lo, hi = cfg.min_offset, cfg.max_off
    values = rng.integers(0, V, size=(n, L)).astype(np.int64)
    offsets = rng.integers(lo, hi + 1, size=n).astype(np.int64)
    off_tok = V + (offsets - 1)
    q = np.full((n, 1), cfg.query_id, dtype=np.int64)
    tokens = np.concatenate([values, off_tok[:, None], q], axis=1)
    target_pos = L - offsets                      # index de sequence
    target_value = values[np.arange(n), target_pos]
    return {
        "tokens": tokens,
        "target_value": target_value.astype(np.int64),
        "target_pos": target_pos.astype(np.int64),
        "offset": offsets,
    }


def oracle_copy_offset(
    tokens: np.ndarray, cfg: CopyOffsetConfig = CopyOffsetConfig()
) -> tuple[np.ndarray, np.ndarray]:
    """Oracle exact du banc : relit l'offset DANS le contenu et resout la reference.

    Independant du generateur (il ne partage que la convention de disposition) :
    c'est ce qui permet de valider le generateur au lieu de le croire.
    """
    tokens = np.atleast_2d(np.asarray(tokens, dtype=np.int64))
    L, V = cfg.seq_values, cfg.n_symbols
    if tokens.shape[1] != cfg.n_tokens:
        raise ValueError(
            f"sequence de longueur {tokens.shape[1]} != n_tokens={cfg.n_tokens}"
        )
    off_tok = tokens[:, L]
    offsets = (off_tok - V) + 1
    if np.any((offsets < 1) | (offsets > L)):
        raise ValueError("token d'offset hors bornes du banc")
    pos = L - offsets
    vals = tokens[np.arange(tokens.shape[0]), pos]
    return vals.astype(np.int64), pos.astype(np.int64)


def generate_variable_binding(
    rng: np.random.Generator, n: int, cfg: VarBindingConfig = VarBindingConfig()
) -> dict[str, np.ndarray]:
    """Tire ``n`` exemples variable->valeur avec cible et position exactes."""
    if n <= 0:
        raise ValueError("n doit etre strictement positif")
    P, Vv, Vl = cfg.n_pairs, cfg.n_vars, cfg.n_vals
    vars_ = np.stack([rng.choice(Vv, size=P, replace=False) for _ in range(n)])
    vals = rng.integers(0, Vl, size=(n, P)).astype(np.int64)
    query_rank = rng.integers(0, P, size=n)
    rows = np.arange(n)
    x_q = vars_[rows, query_rank]
    seq = np.empty((n, 2 * P + 2), dtype=np.int64)
    seq[:, 0:2 * P:2] = vars_
    seq[:, 1:2 * P:2] = Vv + vals
    seq[:, 2 * P] = cfg.query_marker
    seq[:, 2 * P + 1] = x_q
    target_pos = 2 * query_rank + 1
    target_value = (Vv + vals[rows, query_rank]).astype(np.int64)
    return {
        "tokens": seq,
        "target_value": target_value,
        "target_pos": target_pos.astype(np.int64),
        "query_rank": query_rank.astype(np.int64),
    }


def oracle_variable_binding(
    tokens: np.ndarray, cfg: VarBindingConfig = VarBindingConfig()
) -> tuple[np.ndarray, np.ndarray]:
    """Oracle exact du banc variable->valeur (relit le contexte)."""
    tokens = np.atleast_2d(np.asarray(tokens, dtype=np.int64))
    if tokens.shape[1] != cfg.n_tokens:
        raise ValueError(
            f"sequence de longueur {tokens.shape[1]} != n_tokens={cfg.n_tokens}"
        )
    P, Vv = cfg.n_pairs, cfg.n_vars
    x_q = tokens[:, -1]
    pair_vars = tokens[:, 0:2 * P:2]
    match = pair_vars == x_q[:, None]
    if not np.all(match.sum(axis=1) == 1):
        raise ValueError("variable interrogee absente ou dupliquee dans le contexte")
    rank = match.argmax(axis=1)
    pos = 2 * rank + 1
    vals = tokens[np.arange(tokens.shape[0]), pos]
    if np.any(vals < Vv):
        raise ValueError("la position liee ne porte pas un symbole de valeur")
    return vals.astype(np.int64), pos.astype(np.int64)


def exact_position_distribution(
    cfg: CopyOffsetConfig = CopyOffsetConfig()
) -> np.ndarray:
    """Distribution ground-truth EXACTE des positions de reference du banc.

    Uniforme sur ``[0, L)`` quand ``min_offset..max_off`` couvre tout le bloc ;
    sinon la masse est portee par ``L - k`` pour ``k`` dans les bornes.
    Sert de reference pour le controle shuffle et la lecture par position.
    """
    L = cfg.seq_values
    counts = np.zeros(L, dtype=np.float64)
    for k in range(cfg.min_offset, cfg.max_off + 1):
        counts[L - k] += 1.0
    return counts / counts.sum()


def paired_by_offset(
    cfg: CopyOffsetConfig, rng: np.random.Generator, n_pairs: int
) -> dict[str, np.ndarray]:
    """Paires contre-factuelles APPARIEES pour l'interchange.

    Chaque paire partage le MEME bloc de valeurs et ne differe que par
    l'offset : le contexte amont est identique, seule la reference correcte
    change. C'est ce qui rend un echange de representation interpretable —
    si la sortie suit le donneur, elle suit la *reference*, pas une
    correlation de surface.
    """
    if n_pairs <= 0:
        raise ValueError("n_pairs doit etre strictement positif")
    base = generate_copy_offset(rng, n_pairs, cfg)
    L = cfg.seq_values
    V = cfg.n_symbols
    # offset du donneur : decale, borne a 1..L, et JAMAIS egal a celui de l'hote.
    off_a = base["offset"]
    off_b = rng.integers(cfg.min_offset, cfg.max_off + 1, size=n_pairs)
    collide = off_b == off_a
    off_b[collide] = 1 + (off_b[collide] % cfg.max_off)
    collide = off_b == off_a
    off_b[collide] = cfg.max_off
    tok_b = base["tokens"].copy()
    tok_b[:, L] = V + (off_b - 1)
    val_b, pos_b = oracle_copy_offset(tok_b, cfg)
    return {
        "tokens_a": base["tokens"],
        "tokens_b": tok_b,
        "target_value_a": base["target_value"],
        "target_value_b": val_b,
        "target_pos_a": base["target_pos"],
        "target_pos_b": pos_b,
        "offset_a": off_a,
        "offset_b": off_b,
    }


def paired_by_query(
    cfg: VarBindingConfig, rng: np.random.Generator, n_pairs: int
) -> dict[str, np.ndarray]:
    """Paires contre-factuelles appariees du second banc (variable->valeur).

    Analogue exact de :func:`paired_by_offset` pour le banc variable->valeur :
    chaque paire partage **tout le contexte de liaisons** et ne differe que par
    la variable interrogee. La reference correcte change donc a contexte
    strictement identique — condition pour qu'un echange de representation
    soit interpretable comme un suivi de *reference*, pas de surface.
    """
    if n_pairs <= 0:
        raise ValueError("n_pairs doit etre strictement positif")
    base = generate_variable_binding(rng, n_pairs, cfg)
    tok_a = base["tokens"]
    x_q_a = tok_a[:, -1]
    # variable interrogee du donneur : celle d'une AUTRE paire du contexte,
    # jamais la meme que l'hote.
    alt_rank = (base["query_rank"] + 1) % cfg.n_pairs
    rows = np.arange(n_pairs)
    x_q_b = tok_a[rows, 2 * alt_rank]
    tok_b = tok_a.copy()
    tok_b[:, -1] = x_q_b
    val_b, pos_b = oracle_variable_binding(tok_b, cfg)
    if np.any(x_q_b == x_q_a):
        raise ValueError("appariement par requete degenere (meme variable)")
    return {
        "tokens_a": tok_a,
        "tokens_b": tok_b,
        "target_value_a": base["target_value"],
        "target_value_b": val_b,
        "target_pos_a": base["target_pos"],
        "target_pos_b": pos_b,
        "query_rank_a": base["query_rank"],
        "query_rank_b": alt_rank.astype(np.int64),
    }


# --------------------------------------------------------------------------- #
# Probe lineaire (ridge closed-form) et metriques held-out
# --------------------------------------------------------------------------- #

def ridge_probe(
    x_train: np.ndarray, y_train: np.ndarray, alpha: float = 1e-2
) -> np.ndarray:
    """Ridge closed-form avec biais, en numpy pur.

    ``x_train`` (n, d) ; ``y_train`` (n,) indices OU (n, c) one-hot/cibles
    continues. Renvoie la matrice de poids (d + 1, c) — le biais est la
    derniere ligne (colonne d'appariement ajoutee a la conception).
    """
    x = np.asarray(x_train, dtype=np.float64)
    y = np.asarray(y_train, dtype=np.float64)
    if x.ndim != 2:
        raise ValueError("x_train doit etre (n, d)")
    if y.ndim == 1:
        y = y[:, None]
    if y.shape[0] != x.shape[0]:
        raise ValueError("x_train et y_train n'ont pas le meme nombre d'exemples")
    if alpha < 0:
        raise ValueError("alpha doit etre positif ou nul")
    design = np.concatenate([x, np.ones((x.shape[0], 1))], axis=1)
    gram = design.T @ design
    reg = alpha * np.eye(gram.shape[0])
    reg[-1, -1] = 0.0  # le biais n'est pas regularise
    return np.linalg.solve(gram + reg, design.T @ y)


def probe_metrics(
    x_test: np.ndarray, y_test: np.ndarray, weights: np.ndarray
) -> dict[str, float]:
    """Metriques held-out d'un probe : R², RMSE, exactitude (si classification).

    Pour une cible *entiere* (position, symbole), ``y_test`` est traite comme
    une classe : la prediction est l'argmax de la lecture linéaire, et
    ``exact_hit`` est le taux d'exactitude. ``r2`` et ``rmse`` sont calcules
    sur la meme lecture continue — ils sont reportes pour la gradation de
    l'erreur de localisation, pas comme substitut du taux d'exactitude.
    """
    x = np.asarray(x_test, dtype=np.float64)
    y = np.asarray(y_test)
    if x.ndim != 2:
        raise ValueError("x_test doit etre (n, d)")
    if y.ndim != 1:
        raise ValueError("y_test doit etre (n,) pour ces metriques")
    design = np.concatenate([x, np.ones((x.shape[0], 1))], axis=1)
    pred = design @ weights                      # (n, c) ou (n, 1)
    if pred.shape[1] == 1:
        pred_cont = pred[:, 0]
        exact = float(np.mean(np.rint(pred_cont) == y))
    else:
        pred_cls = pred.argmax(axis=1)
        exact = float(np.mean(pred_cls == y))
        pred_cont = pred_cls.astype(np.float64)
    resid = pred_cont - y.astype(np.float64)
    ss_res = float(np.sum(resid**2))
    ss_tot = float(np.sum((y.astype(np.float64) - y.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    return {
        "exact_hit": exact,
        "rmse": float(np.sqrt(ss_res / y.shape[0])),
        "r2": float(r2),
        "n_test": int(y.shape[0]),
    }


def self_location_table(
    activations: Mapping[str, np.ndarray],
    positions: np.ndarray,
    *,
    values: np.ndarray | None = None,
    alpha: float = 1e-2,
    train_frac: float = 0.7,
    n_labels: int | None = None,
) -> list[dict[str, Any]]:
    """Erreur de self-location par couche/tete, split gelé train/held-out.

    ``activations`` : mapping ``"L{layer}H{head}" -> (n, d_head)`` (et
    eventuellement ``"L{layer}"`` pour le residual de couche). Le split est
    fait une fois, sur les indices, et partagé par tous les probes — sinon
    chaque tete serait évaluée sur un jeu différent, ce qui rend les
    comparaisons entre tetes illisibles.

    Renvoie une ligne par entree : position (self-location) et, si ``values``
    est fourni, valeur (readout de copie) — jamais un score in-sample.
    """
    positions = np.asarray(positions)
    if positions.ndim != 1:
        raise ValueError("positions doit etre (n,)")
    if not 0.0 < train_frac < 1.0:
        raise ValueError("train_frac doit etre dans ]0, 1[")
    n = positions.shape[0]
    n_train = int(round(n * train_frac))
    if n_train < 2 or n - n_train < 2:
        raise ValueError("jeu trop petit pour un split train/held-out")
    order = np.arange(n)
    tr, te = order[:n_train], order[n_train:]
    rows: list[dict[str, Any]] = []
    for key in sorted(activations):
        acts = np.asarray(activations[key], dtype=np.float64)
        if acts.shape[0] != n:
            raise ValueError(f"{key}: {acts.shape[0]} exemples != {n} positions")
        if n_labels is not None:
            y_pos = np.eye(int(n_labels))[positions]
        else:
            y_pos = positions.astype(np.float64)[:, None]
        w_pos = ridge_probe(acts[tr], y_pos[tr], alpha=alpha)
        m_pos = probe_metrics(acts[te], positions[te], w_pos)
        row: dict[str, Any] = {
            "unit": key,
            "position_exact": m_pos["exact_hit"],
            "position_rmse": m_pos["rmse"],
            "position_r2": m_pos["r2"],
        }
        if values is not None:
            vals = np.asarray(values)
            if vals.shape[0] != n:
                raise ValueError(f"{key}: {vals.shape[0]} valeurs != {n} positions")
            classes = np.unique(vals)
            index = {int(v): i for i, v in enumerate(classes)}
            y_val = np.zeros((n, len(classes)))
            for i, v in enumerate(vals):
                y_val[i, index[int(v)]] = 1.0
            w_val = ridge_probe(acts[tr], y_val[tr], alpha=alpha)
            m_val = probe_metrics(acts[te], vals[te], w_val)
            row["value_exact"] = m_val["exact_hit"]
            row["value_rmse"] = m_val["rmse"]
        rows.append(row)
    return rows


# --------------------------------------------------------------------------- #
# Controles et lecture comportementale
# --------------------------------------------------------------------------- #

def copy_success_by_position(
    predicted: np.ndarray, target_value: np.ndarray, target_pos: np.ndarray,
    n_positions: int,
) -> np.ndarray:
    """Taux de reussite par position de reference (lecture brute du modele).

    La distribution ground-truth exacte (:func:`exact_position_distribution`)
    dit ce qu'un hasard par position produirait ; ce vecteur dit ce que le
    modele produit réellement.
    """
    predicted = np.asarray(predicted)
    target_value = np.asarray(target_value)
    target_pos = np.asarray(target_pos)
    if not (predicted.shape == target_value.shape == target_pos.shape):
        raise ValueError("predicted, target_value et target_pos doivent etre alignes")
    out = np.zeros(int(n_positions), dtype=np.float64)
    counts = np.zeros(int(n_positions), dtype=np.float64)
    for p in range(int(n_positions)):
        m = target_pos == p
        counts[p] = m.sum()
        if counts[p] > 0:
            out[p] = float(np.mean(predicted[m] == target_value[m]))
    return np.divide(out, 1.0, out=np.full_like(out, np.nan), where=counts > 0)


def shuffle_control_scores(
    activations: np.ndarray, positions: np.ndarray, values: np.ndarray,
    *, rng: np.random.Generator, alpha: float = 1e-2, train_frac: float = 0.7,
) -> dict[str, float]:
    """Controle shuffle : memes probes, appariement cible/representation detruit.

    La permutation est appliquee aux ETIQUETTES du jeu d'entrainement
    seulement, et le held-out reste intact : on mesure donc la capacite du
    probe a generaliser sans signal (plancher empirique), pas une
    auto-prediction.
    """
    acts = np.asarray(activations, dtype=np.float64)
    positions = np.asarray(positions)
    values = np.asarray(values)
    n = positions.shape[0]
    n_train = int(round(n * train_frac))
    tr, te = np.arange(n_train), np.arange(n_train, n)
    perm = rng.permutation(n_train)
    classes = np.unique(values)
    index = {int(v): i for i, v in enumerate(classes)}
    y_val = np.zeros((n, len(classes)))
    for i, v in enumerate(values):
        y_val[i, index[int(v)]] = 1.0
    w_shuf = ridge_probe(acts[tr], y_val[tr][perm], alpha=alpha)
    m_shuf = probe_metrics(acts[te], values[te], w_shuf)
    n_labels = int(positions.max()) + 1
    y_pos = np.eye(n_labels)[positions]
    w_pos = ridge_probe(acts[tr], y_pos[tr][perm], alpha=alpha)
    m_pos = probe_metrics(acts[te], positions[te], w_pos)
    return {
        "value_exact": m_shuf["exact_hit"],
        "position_exact": m_pos["exact_hit"],
    }


def location_causal_verdict(
    follow_donor: float,
    sham: float,
    random_target: float,
    damage: Mapping[str, float],
    *,
    min_follow: float = 0.5,
    min_gap: float = 0.25,
    max_off_target: float = 0.10,
) -> dict[str, Any]:
    """Verdict causal du panneau de patching, canaux séparés (#15475).

    ``follow_donor`` : taux auquel la sortie patchée suit la reference du
    donneur apparié ; ``sham`` (auto-echange, doit rester au niveau baseline) et
    ``random_target`` (échange non apparié) sont les deux planchers. Le verdict
    exige que l'effet apparié depasse le sham d'au moins ``min_gap`` ET que le
    dommage hors cible reste sous ``max_off_target`` — la selectivité et
    l'effet sont DEUX conditions, jamais une seule.
    """
    effect = float(follow_donor)
    gap = effect - max(float(sham), float(random_target))
    off = float(damage.get("off_target_rel", float("inf")))
    selective = off <= max_off_target
    if selective and effect >= min_follow and gap >= min_gap:
        verdict = "causal"
    elif not selective:
        verdict = "global_damage"
    elif effect >= min_follow:
        verdict = "undiscriminated"      # effet present mais sham non separe
    else:
        verdict = "no_effect"
    return {
        "verdict": verdict,
        "follow_donor": effect,
        "sham": float(sham),
        "random_target": float(random_target),
        "gap_vs_controls": float(gap),
        "off_target_rel": off,
        "selectivity_ok": bool(selective),
    }


# --------------------------------------------------------------------------- #
# Gate de promotion
# --------------------------------------------------------------------------- #

@dataclass
class PromotionEvidence:
    """Preuves agregees (multi-seeds) pour le gate de promotion du S-Lens."""

    position_exact: float          # meilleure unite, moyenne multi-seed
    position_exact_shuffle: float  # plancher shuffle correspondant
    value_exact: float             # readout de copie du meme unite
    copy_accuracy: float           # exactitude comportementale du modele
    causal_verdict: str            # de location_causal_verdict
    second_task_position_exact: float = float("nan")
    second_task_shuffle: float = float("nan")
    second_task_causal: str = ""
    seeds_stable: bool = True
    notes: list[str] = field(default_factory=list)


def promotion_verdict(ev: PromotionEvidence, *, margin: float = 0.15) -> str:
    """`PROMOTE / SPECIALIZED_ONLY / INCONCLUSIVE` — criteres explicites.

    * ``INCONCLUSIVE`` : l'effet n'est pas stable multi-seeds, OU la
      localisation ne se detache pas du shuffle (pas de signal a interpreter).
    * ``PROMOTE`` : localisation au-dessus du shuffle sur les DEUX bancs,
      verdict causal ``causal`` sur le banc primaire, second banc testé.
    * ``SPECIALIZED_ONLY`` : signal sur le banc primaire uniquement (ou sans
      jambe causale hors banc primaire) — demonstrateur spécialisé, aucune
      issue notebook/API définitive (cf. gate #15481).
    """
    if not ev.seeds_stable:
        return "INCONCLUSIVE"
    primary_gain = ev.position_exact - ev.position_exact_shuffle
    if primary_gain < margin:
        return "INCONCLUSIVE"
    second = ev.second_task_position_exact - ev.second_task_shuffle
    if ev.causal_verdict != "causal":
        return "SPECIALIZED_ONLY"
    if not np.isfinite(ev.second_task_position_exact):
        return "SPECIALIZED_ONLY"
    if second < margin:
        return "SPECIALIZED_ONLY"
    if ev.second_task_causal and ev.second_task_causal != "causal":
        return "SPECIALIZED_ONLY"
    return "PROMOTE"


# --------------------------------------------------------------------------- #
# Agregation multi-runs (POC : le notebook reste mince, la logique est testee)
# --------------------------------------------------------------------------- #

def load_run(path: str | "Path") -> dict[str, Any]:
    """Charge un npz de run POC et separe le manifeste des tableaux.

    Le manifeste est stocke dans ``__meta__`` (chaine JSON) : on le relit ici
    pour que le notebook ne manipule jamais un dict opaque a la main.
    """
    import json as _json
    from pathlib import Path as _Path

    with np.load(_Path(path), allow_pickle=False) as npz:
        arrays = {k: npz[k] for k in npz.files}
    meta = _json.loads(str(arrays.pop("__meta__")))
    arrays["patch_stats"] = _json.loads(str(arrays["patch_stats"]))
    return {"meta": meta, "arrays": arrays}


def run_metrics(run: Mapping[str, Any], *, alpha: float = 1e-2,
                rng: np.random.Generator | None = None) -> dict[str, Any]:
    """Metriques d'un run : self-location par tete, shuffle, readout, causal.

    Renvoie la meilleure unite (position), le meilleur readout de valeur, les
    planchers shuffle correspondants et le verdict causal du patching.
    """
    if rng is None:
        rng = np.random.default_rng(int(run["meta"].get("seed", 0)))
    arrays = run["arrays"]
    positions = arrays["target_pos"]
    values = arrays["target_value"]
    n_pos = int(max(positions.max() + 1, arrays["tokens"].shape[1]))
    head_keys = [k for k in arrays if k.startswith("L") and "H" in k and k.endswith("_q")]
    layer_keys = [k for k in arrays if k.startswith("L") and "H" not in k and k.endswith("_q")]
    # ``_q`` marque "capture a la position de requete" : c'est une convention de
    # stockage, pas une propriete de l'unite. Les rapports lisent ``L0H0``.
    units = {k.removesuffix("_q"): arrays[k] for k in sorted(head_keys + layer_keys)}
    table = self_location_table(units, positions, values=values, alpha=alpha,
                                n_labels=n_pos)
    by_unit = {row["unit"]: row for row in table}
    best_pos = max(table, key=lambda r: r["position_exact"])
    best_val = max(table, key=lambda r: r.get("value_exact", -1.0))
    shuffle = shuffle_control_scores(
        units[best_pos["unit"]], positions, values, rng=rng, alpha=alpha)
    stats = dict(arrays["patch_stats"])
    damage = {
        "off_target_rel": stats["off_target_rel"],
        "target_rel": stats["target_rel"],
        "selectivity_ratio": stats["selectivity_ratio"],
    }
    causal = location_causal_verdict(
        stats["follow_donor"], stats["sham"], stats["random_target"], damage)
    return {
        "task": run["meta"]["task"],
        "arch": run["meta"]["arch"],
        "seed": int(run["meta"]["seed"]),
        "table": table,
        "best_unit": best_pos["unit"],
        "position_exact": float(best_pos["position_exact"]),
        "position_exact_shuffle": float(shuffle["position_exact"]),
        "value_exact": float(best_val.get("value_exact", float("nan"))),
        "value_exact_shuffle": float(shuffle["value_exact"]),
        "copy_accuracy": float(arrays["predictions_accuracy"]),
        "causal": causal,
        "patch_stats": stats,
    }


def evidence_from_runs(
    runs: Sequence[Mapping[str, Any]], *, task: str = "copy_offset",
    second_task: str = "variable_binding", stability_tol: float = 0.10,
) -> tuple[PromotionEvidence, list[dict[str, Any]]]:
    """Agrege les runs d'un POC en :class:`PromotionEvidence` + table detaillee.

    La stabilite multi-seeds est exigeante : l'ecart de localisation au-dessus
    du shuffle doit rester positif pour CHAQUE seed du banc primaire (une
    moyenne qui tient grace a une seed sur quatre n'est pas une generalisation).
    """
    rows = [run_metrics(r) for r in runs]
    primary = [r for r in rows if r["task"] == task]
    secondary = [r for r in rows if r["task"] == second_task]
    if not primary:
        raise ValueError(f"aucun run pour le banc primaire {task!r}")

    gains = [r["position_exact"] - r["position_exact_shuffle"] for r in primary]
    seeds_stable = all(g > 0 for g in gains) and (
        max(gains) - min(gains) <= stability_tol * max(1.0, max(gains))
    )
    best_primary = max(primary, key=lambda r: r["position_exact"])
    causal_verdicts = [r["causal"]["verdict"] for r in primary]
    # le verdict causal agrege = le plus frequent (mode) ; un partage exact
    # n'est pas une preuve de selectivite et retombe sur le pire cas.
    causal_mode = max(set(causal_verdicts), key=causal_verdicts.count)
    if causal_verdicts.count(causal_mode) * 2 <= len(causal_verdicts):
        causal_mode = "undiscriminated"

    notes: list[str] = []
    if secondary:
        sec_best = max(secondary, key=lambda r: r["position_exact"])
        sec_gain = sec_best["position_exact"] - sec_best["position_exact_shuffle"]
        sec_causal = max(
            [r["causal"]["verdict"] for r in secondary],
            key=[r["causal"]["verdict"] for r in secondary].count,
        )
        sec_pos = float(sec_best["position_exact"])
        sec_shuf = float(sec_best["position_exact_shuffle"])
    else:
        sec_pos = sec_shuf = float("nan")
        sec_causal = ""
        sec_gain = float("nan")
        notes.append("banc secondaire absent : gate de promotion non evaluable")

    ev = PromotionEvidence(
        position_exact=float(best_primary["position_exact"]),
        position_exact_shuffle=float(best_primary["position_exact_shuffle"]),
        value_exact=float(best_primary["value_exact"]),
        copy_accuracy=float(best_primary["copy_accuracy"]),
        causal_verdict=causal_mode,
        second_task_position_exact=sec_pos,
        second_task_shuffle=sec_shuf,
        second_task_causal=sec_causal,
        seeds_stable=bool(seeds_stable),
        notes=notes,
    )
    if not np.isfinite(sec_gain):
        pass
    elif sec_gain <= 0:
        notes.append(
            "le second banc ne se detache pas de son plancher shuffle : "
            "le S-Lens reste un demonstrateur specialise"
        )
    return ev, rows


# --------------------------------------------------------------------------- #
# Manifeste POC-local
# --------------------------------------------------------------------------- #

def slens_manifest(
    *, task: str, arch: str, run: str, seed: int, layer: int,
    d_model: int, n_heads: int, n_layers: int, n_test: int,
    prompt_set: str = "", **extra: Any,
) -> dict[str, Any]:
    """Manifeste POC-local : champs d'alignement du contrat v1 + note de statut.

    Volontairement NON validable par :func:`ict.trace_contract.validate_manifest`
    (l'instrument ``slens`` n'est pas dans l'enum v1) — la note embarquée dit
    pourquoi et ce que la promotion devra ajouter.
    """
    if not task or not arch:
        raise ValueError("task et arch sont requis")
    manifest: dict[str, Any] = {
        "instrument": "slens_poc",
        "contract_version": "poc-0.1.0",
        "contract_note": SLENS_CONTRACT_NOTE,
        "task": task,
        "arch": arch,
        "run": run,
        "seed": int(seed),
        "layer": int(layer),
        "n_layers": int(n_layers),
        "d_model": int(d_model),
        "n_heads": int(n_heads),
        "prompt_set": prompt_set,
        "n_test": int(n_test),
    }
    manifest.update(extra)
    return manifest
