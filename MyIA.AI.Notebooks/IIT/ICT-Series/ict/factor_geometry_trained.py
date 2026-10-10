"""Boucle fermee de la geometrie factorisee (#15478).

Le mode *factored-geometry* mesurait jusqu'ici deux choses qui partagent le
meme angle mort :

- des activations **simulees** (``factor_geometry.synthesize_activations``),
  ou la factorisation est posee par construction, donc retrouvee ;
- un temoin nul de sous-espaces **aleatoires**, qui ignore le biais inductif
  de l'architecture — il ne repond pas a l'objection « un modele non entraine
  a peut-etre deja des sous-espaces separes ».

Ce module ferme la boucle. Un modele est **reellement entraine** sur le banc
factorise, la geometrie est mesuree sur **ses** activations, et le temoin nul
est celui d'initialisations **non entrainees de la meme architecture**.

Trois pieces, dans l'ordre ou elles s'enchainent :

1. :func:`predictive_matrix` et :func:`bayes_floor` — le plancher de perte
   Bayes-optimal du processus, **exact**, lu sur la filtration forward du banc.
   Il sert de condition d'entree : aucun verdict geometrique n'est rendu si le
   modele n'a pas appris le processus.
2. :class:`FactoredRNN`, :func:`train_model`, :func:`collect_activations` — le
   modele et sa boucle d'entrainement, avec arret sur la meilleure validation.
3. :func:`probe_coefficient_basis`, :func:`factor_geometry_report` et
   :func:`untrained_null` — la lecture geometrique, et son temoin.

Les trois vues sont **rapportees a cote, jamais fusionnees** : qualite des
probes (decodabilite), recouvrement des sous-espaces de COEFFICIENTS, et
recouvrement des directions de VARIANCE (deja fourni par ``factor_geometry``).

Le module est numpy-only pour tout ce qui est mesure ; ``torch`` n'est requis
que pour entrainer, et son absence degrade proprement (``HAS_TORCH``).

Reference du protocole : issue #15478, criteres ajoutes le 2026-09-15 par le
coordinateur apres lecture du depot ``factored-reps``.
"""

from __future__ import annotations

from typing import Callable, Dict, Mapping, Sequence

import numpy as np

from ict.factor_geometry import basis_overlap, max_principal_angle

try:  # torch n'est requis que pour l'entrainement
    import torch
    import torch.nn as nn

    HAS_TORCH = True
except Exception:  # pragma: no cover - depend de l'environnement
    torch = None  # type: ignore
    nn = None  # type: ignore
    HAS_TORCH = False

Array = np.ndarray

__all__ = [
    "HAS_TORCH",
    "predictive_matrix",
    "bayes_floor",
    "FactoredRNN",
    "joint_nll",
    "train_model",
    "collect_activations",
    "probe_coefficient_basis",
    "subspace_rank",
    "factor_geometry_report",
    "untrained_null",
]


# --------------------------------------------------------------------------
# 1. Plancher de Bayes-optimal — exact, lu sur la filtration du banc
# --------------------------------------------------------------------------


def predictive_matrix(process) -> Array:
    """``P[s, y] = P(observation suivante = y | etat cache courant = s)``.

    Deux formes selon le generateur, et c'est la seule difference a porter :

    - processus a sortie **Moore** (``Mess3Canonical``) : l'observation est
      emise depuis l'etat d'arrivee, donc ``P = T @ E`` ou ``T`` est la
      transition et ``E[i, y] = P(y | s = i)`` ;
    - processus **Mealy** (``RRXOR``) : l'observation vit sur l'arete, donc
      ``P[s, y] = sum_s' W[s, s', y]`` somme sur les etats d'arrivee.

    Le discriminant est la presence d'une matrice d'emission : un processus de
    Moore en expose une, un processus de Mealy expose un tenseur d'aretes.
    """
    if hasattr(process, "emission_matrix"):
        return np.asarray(process.transition_matrix(), dtype=np.float64) @ np.asarray(
            process.emission_matrix(), dtype=np.float64
        )
    w = np.asarray(process.edge_tensor(), dtype=np.float64)
    return np.stack([w[:, :, y].sum(axis=1) for y in range(w.shape[2])], axis=1)


def bayes_floor(process, obs: Array, burn: int = 32) -> float:
    """Perte Bayes-optimale du processus, en nats par pas.

    ``E[-log P(y_t | y_<t)]`` calcule sur les beliefs **exacts** de la
    filtration forward (``process.beliefs``), donc sans approximation : c'est
    une borne inferieure atteignable par aucun modele, pas une estimation.

    ``burn`` retire les premiers pas, ou la filtration part du prior
    stationnaire et n'a pas encore resorbe son ambiguite de phase.
    """
    obs = np.asarray(obs)
    if obs.ndim != 1:
        raise ValueError("bayes_floor attend une serie d'observations 1D")
    if burn < 0 or burn >= len(obs) - 1:
        raise ValueError(f"burn={burn} hors bornes pour {len(obs)} pas")
    beliefs = np.asarray(process.beliefs(obs), dtype=np.float64)
    pred = beliefs[:-1] @ predictive_matrix(process)
    y = obs[1:].astype(np.int64)
    nll = -np.log(np.clip(pred[np.arange(len(y)), y], 1e-12, None))
    return float(nll[burn:].mean())


# --------------------------------------------------------------------------
# 2. Modele et boucle d'entrainement
# --------------------------------------------------------------------------


if HAS_TORCH:

    class FactoredRNN(nn.Module):
        """GRU a deux tetes sur les observations jointes d'un banc a 2 facteurs.

        L'entree est la concatenation des plongements des deux canaux ; la
        sortie est une tete par facteur, chacune predisant le **pas suivant**
        de son canal. La perte est la somme des deux entropies croisees, ce
        qui rend la loss du modele directement comparable au plancher de Bayes
        joint (les deux facteurs sont independants dans le banc).

        L'etat cache du GRU est le substrat de mesure : c'est l'analogue du
        *residual stream* pour ce modele, et c'est sur lui que la geometrie
        est lue — jamais sur les entrees.
        """

        def __init__(self, n_a: int = 3, n_b: int = 2, hidden: int = 64, emb: int = 8, seed: int = 0):
            super().__init__()
            torch.manual_seed(seed)
            self.n_a, self.n_b, self.hidden = n_a, n_b, hidden
            self.emb_a = nn.Embedding(n_a, emb)
            self.emb_b = nn.Embedding(n_b, emb)
            self.gru = nn.GRU(2 * emb, hidden, batch_first=True)
            self.head_a = nn.Linear(hidden, n_a)
            self.head_b = nn.Linear(hidden, n_b)

        def forward(self, x, hidden=None):
            h = torch.cat([self.emb_a(x[:, :, 0]), self.emb_b(x[:, :, 1])], dim=-1)
            out, hn = self.gru(h, hidden)
            return self.head_a(out), self.head_b(out), out


def _require_torch() -> None:
    if not HAS_TORCH:
        raise RuntimeError(
            "torch est requis pour entrainer (pip install torch) : "
            "les mesures de geometrie restent disponibles, l'entrainement non"
        )


def joint_nll(model, x) -> float:
    """Perte jointe du modele en nats par pas (comparable au plancher de Bayes)."""
    _require_torch()
    la, lb, _ = model(x)
    return float(
        nn.functional.cross_entropy(la[:, :-1].reshape(-1, la.shape[-1]), x[:, 1:, 0].reshape(-1)).item()
        + nn.functional.cross_entropy(lb[:, :-1].reshape(-1, lb.shape[-1]), x[:, 1:, 1].reshape(-1)).item()
    )


def train_model(
    model,
    x_train,
    x_val,
    *,
    steps: int = 1500,
    lr: float = 3e-3,
    clip: float = 1.0,
    eval_every: int = 50,
    seed: int = 0,
) -> Dict[str, object]:
    """Entraine ``model`` et retient l'etat de **meilleure validation**.

    L'arret sur la meilleure validation n'est pas un confort : sur ce banc le
    train continue de descendre alors que la validation remonte (le modele
    memorise les sequences), et c'est l'etat de validation qui merite d'etre
    mesure — c'est le seul qui ait appris le *processus* plutot que
    l'echantillon. Le retour porte les deux courbes, pour que le sur-apprentissage
    soit visible et non pas suppose.

    ``seed`` ne fixe que l'ordre des pas ; l'initialisation est celle du modele.
    """
    _require_torch()
    torch.manual_seed(seed)
    opt = torch.optim.Adam(model.parameters(), lr=lr)
    history: list = []
    best = (float("inf"), -1, None)
    for step in range(1, steps + 1):
        model.train()
        la, lb, _ = model(x_train)
        loss = nn.functional.cross_entropy(
            la[:, :-1].reshape(-1, la.shape[-1]), x_train[:, 1:, 0].reshape(-1)
        ) + nn.functional.cross_entropy(
            lb[:, :-1].reshape(-1, lb.shape[-1]), x_train[:, 1:, 1].reshape(-1)
        )
        opt.zero_grad()
        loss.backward()
        nn.utils.clip_grad_norm_(model.parameters(), clip)
        opt.step()
        if step % eval_every == 0 or step == 1:
            model.eval()
            with torch.no_grad():
                val = joint_nll(model, x_val)
            history.append((step, float(loss.item()), val))
            if val < best[0]:
                best = (val, step, {k: v.detach().clone() for k, v in model.state_dict().items()})
    if best[2] is not None:
        model.load_state_dict(best[2])
    return {"best_val_nll": best[0], "best_step": best[1], "history": history}


def collect_activations(model, x) -> Array:
    """Etats caches du modele sur ``x``, aplatis en ``(T, hidden)`` (numpy).

    Le modele est laisse dans son etat courant : l'appelant decide s'il veut
    les activations d'un modele entraine ou d'une initialisation non entrainee.
    """
    _require_torch()
    was_training = model.training
    model.eval()
    with torch.no_grad():
        _, _, out = model(x)
    if was_training:
        model.train()
    return out.reshape(-1, out.shape[-1]).cpu().numpy().astype(np.float64)


# --------------------------------------------------------------------------
# 3. Lecture geometrique, et son temoin
# --------------------------------------------------------------------------


def probe_coefficient_basis(activations: Array, targets: Array, ridge: float = 1e-3) -> Array:
    """Base orthonormee du sous-espace des COEFFICIENTS de la sonde ridge.

    La sonde ajuste ``activations -> targets`` (les beliefs exacts du facteur,
    en held-out) et l'on garde l'espace colonne de sa matrice de coefficients,
    pas l'ajustement lui-meme. C'est une vue differente de celle des directions
    de variance : elle dit quelles directions le modele **utilise pour etre lu**,
    et non dans quelles directions il varie le plus.

    Retour : ``(D, k)`` a colonnes orthonormees, ``k`` = rang numerique.
    """
    H = np.asarray(activations, dtype=np.float64)
    Y = np.asarray(targets, dtype=np.float64)
    if H.ndim != 2 or Y.ndim != 2 or H.shape[0] != Y.shape[0]:
        raise ValueError(
            f"formes incompatibles : activations {H.shape}, cibles {Y.shape} (meme nombre de lignes attendu)"
        )
    Hc = H - H.mean(axis=0, keepdims=True)
    Yc = Y - Y.mean(axis=0, keepdims=True)
    d = Hc.shape[1]
    gram = Hc.T @ Hc + ridge * np.eye(d)
    W = np.linalg.solve(gram, Hc.T @ Yc)  # (D, m)
    u, s, _ = np.linalg.svd(W, full_matrices=False)
    if s.size == 0 or s[0] <= 0.0:
        return np.zeros((d, 0))
    keep = s > (s[0] * 1e-8)
    return u[:, keep]


def subspace_rank(basis: Array, tol: float = 1e-8) -> int:
    """Rang numerique d'un sous-espace donne par une base a colonnes orthonormees."""
    b = np.asarray(basis, dtype=np.float64)
    if b.size == 0:
        return 0
    return int(np.sum(np.linalg.svd(b, compute_uv=False) > tol))


def _span_basis(*bases: Array) -> Array:
    """Base orthonormee de la somme des sous-espaces fournis."""
    parts = [np.asarray(b, dtype=np.float64) for b in bases if np.asarray(b).size]
    if not parts:
        return np.zeros((0, 0))
    stacked = np.concatenate(parts, axis=1)
    u, s, _ = np.linalg.svd(stacked, full_matrices=False)
    if s.size == 0 or s[0] <= 0.0:
        return np.zeros((stacked.shape[0], 0))
    return u[:, s > (s[0] * 1e-8)]


def factor_geometry_report(
    activations: Array,
    belief_a: Array,
    belief_b: Array,
    *,
    ridge: float = 1e-3,
) -> Dict[str, float]:
    """Les trois lectures, **a cote et jamais fusionnees**.

    - ``probe_r2_a`` / ``probe_r2_b`` : decodabilite tenue hors echantillon
      (R^2 de la sonde ridge en validation croisee par moities) ;
    - ``dim_a``, ``dim_b``, ``dim_union`` : dimensions des sous-espaces de
      coefficients, et de leur somme ;
    - ``additivity_gap`` = ``dim_union - (dim_a + dim_b)`` : **0** si les
      facteurs occupent des directions additives, **negatif** s'ils se
      recouvrent — c'est la mesure directe de l'entremellement ;
    - ``overlap_coef_max`` : plus grand |cos| entre les directions de LECTURE
      des deux facteurs ;
    - ``angle_coef_deg`` : plus grand angle principal entre ces sous-espaces.
    """
    H = np.asarray(activations, dtype=np.float64)
    Ba = probe_coefficient_basis(H, belief_a, ridge=ridge)
    Bb = probe_coefficient_basis(H, belief_b, ridge=ridge)
    Bu = _span_basis(Ba, Bb)
    da, db, du = subspace_rank(Ba), subspace_rank(Bb), subspace_rank(Bu)
    if Ba.size and Bb.size:
        ov = float(basis_overlap(Ba, Bb).max())
        ang = max_principal_angle(Ba, Bb)
    else:
        ov, ang = float("nan"), float("nan")
    return {
        "probe_r2_a": probe_holdout_r2(H, belief_a, ridge=ridge),
        "probe_r2_b": probe_holdout_r2(H, belief_b, ridge=ridge),
        "dim_a": float(da),
        "dim_b": float(db),
        "dim_union": float(du),
        "additivity_gap": float(du - (da + db)),
        "overlap_coef_max": ov,
        "angle_coef_deg": ang,
    }


def probe_holdout_r2(activations: Array, targets: Array, ridge: float = 1e-3, folds: int = 2) -> float:
    """R^2 hors echantillon d'une sonde ridge, en validation croisee par blocs.

    Les blocs sont **contigus** et non aleatoires : les observations du banc
    sont temporellement correlees, et un decoupage aleatoire laisserait fuir
    l'information d'un pas vers son voisin.
    """
    H = np.asarray(activations, dtype=np.float64)
    Y = np.asarray(targets, dtype=np.float64)
    n = H.shape[0]
    if n < folds * 4:
        return float("nan")
    bounds = np.linspace(0, n, folds + 1).astype(int)
    ss_res, ss_tot, y_all = 0.0, 0.0, Y.mean(axis=0, keepdims=True)
    for i in range(folds):
        te = slice(bounds[i], bounds[i + 1])
        tr = np.r_[np.arange(0, bounds[i]), np.arange(bounds[i + 1], n)]
        Htr, Ytr = H[tr], Y[tr]
        mu = Htr.mean(axis=0, keepdims=True)
        d = Htr.shape[1]
        W = np.linalg.solve((Htr - mu).T @ (Htr - mu) + ridge * np.eye(d), (Htr - mu).T @ (Ytr - Ytr.mean(0)))
        pred = (H[te] - mu) @ W + Ytr.mean(0)
        ss_res += float(((Y[te] - pred) ** 2).sum())
        ss_tot += float(((Y[te] - y_all) ** 2).sum())
    return float(1.0 - ss_res / ss_tot) if ss_tot > 0 else float("nan")


def untrained_null(
    build_model: Callable[[int], object],
    x,
    belief_a: Array,
    belief_b: Array,
    *,
    n_init: int = 6,
    ridge: float = 1e-3,
    seed0: int = 0,
) -> Dict[str, Dict[str, float]]:
    """Temoin nul par initialisations **non entrainees** de la meme architecture.

    C'est l'objection que le nul de sous-espaces aleatoires ne traite pas :
    « un modele non entraine a peut-etre deja des sous-espaces separes ».
    On repond en mesurant, sur ``n_init >= 5`` initialisations seedees, la meme
    lecture geometrique que sur le modele entraine — puis en rapportant les
    percentiles 5 / 50 / 95 de chaque metrique.

    Le verdict geometrique du modele entraine ne vaut que s'il sort de cette
    bande : sinon l'architecture seule suffisait, et la mesure ne dit rien de
    ce qui a ete appris.
    """
    if n_init < 5:
        raise ValueError(f"le temoin exige au moins 5 initialisations, recu {n_init}")
    per_metric: Dict[str, list] = {}
    for i in range(n_init):
        model = build_model(seed0 + i)
        acts = collect_activations(model, x)
        rep = factor_geometry_report(acts, belief_a, belief_b, ridge=ridge)
        for k, v in rep.items():
            per_metric.setdefault(k, []).append(v)
    out: Dict[str, Dict[str, float]] = {}
    for k, vals in per_metric.items():
        arr = np.asarray([v for v in vals if np.isfinite(v)], dtype=np.float64)
        if arr.size == 0:
            out[k] = {"p05": float("nan"), "p50": float("nan"), "p95": float("nan"), "n": 0.0}
            continue
        out[k] = {
            "p05": float(np.percentile(arr, 5)),
            "p50": float(np.percentile(arr, 50)),
            "p95": float(np.percentile(arr, 95)),
            "n": float(arr.size),
        }
    return out
