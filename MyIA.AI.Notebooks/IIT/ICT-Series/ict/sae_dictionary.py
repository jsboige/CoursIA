"""Entrainement CPU d'un dictionnaire sparse (SAE top-k) pour le pilote causal #15480.

Composante **SAE** du pilote de triangulation SAE-J-Lens-F-Lens : l'issue
#15480 demande un « dictionnaire sparse adapte au petit modele », avec
sparsite, FVU et selectivite aux facteurs. Les deux modules SAE existants de
la serie sont des **consommateurs** de SAE pre-entraines (:mod:`ict.sae_traces`
recharge les traces du SAE officiel Qwen-Scope, :mod:`ict.sae_calibration` en
mesure la fidelite) ; aucun n'entraine. Ce module apporte l'entrainement
lui-meme, en restant dans la discipline d'architecture de la serie :
numpy uniquement, le GPU reste confine aux extractions.

* :class:`TopKSae` -- sparse autoencoder ``topk(relu(x @ W_enc.T + b_enc), k)``
  (meme convention d'encodage que la demo Qwen-Scope documentee dans
  :mod:`ict.sae_calibration`), decodeur a colonnes unit-norm, entraine par
  descente de gradient explicite (sous-gradients relu/top-k masques).
* :func:`train_sae` -- API fonctionnelle : entraine et retourne le SAE avec
  FVU/L0 finaux reutilises de :mod:`ict.sae_calibration` (aucune metrique
  dupliquee ici).
* :func:`factor_auc` -- AUC de Mann-Whitney par feature contre un label binaire
  de facteur (rangs moyens, ties inclus : une feature morte rend 0.5).
* :func:`factor_selectivity` -- z-score de selectivite par feature contre des
  relabelisations aleatoires appariees en effectifs, meme discipline de null
  apparie que :func:`ict.lens_gates.separation_zscore` : une feature ne compte
  comme dediee au facteur que si son AUC ecrase ce que le hasard du
  relabelisation produit.

Le design est volontairement orthogonal au banc factorise : l'entree est une
matrice d'activations ``[n, d]`` quelconque -- elle sera branchee sur les
activations du petit transformer hookable (en aval de la pile #15479) sans
changement d'interface.

Limite mesuree (a connaitre avant de demander l'impossible au module) : sur
un corpus k=3 exactement reconstructible par 24 directions dans d=12
(sur-complet x2), l'entrainement full-batch avec moment recouvre ~90 % de la
variance (FVU 0.09-0.14 inter-seeds) et retrouve ~17/24 atomes a un
alignement > 0.95 ; le residu est un **plateau de melange** (les atomes
restants captent des combinaisons de directions vraies), connu des top-k SAE
sans perte auxiliaire de resurrection. Le pilote #15480 consomme la
selectivite aux facteurs, qui ne depend pas de la perfection de la
reconstruction : les features de bloc pur sont les mieux apprises.
"""

from __future__ import annotations

import numpy as np

from ict.sae_calibration import fraction_variance_unexplained, l0_measured

__all__ = [
    "TopKSae",
    "train_sae",
    "factor_auc",
    "factor_selectivity",
]


# --------------------------------------------------------------------------- #
# SAE top-k
# --------------------------------------------------------------------------- #
class TopKSae:
    """Sparse autoencoder top-k, decodeur a colonnes unit-norm.

    Encodage : ``a = relu(x @ W_enc.T + b_enc)`` puis seul le top-k des
    activations par echantillon survit (les autres valent exactement zero,
    comme dans un SAE top-k officiel ou toute activation hors top-k est nulle
    par construction). Decodage : ``x_hat = z @ W_dec.T + b_dec`` avec
    ``b_dec`` initialise a la moyenne du corpus au premier appel de
    :meth:`train`.
    """

    def __init__(self, n_input: int, n_features: int, k: int, seed: int = 0):
        if not 1 <= k <= n_features:
            raise ValueError(f"k={k} hors bornes [1, n_features={n_features}]")
        rng = np.random.default_rng(seed)
        w_dec = rng.normal(size=(n_input, n_features))
        w_dec /= np.linalg.norm(w_dec, axis=0, keepdims=True)
        self.W_dec = w_dec
        # Init lie : l'encodeur part transposé du decodeur (precedent standard
        # des SAE a l'initialisation, accelere la convergence du dictionnaire).
        self.W_enc = w_dec.T.copy()
        self.b_enc = np.zeros(n_features)
        self.b_dec: np.ndarray | None = None
        self.k = k
        self.seed = seed

    # -- passe avant ------------------------------------------------------- #
    def precode(self, x: np.ndarray) -> np.ndarray:
        """Pre-activations ``x @ W_enc.T + b_enc`` (relu non appliquee)."""
        return x @ self.W_enc.T + self.b_enc

    def encode(self, x: np.ndarray) -> np.ndarray:
        """Codes sparse : au plus ``k`` valeurs strictement positives par ligne."""
        a = np.maximum(self.precode(x), 0.0)
        if self.k >= a.shape[1]:
            return a
        # relu d'abord, puis top-k des activations non nulles : si moins de k
        # pre-activations sont positives, des zeros sont retenus et L0 < k
        # (cohérent avec la doc de l0_measured : L0 mesure <= k).
        idx = np.argpartition(a, a.shape[1] - self.k, axis=1)[:, -self.k :]
        keep = np.zeros_like(a)
        np.put_along_axis(keep, idx, 1.0, axis=1)
        return a * keep

    def decode(self, z: np.ndarray) -> np.ndarray:
        if self.b_dec is None:
            raise ValueError("b_dec non initialise : appeler train() d'abord")
        return z @ self.W_dec.T + self.b_dec

    # -- entrainement ------------------------------------------------------ #
    def train(
        self,
        x: np.ndarray,
        n_steps: int = 400,
        lr: float = 0.05,
        warmup_steps: int = 40,
        momentum: float = 0.9,
    ) -> dict:
        """Descente de gradient explicite full-batch avec moment sur l'erreur de reconstruction.

        Le sous-gradient traverse le top-k par un masque : seules les
        activations retenues (strictement positives) propagent. Apres chaque
        pas, les colonnes du decodeur sont re-normalisees a la norme unite
        (standard des SAE : le dictionnaire reste sur la sphere, la norme est
        portee par les codes). Le moment (default 0.9) compense l'absence
        d'Adam : la descente full-batch numpy converge sinon trop lentement
        sur les dictionnaires sur-complets (mesure de calibration : FVU
        divise par ~2 sur les corpus durs a steps egaux).
        """
        if self.b_dec is None:
            self.b_dec = x.mean(axis=0).copy()
        n = x.shape[0]
        if warmup_steps >= n_steps:
            raise ValueError("warmup_steps doit rester < n_steps")
        vel = {
            "w_dec": np.zeros_like(self.W_dec),
            "b_dec": np.zeros_like(self.b_dec),
            "w_enc": np.zeros_like(self.W_enc),
            "b_enc": np.zeros_like(self.b_enc),
        }
        history: list[float] = []
        for step in range(n_steps):
            a = self.precode(x)
            z = self.encode_from_pre(a)
            recon = z @ self.W_dec.T + self.b_dec
            err = recon - x
            # decroissance du pas (lineaire apres warmup) : stabilise la
            # convergence full-batch.
            progress = (step - warmup_steps) / (n_steps - warmup_steps)
            step_size = lr if step < warmup_steps else lr * (1.0 - progress)
            history.append(float(np.mean(err**2)))
            d_w_dec = (2.0 / n) * err.T @ z
            d_b_dec = (2.0 / n) * err.sum(axis=0)
            mask = z > 0
            d_a = ((2.0 / n) * err @ self.W_dec) * mask
            d_w_enc = d_a.T @ x
            d_b_enc = d_a.sum(axis=0)
            vel["w_dec"] = momentum * vel["w_dec"] + d_w_dec
            vel["b_dec"] = momentum * vel["b_dec"] + d_b_dec
            vel["w_enc"] = momentum * vel["w_enc"] + d_w_enc
            vel["b_enc"] = momentum * vel["b_enc"] + d_b_enc
            self.W_dec -= step_size * vel["w_dec"]
            self.b_dec -= step_size * vel["b_dec"]
            self.W_enc -= step_size * vel["w_enc"]
            self.b_enc -= step_size * vel["b_enc"]
            self.W_dec /= np.linalg.norm(self.W_dec, axis=0, keepdims=True)
        return {"mse_final": history[-1], "mse_history": history}

    def encode_from_pre(self, a: np.ndarray) -> np.ndarray:
        """Top-k relu depuis des pre-activations deja calculees."""
        r = np.maximum(a, 0.0)
        if self.k >= r.shape[1]:
            return r
        idx = np.argpartition(r, r.shape[1] - self.k, axis=1)[:, -self.k :]
        keep = np.zeros_like(r)
        np.put_along_axis(keep, idx, 1.0, axis=1)
        return r * keep


def train_sae(
    x: np.ndarray,
    n_features: int,
    k: int,
    seed: int = 0,
    n_steps: int = 400,
    lr: float = 0.05,
    momentum: float = 0.9,
) -> dict:
    """Entraine un :class:`TopKSae` et retourne SAE + metriques de calibration.

    Les metriques viennent de :mod:`ict.sae_calibration` (FVU, L0 mesure) --
    ce module n'en redefinit aucune.
    """
    sae = TopKSae(x.shape[1], n_features, k=k, seed=seed)
    info = sae.train(x, n_steps=n_steps, lr=lr, momentum=momentum)
    z = sae.encode(x)
    recon = sae.decode(z)
    return {
        "sae": sae,
        "codes": z,
        "reconstruction": recon,
        "fvu": fraction_variance_unexplained(x, recon),
        "l0": l0_measured(z),
        "mse_final": info["mse_final"],
    }


# --------------------------------------------------------------------------- #
# Selectivite aux facteurs
# --------------------------------------------------------------------------- #
def _rank_mean_axis0(a: np.ndarray) -> np.ndarray:
    """Rangs moyens (1..n, ties au rang moyen) le long de l'axe 0, numpy pur."""
    n = a.shape[0]
    order = np.argsort(a, axis=0, kind="stable")
    ranks = np.empty_like(a, dtype=float)
    cols = np.arange(a.shape[1])[None, :]
    # rang ordinal d'abord (les ties recevront des ordinaux consecutifs).
    # order[i, j] = ligne du i-eme plus petit de la colonne j : c'est l'axe 0
    # qui recoit order, l'axe 1 qui recoit la colonne j.
    ranks[order, cols] = np.broadcast_to(np.arange(1, n + 1)[:, None], a.shape)
    # moyennage des ties : pour chaque colonne, grouper par valeur
    out = np.empty_like(ranks)
    for j in range(a.shape[1]):
        col = a[:, j]
        sorted_col = np.sort(col)
        # bornes des groupes de valeurs egales
        uniq, starts = np.unique(sorted_col, return_index=True)
        ends = np.append(starts[1:], n)
        # rang moyen d'une valeur = moyenne des ordinaux du groupe
        mean_rank = {
            v: (s + 1 + e) / 2.0 for v, s, e in zip(uniq, starts, ends, strict=True)
        }
        out[:, j] = np.array([mean_rank[v] for v in col])
    return out


def factor_auc(acts: np.ndarray, labels: np.ndarray) -> np.ndarray:
    """AUC de Mann-Whitney par feature : P(act_pos > act_neg) + 0.5 P(=).

    ``acts`` : ``[n, r]`` activations (sparse OK) ; ``labels`` : ``[n]`` booleen
    (facteur present / absent, les co-occurrences de facteurs restent dans
    leurs labels respectifs). Une feature jamais active rend exactement 0.5.
    """
    labels = np.asarray(labels, dtype=bool)
    n_pos = int(labels.sum())
    n_neg = int((~labels).sum())
    if n_pos == 0 or n_neg == 0:
        raise ValueError("factor_auc exige deux classes non vides")
    ranks = _rank_mean_axis0(np.asarray(acts, dtype=float))
    sum_pos = ranks[labels].sum(axis=0)
    return (sum_pos - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg)


def factor_selectivity(
    acts: np.ndarray,
    labels: np.ndarray,
    n_null: int = 200,
    seed: int = 0,
) -> dict:
    """z-score de selectivite de chaque feature contre un null apparie.

    Null : ``n_null`` relabelisations aleatoires **appariees en effectifs**
    (permutations du meme vecteur de labels -- chaque tirage a exactement
    autant de positifs que l'observe). Les rangs des activations ne dependent
    pas du label, ils sont calcules une fois puis re-agreges par tirage.
    Discipline identique a :func:`ict.lens_gates.separation_zscore` : ce que
    le hasard du relabelisation produit fixe le zero de l'echelle.
    """
    labels = np.asarray(labels, dtype=bool)
    n_pos = int(labels.sum())
    n = labels.shape[0]
    ranks = _rank_mean_axis0(np.asarray(acts, dtype=float))
    auc_obs = factor_auc(acts, labels)

    rng = np.random.default_rng(seed)
    aucs_null = np.empty((n_null, acts.shape[1]))
    base = np.zeros(n, dtype=bool)
    base[:n_pos] = True
    for t in range(n_null):
        perm = rng.permutation(n)
        lab = base[perm]
        sum_pos = ranks[lab].sum(axis=0)
        np1 = n_pos
        aucs_null[t] = (sum_pos - np1 * (np1 + 1) / 2.0) / (n_pos * (n - n_pos))

    mu = aucs_null.mean(axis=0)
    sd = aucs_null.std(axis=0)
    # garde isfinite explicite : une feature a variance nulle d'AUC sous null
    # (ex. jamais active -> AUC constante 0.5) doit rendre z = 0, pas NaN
    # (lecon de lens_gates : nan passe sous un garde de comparaison).
    with np.errstate(divide="ignore", invalid="ignore"):
        z = np.where(np.isfinite(sd) & (sd > 0), (auc_obs - mu) / np.where(sd > 0, sd, 1.0), 0.0)
    return {
        "auc": auc_obs,
        "z": z,
        "auc_null_mean": mu,
        "auc_null_std": sd,
        "n_null": n_null,
    }
