"""L'inférence active et l'expected free energy pilote l'action (strate 4, ICT-14b).

ICT-14 a établi la jambe énergie-libre *rétrospective* : la surprise
``S_t`` de l'observation sous le modèle génératif (cas gaussien fermé),
``F = accuracy + complexity``. Verdict honnête : à précision fixe, ``F``
n'est qu'un habillage du MSE. La strate 4 restait une strate-formule :
la free energy « n'était pas tracée » comme mécanisme *prospectif* de
sélection d'action.

Ce module épaissit la strate 4 en un **strat-banc** : l'**expected free
energy (EFE)** — la free energy *attendue* d'une politique — pilote
l'action, et l'on mesure si sa composante épistémique change le
comportement de l'agent. C'est la généralisation prospection → action du
représentant interne ``p_hat`` : non plus prédire passivement, mais
**choisir la prochaine observation** pour minimiser la surprise attendue.

Décomposition de l'EFE (Friston da Costa 2023 ; réduction bandelette)
---------------------------------------------------------------------
Pour une action (bras) ``k`` et une croyance ``q(theta_k)`` sur le
paramètre de récompense, l'EFE ``G(k)`` se décompose en deux termes **tous
deux en nats** (même unité — condition sine qua non pour que le point
``lam = 1`` soit un équilibre interprétable, cf. erreur-tyque corrigée :
normaliser arbitrairement l'un des termes détruit la balance et fait
dégénérer l'agent en politique gloutonne) :

* **Terme épistémique** (valeur d'information, saillance) : le gain
  d'information **attendu** sur le paramètre,
  ``E_o[ KL(q(theta_k | o) || q(theta_k)) ]`` (la *Bayesian surprise*
  espérée). L'agent cherche les observations qui réduiraient le plus son
  incertitude. C'est le moteur de l'exploration.
* **Terme pragmatique** (valence, utilité attendue) : la log-vraisemblance
  attendue de l'issue sous une **préférence** ``C`` (catégorielle sur les
  issues, ``P(o=1)=c``),
  ``E_q[ ln P(o | C) ] = p_k ln c + (1-p_k) ln(1-c)``. Maximiser ce terme
  seul = politique *gloutonne* (le ``pi`` reward-driven pur d'ICT-12c).
  La **sharpness** de la préférence ``c`` contrôle le couple
  exploration/exploitation : préférence faible (``c`` proche de 0.5) =>
  le terme épistémique peut dominer et l'agent explore ; préférence
  tranchée (``c`` proche de 1) => exploitation pure. C'est un résultat
  *fidèle à la théorie* (un agent AIF sous préférence incertaine explore
  plus), et le levier falsifiable du banc.

L'agent maximise la valeur ``value(k) = lam * epistemic(k) + pragmatic(k)``
(``lam`` = poids sur l'épistémique ; équivalent à minimiser
``G = -value``).

Non-stationnarité et oubli (modeling AIF standard)
--------------------------------------------------
En régime non-stationnaire, un agent AIF **n'assume pas** un paramètre
stationnaire : il applique un **oubli géométrique** sur ses pseudo-comptes
(facteur ``forget < 1``), de sorte que la croyance sur un bras moins
échantillonné décline et redevient ré-évaluable. Sans oubli, une croyance
sur-confiancée (200 tirages accumulés) fige l'agent sur l'ancien optimum :
aucune politique (même A) ne récupère. L'oubli est la **condition
expérimentale** qui rend la prédiction A > B testable.

Les trois agents du banc (notebook ICT-14b)
-------------------------------------------
* **Agent A — inférence active** : ``lam = 1`` (epistémique + pragmatique).
* **Agent B — reward-driven** (le ``pi`` d'ICT-12c) : politique gloutonne
  sur la moyenne a posteriori, soit ``lam = 0``.
* **Agent C — null adverse** : EFE à terme épistémique **ablaté**,
  ``lam = 0`` ; par construction ≡ B. Si A ≡ C, l'« inférence active » du
  banc est décorative — c'est le contrôle qui crédite (ou non) le mécanisme.

Prédiction pré-enregistrée
--------------------------
* **Régime non-stationnaire** (changement de bras optimal à ``T/2``,
  oubli actif) : A > B en récupération du bras optimal (l'exploration
  épistémique ré-échantillonne ce que B fige). La dissociation
  s'enregistre dans la matrice 4-objets (#7734) : ``pi`` (valence) vs
  ``q`` (représentation prédictive).
* **Régime stationnaire** : A ≈ B — frontière de validité attendue.

Discipline « sans complaisance » : verdicts **par régime, jamais
agrégés**, multi-seed >= 4, null adverse exécuté. Numpy CPU pur, gel GPU
respecté — comme tout le package léger ``ict``.
"""

from __future__ import annotations

from typing import Dict, Optional, Tuple

import numpy as np

# --------------------------------------------------------------------------- #
#  Grille de représentation de la croyance sur theta in (0, 1)                 #
# --------------------------------------------------------------------------- #
# Les modules voisins (free_energy) restent numpy-only ; on évite scipy. La
# croyance Beta(α, β) est représentée par sa densité discrétisée sur une grille
# fine de [eps, 1-eps]. Toutes les quantités (moyenne, entropie, KL, gain
# d'information espéré) se calculent par sommes discrètes — transparent et
# reproductible, et homogène au reste du package.
_GRID_N = 200
_GRID_EPS = 1e-3
_THETA_GRID = np.linspace(_GRID_EPS, 1.0 - _GRID_EPS, _GRID_N)
_DTHETA = _THETA_GRID[1] - _THETA_GRID[0]

# Préférence par défaut sur l'issue de récompense (c < 1 : non-tranchée, pour
# que le terme épistémique puisse dominer — cf. docstring). Le notebook balaie
# c pour montrer le couple exploration/exploitation.
DEFAULT_C = 0.6
# Oubli géométrique par défaut en régime non-stationnaire (effective sample
# size ~ 1/(1-forget)). Choisi à 0.99 (ESS ~ 100) d'après le balayage empirique
# du notebook : c'est le régime où la croyance stale du greedy se fige sur
# l'ancien optimum (B s'effondre) tandis que l'exploration épistémique dirigée
# de A ré-échantillonne le nouveau bras optimal. À forget trop rapide (0.97),
# l'oubli seul suffit à récupérer et le terme épistémique devient redondant —
# c'est la frontière honnête documentée dans le banc. Stationnaire => 1.0.
DEFAULT_FORGET = 0.99


def _beta_pdf_grid(alpha: np.ndarray, beta: np.ndarray) -> np.ndarray:
    """Densité Beta(α, β) discrétisée sur la grille, normalisée.

    Renvoie un tableau (K, _GRID_N) de lois par bras. On travaille en espace
    log pour la stabilité (Beta(α,β) ~ θ^(α-1) (1-θ)^(β-1) sans besoin de la
    constante de normalisation : on renormalise après exponentiation).
    """
    a = np.asarray(alpha, dtype=float)
    b = np.asarray(beta, dtype=float)
    # (K,1) broadcast vs (GRID_N,)
    log_pdf = (a[:, None] - 1.0) * np.log(_THETA_GRID)[None, :]
    log_pdf += (b[:, None] - 1.0) * np.log(1.0 - _THETA_GRID)[None, :]
    pdf = np.exp(log_pdf - log_pdf.max(axis=1, keepdims=True))
    pdf *= _DTHETA
    pdf /= pdf.sum(axis=1, keepdims=True)
    return pdf


# --------------------------------------------------------------------------- #
#  Environnement : bandit de Bernoulli non-stationnaire (régime erratique)     #
# --------------------------------------------------------------------------- #
class NonStationaryBandit:
    """Bandit de Bernoulli à K bras avec changement de régime à ``switch_t``.

    Le « régime erratique » d'ICT-12c est ici abstracté comme un
    **changement de bras optimal** à mi-horizon : la structure de
    récompense vraie bascule, détruisant tout ``p_hat`` figé sur l'ancien
    optimum. Variante ``stationary=True`` (pas de bascule) pour la
    frontière de validité attendue A ≈ B.

    Les récompenses sont pré-générées en table ``[T, K]`` par seed : les
    trois agents consomment **la même** séquence (common random numbers),
    de sorte que la seule différence inter-agents est la politique. C'est
    ce qui rend la dissociation A vs {B, C} nette et reproductible.
    """

    def __init__(
        self,
        n_arms: int = 3,
        horizon: int = 400,
        switch_t: Optional[int] = None,
        stationary: bool = False,
        probs_pre: Optional[Tuple[float, ...]] = None,
        probs_post: Optional[Tuple[float, ...]] = None,
        seed: int = 0,
    ) -> None:
        self.n_arms = n_arms
        self.horizon = horizon
        self.stationary = stationary
        # Bras optimal avant / après la bascule. Par défaut : le bras 0 est
        # optimal en première moitié, le dernier bras en seconde. Les probas
        # sont choisies pour que la bascule soit nette (0.8 vs 0.2) mais pas
        # triviale (bruit Bernoulli). En stationnaire, probs_post = probs_pre.
        if probs_pre is None:
            base = np.linspace(0.20, 0.80, n_arms)[::-1]  # bras 0 = meilleur
            probs_pre = tuple(float(p) for p in base)
        if probs_post is None:
            if stationary:
                probs_post = probs_pre
            else:
                # Inversion : le dernier bras devient le meilleur.
                probs_post = tuple(float(p) for p in probs_pre[::-1])
        self.probs_pre = np.array(probs_pre)
        self.probs_post = np.array(probs_post)
        self.switch_t = horizon // 2 if switch_t is None else switch_t
        self.seed = seed
        rng = np.random.default_rng(seed)
        # Table de récompenses [T, K] : Uniforme < proba vraie à l'instant t.
        probs_t = np.where(
            np.arange(horizon)[:, None] < self.switch_t,
            self.probs_pre[None, :],
            self.probs_post[None, :],
        )
        self._reward_table = (rng.random((horizon, n_arms)) < probs_t).astype(float)
        # Probabilité vraie par instant (pour le regret et le bras optimal).
        self._probs_t = probs_t

    # -- API d'exécution -------------------------------------------------- #
    def true_best_arm(self, t: int) -> int:
        """Indice du bras de probabilité vraie maximale à l'instant t."""
        return int(np.argmax(self._probs_t[t]))

    def reward(self, t: int, arm: int) -> float:
        """Récompense de l'agent ayant choisi ``arm`` à l'instant ``t``.

        Lit dans la table pré-générée (common random numbers).
        """
        return float(self._reward_table[t, arm])

    def optimal_reward_rate(self, t: int) -> float:
        """Taux de récompense du bras optimal à t (pour le regret)."""
        return float(self._probs_t[t].max())


# --------------------------------------------------------------------------- #
#  Croyance a posteriori Beta par bras (modèle génératif partagé)              #
# --------------------------------------------------------------------------- #
class BetaBelief:
    """Croyance Beta(α_k, β_k) par bras, sur la grille, avec oubli géométrique.

    Modèle génératif partagé par les trois agents : seul le *choix* d'action
    diffère (cf. :func:`choose`). La mise à jour Bayésienne est exacte
    (α += r, β += 1 - r), la densité est représentée discrètement. Le
    facteur ``forget < 1`` (non-stationnaire) applique un oubli géométrique
    des pseudo-comptes à chaque mise à jour : un bras moins échantillonné
    voit sa croyance revenir vers le prior, condition de la récupération.
    """

    def __init__(
        self,
        n_arms: int,
        prior_alpha: float = 1.0,
        prior_beta: float = 1.0,
        forget: float = 1.0,
    ) -> None:
        self.n_arms = n_arms
        self.alpha = np.full(n_arms, float(prior_alpha))
        self.beta = np.full(n_arms, float(prior_beta))
        self.forget = float(forget)
        self._pdf = _beta_pdf_grid(self.alpha, self.beta)

    @property
    def pdf(self) -> np.ndarray:
        return self._pdf

    def mean(self) -> np.ndarray:
        """Moyenne a posteriori par bras = E_q[theta_k] (récompense attendue)."""
        return (self._pdf * _THETA_GRID[None, :]).sum(axis=1)

    def update(self, arm: int, reward: float) -> None:
        """Mise à jour Bayésienne après observation (r in {0, 1}), avec oubli."""
        self.alpha *= self.forget
        self.beta *= self.forget
        if reward >= 0.5:
            self.alpha[arm] += 1.0
        else:
            self.beta[arm] += 1.0
        self._pdf = _beta_pdf_grid(self.alpha, self.beta)


# --------------------------------------------------------------------------- #
#  Les deux termes de l'EFE (tous deux en nats)                                #
# --------------------------------------------------------------------------- #
def expected_reward(belief: BetaBelief) -> np.ndarray:
    """Récompense attendue intuitive = moyenne a posteriori (en [0, 1])."""
    return belief.mean()


def pragmatic_value(belief: BetaBelief, c: float = DEFAULT_C) -> np.ndarray:
    """Terme pragmatique (nats) : log-vraisemblance attendue sous préférence C.

    ``E_q[ln P(o|C)] = p_k ln c + (1 - p_k) ln(1 - c)`` avec ``P(o=1)=c``.
    Strictement croissante en ``p_k`` pour ``c > 0.5`` => argmax =
    politique gloutonne (le ``pi`` d'ICT-12c). La **sharpness** ``c``
    contrôle le poids de l'exploitation.
    """
    p = belief.mean()
    return p * np.log(c) + (1.0 - p) * np.log(1.0 - c)


def epistemic_value(belief: BetaBelief) -> np.ndarray:
    """Terme épistémique (nats) : gain d'information attendu (Bayesian surprise).

    ``E_o[ KL(q(theta_k | o) || q(theta_k)) ]`` pour ``o in {0, 1}``,
    pondéré par la probabilité prédictive de chaque issue. Calculé sur la
    grille : pour o=1, ``q(theta|1) ~ theta * q(theta)`` ; pour o=0,
    ``q(theta|0) ~ (1-theta) * q(theta)`` ; renormalisés.

    Grand pour un bras incertain (posterior large), ~0 pour un bras déjà
    bien estimé (posterior piqué) : c'est le moteur d'exploration.
    """
    q = belief.pdf  # (K, GRID_N)
    theta = _THETA_GRID[None, :]  # (1, GRID_N)
    # q(theta | o=1) et q(theta | o=0), renormalisés
    q1 = theta * q
    q0 = (1.0 - theta) * q
    q1 /= q1.sum(axis=1, keepdims=True) + 1e-300
    q0 /= q0.sum(axis=1, keepdims=True) + 1e-300
    # KL(q(.|o) || q(.)) — on masque les zéros pour log numériquement stable
    def _kl(pa, pb):
        mask = pa > 1e-300
        out = np.zeros_like(pa)
        out[mask] = pa[mask] * (np.log(pa[mask]) - np.log(pb[mask]))
        return out.sum(axis=1)

    kl1 = _kl(q1, q)
    kl0 = _kl(q0, q)
    # Probabilité prédictive de o=1 = moyenne a posteriori
    p_o1 = belief.mean()
    return p_o1 * kl1 + (1.0 - p_o1) * kl0


def choose(
    belief: BetaBelief,
    lam: float,
    rng: np.random.Generator,
    c: float = DEFAULT_C,
) -> int:
    """Choisit le bras maximisant ``lam * epistemic + pragmatic`` (en nats).

    ``lam`` est le **poids sur le terme épistémique** (moteur d'exploration
    informationnelle). ``lam = 0`` <=> politique gloutonne pure (le ``pi``
    reward-driven d'ICT-12c) ; ``lam = 1`` <=> inférence active complète.

    Les deux termes sont en nats : ``lam = 1`` est le point d'équilibre
    interprétable (cf. docstring module — ne pas normaliser arbitrairement).
    Égalité numérique -> on brise par un bruit minuscule déterministe.
    """
    epi = epistemic_value(belief)
    pra = pragmatic_value(belief, c)
    value = lam * epi + pra
    # Brise d'égalité déterministe (n'affecte pas les comparisons nettes).
    value = value + 1e-12 * rng.random(belief.n_arms)
    return int(np.argmax(value))


# --------------------------------------------------------------------------- #
#  Exécution d'un épisode : trace F, termes EFE, actions, croyance             #
# --------------------------------------------------------------------------- #
def free_energy_step(belief: BetaBelief, arm: int, reward: float) -> float:
    """Surprise rétrospective de l'issue observée (jambe F d'ICT-14).

    ``F_t = -ln q(o_t | arm)`` où la prédictive est Bernoulli de paramètre
    la moyenne a posteriori du bras choisi. C'est l'homologue discret de la
    ``gaussian_surprise`` du module :free_energy: — ici dans le cadre
    Bernoulli naturel d'un bandit. Sert à tracer F au cours de l'épisode.
    """
    p1 = float(belief.mean()[arm])
    p1 = min(max(p1, 1e-6), 1.0 - 1e-6)
    prob_obs = p1 if reward >= 0.5 else (1.0 - p1)
    return float(-np.log(prob_obs))


def run_episode(
    env: NonStationaryBandit,
    lam: float,
    c: float = DEFAULT_C,
    forget: float = DEFAULT_FORGET,
    warmup: bool = True,
    prior_alpha: float = 1.0,
    prior_beta: float = 1.0,
) -> Dict[str, np.ndarray]:
    """Exécute un épisode ; renvoie les traces du banc.

    ``lam`` est le poids sur le terme épistémique (cf. :func:`choose`) ;
    ``lam=1`` = agent A (inférence active), ``lam=0`` = agents B/C (greedy).
    ``forget`` est l'oubli géométrique des pseudo-comptes (non-stationnaire).
    ``warmup`` (défaut True) tire chaque bras une fois en round-robin sur les
    K premiers pas — **commun aux trois agents**, il empêche le lock-in initial
    du greedy pour que la comparaison isole l'effet du terme épistémique sur la
    *récupération* post-bascule plutôt que sur la chance d'échantillonnage
    initial.

    Returns
    -------
    dict avec : ``actions``, ``rewards``, ``F`` (surprise/FE rétrospective
    pas-à-pas), ``epi_trace``/``pra_trace`` (termes EFE en nats du bras
    choisi à chaque pas), ``mean_belief`` (récompense attendue par bras),
    ``optimal_arm`` (bras vrai optimal par t), ``regret`` (récompense
    optimale - obtenue, pas-à-pas).
    """
    rng = np.random.default_rng(env.seed * 1000 + 7)
    belief = BetaBelief(env.n_arms, prior_alpha, prior_beta, forget=forget)
    T = env.horizon
    actions = np.empty(T, dtype=int)
    rewards = np.empty(T, dtype=float)
    F = np.empty(T, dtype=float)
    epi_trace = np.empty(T, dtype=float)
    pra_trace = np.empty(T, dtype=float)
    mean_belief = np.empty((T, env.n_arms), dtype=float)
    optimal_arm = np.empty(T, dtype=int)
    regret = np.empty(T, dtype=float)

    epi_full = epistemic_value(belief)
    pra_full = pragmatic_value(belief, c)

    for t in range(T):
        if warmup and t < env.n_arms:
            arm = t  # round-robin, commun aux trois agents (anti lock-in initial)
        else:
            arm = choose(belief, lam, rng, c=c)
        r = env.reward(t, arm)
        # Termes EFE du bras choisi, enregistrés AVANT la mise à jour.
        epi_trace[t] = epi_full[arm]
        pra_trace[t] = pra_full[arm]
        F[t] = free_energy_step(belief, arm, r)
        actions[t] = arm
        rewards[t] = r
        mean_belief[t] = belief.mean()
        optimal_arm[t] = env.true_best_arm(t)
        regret[t] = env.optimal_reward_rate(t) - env._probs_t[t, arm]
        belief.update(arm, r)
        epi_full = epistemic_value(belief)
        pra_full = pragmatic_value(belief, c)

    return {
        "actions": actions,
        "rewards": rewards,
        "F": F,
        "epi_trace": epi_trace,
        "pra_trace": pra_trace,
        "mean_belief": mean_belief,
        "optimal_arm": optimal_arm,
        "regret": regret,
        "switch_t": env.switch_t,
    }


def recovery_rate(actions: np.ndarray, env: NonStationaryBandit, window: Optional[int] = None) -> float:
    """Taux de tirage du bras optimal **après** la bascule de régime.

    Mesure de « récupération de p_hat » : fraction des pas post-``switch_t``
    où l'agent tire le (nouveau) bras optimal. L'agent figé sur l'ancien
    optimum (B) reste bas ; l'agent explorateur (A) ré-échantillonne et
    remonte. ``window`` limite la fenêtre post-bascule évaluée.
    """
    T = env.horizon
    s = env.switch_t
    if window is not None:
        end = min(T, s + window)
    else:
        end = T
    if end <= s:
        return float("nan")
    post = actions[s:end]
    opt = env.true_best_arm  # t-dependent
    correct = sum(
        1 for i, t in enumerate(range(s, end)) if post[i] == opt(t)
    )
    return correct / max(1, (end - s))


def cumulative_regret(trace: Dict[str, np.ndarray]) -> float:
    """Regret cumulé sur l'épisode (somme des regrets instantanés)."""
    return float(trace["regret"].sum())
