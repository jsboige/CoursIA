"""Animat inhibé (Laborit) — contrôlabilité de l'environnement, inhibition de l'action (#7741).

Contexte
--------
Henri Laborit (*L'Éloge de la fuite*) : des rats soumis à des chocs développent
une hypertension durable surtout quand **ni fuite ni action défensive** ne sont
possibles. C'est l'**inhibition de l'action** : « le système apprend que ses
actions ne contrôlent plus son environnement ». L'analogue formel est un animat
dont les actions, à mesure que la contrôlabilité s'effondre, deviennent
**sans effet** sur la transition d'état — et qui, le détectant, **rigidifie** sa
politique (répétition stérile, effondrement exploratoire).

Ce module instancie ce maillon (absent de la série : grep « Laborit » = 0 dans
``ict/`` avant ce fichier) comme un substrat expérimental falsifiable, et le
relie quantitativement à la **dette d'irréversibilité I(R)** via
:func:`ict.reversibility_budget.work_budget` (la quantité de dynamique
irréversible que l'animat subit sans pouvoir la « défaire »).

Mécanisme
---------
- Un anneau d'états (la 1-torus, minimal). L'action ``a ∈ {−1, 0, +1}`` déplace
  l'animat.
- **Contrôlabilité** ``α ∈ [0, 1]`` : avec probabilité ``α`` l'action est
  appliquée (l'animat contrôle), sinon l'état dérive (action ignorée = inhibition).
  ``α = 0`` = inhibition totale (Laborit) ; ``α = 1`` = contrôle complet.
- L'animat **estime** ``α`` depuis les transitions observées
  (:func:`estimate_controllability`) — c'est la formalisation de « apprend que
  ses actions ne contrôlent plus ».
- Un animat **adaptatif** (:func:`adaptive_animat`) qui, détectant ``ĉ`` faible,
  **inhibe** son action (se repli sur une action par défaut) : sa diversité
  d'action s'effondre = rigidification.

Références
----------
Laborit 1976 (*L'Éloge de la fuite*) ; spec #7741 (jambe C2, conversation de
conception tours 756-761, 2026-07-20) ; pont I(R) via
:mod:`ict.reversibility_budget` (work_budget / ICT-18).
"""

from typing import Dict, Optional, Tuple

import numpy as np


# ---------------------------------------------------------------------------
# Substrat : anneau contrôlable / inhibé.
# ---------------------------------------------------------------------------


class InhibitedEnvironment:
    """Anneau d'états avec un bouton de contrôlabilité ``α`` (inhibition Laborit).

    L'action ``a`` (entier, typiquement −1/0/+1) est appliquée avec probabilité
    ``α`` ; avec probabilité ``1 − α`` l'état dérive d'un pas aléatoire (action
    ignorée). ``α = 0`` = inhibition totale ; ``α = 1`` = contrôle total.

    Parametres
    ----------
    n_states : int
        Nombre d'états sur l'anneau (≥ 3 pour que l'action ait un sens).
    alpha : float
        Contrôlabilité dans ``[0, 1]``.
    drift : str
        Régime de dérive quand l'action est inhibée : ``"uniform"`` (pas aléatoire
        isotrope) ou ``"biased"`` (dérive orientée — environnement hostile).
    rng : Optional[np.random.Generator]
        Générateur pour la stochasticité de la dérive.
    """

    def __init__(
        self,
        n_states: int,
        alpha: float,
        drift: str = "uniform",
        rng: Optional[np.random.Generator] = None,
    ) -> None:
        if n_states < 3:
            raise ValueError(f"n_states >= 3 requis (recu {n_states}).")
        if not 0.0 <= alpha <= 1.0:
            raise ValueError(f"alpha dans [0, 1] requis (recu {alpha}).")
        if drift not in ("uniform", "biased"):
            raise ValueError(f"drift in {{'uniform','biased'}} requis (recu {drift}).")
        self.n_states = n_states
        self.alpha = alpha
        self.drift = drift
        self.rng = rng if rng is not None else np.random.default_rng()

    def intended(self, state: int, action: int) -> int:
        """Effectif attendu de l'action sur l'anneau (modulo n)."""
        return int((state + action) % self.n_states)

    def transition(self, state: int, action: int) -> int:
        """Transition d'un pas. Avec proba ``α`` on applique l'action, sinon dérive."""
        if not 0 <= state < self.n_states:
            raise IndexError(f"state {state} hors borne [0, {self.n_states}).")
        if self.rng.random() < self.alpha:
            return self.intended(state, action)
        # Inhibition : l'action est ignorée, l'état dérive.
        if self.drift == "uniform":
            step = int(self.rng.choice([-1, 0, 1]))
        else:  # biased : environnement qui pousse dans un sens
            step = int(self.rng.choice([0, 1, 1]))
        return int((state + step) % self.n_states)

    def transition_kernel(self, action: int) -> np.ndarray:
        """Matrice de transition ``P[s', s]`` pour une ``action`` fixée.

        Ligne ``s`` sommant à 1. Utile pour brancher ``work_budget`` (I(R)).
        """
        P = np.zeros((self.n_states, self.n_states), dtype=float)
        for s in range(self.n_states):
            target = self.intended(s, action)
            P[target, s] += self.alpha
            if self.drift == "uniform":
                for step in (-1, 0, 1):
                    P[(s + step) % self.n_states, s] += (1.0 - self.alpha) / 3.0
            else:
                for step in (0, 1, 1):
                    P[(s + step) % self.n_states, s] += (1.0 - self.alpha) / 3.0
        return P


# ---------------------------------------------------------------------------
# L'animat : estimation de contrôlabilité + inhibition adaptative.
# ---------------------------------------------------------------------------


def estimate_controllability(
    states: np.ndarray,
    actions: np.ndarray,
    next_states: np.ndarray,
    n_states: int,
) -> float:
    """Estime ``α`` depuis les transitions observées (l'animat détecte l'inhibition).

    On mesure le **déplacement signé** ``d = s' − s`` (ramené dans {−1,0,1} sur
    l'anneau) et on compare sa concordance avec l'action. Sous contrôle total
    (α=1), ``d == action`` toujours ; sous inhibition (α=0, dérive uniforme),
    ``d`` est indépendant de l'action.

    La **ligne de chance** n'est PAS ``1/n`` (la dérive n'est pas uniforme sur
    les états mais sur les pas {−1,0,1}) : on l'estime empiriquement comme la
    concordance moyenne qu'on obtiendrait si le déplacement était indépendant de
    l'action, soit ``chance = mean_{a∈{−1,0,1}} P_d(a)`` où ``P_d`` est la
    marginale observée du déplacement. Alors
    ``α̂ = (concordance − chance) / (1 − chance)``, clippé à ``[0, 1]``.

    C'est la formalisation quantitative de « apprend que ses actions ne
    contrôlent plus l'environnement » : un animat sous α=0 voit α̂ → 0.
    """
    if len(states) == 0:
        return 0.0
    # Déplacement signé sur l'anneau (les pas sont petits, n_states >= 3).
    d = (next_states - states) % n_states
    d = np.where(d > n_states // 2, d - n_states, d)
    observed = float(np.mean(d == actions))
    # Ligne de chance : concordance moyenne si d et action sont indépendants,
    # actions supposées uniformes sur {−1,0,1}.
    chance = float(np.mean([np.mean(d == a) for a in (-1, 0, 1)]))
    if chance >= 1.0:
        return 0.0
    alpha_hat = (observed - chance) / (1.0 - chance)
    return float(np.clip(alpha_hat, 0.0, 1.0))


def adaptive_animat(
    env: InhibitedEnvironment,
    n_steps: int,
    inhibit_threshold: float = 0.3,
    window: int = 30,
    rng: Optional[np.random.Generator] = None,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Animat qui **inhibe** son action quand il détecte une faible contrôlabilité.

    Modèle Laborit : l'animat explore d'abord (actions −1/0/+1 uniformes), estime
    en ligne la contrôlabilité ``ĉ`` sur une fenêtre glissante, et quand ``ĉ``
    passe sous ``inhibit_threshold``, il **se replie sur l'action 0** (no-op) —
    l'inhibition de l'action. Renvoie les trajectoires (états, actions) et la
    trace de ``ĉ`` au cours du temps.

    Under α=1, ``ĉ`` reste élevé → l'animat continue d'explorer (diversité haute).
    Under α=0, ``ĉ`` s'effondre → l'animat inhibe (diversité d'action effondrée).
    """
    rng = rng if rng is not None else np.random.default_rng()
    states = np.empty(n_steps, dtype=int)
    actions = np.empty(n_steps, dtype=int)
    chat = np.empty(n_steps, dtype=float)
    s = int(rng.integers(0, env.n_states))
    recent_s, recent_a, recent_s2 = [], [], []
    for t in range(n_steps):
        # Estimation en ligne de la contrôlabilité sur la fenêtre glissante.
        if len(recent_s) >= window:
            c = estimate_controllability(
                np.array(recent_s), np.array(recent_a), np.array(recent_s2),
                n_states=env.n_states,
            )
        else:
            c = 1.0  # optimisme initial (explore) jusqu'à preuve du contraire.
        chat[t] = c
        if c < inhibit_threshold:
            a = 0  # inhibition : repli sur le no-op.
        else:
            a = int(rng.choice([-1, 0, 1]))
        s2 = env.transition(s, a)
        states[t], actions[t] = s, a
        recent_s.append(s); recent_a.append(a); recent_s2.append(s2)
        if len(recent_s) > window:
            recent_s.pop(0); recent_a.pop(0); recent_s2.pop(0)
        s = s2
    return states, actions, chat


# ---------------------------------------------------------------------------
# Mesures de pathologie (rigidification / effondrement exploratoire).
# ---------------------------------------------------------------------------


def action_entropy(actions: np.ndarray, n_actions: int = 3) -> float:
    """Entropie de Shannon (naturelle) de la distribution d'actions.

    Mesure de **rigidification** : une politique qui se replie sur une seule
    action (inhibition) a une entropie ≈ 0 ; une politique qui explore (−1/0/+1
    uniformes) a ``ln(3) ≈ 1.099``.
    """
    if len(actions) == 0:
        return 0.0
    counts = np.bincount((actions + 1) % n_actions, minlength=n_actions).astype(float)
    p = counts / counts.sum()
    p = p[p > 0]
    return float(-(p * np.log(p)).sum())


def state_coverage(states: np.ndarray, n_states: int) -> int:
    """Nombre d'états distincts visités — mesure d'**effondrement exploratoire**."""
    return int(np.unique(states % n_states).size)


# ---------------------------------------------------------------------------
# Bancs d'essai (protocole #7741) — chacun renvoie un verdict falsifiable.
# ---------------------------------------------------------------------------


def rigidification_test(
    n_states: int = 9,
    n_steps: int = 600,
    inhibit_threshold: float = 0.3,
    seed: int = 0,
) -> Dict[str, float]:
    """Test de RIGIDIFICATION (#7741).

    Sous α=0 (inhibition totale), l'animat détecte ĉ→0 et se replie sur le
    no-op : son entropie d'action s'effondre. Sous α=1 (contrôle), il explore.

    Verdict falsifiable
    -------------------
    ``rigidified`` est True ssi l'entropie d'action sous α=0 est nettement
    inférieure à celle sous α=1 (marge 0.3 nat). Un animat qui n'inhiberait pas
    garderait la même diversité dans les deux régimes — le test le détecterait.
    """
    rng0 = np.random.default_rng(seed)
    rng1 = np.random.default_rng(seed + 1)
    env0 = InhibitedEnvironment(n_states, alpha=0.0, drift="uniform", rng=rng0)
    env1 = InhibitedEnvironment(n_states, alpha=1.0, drift="uniform", rng=rng1)
    _, a0, c0 = adaptive_animat(env0, n_steps, inhibit_threshold, rng=rng0)
    _, a1, c1 = adaptive_animat(env1, n_steps, inhibit_threshold, rng=rng1)
    H0 = action_entropy(a0)
    H1 = action_entropy(a1)
    rigidified = (H1 - H0) > 0.3
    return {
        "action_entropy_controlled": H1,
        "action_entropy_inhibited": H0,
        "entropy_drop": H1 - H0,
        "chat_mean_controlled": float(np.mean(c1)),
        "chat_mean_inhibited": float(np.mean(c0)),
        "rigidified": 1.0 if rigidified else 0.0,
    }


def goal_seeking_efficacy_test(
    n_states: int = 9,
    n_steps: int = 800,
    seed: int = 0,
) -> Dict[str, float]:
    """Test d'EFFICACITÉ D'ACTION ORIENTÉE BUT (#7741).

    La couverture d'états ne s'effondre pas sous inhibition (la dérive porte
    l'animat partout sur un petit anneau) — ce n'est donc pas la bonne
    pathologie. Celle de Laborit est la **perte d'efficacité de l'action** :
    l'animat ne peut plus *atteindre ni maintenir* un but. On mesure le temps
    passé dans une région-cible (état 0 et ses voisins) par un animat qui
    cherche activement à s'y rendre (policy greedy vers 0).

    Verdict falsifiable
    -------------------
    ``lost_control`` est True ssi la fraction de pas dans la cible est
    strictement supérieure sous contrôle (α=1) que sous inhibition (α=0).
    """
    target = {0, 1, n_states - 1}  # état 0 + ses deux voisins sur l'anneau.

    def greedy_toward(state: int) -> int:
        # Pas signé qui rapproche de 0 (mod n).
        fwd = (0 - state) % n_states
        if fwd == 0:
            return 0
        return 1 if fwd <= n_states // 2 else -1

    def target_fraction(alpha: float, rng_seed: int) -> float:
        rng = np.random.default_rng(rng_seed)
        env = InhibitedEnvironment(n_states, alpha=alpha, drift="uniform", rng=rng)
        s = int(rng.integers(0, n_states))
        hits = 0
        for _ in range(n_steps):
            a = greedy_toward(s)
            s = env.transition(s, a)
            if s in target:
                hits += 1
        return hits / n_steps

    frac_controlled = target_fraction(1.0, seed)
    frac_inhibited = target_fraction(0.0, seed + 1)
    lost_control = frac_controlled > frac_inhibited
    return {
        "target_fraction_controlled": frac_controlled,
        "target_fraction_inhibited": frac_inhibited,
        "efficacy_drop": frac_controlled - frac_inhibited,
        "lost_control": 1.0 if lost_control else 0.0,
    }


def controllability_estimation_test(
    n_states: int = 9,
    n_steps: int = 2000,
    seed: int = 0,
) -> Dict[str, float]:
    """Test d'ESTIMATION de contrôlabilité (#7741 — le coeur « apprend »).

    L'animat doit pouvoir **détecter** α depuis les transitions observées (c'est
    le prérequis de l'inhibition : sans détection, pas de « savoir que mes
    actions ne contrôlent plus »). On vérifie que :func:`estimate_controllability`
    récupère α_true à ``±0.1`` près sur plusieurs régimes.

    Verdict falsifiable
    -------------------
    ``detected`` est True ssi |α̂ − α_true| < 0.1 pour α_true ∈ {0.0, 0.5, 1.0}.
    Un estimateur aveugle (constant 0.5) raterait α=0 et α=1.
    """
    detected = True
    errors = {}
    for alpha_true in (0.0, 0.5, 1.0):
        rng = np.random.default_rng(seed)
        env = InhibitedEnvironment(n_states, alpha=alpha_true, drift="uniform", rng=rng)
        s = int(rng.integers(0, n_states))
        S, A, S2 = [], [], []
        for _ in range(n_steps):
            a = int(rng.choice([-1, 0, 1]))
            s2 = env.transition(s, a)
            S.append(s); A.append(a); S2.append(s2)
            s = s2
        a_hat = estimate_controllability(
            np.array(S), np.array(A), np.array(S2), n_states=n_states,
        )
        err = abs(a_hat - alpha_true)
        errors[alpha_true] = err
        if err >= 0.1:
            detected = False
    return {
        **{f"abs_err_alpha_{alpha:.1f}": err for alpha, err in errors.items()},
        "max_abs_err": float(max(errors.values())),
        "detected": 1.0 if detected else 0.0,
    }


def irreversibility_debt_bridge(
    n_states: int = 9,
) -> Dict[str, float]:
    """Pont quantitatif vers la dette d'irréversibilité I(R) (#7741 spec).

    On mesure :func:`ict.reversibility_budget.work_budget` (distance L1/2 entre
    ``P`` et sa projection réversible ``P_rev``) sur le noyau vécu par l'animat.
    Le finding empirique n'est pas « la dette monte sous inhibition » (une
    permutation déterministe porte AUSSY une forte flèche du temps — ``P_rev``
    diffère de ``P``) ; il est plus fin : sous inhibition (α=0), **changer
    d'action ne change plus la dette subie** — l'animat a perdu toute prise sur
    l'irréversibilité qu'il subit, qui devient dictée par la dérive seule. À
    contrôlabilité partielle (α=0.5), l'action modulait encore cette dette.

    Verdict falsifiable
    -------------------
    ``trapped`` est True ssi (a) l'effet de l'action sur la dette sous inhibition
    est nul (|Δ| < 1e-9), ET (b) cet effet était non-négligeable à contrôle
    partiel (|Δ(α=0.5)| > 0.5) — preuve que l'action était opérante puis a cessé
    de l'être.
    """
    from .reversibility_budget import work_budget

    def debt(alpha: float, act: int) -> float:
        env = InhibitedEnvironment(n_states, alpha=alpha, drift="biased")
        P = env.transition_kernel(act)
        pi = np.full(n_states, 1.0 / n_states)
        return work_budget(P, pi)

    def action_effect(alpha: float) -> float:
        return abs(debt(alpha, +1) - debt(alpha, -1))

    eff_inhibited = action_effect(0.0)
    eff_partial = action_effect(0.5)
    trapped = (eff_inhibited < 1e-9) and (eff_partial > 0.5)
    return {
        "debt_inhibited_action_plus1": debt(0.0, +1),
        "debt_inhibited_action_minus1": debt(0.0, -1),
        "debt_partial_action_plus1": debt(0.5, +1),
        "debt_partial_action_minus1": debt(0.5, -1),
        "debt_controlled_action_plus1": debt(1.0, +1),
        "debt_controlled_action_minus1": debt(1.0, -1),
        "action_effect_inhibited": eff_inhibited,
        "action_effect_partial_control": eff_partial,
        "trapped": 1.0 if trapped else 0.0,
    }
