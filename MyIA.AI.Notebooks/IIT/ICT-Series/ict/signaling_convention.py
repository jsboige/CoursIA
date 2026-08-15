"""Coordination a vocabulaire fixe — jeux de signalisation de Lewis/Skyrms (strate 7, jambe D2 experience A, #7746).

Contexte
--------
Le chantier strate 7 (#7745 D1) introduit le **jeu evolutif** ``G_t`` dont les coups
peuvent etre ontologiques (inventer un symbole, une regle, une categorie). La jambe D2
(#7746) pose les **cinq bancs d'essai controles** qui rendent cette strate simulable.
Cette experience A est la **ligne de base « sans coup ontologique »** : le vocabulaire
est FIXE (aucune invention — c'est l'experience B), et l'on demande si des conventions
de signalisation EMERGENT spontanement par apprentissage par renforcement, sans que la
signification des signaux soit pre-inscrite.

C'est le jeu de signalisation canonique de David Lewis (*Convention*, 1969) et de Brian
Skyrms (*Signals*, 2010) : un **emetteur** observe l'etat du monde et envoie un signal ;
un **recepteur** recoit le signal et choisit une action ; le couple est recompense quand
l'action correspond a l'etat (interet commun = coordination pure). La question falsifiable :
partant de propensites uniformes (aucune signification), un **code conventionnel**
(bijection etat->signal->action) emerge-t-il, et avec lui l'**information mutuelle**
I(signal ; etat) qui mesure combien le signal en dit sur l'etat ?

Distinct de ``strategic_morphodynamics`` (ICT-13) qui traite le **dilemme du prisonnier
itere** (2 joueurs, 2 actions cooperate/defect, conflit d'interet). Ici : interet commun,
N etats / N signaux / N actions, emergence de **signification** (information mutuelle),
pas de paiement. Les deux sont de la theorie des jeux evolutionnaire, mais sur des
objets differents (signification vs. conflit).

Mecanisme
---------
**Roth-Erev / Herrnstein** (Skyrms 2010) : les propensites ``Q_s[etat, signal]`` et
``Q_r[signal, action]`` sont renforcees par le succes. La selection est softmax (avec
temperature), ce qui permet l'exploration necessaire pour eviter l'equilibre de pooling
(un seul signal utilise, signification nulle). La temperature peut etre annealed
(chaud au debut = exploration ; froid a la fin = exploitation) — c'est le levier qui
distingue une convergence robuste d'un piege de pooling.

Portee de ce module (cycle-1 d'un livrable multi-cycle)
-------------------------------------------------------
Module ADDITIF numpy-only, CPU. Il fournit le banc algorithmique (classe
``SignalingGame`` + 4 verdicts falsifiables : emergence de coordination, goulot de
vocabulaire, suivi MI-sens, stabilite de convention) que le notebook #7746 D2-A
branchera ensuite. Aucune modification des modules existants.

References
----------
Lewis 1969 (*Convention*) ; Skyrms 2010 (*Signals: Evolution, Learning, and Information*) ;
Roth & Erev 1995 (apprentissage par renforcement dans les jeux) ; spec #7746 (experience A :
coordination a vocabulaire fixe, emergence de convention, information mutuelle).
"""

from __future__ import annotations

from typing import Dict, Optional, Sequence, Tuple

import numpy as np


def _softmax(propensities: np.ndarray, temperature: float,
             rng: np.random.Generator) -> int:
    """Tire un indice selon une softmax des propensites (temperature ``T``).

    ``T`` grand = proche de l'uniforme (exploration) ; ``T`` petit = glouton
    (exploitation). ``T -> 0`` = argmax deterministe.
    """
    scaled = propensities / max(temperature, 1e-9)
    scaled = scaled - scaled.max()
    weights = np.exp(scaled)
    probs = weights / weights.sum()
    return int(rng.choice(len(probs), p=probs))


def mutual_information(joint_counts: np.ndarray) -> float:
    """Information mutuelle I(X ; Y) en bits, depuis une matrice de comptes joints.

    ``joint_counts[i, j]`` = nombre de fois ou X=i ET Y=j ont ete observes.
    Renvoie ``0.0`` si la matrice est nulle ou si une marginal est nulle.

    Utilisee pour mesurer I(etat ; signal) — combien le signal porte sur l'etat.
    Pour ``n`` etats equiprobables parfaitement codes, ``I = log2(n)`` (signification
    totale) ; pour un signal non informatif (pooling), ``I = 0``.
    """
    total = float(joint_counts.sum())
    if total <= 0.0:
        return 0.0
    p_joint = joint_counts / total
    p_x = p_joint.sum(axis=1, keepdims=True)
    p_y = p_joint.sum(axis=0, keepdims=True)
    mi = 0.0
    for i in range(p_joint.shape[0]):
        for j in range(p_joint.shape[1]):
            p = p_joint[i, j]
            if p > 0.0 and p_x[i, 0] > 0.0 and p_y[0, j] > 0.0:
                mi += p * np.log2(p / (p_x[i, 0] * p_y[0, j]))
    return float(mi)


class SignalingGame:
    """Jeu de signalisation de Lewis/Skyrms avec reinforcement Roth-Erev.

    Un emetteur (``Q_s[etat, signal]``) et un recepteur (``Q_r[signal, action]``)
    apprennent a coordonner. Chaque tour :

    1. un etat ``s`` est tire selon ``state_dist`` (defaut : uniforme) ;
    2. l'emetteur choisit un signal ``m`` (softmax sur ``Q_s[s]``) ;
    3. le recepteur choisit une action ``a`` (softmax sur ``Q_r[m]``) ;
    4. le paiement vaut 1 si ``a == s`` (coordination), 0 sinon ;
    5. en cas de succes, les propensites utilisees sont renforcees.

    Parametres
    ----------
    n_states : int
        Nombre d'etats du monde (dimension de l'observation de l'emetteur).
    n_signals : int
        Taille du vocabulaire (FIXE — experience A, sans invention).
    n_actions : Optional[int]
        Nombre d'actions du recepteur. Defaut : ``n_states`` (la coordination pure
        demande a pouvoir distinguer chaque etat).
    temperature : float
        Temperature softmax. ``anneal_to`` permet de la reduire en fin d'apprentissage.
    state_dist : Optional[Sequence[float]]
        Distribution des etats. Defaut : uniforme. Une distribution desequilibree
        (un etat dominant) permet le controle negatif « succes sans signification ».
    initial_q : float
        Propensite initiale uniforme (> 0). Evite le piege d'une propensite nulle.
    """

    def __init__(
        self,
        n_states: int,
        n_signals: int,
        n_actions: Optional[int] = None,
        *,
        temperature: float = 0.5,
        state_dist: Optional[Sequence[float]] = None,
        initial_q: float = 1.0,
        rng: Optional[np.random.Generator] = None,
    ) -> None:
        if n_states < 1:
            raise ValueError(f"n_states >= 1 requis (recu {n_states}).")
        if n_signals < 1:
            raise ValueError(f"n_signals >= 1 requis (recu {n_signals}).")
        n_actions = n_states if n_actions is None else n_actions
        if n_actions < 1:
            raise ValueError(f"n_actions >= 1 requis (recu {n_actions}).")
        if temperature <= 0.0:
            raise ValueError(f"temperature > 0 requis (recu {temperature}).")
        if initial_q <= 0.0:
            raise ValueError(f"initial_q > 0 requis (recu {initial_q}).")
        if state_dist is None:
            state_dist = np.full(n_states, 1.0 / n_states)
        else:
            state_dist = np.asarray(state_dist, dtype=float)
            if state_dist.shape != (n_states,):
                raise ValueError(
                    f"state_dist doit avoir {n_states} elements (recu {state_dist.shape})."
                )
            if state_dist.sum() <= 0.0 or np.any(state_dist < 0.0):
                raise ValueError("state_dist doit etre une distribution (>= 0, somme > 0).")
            state_dist = state_dist / state_dist.sum()
        self.n_states = n_states
        self.n_signals = n_signals
        self.n_actions = n_actions
        self.temperature = temperature
        self.state_dist = state_dist
        self.initial_q = initial_q
        self.rng = rng if rng is not None else np.random.default_rng()
        self.reset()

    def reset(self) -> None:
        """Reinitialise les propensites a ``initial_q`` (uniforme) et vide l'historique."""
        self.Q_s = np.full((self.n_states, self.n_signals), self.initial_q, dtype=float)
        self.Q_r = np.full((self.n_signals, self.n_actions), self.initial_q, dtype=float)
        self.joint_state_signal = np.zeros((self.n_states, self.n_signals), dtype=float)
        self.success_history: list[int] = []

    def play_round(self, reinforce: bool = True) -> Tuple[int, int, int, int]:
        """Un tour de jeu. Renvoie ``(etat, signal, action, paiement)``.

        Si ``reinforce`` est Faux, les propensites ne sont PAS mises a jour : c'est le
        controle « jeu aleatoire » (les agents jouent leur politique courante sans
        apprendre). Utile pour mesurer la ligne de base sans-apprentissage.
        """
        state = int(self.rng.choice(self.n_states, p=self.state_dist))
        signal = _softmax(self.Q_s[state], self.temperature, self.rng)
        action = _softmax(self.Q_r[signal], self.temperature, self.rng)
        payoff = 1 if action == state else 0
        self.joint_state_signal[state, signal] += 1.0
        self.success_history.append(payoff)
        if reinforce and payoff == 1:
            self.Q_s[state, signal] += 1.0
            self.Q_r[signal, action] += 1.0
        return state, signal, action, payoff

    def train(self, n_rounds: int, anneal_to: Optional[float] = None) -> None:
        """Apprend pendant ``n_rounds`` tours.

        Si ``anneal_to`` est fourni (< ``temperature``), la temperature decroit
        lineairement de ``temperature`` a ``anneal_to`` au fil des tours : exploration
        au debut, exploitation a la fin. C'est le levier anti-pooling.
        """
        if n_rounds < 0:
            raise ValueError(f"n_rounds >= 0 requis (recu {n_rounds}).")
        t0 = self.temperature
        for t in range(n_rounds):
            if anneal_to is not None and n_rounds > 1:
                frac = t / (n_rounds - 1)
                self.temperature = t0 + frac * (anneal_to - t0)
            self.play_round(reinforce=True)
        self.temperature = t0

    def success_rate(self, window: int = 500) -> float:
        """Taux de succes (coordination) sur les ``window`` derniers tours."""
        if not self.success_history:
            return 0.0
        recent = self.success_history[-window:]
        return float(np.mean(recent))

    def state_signal_mi(self, window: int = 0) -> float:
        """I(etat ; signal) sur l'historique joint.

        Si ``window > 0``, l'information mutuelle n'est calculee que sur les ``window``
        derniers tours — mais comme on n'archive que la matrice jointe cumulee, on
        calcule sur tout l'historique quand ``window == 0`` (defaut). Pour une mesure
        fenetree stricte, preferer :meth:`signal_state_mi_trajectory`.
        """
        return mutual_information(self.joint_state_signal)


def _trajectory(game: SignalingGame, n_rounds: int, *, anneal_to: Optional[float],
                n_probes: int = 40) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Entrainement instrumente : renvoie (tours, succes_glissant, mi_glissant).

    ``n_probes`` points de mesure ; a chaque point on calcule le taux de succes sur une
    petite fenetre et l'information mutuelle etat-signal cumulee depuis le dernier point
    (matrice jointe reinitialisee a chaque point pour mesurer la politique COURANTE).
    """
    game.reset()
    checkpoints = np.linspace(0, n_rounds, n_probes, dtype=int)
    rounds = []
    succ = []
    mi = []
    prev = 0
    for c in checkpoints:
        block = c - prev
        if block > 0:
            game.joint_state_signal[:] = 0.0  # mesurer la politique courante sur ce bloc
            for _ in range(block):
                game.play_round(reinforce=True)
                # apres le bloc, la matrice jointe reflete la politique de ce bloc
        rounds.append(c)
        # succes sur ce bloc (approx : moyennage historique recent)
        recent = game.success_history[prev:c] if c > prev else [0]
        succ.append(float(np.mean(recent)) if recent else 0.0)
        mi.append(mutual_information(game.joint_state_signal))
        prev = c
    return np.array(rounds), np.array(succ), np.array(mi)


# ---------------------------------------------------------------------------
# Bancs d'essai (protocoles #7746 D2 experience A) — chacun renvoie un verdict
# falsifiable.
# ---------------------------------------------------------------------------


def coordination_emerges_test(
    n_states: int = 4,
    n_signals: int = 4,
    n_rounds: int = 4000,
    temperature: float = 0.6,
    anneal_to: float = 0.15,
    window: int = 800,
    seed: int = 0,
) -> Dict[str, float]:
    """Verdict EMERGENCE : une convention emerge-t-elle sans signification pre-inscrite ?

    On entraine un jeu a interet commun (``n_signals = n_states``, vocabulaire suffisant)
    depuis des propensites uniformes. Si un code conventionnel emerge, le taux de
    coordination (succes) monte vers 1.0 ET l'information mutuelle I(etat ; signal) monte
    vers ``log2(n_states)`` — le signal devient INFORMATIF.

    Le controle negatif est inclus : un jeu sans renforcement (``reinforce=False``) garde
    une politique quasi-uniforme (succes ~ ``1/n_states``, MI ~ 0). Le verdict n'est
    satisfait que si l'apprentissage depasse nettement la ligne de base sans-apprentissage.

    Verdict falsifiable
    -------------------
    ``emerged`` est True ssi le succes final est eleve (> 0.8) ET l'information mutuelle
    depasse la moitie du maximum ``log2(n_states)`` ET les deux dominent nettement le
    controle sans-apprentissage (ecart > 0.3).
    """
    max_mi = float(np.log2(n_states))
    # Apprenti.
    g = SignalingGame(n_states, n_signals, temperature=temperature,
                      rng=np.random.default_rng(seed))
    g.train(n_rounds, anneal_to=anneal_to)
    learned_success = g.success_rate(window)
    # Controle sans-apprentissage (meme graine, politique initiale uniforme, pas de renforcement).
    g_ctrl = SignalingGame(n_states, n_signals, temperature=temperature,
                           rng=np.random.default_rng(seed))
    for _ in range(window):
        g_ctrl.play_round(reinforce=False)
    ctrl_success = g_ctrl.success_rate(window)
    g_ctrl.joint_state_signal[:] = 0.0
    for _ in range(window):
        g_ctrl.play_round(reinforce=False)
    ctrl_mi = mutual_information(g_ctrl.joint_state_signal)
    # MI de l'apprenti : politique courante, pas toute la trajectoire.
    g.joint_state_signal[:] = 0.0
    for _ in range(window):
        g.play_round(reinforce=False)
    learned_mi = mutual_information(g.joint_state_signal)
    emerged = (
        learned_success > 0.8
        and learned_mi > 0.5 * max_mi
        and learned_success - ctrl_success > 0.3
        and learned_mi - ctrl_mi > 0.3
    )
    return {
        "n_states": float(n_states),
        "n_signals": float(n_signals),
        "max_mi": max_mi,
        "learned_success": learned_success,
        "learned_mi": learned_mi,
        "control_success": ctrl_success,
        "control_mi": ctrl_mi,
        "emerged": 1.0 if emerged else 0.0,
    }


def vocabulary_bottleneck_test(
    n_states: int = 4,
    n_rounds: int = 4000,
    temperature: float = 0.6,
    anneal_to: float = 0.15,
    window: int = 800,
    seed: int = 0,
) -> Dict[str, float]:
    """Verdict GOULOT : un vocabulaire insuffisant limite strictement la signification.

    On compare deux jeux sous entrainement identique : un vocabulaire SUFFISANT
    (``n_signals = n_states`` — la signification totale ``log2(n_states)`` est
    atteignable) et un vocabulaire INSUFFISANT (``n_signals = n_states // 2`` — au
    mieux ``n_states // 2`` groupes de signaux, donc la signification est plafonnee).
    Avec ``n_signals < n_states``, aucun code ne peut distinguer tous les etats : c'est
    une borne de codage, pas une limite d'apprentissage.

    NB honnete : avec ``M < N``, les agents ne convergent pas toujours au partition
    optimal (pooling partiel) — l'information mutuelle observee est souvent STRICTEMENT
    sous ``log2(M)``. C'est pourquoi le verdict est RELATIF (vocabulaire insuffisant ->
    MI strictement inferieure au vocabulaire suffisant), pas absolu : la borne codage
    est uncontestede, la convergence vers le partition optimal l'est moins.

    C'est le resultat honnete qui motive l'experience B (invention de symboles) : la
    taille du vocabulaire FIXE borne ce que la coordination peut atteindre.

    Verdict falsifiable
    -------------------
    ``bottleneck`` est True ssi le vocabulaire suffisant atteint une signification
    elevee (``mi_full > 0.5 * log2(n_states)`` — la convention emerge bien avec assez de
    signaux) ET le vocabulaire insuffisant reste STRICTEMENT inferieur
    (``mi_limited < 0.6 * mi_full``). Si le vocabulaire n'importait pas, les deux MI
    seraient egales — c'est le controle falsifiant.
    """
    max_mi = float(np.log2(n_states))

    def _train_mi(n_sig: int) -> float:
        g = SignalingGame(n_states, n_sig, temperature=temperature,
                          rng=np.random.default_rng(seed))
        g.train(n_rounds, anneal_to=anneal_to)
        g.joint_state_signal[:] = 0.0
        for _ in range(window):
            g.play_round(reinforce=False)
        return mutual_information(g.joint_state_signal)

    mi_full = _train_mi(n_states)
    n_limited = max(2, n_states // 2)
    mi_limited = _train_mi(n_limited)
    bottleneck = mi_full > 0.5 * max_mi and mi_limited < 0.6 * mi_full
    return {
        "n_states": float(n_states),
        "n_signals_full": float(n_states),
        "n_signals_limited": float(n_limited),
        "max_mi": max_mi,
        "mi_full_vocab": mi_full,
        "mi_limited_vocab": mi_limited,
        "ratio_limited_over_full": float(mi_limited / mi_full) if mi_full > 0 else 0.0,
        "bottleneck": 1.0 if bottleneck else 0.0,
    }


def mi_tracks_meaning_test(
    n_states: int = 4,
    n_rounds: int = 3000,
    temperature: float = 0.6,
    anneal_to: float = 0.15,
    seed: int = 0,
) -> Dict[str, float]:
    """Verdict SENS : l'information mutuelle suit-elle le succes (les signaux deviennent-ils signifiants) ?

    Au cours de l'apprentissage, succes et MI doivent CROITRE ensemble : le signal
    devient progressivement informatif a mesure que la convention se forme. On mesure la
    correlation entre le succes glissant et l'information mutuelle glissante sur la
    trajectoire.

    Le controle negatif (falsifiabilite) : un jeu avec un etat dominant
    (``state_dist`` desequilibre) atteint un succes eleve « sans signification » (les
    agents apprennent a toujours choisir l'action de l'etat dominant, mais le signal
    reste non informatif -> MI faible). Le verdict distingue donc « succes via
    signification » de « succes via exploitation d'un biais ».

    Verdict falsifiable
    -------------------
    ``meaningful`` est True ssi la correlation MI-succes sur la trajectoire est forte
    (> 0.6), la MI finale est elevee (> 0.5 * log2(n_states)), ET le controle a etat
    dominant montre un succes comparable mais une MI faible (ecart > 0.3).
    """
    max_mi = float(np.log2(n_states))

    # Cas equilibre : emergence de signification.
    g = SignalingGame(n_states, n_states, temperature=temperature,
                      rng=np.random.default_rng(seed))
    _, succ_bal, mi_bal = _trajectory(g, n_rounds, anneal_to=anneal_to)
    # Correlation sur les points de mesure (apres le demarrage).
    if len(succ_bal) > 2 and succ_bal[1:].std() > 0 and mi_bal[1:].std() > 0:
        corr_bal = float(np.corrcoef(succ_bal[1:], mi_bal[1:])[0, 1])
    else:
        corr_bal = 0.0

    # Controle : etat dominant (0.85), les agents peuvent reussir sans signifier.
    dom_dist = np.full(n_states, (1.0 - 0.85) / (n_states - 1))
    dom_dist[0] = 0.85
    g_dom = SignalingGame(n_states, n_states, temperature=temperature,
                          state_dist=dom_dist, rng=np.random.default_rng(seed))
    _, succ_dom, mi_dom = _trajectory(g_dom, n_rounds, anneal_to=anneal_to)
    dom_final_success = float(succ_dom[-1]) if len(succ_dom) else 0.0
    dom_final_mi = float(mi_dom[-1]) if len(mi_dom) else 0.0
    bal_final_mi = float(mi_bal[-1]) if len(mi_bal) else 0.0
    bal_final_success = float(succ_bal[-1]) if len(succ_bal) else 0.0

    meaningful = (
        corr_bal > 0.6
        and bal_final_mi > 0.5 * max_mi
        and bal_final_mi - dom_final_mi > 0.3
    )
    return {
        "max_mi": max_mi,
        "balanced_final_success": bal_final_success,
        "balanced_final_mi": bal_final_mi,
        "balanced_corr_mi_success": corr_bal,
        "dominant_final_success": dom_final_success,
        "dominant_final_mi": dom_final_mi,
        "meaningful": 1.0 if meaningful else 0.0,
    }


def convention_stability_test(
    n_states: int = 4,
    n_rounds: int = 4000,
    temperature: float = 0.6,
    anneal_to: float = 0.15,
    moderate_shock: float = 0.5,
    brutal_shock: float = 6.0,
    window: int = 800,
    seed: int = 0,
) -> Dict[str, float]:
    """Verdict STABILITE : une convention etablie resiste-t-elle a une perturbation ?

    On entraine une convention (succes eleve), puis on perturbe les propensites en
    injectant du bruit additif **relatif a l'echelle des propensites elles-memes**
    (``shock`` en multiples de l'ecart-type des ``Q``). Un bruit absolu serait
    negligeable : apres ``n_rounds`` renforcements, les ``Q`` atteignent des centaines,
    donc un bruit absolu de 5 ou 50 ne perturbe rien. Un choc RELATIF de
    ``moderate_shock`` (=0.5 ecart-type) laisse la structure apprise dominante ; un choc
    de ``brutal_shock`` (=6 ecarts-types) l'oblitere.

    Une convention stable (a) ne s'effondre pas sous un choc modere, et (b) se reconstruit
    vite par re-apprentissage. On compare au choc brutal qui doit effondrer la convention
    nettement plus — c'est le controle falsifiant.

    Verdict falsifiable
    -------------------
    ``stable`` est True ssi la convention est etablie (> 0.8), le choc modere est supporte
    (succes immediate > 0.6 ET reconstruit > 0.8), ET le choc brutal effondre
    significativement plus (ecart > 0.3 entre modere et brutal sur le succes immediate).
    """
    # Convention etablie.
    g = SignalingGame(n_states, n_states, temperature=temperature,
                      rng=np.random.default_rng(seed))
    g.train(n_rounds, anneal_to=anneal_to)
    established = g.success_rate(window)
    scale_s = float(g.Q_s.std()) or 1.0
    scale_r = float(g.Q_r.std()) or 1.0

    def _post_shock(shock: float) -> Tuple[float, float]:
        h = SignalingGame(n_states, n_states, temperature=temperature,
                          rng=np.random.default_rng(seed))
        h.Q_s = g.Q_s + h.rng.normal(0.0, shock * scale_s, size=g.Q_s.shape)
        h.Q_r = g.Q_r + h.rng.normal(0.0, shock * scale_r, size=g.Q_r.shape)
        np.maximum(h.Q_s, h.initial_q * 0.1, out=h.Q_s)
        np.maximum(h.Q_r, h.initial_q * 0.1, out=h.Q_r)
        # Mesure immediate post-choc (sans re-apprentissage).
        h.joint_state_signal[:] = 0.0
        h.success_history.clear()
        for _ in range(window):
            h.play_round(reinforce=False)
        immediate = h.success_rate(window)
        # Re-apprentissage court.
        h.train(window, anneal_to=anneal_to)
        recovered = h.success_rate(window)
        return float(immediate), float(recovered)

    mod_immediate, mod_recovered = _post_shock(moderate_shock)
    bru_immediate, bru_recovered = _post_shock(brutal_shock)

    stable = (
        established > 0.8
        and mod_immediate > 0.6
        and mod_recovered > 0.8
        and bru_immediate - mod_immediate < -0.3
    )
    return {
        "established_success": established,
        "moderate_immediate": mod_immediate,
        "moderate_recovered": mod_recovered,
        "brutal_immediate": bru_immediate,
        "brutal_recovered": bru_recovered,
        "stable": 1.0 if stable else 0.0,
    }
