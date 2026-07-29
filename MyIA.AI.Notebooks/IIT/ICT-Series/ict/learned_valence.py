"""Valence APPRISE, transferable, distincte de la prediction — la «expérience manquante» #7740.

Contexte
--------
``valence`` (ICT-12) programme la valence comme un champ gaussien externe fixe :
la source a une valence *intrinseque* parce que le schema la place la. La question
#7740 (framings user 2026-07-20, issue ouverte par ai-01) est l'envers exact : une
valence qui est **apprise** (acquise par conditionnement Pavlovien), **transferable**
(un signal d'abord neutre devient attractif apres association repetee avec une
source biologiquement pertinente), et **distincte de la representation predictive**
(``p_hat`` predit OU EST la source ; ``pi_t`` encode combien l'agent INVESTIT dans
un signal — investissement semiotique, non poursuite).

Ces deux lectures coexistent sans se confondre :

- valence programmee (``ict.valence.valence_at``) : ICT-12, ligne de base innée.
- valence apprise (ce module) : #7740, acquisition par association.

Mecanisme
---------
On utilise une regle de type **Rescorla-Wagner** (Rescorla & Wagner 1972) : le
changement de valence est proportionnel a l'erreur de prediction, pas a la simple
co-occurrence. Un signal neutre co-occurent avec une source pertinente voit sa
valence monter vers celle de la source ; presente seul (sans source), elle s'eteint
vers zero. C'est ce qui rend la valence *reversible* (mesure de reversibilite #7740)
et non un simple compteur d'apparitions.

Portee de ce module (cycle-1 d'un livrable multi-cycle)
-------------------------------------------------------
Ce module est ADDITIF : il ne modifie pas ``ict.valence``. Il fournit le banc
algorithmique (classe ``LearnedValence`` + tests de transfert / distinctness /
extinction) que le notebook #7740 branchera ensuite pour creuser son propre banc
d'essai. numpy seul, CPU.

References
----------
Pavlov 1927 (*Conditioned Reflexes*) ; Rescorla & Wagner 1972 (erreur de prediction
comme moteur de l'apprentissage associatif) ; spec #7740 (protocole de conditionnement,
signal neutre -> attractif, transfert, distinctness vs ``p_hat``).
"""

import inspect
from typing import Callable, Dict, Optional

import numpy as np


class LearnedValence:
    """Valence par signal, acquise par conditionnement (Rescorla-Wagner).

    ``pi[t]`` est la valence *apprise* du signal ``i`` a l'instant ``t``. Elle
    demarre **neutre** (0 pour tout signal) — par construction, rien n'est
    attractif avant apprentissage. C'est la difference avec ``valence_at`` dont
    la bosse est donnee d'entree.

    Parametres
    ----------
    n_signals : int
        Nombre de signaux distincts dans l'environnement de l'agent.
    lr : float
        Taux d'apprentissage (Rescorla-Wagner). ``Delta pi = lr * (v_source - pi)``.
    decay : float
        Decroissance passive par pas (extinction lente meme en presence du signal
        seul, sans source). 0 = pas de decroissance passive ; l'extinction ne se
        fait alors que par presentation explicite sans source (``condition(...,
        source_present=False)``).
    rng : Optional[np.random.Generator]
        Generateur pour les variantes stochastiques (bruit sur l'association).
    """

    def __init__(
        self,
        n_signals: int,
        lr: float = 0.1,
        decay: float = 0.0,
        rng: Optional[np.random.Generator] = None,
    ) -> None:
        if n_signals < 1:
            raise ValueError(f"n_signals >= 1 requis (recu {n_signals}).")
        if not 0.0 < lr <= 1.0:
            raise ValueError(f"0 < lr <= 1 requis (recu {lr}).")
        if not 0.0 <= decay < 1.0:
            raise ValueError(f"0 <= decay < 1 requis (recu {decay}).")
        self.n_signals = n_signals
        self.lr = lr
        self.decay = decay
        self.rng = rng if rng is not None else np.random.default_rng()
        # pi_t : valence apprise par signal, neutre a l'initialisation.
        self.pi = np.zeros(n_signals, dtype=float)
        # Comptes d'associations (provenance / debug), pas utilises dans pi.
        self.n_co_occurrences = np.zeros(n_signals, dtype=int)
        self.n_alone = np.zeros(n_signals, dtype=int)
        self.t = 0

    def condition(
        self,
        signal_idx: int,
        source_valence: float,
        steps: int = 1,
    ) -> None:
        """Conditionnement (ou extinction) Rescorla-Wagner.

        - ``source_valence > 0`` et signal co-occurrent : la valence du signal
          monte vers ``source_valence`` (acquisition).
        - ``source_valence == 0`` (signal presente seul) : la valence decroit vers
          0 (extinction), via le meme mecanisme d'erreur de prediction.

        Le fait que acquisition et extinction partagent la MEME regle (erreur de
        prediction) est precisement ce qui rend la valence reversible (#7740) :
        pas deux systemes, un seul qui s'adapte au signe de l'erreur.

        Notes
        -----
        Si ``decay > 0``, la decroissance passive s'applique au vecteur ``pi``
        ENTIER a chaque pas (tous les signaux), pas seulement au signal
        conditionne : l'horloge du banc avance d'un pas a chaque appel de
        ``condition``, et le temps passe donc globalement sur tout le paysage
        associatif. Intentionnel (un signal non renforce decroit passivement
        meme pendant qu'un autre est conditionne) ; le defaut ``decay=0.0`` le
        desactive (review ai-01 #8823).
        """
        if not 0 <= signal_idx < self.n_signals:
            raise IndexError(f"signal_idx {signal_idx} hors borne [0, {self.n_signals}).")
        for _ in range(steps):
            delta = self.lr * (source_valence - self.pi[signal_idx])
            self.pi[signal_idx] += delta
            if source_valence > 0:
                self.n_co_occurrences[signal_idx] += 1
            else:
                self.n_alone[signal_idx] += 1
            if self.decay > 0.0:
                self.pi *= (1.0 - self.decay)
            self.t += 1

    def valence(self, signal_idx: int) -> float:
        """Valence apprise courante du signal (scalaire)."""
        if not 0 <= signal_idx < self.n_signals:
            raise IndexError(f"signal_idx {signal_idx} hors borne [0, {self.n_signals}).")
        return float(self.pi[signal_idx])

    def valence_vector(self) -> np.ndarray:
        """Vecteur pi_t complet (tous les signaux)."""
        return self.pi.copy()

    def attract_prob(self, signal_idx: int) -> float:
        """Probabilite (proxy) que le signal seul pousse maintenant a l'approche.

        Proxy de transfert : un signal neutre (pi=0) n'attire pas ; un signal
        conditionne (pi proche de la source) attire. Clippe dans [0, 1].
        """
        return float(np.clip(self.pi[signal_idx], 0.0, 1.0))


# ---------------------------------------------------------------------------
# Bancs d'essai (protocoles #7740) — chacun renvoie un verdict falsifiable.
# ---------------------------------------------------------------------------


def valence_transfer_test(
    n_signals: int = 4,
    pertinent_idx: int = 0,
    neutral_idx: int = 1,
    source_valence: float = 1.0,
    n_condition: int = 50,
    lr: float = 0.1,
    seed: int = 0,
) -> Dict[str, float]:
    """Test de TRANSFERT (#7740 protocole canonique).

    Un signal neutre (``neutral_idx``) est presente en co-occurrence repetee avec
    une source biologiquement pertinente (``pertinent_idx``, valence innée
    ``source_valence``). On mesure si le signal neutre devient attractif PAR
    LUI-MEME (presente seul, sans la source).

    Verdict falsifiable
    -------------------
    ``transferred`` est True si et seulement si la valence post-conditionnement
    du signal neutre est elevee (> 0.5) ET un signal non-conditionne (controle)
    reste neutre (< 0.05). Un mecanisme qui monterait TOUS les signaux n'est pas
    du transfert — c'est une fuite de l'inné vers tout.
    """
    lv = LearnedValence(n_signals, lr=lr, rng=np.random.default_rng(seed))
    pre = lv.valence(neutral_idx)
    # Conditionnement : signal neutre + source pertinente co-occurs.
    lv.condition(neutral_idx, source_valence=source_valence, steps=n_condition)
    post = lv.valence(neutral_idx)
    # Controle : un signal jamais associe doit rester neutre.
    control_idx = neutral_idx + 1 if neutral_idx + 1 < n_signals else 0
    if control_idx == neutral_idx:
        control_idx = (neutral_idx + 1) % n_signals
    # control_idx doit differer de neutral_idx ET de pertinent_idx si possible
    if control_idx == pertinent_idx:
        control_idx = (control_idx + 1) % n_signals
        if control_idx == neutral_idx:
            control_idx = (control_idx + 1) % n_signals
    control_post = lv.valence(control_idx)
    transferred = post > 0.5 and control_post < 0.05
    return {
        "pre_valence_neutral": pre,
        "post_valence_neutral": post,
        "transfer_gain": post - pre,
        "control_valence_unconditioned": control_post,
        "n_condition": float(n_condition),
        "transferred": 1.0 if transferred else 0.0,
    }


def _call_predict_fn(
    predict_fn: Callable[..., float],
    signal_idx: int,
    valence_vector: np.ndarray,
) -> float:
    """Invoque un predicteur sur ``(signal_idx[, valence_vector])``.

    Dispatch selon l'arite de ``predict_fn`` :

    - **1 parametre** ``(signal_idx)`` : predicteur *state-invariant* (la prediction
      ne lit pas la valence). ``delta_err`` vaut alors 0 -> ``distinct``.
    - **>=2 parametres** ``(signal_idx, valence_vector)`` : predicteur
      *state-coupled*. Un re-vetement de la valence (ex.
      ``lambda i, pi: 1.0 - pi[i]``) voit son erreur changer entre pre et post
      (pi monte) -> ``delta_err > 0`` -> ``distinct == 0``.

    C'est ce passage du vecteur de valence au predicteur qui rend le banc
    REELLEMENT falsifiable (review ai-01 #8823) : sans lui, ``predict_fn``
    ne pouvait pas observer la valence, et le verdict ``distinct`` etait
    satisfait par construction pour toute fonction pure.
    """
    try:
        n_params = len(inspect.signature(predict_fn).parameters)
    except (ValueError, TypeError):
        n_params = 1
    if n_params >= 2:
        return float(predict_fn(signal_idx, valence_vector))
    return float(predict_fn(signal_idx))


def valence_prediction_distinctness_test(
    predict_fn: Callable[..., float],
    n_signals: int = 4,
    conditioned_idx: int = 1,
    source_valence: float = 1.0,
    n_condition: int = 50,
    lr: float = 0.1,
    seed: int = 0,
) -> Dict[str, float]:
    """Test de DISTINCTNESS vs prediction (#7740 — le coeur falsifiable).

    L'enjeu #7740 : ``pi_t`` (valence) et ``p_hat`` (prediction) doivent pouvoir
    DIVERGER. Si la valence apprise n'etait qu'un re-vetement de la prediction,
    l'experience manquante serait vide. Ce test construit la divergence :

    - un signal est bien PREDIT (``predict_fn`` eleve, invariant) ;
    - mais sa valence est apprise (monte apres conditionnement) ;
    - donc valence et prediction decorrelent.

    ``predict_fn`` renvoie l'erreur de prediction (0 = prediction parfaite, grande
    = mauvaise prediction) pour le signal ``i``. Deux arites acceptees :

    - ``predict_fn(i)`` : prediction *state-invariant* (ne lit pas la valence).
    - ``predict_fn(i, pi_t)`` : prediction *state-coupled* (peut lire la valence).

    On l'invoque AVANT et APRES le conditionnement en passant le vecteur ``pi_t``
    courant. Un predicteur invariant garde la meme erreur ; un predicteur couple a
    la valence la voit changer. C'est cette possibilite de couplage qui rend le
    verdict REELLEMENT falsifiable : un re-vetement de ``pi`` par ``p_hat`` est
    desormais detectable (le controle negatif
    ``test_coupled_predictor_is_not_distinct`` le prouve).

    Verdict falsifiable
    -------------------
    ``distinct`` est True si et seulement si le signal conditionne voit sa valence
    monter (delta_pi > 0.3) ET son erreur de prediction ne change pas
    (|delta_err| < 1e-6). Un predicteur state-invariant (1 arg) satisfait
    ``delta_err == 0`` -> distinct ; un predicteur state-coupled (>=2 args) qui
    re-vet la valence fait monter ``delta_err`` -> NON distinct.
    """
    lv = LearnedValence(n_signals, lr=lr, rng=np.random.default_rng(seed))
    pre_pi = lv.valence(conditioned_idx)
    pre_err = _call_predict_fn(predict_fn, conditioned_idx, lv.valence_vector())
    lv.condition(conditioned_idx, source_valence=source_valence, steps=n_condition)
    post_pi = lv.valence(conditioned_idx)
    post_err = _call_predict_fn(predict_fn, conditioned_idx, lv.valence_vector())
    delta_pi = post_pi - pre_pi
    delta_err = abs(post_err - pre_err)
    distinct = delta_pi > 0.3 and delta_err < 1e-6
    return {
        "pre_valence": pre_pi,
        "post_valence": post_pi,
        "delta_valence": delta_pi,
        "pre_prediction_error": pre_err,
        "post_prediction_error": post_err,
        "delta_prediction_error": delta_err,
        "distinct": 1.0 if distinct else 0.0,
    }


def extinction_test(
    n_signals: int = 4,
    conditioned_idx: int = 1,
    source_valence: float = 1.0,
    n_condition: int = 50,
    n_extinction: int = 200,
    lr: float = 0.1,
    seed: int = 0,
) -> Dict[str, float]:
    """Test de REVERSIBILITE (#7740 mesure : reversibilite sur suppression).

    Une valence apprise doit pouvoir S'ETEINDRE quand l'association est retiree
    (le signal est presente seul, sans source). Une valence qui ne decroit jamais
    serait un investissement fige (pathologique). Comme acquisition et extinction
    partagent la regle Rescorla-Wagner, presenter le signal seul (source_valence=0)
    ramene pi vers 0.

    Verdict falsifiable
    -------------------
    ``reversible`` est True ssi la valence post-extinction est faible (< 0.1)
    apres avoir ete elevee (> 0.5) post-acquisition.
    """
    lv = LearnedValence(n_signals, lr=lr, rng=np.random.default_rng(seed))
    pre = lv.valence(conditioned_idx)
    lv.condition(conditioned_idx, source_valence=source_valence, steps=n_condition)
    acquired = lv.valence(conditioned_idx)
    # Extinction : signal presente seul (pas de source).
    lv.condition(conditioned_idx, source_valence=0.0, steps=n_extinction)
    extinguished = lv.valence(conditioned_idx)
    reversible = acquired > 0.5 and extinguished < 0.1
    return {
        "pre_valence": pre,
        "acquired_valence": acquired,
        "extinguished_valence": extinguished,
        "reversible": 1.0 if reversible else 0.0,
    }
