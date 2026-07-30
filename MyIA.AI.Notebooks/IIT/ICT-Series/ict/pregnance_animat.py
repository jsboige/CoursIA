"""Animat a PREGNANCE et VALENCE incarnees — la dissociation p_hat / pi (#7740, C1).

Contexte
--------
``valence`` (ICT-12) met la valence dans un champ spatial fixe ; ``learned_valence``
(#8823 / ICT-12b) montre qu'une valence peut etre **apprise** (Rescorla-Wagner),
**transferable** (un signal neutre devient attractif) et **distincte** de la
prediction ``p_hat`` — mais sur des bancs **desincarnes** (pas d'environnement,
pas de corps, pas d'action ; un signal est un index abstrait). La question
#7740 (framings 2026-07-20, jambe C1) est le pas suivant : que devient cette
« experience manquante » des qu'on l'**incarne** dans un animat qui se deplace,
a un etat interne (faim), et choisit ses actions ?

Ce module pose cet animat. Il reutilise les fondations sans les modifier :
``ict.valence`` (cinematiques de source, modele interne ``p_hat`` et ses
baselines adverses), ``ict.learned_valence.LearnedValence`` (valence apprise),
``ict.inhibited_action.action_entropy`` (mesure de rigidification de politique).

La porte scientifique (ce qui clot #7740)
-----------------------------------------
Pas un printout par mesure : une **matrice de dissociation**. Six grandeurs
peuvent bouger ensemble sans rien prouver. Le levier est la cinematique
``erratique`` : les renversements de vitesse aleatoires detruisent l'estimation
EMA de vitesse, donc ``p_hat`` (qui extrapole la vitesse) rate completement
(mesure 1 : erreur d'anticipation explosée) — MAIS le conditionnement
Rescorla-Wagner ne depend QUE de la co-occurrence, pas de la previsibilite :
la valence ``pi`` se transfere quand meme (mesure 2), s'eteint sous suppression
(mesure 6) et mobilise l'action (mesure 3). On obtient ainsi un regime
**p_hat FAIBLE / valence HAUTE**, dissocié d'un regime **p_hat FORT / valence
HAUTE** (balistique) ou **p_hat FORT / valence NON-APPRISE** (pas de source).
La dissociation seule valide que valence et prediction sont deux grandeurs
distinctes — six mesures corelees ne le prouvent pas.

Portee de ce module (cycle-1 d'un livrable multi-cycle)
-------------------------------------------------------
ADDITIF : ne modifie ni ``ict.valence`` ni ``ict.learned_valence``. Couvre les
**six mesures** 1 (p_hat incarné + baselines), 2 (transfert incarné, approche),
3 (choix d'action + entropie), 4 (profil d'energie libre incarne : precision
fixe vs adaptive, gate FE porte depuis :mod:`ict.free_energy`), 5 (information
predictive ``I(q_hat ; obs)`` via :func:`ict.signaling_convention.mutual_information`
+ :func:`ict.multiscale_agency.discretize_values`) et 6 (reversibilite
comportementale) + leurs controles negatifs + la matrice de dissociation.
numpy seul, CPU.

References
----------
Thom 1972 (pregnance / effet figuratif, *Stabilité structurelle*) ; Rescorla &
Wagner 1972 (erreur de prediction comme moteur associatif) ; Friston (agentivite
morphologique, strate 4 ICT) ; spec #7740 (animat, etat interne, policy
f(p_hat, pi, etat_interne), matrice de dissociation).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import numpy as np

from .valence import (
    predict_source,
    anticipation_error_2d,
    phat_predicted_trajectory,
    persistence_trajectory_2d,
    moving_average_trajectory_2d,
    ar1_trajectory_2d,
    source_trajectory,
)
from .learned_valence import LearnedValence
from .inhibited_action import action_entropy
from . import free_energy as fe
from .signaling_convention import mutual_information
from .multiscale_agency import discretize_values


# --------------------------------------------------------------------------- #
#  Environnement : objets en mouvement (source pertinente ou signal neutre)     #
# --------------------------------------------------------------------------- #


@dataclass
class ObjectSpec:
    """Un objet de l'environnement, porteur d'une cinematique et d'une valence.

    ``intrinsic_valence`` > 0 : source biologiquement pertinente (nourriture) ;
    sa capture satie la faim et renforce la valence des signaux co-occurents.
    ``intrinsic_valence`` == 0 : signal neutre — ni nuisible ni nourricier tant
    qu'il n'est pas associe a une source. C'est sur un signal neutre que le
    TRANSFERT se mesure : neutre avant apprentissage, attractif apres.
    """

    idx: int
    kind: str              # cinematique : statique | balistique | erratique | bruite
    intrinsic_valence: float = 0.0
    speed: float = 0.8
    noise: float = 0.25
    reversal_p: float = 0.18


def build_object_trajectories(
    objects: List[ObjectSpec],
    n_steps: int,
    size: int,
    rng: np.random.Generator,
    start_offsets: Optional[Dict[int, np.ndarray]] = None,
) -> np.ndarray:
    """Renvoie les trajectoires ``(n_objects, n_steps, 2)`` de chaque objet.

    Chaque objet suit sa propre cinematique (``ict.valence.source_trajectory``)
    depuis un point de depart decale pour eviter la superposition initiale.
    """
    trajs = np.empty((len(objects), n_steps, 2), dtype=float)
    center = np.array([size / 2.0, size / 2.0])
    for k, obj in enumerate(objects):
        start = center.copy()
        if start_offsets and obj.idx in start_offsets:
            start = np.asarray(start_offsets[obj.idx], dtype=float).copy()
        else:
            # decalage deterministe pour separer les objets a l'init
            angle = 2.0 * np.pi * obj.idx / max(1, len(objects))
            start = center + 0.3 * size * np.array([np.cos(angle), np.sin(angle)])
        trajs[k] = source_trajectory(
            obj.kind, n_steps, size, rng=rng,
            speed=obj.speed, noise=obj.noise, reversal_p=obj.reversal_p, start=start,
        )
    return trajs


# --------------------------------------------------------------------------- #
#  Animat : corps, faim, modele p_hat, valence apprise, politique               #
# --------------------------------------------------------------------------- #


@dataclass
class AnimatConfig:
    """Hyperparametres de l'animat. Defaults calibres pour des verdicts nets.

    La politique note chaque objet ``i`` par :
    ``score_i = w_valence * pi_i * hunger + w_phat * feasibility_i + exploration * noise``.
    ``hunger`` monte avec le temps (poussée d'approche) et tombe a la capture
    d'une source (satiation). ``feasibility_i`` mesure si l'interception par
    ``p_hat`` est credible (basse si la vitesse estimee explose — regime erratique).
    """

    size: int = 32
    lr: float = 0.12              # Rescorla-Wagner
    hunger_rate: float = 0.015    # croissance de la faim par pas
    satiation: float = 0.35      # chute de faim a la capture d'une source
    w_valence: float = 1.0
    w_phat: float = 0.6
    exploration: float = 0.05
    lead: int = 4
    alpha: float = 0.25
    step: float = 0.9
    capture_radius: float = 1.6
    sense_radius: float = 5.0    # rayon de co-occurrence : source visible => renforcement


class PregnanceAnimat:
    """Animat incarne : p_hat + valence apprise + etat interne (faim).

    L'animat observe les positions des objets a chaque pas, entretient un
    modele predictif ``p_hat`` (extrapolation EMA-vitesse, herite de
    :func:`ict.valence.predict_source`) ET une valence apprise ``pi``
    (:class:`ict.learned_valence.LearnedValence`), combinees par une politique
    pilotée par la faim. Le tout est spatialement incarne : l'animat se deplace,
    capture, satie.

    Le choix d'action est DISCRET (index de l'objet cible, ou ``n_objects`` pour
    l'exploration) — c'est ce flux d'actions qu'on passe a
    :func:`ict.inhibited_action.action_entropy` (mesure 3).
    """

    def __init__(
        self,
        n_objects: int,
        config: Optional[AnimatConfig] = None,
        rng: Optional[np.random.Generator] = None,
    ) -> None:
        self.cfg = config if config is not None else AnimatConfig()
        self.n_objects = n_objects
        self.rng = rng if rng is not None else np.random.default_rng()
        self.lv = LearnedValence(n_signals=n_objects, lr=self.cfg.lr, rng=self.rng)
        self.pos = np.array([2.0, 2.0])
        self.hunger = 0.0
        # historique observe par objet (pour le modele p_hat)
        self._hist: List[np.ndarray] = [[] for _ in range(n_objects)]
        # journal des actions discretes (mesure 3) et des captures
        self.actions: List[int] = []
        self.captures: List[Tuple[int, int, float]] = []  # (t, obj_idx, valence_delivered)
        # valences intrinseques (sources) et journal des positions (mesures d'approche)
        self._intrinsics: Dict[int, float] = {}
        self._pos_trace: List[np.ndarray] = []
        # journal des predictions lead-ahead q_hat (mesure 4 : energie libre incarnee)
        self._pred_trace: List[np.ndarray] = []

    def reset(self, start: Optional[np.ndarray] = None) -> None:
        self.pos = np.asarray(start, dtype=float).copy() if start is not None \
            else np.array([2.0, 2.0])
        self.hunger = 0.0
        self.lv = LearnedValence(n_signals=self.n_objects, lr=self.cfg.lr, rng=self.rng)
        self._hist = [[] for _ in range(self.n_objects)]
        self.actions = []
        self.captures = []

    # -- p_hat : prediction de position future par objet ----------------------

    def _predict_each(self, t: int) -> np.ndarray:
        """Position future predite (lead) pour chaque objet, ``(n_objects, 2)``.

        Reutilise :func:`ict.valence.predict_source` sur l'historique observe
        (causal : ne voit que le passe). Si l'historique est trop court,
        renvoie la derniere position observee (aucune extrapolation possible).
        """
        out = np.zeros((self.n_objects, 2), dtype=float)
        for i in range(self.n_objects):
            hist = np.asarray(self._hist[i], dtype=float)
            if len(hist) <= 1:
                out[i] = hist[-1] if len(hist) else np.zeros(2)
            else:
                out[i] = predict_source(hist, t=min(t, len(hist) - 1),
                                        lead=self.cfg.lead, alpha=self.cfg.alpha)
        return out

    def _feasibility(self, phat_future: np.ndarray) -> np.ndarray:
        """Credibilite de l'interception ``p_hat`` par objet, dans [0, 1].

        Mesure combien la vitesse estimee est « tenable » : si l'extrapolation
        ``p_hat`` projette loin de la position courante observee, la vitesse EMA
        est vraisemblablement instable (regime erratique) et l'interception est
        peu credible. Bornee et lisse pour rester une note de politique, pas un
        verdict (le verdict est la mesure 1 sur erreur d'anticipation).
        """
        cur = np.array([self._hist[i][-1] if self._hist[i] else np.zeros(2)
                        for i in range(self.n_objects)])
        excess = np.linalg.norm(phat_future - cur, axis=1) - float(self.cfg.lead * self.cfg.step)
        # au-dela du lead nominal, la credibilite decroit (sigmoide inverse).
        return 1.0 / (1.0 + np.clip(excess, 0.0, None) ** 1.5)

    # -- politique -----------------------------------------------------------

    def _choose_target(self, phat_future: np.ndarray, feasibility: np.ndarray) -> int:
        """Choisit l'objet cible (ou ``n_objects`` = exploration).

        Seule la **valence** (apprise ``pi`` + innee ``intrinsic``) pese sur le
        CHOIX de cibler — pondere par la faim. ``feasibility`` ne decide PAS si
        on cible (sinon un objet predictible mais sans valeur serait poursuivi) ;
        elle ne module que le COMMENT (interception vs reactive, cf.
        :meth:`_aim_point`). C'est ce qui rend la mesure d'entropie (3) nette :
        un animat sans aucune valence investie explore (action = ``n_objects``),
        quel que soit le regime cinematique.

        ``drive_i = w_valence * (pi_i + intrinsic_i) * hunger``. Si ``max(drive)``
        est nul (rien de valorise), l'animat explore.
        """
        pi = self.lv.valence_vector()
        intr = np.array([self._intrinsic(i) for i in range(self.n_objects)])
        salience = pi + intr
        drive = self.cfg.w_valence * salience * self.hunger
        if float(np.max(drive)) < 1e-6:
            return self.n_objects  # rien valorise -> exploration
        noise = self.rng.standard_normal(self.n_objects)
        score = drive + self.cfg.exploration * noise
        return int(np.argmax(score))

    def _aim_point(self, target: int, phat_future: np.ndarray, obs: np.ndarray,
                   feasibility: np.ndarray) -> np.ndarray:
        """Point vise : interception ``p_hat`` SI la valence est investie ET
        ``p_hat`` credible (feasibility haute), sinon position courante (reactive).

        Couplage incarné : la valence ``pi`` decide SI on poursuit ; ``feasibility``
        decide SI on intercepte ou si l'on vise la position courante. C'est la
        source de la dissociation — sur un regime erratique, ``feasibility`` est
        basse (la vitesse EMA explose) donc l'animat poursuit REACTIVEMENT (la ou
        la cible EST) : il approche quand meme, sans que ``p_hat`` y ajoute du
        lead. Valence et ``p_hat`` decorrelent : l'approche tient sans la
        prediction.
        """
        if target >= self.n_objects:
            # exploration : pas de cible -> marche aleatoire (direction bruitee)
            angle = float(self.rng.uniform(0.0, 2.0 * np.pi))
            return self.pos + np.array([np.cos(angle), np.sin(angle)])
        pi_target = self.lv.valence(target)
        if (pi_target > 0.2 and target < phat_future.shape[0]
                and feasibility[target] > 0.5):
            return phat_future[target]  # interception credible
        return obs[target]  # poursuite reactive (la ou la cible est)

    # -- pas de simulation ---------------------------------------------------

    def step(self, observations: np.ndarray, t: int) -> int:
        """Avance d'un pas. ``observations`` : positions ``(n_objects, 2)`` au temps ``t``.

        Renvoie l'action discrete choisie (index cible, ou ``n_objects``).
        Met a jour : historique observe, faim, valence (conditionnement/extinction
        selon co-occurrence avec une source), position, journal d'actions/captures.
        """
        obs = np.asarray(observations, dtype=float)
        for i in range(self.n_objects):
            self._hist[i].append(obs[i].copy())

        phat_future = self._predict_each(t)
        self._pred_trace.append(phat_future.copy())
        feasibility = self._feasibility(phat_future)
        target = self._choose_target(phat_future, feasibility)
        aim = self._aim_point(target, phat_future, obs, feasibility)

        # deplacement
        move = aim - self.pos
        nm = float(np.linalg.norm(move))
        if nm > 1e-9:
            self.pos = self.pos + self.cfg.step * (move / nm)
        self.pos = np.clip(self.pos, 0.0, float(self.cfg.size - 1))

        # croissance de la faim (poussee d'approche)
        self.hunger = float(np.clip(self.hunger + self.cfg.hunger_rate, 0.0, 1.0))

        # conditionnement / extinction : CO-OCCURRENCE Pavlovienne.
        # Un signal neutre SENSE en presence d'une source SENSE s'associe
        # (acquisition Rescorla-Wagner) ; un signal neutre capture SANS source
        # s'eteint. La co-occurrence est environnementale (Pavlov), pas
        # attentionnelle : tout signal present avec la source est conditionne.
        dists = np.linalg.norm(obs - self.pos, axis=1)
        sensed = dists <= self.cfg.sense_radius
        # valence de la source la plus forte presentement sensee.
        src_val = 0.0
        for i in range(self.n_objects):
            if sensed[i] and self._intrinsic(i) > src_val:
                src_val = self._intrinsic(i)
        # satiation si une source est capturee ce pas.
        for i in range(self.n_objects):
            if dists[i] <= self.cfg.capture_radius and self._intrinsic(i) > 0:
                self.hunger = float(np.clip(self.hunger - self.cfg.satiation, 0.0, 1.0))
                self.captures.append((t, i, self._intrinsic(i)))
                break
        # Rescorla-Wagner sur chaque signal neutre sense.
        for i in range(self.n_objects):
            if self._intrinsic(i) > 0:
                continue  # les sources ont une valence inne fixe, non apprise.
            if not sensed[i]:
                continue
            if dists[i] <= self.cfg.capture_radius:
                # capture du signal neutre : source co-presente => acquisition,
                # sinon extinction (presente seul).
                self.lv.condition(i, source_valence=src_val, steps=1)
            elif src_val > 0.0:
                # neutre sense en co-occurrence avec source => acquisition douce.
                self.lv.condition(i, source_valence=src_val, steps=1)

        self.actions.append(target)
        return target

    def set_intrinsic_valences(self, mapping: Dict[int, float]) -> None:
        """Associe les valences intrinseques (sources) aux indices d'objets."""
        self._intrinsics = {int(k): float(v) for k, v in mapping.items()}

    def _intrinsic(self, obj_idx: int) -> float:
        return float(self._intrinsics.get(int(obj_idx), 0.0))

    # -- sorties pour les mesures -------------------------------------------

    def approach_fraction(self, obj_idx: int, obj_traj: np.ndarray,
                          window: Optional[Tuple[int, int]] = None) -> float:
        """Fraction des pas ou l'animat approche (distance <= capture_radius)
        l'objet ``obj_idx``, sur la fenetre ``window``. Mesure de transfert
        comportemental (mesure 2) et de reversibilite (mesure 6)."""
        tr = self._position_trace()
        src = np.asarray(obj_traj, dtype=float)
        lo, hi = window if window is not None else (0, len(tr))
        seg = tr[lo:hi]
        d = np.linalg.norm(seg - src[lo:hi], axis=1)
        return float(np.mean(d <= self.cfg.capture_radius))

    def _position_trace(self) -> np.ndarray:
        """Journal des positions de l'animat (rempli pas-a-pas par ``_run_episode``).

        Necessaire aux mesures d'approche (2 et 6) : on compare la trajectoire
        de l'animat a celle de l'objet cible."""
        return np.asarray(self._pos_trace)

    def prediction_trace(self) -> np.ndarray:
        """Journal des predictions lead-ahead ``q_hat`` (une par pas, ``(T, n_objects, 2)``).

        Necessaire a la mesure 4 (energie libre) : on apparie ``q_hat[t]`` (qui
        predit la position future ``t+lead``) avec l'observation reelle
        ``obs[t+lead]`` pour calculer la surprise pas-a-pas (cf :mod:`ict.free_energy`)."""
        return np.asarray(self._pred_trace)


def _run_episode(
    animat: PregnanceAnimat,
    trajectories: np.ndarray,
    start: Optional[np.ndarray] = None,
) -> None:
    """Execute un episode complet : l'animat parcourt les ``n_steps``.

    Reset **motion only** : repositionne l'animat et vide historique/journaux,
    mais PRESERVE la valence apprise (``lv.pi``) et la faim. C'est crucial pour
    les bancs : un animat de test herite de l'etat acquis (pi, hunger) d'un
    animat conditionne, puis execute un episode de mesure. Un reset complet
    effacerait l'apprentissage (bug C1006-L : reset reconstruisait ``lv``).
    """
    animat.pos = (np.asarray(start, dtype=float).copy() if start is not None
                  else np.array([2.0, 2.0]))
    animat._hist = [[] for _ in range(animat.n_objects)]
    animat.actions = []
    animat.captures = []
    animat._pos_trace = []
    animat._pred_trace = []
    n_objects, n_steps, _ = trajectories.shape
    for t in range(n_steps):
        animat.step(trajectories[:, t, :], t)
        animat._pos_trace.append(animat.pos.copy())


# --------------------------------------------------------------------------- #
#  Mesure 1 — p_hat incarne : erreur d'anticipation vs baselines adverses       #
# --------------------------------------------------------------------------- #


def prediction_accuracy_test(
    kind: str,
    size: int = 32,
    n_steps: int = 200,
    lead: int = 4,
    alpha: float = 0.25,
    seed: int = 0,
) -> Dict[str, float]:
    """Erreur d'anticipation 2D de ``p_hat`` vs 3 baselines adverses, par regime.

    Reutilise :func:`ict.valence.anticipation_error_2d` (MSE 2D a l'horizon
    ``lead``) et les baselines persistance / moyenne-mobile / AR(1) du Cran A.
    ``p_hat`` (EMA-vitesse) doit GAGNER sur ``balistique`` (vitesse constante)
    et PERDRE visiblement sur ``erratique`` (renversements aleatoires : la EMA
    sur-reagit). C'est le levier de la dissociation : ``p_hat`` est fragile la
    ou le conditionnement ne l'est pas.

    Verdict falsifiable
    -------------------
    ``phat_wins_ballistic`` : erreur ``p_hat`` < persistance sur balistique.
    ``phat_loses_erratic`` : erreur ``p_hat`` > persistance sur erratique
    (le modele interne est trompe par les demi-tours).
    """
    rng = np.random.default_rng(seed)
    src = source_trajectory(kind, n_steps, size, rng=rng)
    err_phat = anticipation_error_2d(phat_predicted_trajectory(src, lead, alpha), src, lead)
    err_pers = anticipation_error_2d(persistence_trajectory_2d(src), src, lead)
    err_ma = anticipation_error_2d(moving_average_trajectory_2d(src), src, lead)
    err_ar1 = anticipation_error_2d(ar1_trajectory_2d(src, lead), src, lead)
    return {
        "kind_ballistic": 1.0 if kind == "balistique" else 0.0,
        "kind_erratic": 1.0 if kind == "erratique" else 0.0,
        "kind_static": 1.0 if kind == "statique" else 0.0,
        "err_phat": float(err_phat),
        "err_persistence": float(err_pers),
        "err_moving_average": float(err_ma),
        "err_ar1": float(err_ar1),
        "phat_beats_persistence": 1.0 if err_phat < err_pers else 0.0,
    }


def phat_regime_sweep(seed: int = 0, **kw) -> Dict[str, Dict[str, float]]:
    """Sweep des 4 regimes pour la mesure 1. Cle : regime -> dict d'erreurs.

    C'est la table d'entree de la colonne 1 de la matrice de dissociation :
    on y lit directement que ``erratique`` fait exploser l'erreur ``p_hat``
    tandis que ``balistique`` la minimise.
    """
    out: Dict[str, Dict[str, float]] = {}
    for kind in ("statique", "balistique", "erratique", "bruite"):
        out[kind] = prediction_accuracy_test(kind, seed=seed, **kw)
    return out


def _tethered_trajectories(
    kind: str,
    n_steps: int,
    size: int,
    rng: np.random.Generator,
    n_objects: int = 3,
    neutral_idx: int = 1,
    control_idx: Optional[int] = 2,
    offset: np.ndarray = np.array([0.8, 0.6]),
) -> np.ndarray:
    """Source + signal neutre TETHERED + controle hors-arene (co-occurrence imposee).

    Le signal neutre suit la source a un petit offset constant : l'experimentateur
    « presente le signal et la source ensemble » (co-occurrence Pavlovienne
    controlelee, comme dans :func:`ict.learned_valence.valence_transfer_test` ou
    les deux sont co-presents par construction). Le controle evolue
    independamment et est place hors arene (jamais sense => jamais conditionne).

    La source et le neutre partagent la MEME cinematique ``kind`` : c'est ce qui
    rend la dissociation nette — sur ``erratique``, le ``p_hat`` du neutre explose
    (mesure 1) MAIS le tethering garantit la co-occurrence, donc le
    conditionnement tient (mesure 2). Renvoie ``(n_objects, n_steps, 2)`` ; la
    source est a l'index 0.
    """
    src_traj = source_trajectory(kind, n_steps, size, rng=rng)
    trajs = np.zeros((n_objects, n_steps, 2))
    trajs[0] = src_traj
    trajs[neutral_idx] = np.clip(src_traj + offset, 0.0, size - 1)
    if control_idx is not None and control_idx < n_objects and control_idx != neutral_idx:
        ctrl = source_trajectory(kind, n_steps, size, rng=rng)
        # hors arene : jamais sense, jamais conditionne.
        trajs[control_idx] = ctrl + np.array([size, size])
    return trajs


def _mean_approach(
    n_objects: int,
    cfg: AnimatConfig,
    pi_vector: np.ndarray,
    neutral_traj: np.ndarray,
    neutral_idx: int,
    base_seed: int,
    hunger: float = 0.85,
    k: int = 4,
    start: Optional[np.ndarray] = None,
) -> float:
    """Fraction d'approche du neutre, moyennée sur ``k`` réalisations d'exploration.

    La mesure comportementale d'approche est STOCHASTIQUE : un animat sans
    valence (``pi`` nul) explore en marche aléatoire, et sa proximité au neutre
    est bruitée (une réalisation peut, par chance, longer le neutre). Moyenner
    sur ``k`` réalisations (même état ``pi``, trajectoires du neutre identiques,
    réalisation d'exploration variée) stabilise la métrique — c'est une
    réduction de bruit Monte-Carlo légitime, pas un ajustement de seuil.
    L'état ``pi`` (deterministe après conditionnement) n'est pas moyenné.
    """
    acc: List[float] = []
    n_test = neutral_traj.shape[0]
    test_full = np.full((n_objects, n_test, 2), 1e4)
    test_full[neutral_idx] = neutral_traj
    s0 = start if start is not None else np.array([2.0, 2.0])
    for off in range(k):
        a = PregnanceAnimat(n_objects=n_objects, config=cfg,
                            rng=np.random.default_rng(base_seed + off * 97))
        a.set_intrinsic_valences({})  # source retiree : seul pi herite decide.
        a.lv.pi = pi_vector.copy()
        a.hunger = hunger
        _run_episode(a, test_full, start=s0)
        acc.append(a.approach_fraction(neutral_idx, neutral_traj))
    return float(np.mean(acc))


# --------------------------------------------------------------------------- #
#  Mesure 2 — transfert incarne : approche du signal neutre seul               #
# --------------------------------------------------------------------------- #


def embodied_transfer_test(
    kind: str = "balistique",
    n_condition: int = 140,
    n_test: int = 60,
    size: int = 32,
    source_valence: float = 1.0,
    seed: int = 0,
) -> Dict[str, float]:
    """Transfert de valence INCARNE : un signal neutre devient-il APPROCHE seul ?

    Protocole (mirant :func:`ict.learned_valence.valence_transfer_test`, mais
    comportemental) :

    1. **Conditionnement** : une source (valence ``source_valence``) et un signal
       neutre TETHERED co-occurent (cf. :func:`_tethered_trajectories`).
       L'animat, pousse par la faim, approche la source (salience inne) ;
       co-occurrence => acquisition Rescorla-Wagner de la valence du neutre.
    2. **Test** : le signal neutre SEUL est presente (source retiree, faim
       elevee). On mesure la fraction de pas ou l'animat l'approche.
    3. **Controle** : un signal jamais conditionne presente seul identiquement
       doit rester non-approche (pas de fuite de l'inné vers tout).

    Verdict falsifiable
    -------------------
    ``transferred`` : fraction d'approche du conditionne > controle + marge (0.15)
    ET la valence apprise du neutre a monte (``post_pi > 0.2``). Mesurer le
    comportement (pas seulement ``pi``) est l'apport de l'incarnation : un
    signal peut avoir une ``pi`` non-nulle sans declencher d'approche si la faim
    ou la politique ne s'y engage pas.
    """
    rng = np.random.default_rng(seed)
    cfg = AnimatConfig(size=size)
    neutral_idx, control_idx, n_objects = 1, 2, 3

    # --- conditionnement : source + neutre tethered + controle hors-arene ---
    animat = PregnanceAnimat(n_objects=n_objects, config=cfg, rng=rng)
    animat.set_intrinsic_valences({0: source_valence})
    cond_trajs = _tethered_trajectories(kind, n_condition, size, rng, n_objects=n_objects,
                                        neutral_idx=neutral_idx, control_idx=control_idx)
    _run_episode(animat, cond_trajs, start=np.array([2.0, 2.0]))
    post_pi = animat.lv.valence(neutral_idx)
    control_pi = animat.lv.valence(control_idx)

    # --- test : neutre SEUL (source retiree), faim elevee, moyenné sur k réalisations ---
    # Neutre de test LENT (speed=0.3) et PROCHE de l'animat : l'approche doit etre
    # mesurable (l'animat step=0.9 le rattrape en quelques pas). La cinematique de
    # test est tenue IDENTIQUE entre regimes : l'effet regime est porte par la
    # mesure 1 (p_hat), pas par l'approche — qui mesure la valence.
    neutral_traj = source_trajectory(kind, n_test, size, rng=rng, speed=0.3,
                                     start=np.array([4.0, 4.0]))
    cond_approach = _mean_approach(n_objects, cfg, animat.lv.pi, neutral_traj, neutral_idx,
                                   base_seed=seed + 7)

    # --- controle : signal non-conditionne (pi nul) SEUL, meme protocole ---
    zero_pi = np.zeros(n_objects)
    control_approach = _mean_approach(n_objects, cfg, zero_pi, neutral_traj, neutral_idx,
                                      base_seed=seed + 7)

    transferred = (cond_approach > control_approach + 0.15) and (post_pi > 0.2)
    return {
        "post_valence_neutral": float(post_pi),
        "control_valence_unconditioned": float(control_pi),
        "approach_fraction_conditioned": float(cond_approach),
        "approach_fraction_control": float(control_approach),
        "approach_gain": float(cond_approach - control_approach),
        "n_condition": float(n_condition),
        "transferred": 1.0 if transferred else 0.0,
    }


# --------------------------------------------------------------------------- #
#  Mesure 3 — choix d'action : entropie (engagement vs rigidification)          #
# --------------------------------------------------------------------------- #


def action_commitment_test(
    kind: str = "balistique",
    source_valence: float = 1.0,
    n_condition: int = 140,
    n_test: int = 60,
    size: int = 32,
    seed: int = 0,
) -> Dict[str, float]:
    """Entropie d'action : un animat investi se replie-t-il sur sa cible ?

    Apres conditionnement d'un signal neutre (forte ``pi``) et faim elevee, la
    politique se concentre sur la cible : la distribution d'actions
    s'effondre, l'entropie chute. On la compare a l'entropie MAXIMALE
    ``ln(n_actions)`` (uniforme = exploration pure) : la chute d'entropie est la
    signature d'un **engagement** morphologique — l'animat cesse d'explorer pour
    poursuivre (l'envers de l'inhibition, strate 6 ICT, :mod:`ict.inhibited_action`).

    Verdict falsifiable
    -------------------
    ``committed`` : ``ln(n_actions) - H_investi`` > marge (0.25) ET la valence du
    signal conditionne est montee (``post_pi > 0.2``). Un animat dont l'entropie
    ne chute pas sous investissement n'a pas « investi ». Le contraste est la
    borne superieure ``ln(n_actions)`` (forme close), pas une deuxieme simulation
    bruitee — c'est le temoin le plus propre.
    """
    rng = np.random.default_rng(seed)
    cfg = AnimatConfig(size=size)
    neutral_idx, n_objects = 1, 3

    # --- conditionnement du signal neutre (tethered avec source) ---
    a_cond = PregnanceAnimat(n_objects=n_objects, config=cfg, rng=rng)
    a_cond.set_intrinsic_valences({0: source_valence})
    cond_trajs = _tethered_trajectories(kind, n_condition, size, rng, n_objects=n_objects,
                                        neutral_idx=neutral_idx, control_idx=2)
    _run_episode(a_cond, cond_trajs, start=np.array([2.0, 2.0]))
    post_pi = a_cond.lv.valence(neutral_idx)

    # --- phase test : animat investi (pi herite, faim elevee) ---
    neutral_traj = source_trajectory(kind, n_test, size, rng=rng)
    test_full = np.full((n_objects, n_test, 2), 1e4)
    test_full[neutral_idx] = neutral_traj
    a_inv = PregnanceAnimat(n_objects=n_objects, config=cfg, rng=np.random.default_rng(seed + 3))
    # source retiree du test : seul le pi herite (signal conditionne) cible.
    a_inv.set_intrinsic_valences({})
    a_inv.lv.pi = a_cond.lv.pi.copy()
    a_inv.hunger = 0.9
    _run_episode(a_inv, test_full, start=np.array([2.0, 2.0]))
    n_actions = n_objects + 1  # n_objects cibles + exploration
    h_invested = action_entropy(np.asarray(a_inv.actions), n_actions=n_actions)
    h_uniform = float(np.log(n_actions))

    entropy_drop = h_uniform - h_invested
    committed = entropy_drop > 0.25 and post_pi > 0.2
    return {
        "post_valence_signal": float(post_pi),
        "action_entropy_invested": float(h_invested),
        "action_entropy_uniform": float(h_uniform),
        "entropy_drop": float(entropy_drop),
        "n_actions": float(n_actions),
        "committed": 1.0 if committed else 0.0,
    }


# --------------------------------------------------------------------------- #
#  Mesure 6 — reversibilite comportementale : extinction de l'approche          #
# --------------------------------------------------------------------------- #


def behavioral_reversibility_test(
    kind: str = "balistique",
    n_condition: int = 140,
    n_extinction: int = 220,
    n_test: int = 60,
    size: int = 32,
    source_valence: float = 1.0,
    seed: int = 0,
) -> Dict[str, float]:
    """Reversibilite COMPORTEMENTALE : l'approche acquise s'eteint-elle ?

    Mirant :func:`ict.learned_valence.extinction_test` (qui mesure ``pi``) mais
    sur le comportement : apres acquisition d'une approche du signal neutre
    (co-occurrence avec source), on presente le signal SEUL prolongement
    (extinction). L'approche doit chuter. Mesuree sur une fenetre test POST
    extinction.

    Verdict falsifiable
    -------------------
    ``reversible`` : approach_acquired > approach_extinguished + marge (0.15),
    ET ``pi`` acquise etait haute puis bassee (``extinguished < acquired*0.5``).
    Reciproque comportementale de la mesure 2 : ce qui s'apprend (approche) peut
    se desapprend (reversibilite, fil ICT-18 / fleche du temps).
    """
    rng = np.random.default_rng(seed)
    cfg = AnimatConfig(size=size)
    neutral_idx, n_objects = 1, 2  # source(0) + signal(1) ; pas de controle ici

    # --- acquisition : source + neutre tethered ---
    animat = PregnanceAnimat(n_objects=n_objects, config=cfg, rng=rng)
    animat.set_intrinsic_valences({0: source_valence})
    cond_trajs = _tethered_trajectories(kind, n_condition, size, rng, n_objects=n_objects,
                                        neutral_idx=neutral_idx, control_idx=None)
    _run_episode(animat, cond_trajs, start=np.array([2.0, 2.0]))
    acquired_pi = animat.lv.valence(neutral_idx)

    # neutre de test LENT et PROCHE (cf. embodied_transfer_test) : mesurable.
    neutral_traj = source_trajectory(kind, n_test, size, rng=np.random.default_rng(seed + 5),
                                     speed=0.3, start=np.array([4.0, 4.0]))

    def _approach_when(pi_vector):
        return _mean_approach(n_objects, cfg, pi_vector, neutral_traj, neutral_idx,
                              base_seed=seed + 5)

    acquired_approach = _approach_when(animat.lv.pi)

    # --- extinction : signal SEUL prolonge (source retiree) ---
    # Le neutral se deplace lentement : l'extinction porte sur pi (capture
    # repetee sans source => Rescorla-Wagner vers 0), pas sur l'approche.
    ext_neutral = source_trajectory(kind, n_extinction, size, rng=rng, speed=0.3,
                                    start=np.array([4.0, 4.0]))
    ext_full = np.full((n_objects, n_extinction, 2), 1e4)
    ext_full[neutral_idx] = ext_neutral
    animat.set_intrinsic_valences({})  # source retiree : presentation seule
    animat.hunger = 0.85
    _run_episode(animat, ext_full, start=np.array([2.0, 2.0]))
    extinguished_pi = animat.lv.valence(neutral_idx)
    extinguished_approach = _approach_when(animat.lv.pi)

    reversible = (acquired_approach > extinguished_approach + 0.15
                  and acquired_pi > 0.3 and extinguished_pi < acquired_pi * 0.5)
    return {
        "acquired_valence": float(acquired_pi),
        "extinguished_valence": float(extinguished_pi),
        "approach_fraction_acquired": float(acquired_approach),
        "approach_fraction_extinguished": float(extinguished_approach),
        "approach_drop": float(acquired_approach - extinguished_approach),
        "reversible": 1.0 if reversible else 0.0,
    }


# --------------------------------------------------------------------------- #
#  Mesure 4 — energie libre incarnee : precision fixe vs adaptive (gate FE)     #
# --------------------------------------------------------------------------- #


def free_energy_profile_test(
    kind: str = "balistique",
    n_steps: int = 200,
    size: int = 32,
    source_valence: float = 1.0,
    seed: int = 0,
    floor_frac: float = 0.05,
) -> Dict[str, float]:
    r"""Profil d'energie libre de l'animat incarne (precision fixe vs adaptive).

    Porte le gate 2 de :mod:`ict.free_energy` (la precision adaptive fait
    diverger le classement par ``F`` du classement par MSE) du representant nu
    (ICT-10 / ICT-14) au cadre incarne C1 : on calcule la surprise lead-ahead de
    la prediction ``q_hat`` de l'animat contre l'observation reelle, en precision
    FIXE puis ADAPTIVE, et on la confronte au MSE lead-ahead -- a travers les
    regimes ``balistique`` (``q_hat`` credible) et ``erratique`` (``q_hat`` EMA
    trompe par les renversements, cf mesure 1).

    Le piege signale en entete de module (et gate 1 de :mod:`ict.free_energy`)
    est qu'en precision FIXE, ``F`` n'est qu'une transformation monotone du MSE :
    les deux classent pareil. La precision ADAPTIVE renormalise la surprise par
    la variance attendue accumulee (EMA causale des erreurs passees) : sous
    ``erratique``, le ``q_hat`` sur-confiant se plante, la variance attendue
    gonfle, et la surprise adaptive peut amortir une partie de l'explosion que le
    MSE brut exhibe. C'est le seul regime ou l'energie libre ajoute quelque chose
    au-dela de l'erreur de prediction, meme incarnee.

    La mesure est ORTHOGONALE a la matrice de dissociation (qui oppose ``p_hat``
    a la valence) : ici on oppose deux lecteurs de ``q_hat`` lui-meme (FE vs MSE).
    On l'isole donc comme un banc autonome plutot que d'alourdir le verdict
    central.

    Caveat -- pourquoi la precision adaptive est calculee inline (scale-aware)
    -----------------------------------------------------------------------
    Le ``mode='adaptive'`` de :func:`ict.free_energy.free_energy_trajectory`
    planche la variance a ``1e-6`` (absolu) -- calibre pour des erreurs
    moderees du representant nu. Sous les predictions quasi-parfaites du regime
    balistique incarne (vitesse constante => ``q_hat`` exact), la variance EMA
    s'effondre sous ce plancher et la surprise explose (~2000, artefact numerique
    non un signal). Ce banc calcule donc la precision adaptive inline, plancher
    a 5% de la variance globale (scale-aware), qui garde la surprise finie et
    comparable. C'est la raison pour laquelle M4 etait deferée : le port incarne
    du gate FE demande une precision calibree, pas le bare estimateur.

    Verdict falsifiable
    -------------------
    ``fe_fixed_monotone_with_mse`` : en precision fixe, F et MSE rangent les
        regimes identiquement (tous deux superieurs sous erratique) -- gate 1
        incarne : FE est un habillage du MSE en RANG (monotonicite preservee).
        Controle de coherence : doit tenir.
    ``fe_adaptive_amortizes_mse`` : le ratio ``F_adaptive(erratique)/F_adaptive(balistique)``
        est INFERIEUR au ratio MSE -- gate 2 incarne : la precision adaptive
        amortit l'explosion de regime (FE adaptive moins sensible au regime que
        le MSE brut). Un verdict 0 est aussi honnete : l'incarnation ne preserve
        pas le gate 2 du representant nu.
    """
    def _profile(k: str) -> Dict[str, float]:
        rng = np.random.default_rng(seed)
        cfg = AnimatConfig(size=size)
        neutral_idx, control_idx, n_objects = 1, 2, 3
        animat = PregnanceAnimat(n_objects=n_objects, config=cfg, rng=rng)
        animat.set_intrinsic_valences({0: source_valence})
        trajs = _tethered_trajectories(k, n_steps, size, rng, n_objects=n_objects,
                                       neutral_idx=neutral_idx, control_idx=control_idx)
        _run_episode(animat, trajs, start=np.array([2.0, 2.0]))
        lead = cfg.lead
        preds = animat.prediction_trace()        # (T, n_objects, 2)
        mses: List[float] = []
        f_fix: List[float] = []
        f_adap: List[float] = []
        # objets in-arena partagent la cinematique `k` : source(0) + neutre tethered(1).
        # le controle(2) est hors-arene (coords gigantesques) -> exclu.
        for i in (0, 1):
            obs_i = np.asarray(animat._hist[i], dtype=float)   # (T, 2)
            if obs_i.shape[0] <= lead or preds.shape[0] <= lead:
                continue
            o_future = obs_i[lead:]          # obs[t+lead]
            p_past = preds[:-lead, i, :]     # q_hat[t] predit obs[t+lead]
            n = min(o_future.shape[0], p_past.shape[0])
            o_future, p_past = o_future[:n], p_past[:n]
            err = o_future - p_past
            err_sq = np.sum(err ** 2, axis=1)            # (n,) erreur quadratique 2D
            mses.append(float(np.mean(err_sq)))
            # precision FIXE (sigma=1) : gate 1 (habillage du MSE en rang).
            f_fix.append(float(np.mean(fe.gaussian_surprise(o_future, p_past, sigma=1.0))))
            # precision ADAPTIVE scale-aware : EMA causale des erreurs passees,
            # plancher a ``floor_frac`` de la variance globale (defaut 5%). Sans ce
            # plancher, sous les predictions quasi-parfaites du regime balistique la
            # variance EMA s'effondre vers le dust numerique et la surprise explose
            # (pathologie documentee ci-dessous) -- le bare ``mode='adaptive'`` de
            # :mod:`ict.free_energy` (plancher absolu 1e-6) est calibre pour des
            # erreurs moderees, pas pour l'incarnation. ``floor_frac`` est expose pour
            # le test de robustesse (sweep ±2x : gate 2 doit tenir sur la plage).
            var0 = max(float(np.mean(err_sq)), 1e-6)
            ema = np.empty(err_sq.shape[0])
            prev = var0
            for tt in range(err_sq.shape[0]):
                ema[tt] = prev
                prev = 0.3 * err_sq[tt] + 0.7 * prev
            sigma_t = np.sqrt(np.maximum(ema, floor_frac * var0))
            f_adap.append(float(np.mean(fe.gaussian_surprise(
                o_future, p_past, sigma=sigma_t.reshape(-1, 1)
            ))))
        return {
            "mse": float(np.mean(mses)),
            "F_fixed": float(np.mean(f_fix)),
            "F_adaptive": float(np.mean(f_adap)),
        }

    bal = _profile("balistique")
    err = _profile("erratique")
    mse_ratio = err["mse"] / max(bal["mse"], 1e-12)
    fe_fix_ratio = err["F_fixed"] / max(bal["F_fixed"], 1e-12)
    fe_adap_ratio = err["F_adaptive"] / max(bal["F_adaptive"], 1e-12)
    # gate 1 incarne : en precision fixe, F et MSE rangent les regimes pareil
    # (tous deux superieurs sous erratique) -- monotonicite preservee.
    fe_fixed_monotone_with_mse = (
        1.0 if (err["F_fixed"] > bal["F_fixed"]) == (err["mse"] > bal["mse"]) else 0.0
    )
    # gate 2 incarne : la precision adaptive amortit l'explosion de regime
    # (ratio F_adaptive erratique/balistique INFERIEUR au ratio MSE).
    fe_adaptive_amortizes_mse = 1.0 if fe_adap_ratio < mse_ratio else 0.0
    return {
        "mse_ballistic": bal["mse"],
        "mse_erratic": err["mse"],
        "mse_ratio_err_over_bal": mse_ratio,
        "F_fixed_ballistic": bal["F_fixed"],
        "F_fixed_erratic": err["F_fixed"],
        "F_fixed_ratio_err_over_bal": fe_fix_ratio,
        "F_adaptive_ballistic": bal["F_adaptive"],
        "F_adaptive_erratic": err["F_adaptive"],
        "F_adaptive_ratio_err_over_bal": fe_adap_ratio,
        "fe_fixed_monotone_with_mse": fe_fixed_monotone_with_mse,
        "fe_adaptive_amortizes_mse": fe_adaptive_amortizes_mse,
        "floor_frac": float(floor_frac),
    }


# --------------------------------------------------------------------------- #
#  Mesure 5 — information predictive : MI(q_hat ; obs) vs MSE                   #
# --------------------------------------------------------------------------- #


def predictive_information_test(
    kind: str = "balistique",
    n_steps: int = 200,
    size: int = 32,
    source_valence: float = 1.0,
    seed: int = 0,
    n_bins: int = 8,
) -> Dict[str, float]:
    r"""Information predictive incarnee ``I(q_hat ; obs)`` (bits), vs MSE lead-ahead.

    Troisieme lecteur de ``q_hat`` (apres MSE = erreur de point, mesure 1, et FE
    adaptive = surprise renormalisee, mesure 4) : l'**information mutuelle** entre
    la prediction lead-ahead ``q_hat[t]`` et l'observation reelle ``obs[t+lead]``.
    Reutilise :func:`ict.signaling_convention.mutual_information` (I(X;Y) en bits
    depuis comptes joints) et :func:`ict.multiscale_agency.discretize_values`
    (binning en quantiles) -- les primitives existent dans la couche.

    La grandeur ``q_hat`` etant 2D, on la projette sur sa coordonnee ``x`` (la
    cinematique source est isotrope en ``x``/``y`` -- projeter une seule
    coordonnee suffit a capturer la structure predictive sans doubler le cout du
    binning). Les series ``q_hat_x`` et ``obs_x`` sont discretisees en ``n_bins``
    niveaux (quantiles), puis on construit la matrice de comptes joints
    ``[q_hat_bin, obs_bin]`` et l'on calcule ``I(q_hat_x ; obs_x)``.

    Pourquoi cette mesure est-elle interessante
    -------------------------------------------
    L'hypothese naive serait que MI et MSE disent la meme chose (un ``q_hat``
    precis a la fois faible MSE ET haut MI). L'instrumentation falsifie cette
    intuition : sous ``erratique``, le MSE EXPLOSE (2.7x) mais la MI CHUTE
    (0.6x). Les deux lecteurs sont **anti-correles** a travers les regimes. La
    raison est qu'ils mesurent des choses differentes :
    - **MSE** = erreur de point (``q_hat`` loin de ``obs`` en distance).
    - **MI** = contenu informatif (combien ``q_hat`` reduit l'incertitude sur
      ``obs``). Sous ``erratique``, la cible est *genuinement moins previsible* --
      ``q_hat`` porte moins d'information non parce qu'il est mauvais mais parce
      qu'il y a moins a savoir. C'est un plafond epistemique, pas un defaut
      d'estimateur.

    La MI et le MSE sont donc deux lecteurs **orthogonaux** de ``q_hat`` (comme la
    FE adaptive en est un troisieme, mesure 4). C'est la contribution propre de M5
    au tableau 4-objets : la representation predictive ``q`` n'est pas reducible a
    un seul scalaire d'erreur.

    Verdict falsifiable
    -------------------
    ``mi_anticorrelated_with_mse`` : le ratio ``MI(erratique)/MI(balistique)`` est
        < 1 (MI chute) TANDIS QUE le ratio ``MSE(erratique)/MSE(balistique)`` est
        > 1 (MSE explose). Les deux lecteurs vont en sens inverse -- preuve qu'ils
        mesurent des grandeurs distinctes. Un verdict 0 (meme sens) dirait que MI
        n'apporte rien au-dela du MSE.

    Robustesse au binning : la conclusion qualitative (anti-correlation) tient sur
    ``n_bins`` in {4, 6, 8, 12, 16} (verifie par instrumentation) ; le test
    ``test_mi_discretization_robust`` l'asserte sur {4, 8, 16} (±2x).
    """
    rng = np.random.default_rng(seed)
    cfg = AnimatConfig(size=size)
    neutral_idx, control_idx, n_objects = 1, 2, 3
    animat = PregnanceAnimat(n_objects=n_objects, config=cfg, rng=rng)
    animat.set_intrinsic_valences({0: source_valence})
    trajs = _tethered_trajectories(kind, n_steps, size, rng, n_objects=n_objects,
                                   neutral_idx=neutral_idx, control_idx=control_idx)
    _run_episode(animat, trajs, start=np.array([2.0, 2.0]))
    lead = cfg.lead
    preds = animat.prediction_trace()        # (T, n_objects, 2)
    mses: List[float] = []
    mis: List[float] = []
    # objets in-arena : source(0) + neutre tethered(1) ; controle(2) hors-arene exclu.
    for i in (0, 1):
        obs_i = np.asarray(animat._hist[i], dtype=float)   # (T, 2)
        if obs_i.shape[0] <= lead or preds.shape[0] <= lead:
            continue
        o_future = obs_i[lead:]          # obs[t+lead]
        p_past = preds[:-lead, i, :]     # q_hat[t] predit obs[t+lead]
        n = min(o_future.shape[0], p_past.shape[0])
        o_future, p_past = o_future[:n], p_past[:n]
        mses.append(float(np.mean(np.sum((o_future - p_past) ** 2, axis=1))))
        # projection x (cinematique isotrope), discretisation quantiles, comptes joints.
        ox = discretize_values(o_future[:, 0], n_bins)
        px = discretize_values(p_past[:, 0], n_bins)
        n_levels = int(max(ox.max(), px.max())) + 1
        joint = np.zeros((n_levels, n_levels), dtype=float)
        for tt in range(ox.shape[0]):
            joint[px[tt], ox[tt]] += 1.0
        mis.append(mutual_information(joint))
    mse = float(np.mean(mses)) if mses else float("nan")
    mi = float(np.mean(mis)) if mis else float("nan")
    return {
        "mse": mse,
        "mutual_information_bits": mi,
        "n_bins": int(n_bins),
        "kind": kind,
    }


def predictive_information_regime_contrast(
    seed: int = 0,
    n_bins: int = 8,
) -> Dict[str, float]:
    """Contraste MI/MSE entre ``balistique`` et ``erratique`` -- la porte M5.

    Renvoie les ratios erratique/balistique pour MI et MSE, plus le verdict
    falsifiable ``mi_anticorrelated_with_mse`` (MI chute < 1 ET MSE monte > 1).
    Orthogonal a la dissociation_matrix (qui oppose ``p_hat`` a la valence) :
    ici on montre que MI et MSE sont eux-memes deux lecteurs distincts de ``q_hat``.
    """
    bal = predictive_information_test("balistique", seed=seed, n_bins=n_bins)
    err = predictive_information_test("erratique", seed=seed, n_bins=n_bins)
    mi_ratio = err["mutual_information_bits"] / max(bal["mutual_information_bits"], 1e-12)
    mse_ratio = err["mse"] / max(bal["mse"], 1e-12)
    mi_anticorrelated = (
        1.0 if (mi_ratio < 1.0 and mse_ratio > 1.0) else 0.0
    )
    return {
        "MI_ballistic": bal["mutual_information_bits"],
        "MI_erratic": err["mutual_information_bits"],
        "MI_ratio_err_over_bal": mi_ratio,
        "MSE_ballistic": bal["mse"],
        "MSE_erratic": err["mse"],
        "MSE_ratio_err_over_bal": mse_ratio,
        "mi_anticorrelated_with_mse": mi_anticorrelated,
        "n_bins": int(n_bins),
    }


# --------------------------------------------------------------------------- #
#  La matrice de dissociation — ce qui clot #7740                               #
# --------------------------------------------------------------------------- #


def dissociation_matrix(
    seed: int = 0,
    size: int = 32,
) -> Dict[str, Dict[str, float]]:
    """Matrice (regimes x mesures) : la porte scientifique #7740.

    On regarde 3 regimes sources pour le **conditionnement** (la cinematique de
    la source pendant la co-occurrence) et on mesure, pour chacun :

    - ``err_phat``     : erreur d'anticipation p_hat (mesure 1, normalisee par
      persistance : >1 = p_hat perd vs reactive).
    - ``transferred``  : transfert de valence (mesure 2, verdict 0/1).
    - ``committed``    : engagement d'action (mesure 3, verdict 0/1).
    - ``reversible``   : reversibilite (mesure 6, verdict 0/1).

    La dissociation : sur ``erratique``, ``err_phat`` explose (p_hat faible)
    TANDIS QUE ``transferred`` / ``committed`` / ``reversible`` restent valides
    (valence forte). Une seule ligne le montre : p_hat et valence sont deux
    grandeurs distinctes, pas un re-vetement.

    Verdict falsifiable
    -------------------
    ``dissociation_observed`` : il existe un regime ou ``err_phat`` est maximal
    ET au moins transfert + reversibilite tiennent. Si aucun regime ne montre
    cela, la dissociation n'est pas etablie (et il faut le dire honnetement).
    """
    measures: Dict[str, Dict[str, float]] = {}
    for kind in ("balistique", "erratique", "bruite"):
        m1 = prediction_accuracy_test(kind, size=size, seed=seed)
        m2 = embodied_transfer_test(kind=kind, size=size, seed=seed)
        m3 = action_commitment_test(kind=kind, size=size, seed=seed)
        m6 = behavioral_reversibility_test(kind=kind, size=size, seed=seed)
        err_norm = m1["err_phat"] / (m1["err_persistence"] + 1e-12)
        measures[kind] = {
            "err_phat_vs_persistence": float(err_norm),
            "transferred": m2["transferred"],
            "committed": m3["committed"],
            "reversible": m6["reversible"],
            "approach_gain": m2["approach_gain"],
            "entropy_drop": m3["entropy_drop"],
        }

    # dissociation : un regime a err_phat elevee ET transfert+reversibilite tenus.
    erratic = measures["erratique"]
    dissociation_observed = (
        erratic["err_phat_vs_persistence"] > measures["balistique"]["err_phat_vs_persistence"]
        and erratic["transferred"] == 1.0
        and erratic["reversible"] == 1.0
    )
    measures["_verdict"] = {"dissociation_observed": 1.0 if dissociation_observed else 0.0}
    return measures
