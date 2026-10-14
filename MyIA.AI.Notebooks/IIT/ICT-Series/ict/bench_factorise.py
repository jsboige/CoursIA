"""Banc synthetique factorise pour la triangulation causale (issue #15480).

Le banc produit des sequences dont la factorisation latente est CONNUE :
deux processus generatifs independants, un par facteur. Les etats de belief
exacts se calculent par filtration forward sur chaque facteur separement
(independance des generateurs), sans approximation.

Deux generateurs sont fournis :

- :class:`Mess3` : POMDP a 3 etats caches en cycle (avec probabilite de
  glissement), emissions gaussiennes 1D. La geometrie de belief vit dans le
  2-simplexe.
- :class:`RRXOR` : processus XOR recursif. Bits d'entree iid uniformes
  ``b_t`` ; etat cache ``(b_{t-1}, b_t)`` ; observation ``y_t = b_{t-1} XOR
  b_t``. Le belief exact vit sur les 4 sommets du 3-simplexe.

La classe :class:`FactoredBench` combine deux generateurs quelconques en un
banc a deux facteurs (l'issue nomme ``Mess3 x RRXOR`` ou deux Mess3
independants ; les deux sont couverts par la meme architecture), construit
les jeux vary-one (un facteur gele, l'autre qui varie par seed) et fournit
les beliefs joints exacts comme produit des marginales.

L'engine d'intervention qui consommera ce banc est la couche transversale
#15479 (``ict/causal_engine.py`` + hooks), pas ce module : le banc ne fait
que generer et filtrer.

Regimes generatifs (#15478, suivi #20071) : deux constructions etendent ce
banc au-dela de l'independance des facteurs, chacune exposee avec les memes
interfaces que les generateurs canoniques pour que la couche de mesure s'y
applique sans adaptation --

- :class:`NoisedChannel` : degrade le CANAL D'EMISSION d'un generateur
  (matrice ``E`` ou tenseur d'aretes ``W`` meprises vers l'uniforme, gamma de
  0 a 1) sans toucher aux transitions -- critere « bruit sur le canal
  generatif » ;
- :class:`ConditionalBench` : le token du facteur PARENT selectionne la
  variante d'emission du facteur ENFANT, a marginales appariees exactement --
  critere « structure generative conditionnelle ». Le plancher de Bayes de
  l'enfant conditionnel se lit avec :func:`conditional_child_floor`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Sequence, Tuple

import numpy as np

Array = np.ndarray


class ProcessError(ValueError):
    """Erreur de parametrage ou d'usage d'un generateur du banc."""


@dataclass(frozen=True)
class Mess3_ObsCoupled:
    """Mess3 legacy : 3 etats caches en cycle, emissions GAUSSIENNES 1D.

    DEPRECIE pour les bancs de geometrie de croyance : les emissions
    gaussiennes separees (>= 4 sigma) couplent presque deterministiquement
    observation et etat cache, donc ``obs ~ etat`` et le belief exact
    s'effondre en Dirac (P(s_k | o_0..k) ~ delta_{s_k}). La geometrie
    fractale du simplexe n'a pas lieu d'etre dans ce cas.

    Ce banc reste disponible pour les comparaisons de probe lineaire sur
    signaux continus, mais il NE REMPLACE PAS le Mess3 canonique
    (:class:`Mess3`) pour les tests de belief-state learning.

    Reference : voir :class:`Mess3` (Marzen & Crutchfield 2017 [20] du
    papier 2405.15943).
    """

    stay: float = 0.95
    means: Tuple[float, float, float] = (-0.15, 0.0, 0.15)
    std: float = 0.05
    n_states: int = 3
    name: str = "mess3_obs_coupled"

    def __post_init__(self) -> None:
        if not 0.0 < self.stay < 1.0:
            raise ProcessError(f"stay doit etre dans (0,1), recu {self.stay}")
        if self.std <= 0:
            raise ProcessError(f"std doit etre > 0, recu {self.std}")
        if len(self.means) != self.n_states:
            raise ProcessError("une moyenne par etat requise")

    def transition_matrix(self) -> Array:
        slip = 1.0 - self.stay
        t = np.zeros((self.n_states, self.n_states))
        for i in range(self.n_states):
            t[i, i] = self.stay
            t[i, (i + 1) % self.n_states] = slip
        return t

    def stationary(self) -> Array:
        return np.full(self.n_states, 1.0 / self.n_states)

    def emission_loglik(self, obs: Array) -> Array:
        means = np.asarray(self.means)[None, :]
        return -0.5 * ((obs[:, None] - means) / self.std) ** 2 - np.log(
            self.std * np.sqrt(2.0 * np.pi)
        )

    def sample(self, n: int, seed: int) -> Tuple[Array, Array]:
        rng = np.random.default_rng(seed)
        t = self.transition_matrix()
        states = np.empty(n, dtype=np.int64)
        obs = np.empty(n)
        s = rng.choice(self.n_states, p=self.stationary())
        for k in range(n):
            states[k] = s
            obs[k] = rng.normal(self.means[s], self.std)
            s = rng.choice(self.n_states, p=t[s])
        return states, obs

    def beliefs(self, obs: Array) -> Array:
        if obs.ndim != 1:
            raise ProcessError("Mess3_ObsCoupled.beliefs attend une serie 1D")
        t = self.transition_matrix()
        prior = self.stationary()
        ll = self.emission_loglik(obs)
        out = np.empty((len(obs), self.n_states))
        b = prior
        for k in range(len(obs)):
            pred = b @ t if k > 0 else b
            w = pred * np.exp(ll[k] - ll[k].max())
            z = w.sum()
            if z <= 0.0:
                raise ProcessError(f"log-vraisemblance degeneratee au pas {k}")
            b = w / z
            out[k] = b
        return out


@dataclass(frozen=True)
class Mess3Canonical:
    """Mess3 canonique (Marzen & Crutchfield 2017) : POMDP a 3 etats
    caches en cycle + emissions ternaires DISCRETES non-couplees a l'etat.

    Conformite au papier 2405.15943 §2.2 : l'observation est emise avec une
    matrice d'emission E[y | s] qui n'est ni deterministe (sinon obs = etat)
    ni diagonalement dominante (sinon obs ~ etat avec peu de bruit). On
    prend E[y | s] = (1/3 + delta) sur la diagonale + (1/3 - delta)/(n-1)
    hors diagonale, avec delta = 0.2 (regime intermediaire ou le belief
    vit dans le 2-simplexe sans s'effondrer en Dirac).

    L'observation est un indice dans {0, 1, 2} : alphabet ternaire.
    L'etat cache reste dans {0, 1, 2}. La persistance p_stay = 0.95 assure
    que les trajectoires sont longues (coherence temporelle du belief).

    Reference :
    - Marzen & Crutchfield 2017, "Inference, Prediction, and Animats",
      ref [20] du papier 2405.15943.
    - arXiv:2405.15943 §2.2 (geometrie de croyance dans le simplexe).
    """

    stay: float = 0.95
    emission_diag: float = 0.5  # P(y = s | s) ; off-diag = (1 - diag) / (n - 1)
    n_states: int = 3
    name: str = "mess3_canonical"

    def __post_init__(self) -> None:
        if not 0.0 < self.stay < 1.0:
            raise ProcessError(f"stay doit etre dans (0,1), recu {self.stay}")
        if not (1.0 / self.n_states) < self.emission_diag < 1.0:
            raise ProcessError(
                f"emission_diag doit etre dans (1/{self.n_states}, 1), recu {self.emission_diag}"
            )
        if self.n_states < 2:
            raise ProcessError("n_states doit etre >= 2")

    def transition_matrix(self) -> Array:
        """T[i, j] = P(s_{t+1} = j | s_t = i) : rester, sinon avancer au suivant du cycle."""
        slip = 1.0 - self.stay
        t = np.zeros((self.n_states, self.n_states))
        for i in range(self.n_states):
            t[i, i] = self.stay
            t[i, (i + 1) % self.n_states] = slip
        return t

    def stationary(self) -> Array:
        return np.full(self.n_states, 1.0 / self.n_states)

    def emission_matrix(self) -> Array:
        """E[i, y] = P(y_t = y | s_t = i) : matrice stochastique.

        Diagonale : ``emission_diag`` (P(y = s | s)). Hors diagonale :
        ``(1 - emission_diag) / (n - 1)``. Pour n=3 et emission_diag=0.5,
        la diagonale domine moderement (50% que obs = etat), laissant 50%
        que obs soit l'un des 2 autres etats. Le belief vit alors dans le
        2-simplexe sans s'effondrer en Dirac (qui aurait emission_diag=1.0).
        """
        n = self.n_states
        diag = self.emission_diag
        off = (1.0 - diag) / (n - 1)
        e = np.full((n, n), off)
        for i in range(n):
            e[i, i] = diag
        return e

    def sample(self, n: int, seed: int) -> Tuple[Array, Array]:
        """Echantillonne n pas. Retourne (etats, observations) en indices entiers."""
        rng = np.random.default_rng(seed)
        t = self.transition_matrix()
        e = self.emission_matrix()
        states = np.empty(n, dtype=np.int64)
        obs = np.empty(n, dtype=np.int64)
        s = rng.choice(self.n_states, p=self.stationary())
        for k in range(n):
            states[k] = s
            obs[k] = rng.choice(self.n_states, p=e[s])
            s = rng.choice(self.n_states, p=t[s])
        return states, obs

    def beliefs(self, obs: Array) -> Array:
        """Filtration forward exacte : belief[k] = P(s_k | obs_{0..k}), forme (T, n_states)."""
        if obs.ndim != 1:
            raise ProcessError("Mess3Canonical.beliefs attend une serie 1D")
        if not np.all(np.isin(obs, np.arange(self.n_states))):
            raise ProcessError(
                f"observations doivent etre dans {{0,..,{self.n_states - 1}}}"
            )
        t = self.transition_matrix()
        e = self.emission_matrix()
        prior = self.stationary()
        out = np.empty((len(obs), self.n_states))
        b = prior
        for k in range(len(obs)):
            pred = b @ t if k > 0 else b
            w = pred * e[:, int(obs[k])]
            z = w.sum()
            if z <= 0.0:
                raise ProcessError(f"vraisemblance nulle au pas {k}")
            b = w / z
            out[k] = b
        return out


# Alias canonique (#16225) : ``Mess3`` designe le generateur CONFORME a la
# litterature -- alphabet discret ternaire qui ne revele pas l'etat cache.
# Le banc gaussien historique reste disponible sous son nom explicite
# ``Mess3_ObsCoupled`` pour les comparaisons de probe sur signaux continus.
Mess3 = Mess3Canonical  # noqa: F811 — un seul generateur Mess3 par defaut


@dataclass(frozen=True)
class RRXOR:
    """RRXOR (Riechers & Crutchfield 2018, arXiv:1706.00883v1, Fig. 4).

    Le processus repete trois etapes : (i) un 0 ou 1 equiprobable ``r1``,
    (ii) un autre 0 ou 1 equiprobable ``r2``, (iii) le XOR des deux derniers
    symboles ``r1 XOR r2``. Correlations par paires nulles, spectre plat :
    toute la structure vit dans la contrainte de triplet.

    L'epsilon-machine compte **5 etats causaux** et est **Mealy** : les
    emissions vivent sur les aretes, pas dans les etats. Etats ordonnes :

    - ``0`` = G (phase de reset, va emettre ``r1``),
    - ``1`` = A0, ``2`` = A1 (memorise ``r1``),
    - ``3`` = X0, ``4`` = X1 (memorise ``r1 XOR r2``, va emettre le XOR).

    Aretes : ``G -(r1, 1/2)-> A_{r1}`` ; ``A_{r1} -(r2, 1/2)-> X_{r1 XOR r2}`` ;
    ``X_v -(v, 1)-> G``. La MSP depuis le prior stationnaire compte 36
    croyances distinctes (31 transitoires + 5 recurrentes, cf. p. 17 de
    l'article) : le regime transitoire resout l'ambiguite de phase du
    processus periodise d'ordre 3.

    Note : la version anterieure de cette classe modelisait
    ``y_t = b_{t-1} XOR b_t`` sur bits iid -- un processus **iid** (les XOR
    adjacents de bits iid sont independants), sans aucune structure. Le banc
    ne meritait pas son nom ; cette version est conforme a la litterature.
    """

    n_states: int = 5
    name: str = "rrxor"

    def edge_tensor(self) -> Array:
        """Tenseur W[s, s', y] = P(transiter s -> s' en emettant y) (Mealy)."""
        w = np.zeros((5, 5, 2))
        w[0, 1, 0] = 0.5; w[0, 2, 1] = 0.5          # G -> A_{r1}
        w[1, 3, 0] = 0.5; w[1, 4, 1] = 0.5          # A0 -> X_{0 XOR r2}
        w[2, 4, 0] = 0.5; w[2, 3, 1] = 0.5          # A1 -> X_{1 XOR r2}
        w[3, 0, 0] = 1.0                            # X0 emet 0 -> G
        w[4, 0, 1] = 1.0                            # X1 emet 1 -> G
        return w

    def transition_matrix(self) -> Array:
        """T[s, s'] = somme des emissions de l'arete (machine agregnee)."""
        return self.edge_tensor().sum(axis=2)

    def stationary(self) -> Array:
        """Distribution stationnaire : (1/3 sur G, 1/6 sur chaque autre etat)."""
        out = np.full(5, 1.0 / 6.0)
        out[0] = 1.0 / 3.0
        return out

    def sample(self, n: int, seed: int) -> Tuple[Array, Array]:
        """Echantillonne n symboles ; retourne (etats d'arrivee par pas, observations)."""
        if n < 1:
            raise ProcessError("RRXOR.sample attend n >= 1")
        rng = np.random.default_rng(seed)
        states = np.empty(n, dtype=np.int64)
        obs = np.empty(n, dtype=np.int64)
        s = 0  # G
        for k in range(n):
            if s == 0:                                # emet r1
                y = int(rng.integers(0, 2))
                s = 1 + y                             # A_{r1}
            elif s in (1, 2):                         # emet r2
                y = int(rng.integers(0, 2))
                s = 3 + ((1 if s == 2 else 0) ^ y)    # X_{r1 XOR r2}
            else:                                     # X : emet le XOR memorise
                y = s - 3
                s = 0
            obs[k] = y
            states[k] = s
        return states, obs

    def beliefs(self, obs: Array) -> Array:
        """Filtration forward exacte sur les aretes (Mealy).

        ``out[k] = P(s_k | y_0..y_k)`` ou ``s_k`` est l'etat d'arrivee du
        symbole ``y_k`` ; mise a jour ``b <- normaliser(b @ W[:, :, y])``
        depuis le prior stationnaire sur l'etat emetteur initial.
        """
        if obs.ndim != 1 or not np.all(np.isin(obs, (0, 1))):
            raise ProcessError("RRXOR.beliefs attend une serie binaire 1D")
        w = self.edge_tensor()
        b = self.stationary()
        out = np.empty((len(obs), 5))
        for k in range(len(obs)):
            v = b @ w[:, :, int(obs[k])]
            b = v / v.sum()
            out[k] = b
        return out


@dataclass(frozen=True)
class RRXOR_Iid:
    """RRXOR legacy : bits iid ``b_t``, observation ``y_t = b_{t-1} XOR b_t``.

    DEPRECIE : les XOR adjacents de bits iid sont eux-memes iid -- ce banc
    ne portait AUCUNE structure et ne meritait pas le nom RRXOR (cf.
    :class:`RRXOR`, conforme a Riechers & Crutchfield 2018). Conserve pour
    la REPRODUCTIBILITE de la batterie d'intervention (#15480/#16230) et du
    pilote ICT-40, calibres sur ce banc ; toute nouvelle etude doit utiliser
    :class:`RRXOR`.
    """

    n_states: int = 4
    name: str = "rrxor_iid"

    def transition_matrix(self) -> Array:
        """T[(a,b) -> (b,c)] = 1/2 pour c dans {0,1} : le bit frais est iid uniforme."""
        t = np.zeros((4, 4))
        for a in (0, 1):
            for b in (0, 1):
                for c in (0, 1):
                    t[2 * a + b, 2 * b + c] = 0.5
        return t

    def stationary(self) -> Array:
        return np.full(4, 0.25)

    def emission_matrix(self) -> Array:
        """E[i, y] = P(y_t = y | etat i) : deterministe, y = a XOR b."""
        e = np.zeros((4, 2))
        for a in (0, 1):
            for b in (0, 1):
                e[2 * a + b, a ^ b] = 1.0
        return e

    def sample(self, n: int, seed: int) -> Tuple[Array, Array]:
        """Echantillonne n bits iid + l'observation XOR ; retourne (etats (b_{t-1}, b_t), y)."""
        rng = np.random.default_rng(seed)
        bits = rng.integers(0, 2, size=n + 1)
        states = 2 * bits[:-1] + bits[1:]
        obs = bits[:-1] ^ bits[1:]
        return states, obs

    def beliefs(self, obs: Array) -> Array:
        """Filtration forward exacte sur les 4 etats ; observation binaire deterministe."""
        if obs.ndim != 1 or not np.all(np.isin(obs, (0, 1))):
            raise ProcessError("RRXOR_Iid.beliefs attend une serie binaire 1D")
        t = self.transition_matrix()
        e = self.emission_matrix()
        prior = self.stationary()
        out = np.empty((len(obs), 4))
        b = prior
        for k in range(len(obs)):
            pred = b @ t if k > 0 else b
            w = pred * e[:, int(obs[k])]
            b = w / w.sum()
            out[k] = b
        return out


@dataclass(frozen=True)
class NoisedChannel:
    """Processus dont le CANAL D'EMISSION est degrade (regime generatif, #20071).

    Le bruit porte sur les emissions du generateur -- la matrice d'emission
    ``E`` (Moore) ou les distributions d'aretes ``W`` (Mealy) -- et sur RIEN
    d'autre : chaque ligne d'emission est meprisee vers l'uniforme,

        E_gamma[i, :] = (1 - gamma) * E[i, :] + gamma * uniforme,

    ce qui degrade le canal de facon monotone en information : ``gamma = 0``
    reproduit le processus d'origine (meme loi), ``gamma = 1`` rend les
    emissions muettes sur l'etat cache. Les TRANSITIONS ne changent pas --
    pour un Mealy, la mixture est prise CONDITIONNELLEMENT a l'arete, donc le
    tenseur somme ``T = sum_y W`` est preserve exactement. La dynamique
    latente reste intacte ; c'est la LISIBILITE des facteurs qui s'effondre.
    C'est l'objet du critere « bruit sur le canal generatif » (#15478, suivi
    #20071) : contrairement au bruit additif sur les activations, l'objection
    porte ici sur le PROCESSUS lui-meme.

    Le wrapper expose l'interface complete d'un generateur (``sample``,
    ``beliefs``, ``emission_matrix``/``edge_tensor``, ``transition_matrix``,
    ``stationary``), donc la couche de mesure
    (``factor_geometry_trained.bayes_floor`` via ``predictive_matrix``)
    s'applique SANS adaptation : le plancher de Bayes du processus bruite est
    lu sur ses propres emissions degradees, exactement.

    Les generateurs a emissions continues (``Mess3_ObsCoupled``) n'exposent
    ni matrice ni tenseur : refuses a la construction.
    """

    wrapped: object
    gamma: float = 0.0

    def __post_init__(self) -> None:
        if not 0.0 <= self.gamma <= 1.0:
            raise ProcessError(f"gamma doit etre dans [0, 1], recu {self.gamma}")
        for attr in ("sample", "beliefs", "transition_matrix", "stationary", "n_states", "name"):
            if not hasattr(self.wrapped, attr):
                raise ProcessError(
                    f"{type(self.wrapped).__name__} n'expose pas '{attr}' : generateur incompatible"
                )
        if not hasattr(self.wrapped, "emission_matrix") and not hasattr(self.wrapped, "edge_tensor"):
            raise ProcessError(
                "NoisedChannel exige un processus parametre (emission_matrix Moore "
                "ou edge_tensor Mealy) ; les emissions continues ne sont pas supportees"
            )

    @property
    def n_states(self) -> int:
        return self.wrapped.n_states

    @property
    def name(self) -> str:
        return f"{self.wrapped.name}_canal(gamma={self.gamma:g})"

    def _is_moore(self) -> bool:
        return hasattr(self.wrapped, "emission_matrix")

    def __getattr__(self, item: str):
        """Duck-typing honnete : le wrapper n'expose QUE l'interface du type emballe.

        ``emission_matrix`` n'existe PAS sur un wrapper Mealy (et
        reciproquement pour ``edge_tensor``) : les consommateurs qui
        discriminent par ``hasattr`` -- dont ``factor_geometry_trained.
        predictive_matrix`` -- doivent voir le BON type, pas un objet qui
        expose les deux et leve selon l'appel.
        """
        if item == "emission_matrix":
            if self._is_moore():
                return self._noised_emission_matrix
            raise AttributeError(
                f"{type(self).__name__} emballe un Mealy : pas de emission_matrix"
            )
        if item == "edge_tensor":
            if not self._is_moore():
                return self._noised_edge_tensor
            raise AttributeError(
                f"{type(self).__name__} emballe un Moore : pas de edge_tensor"
            )
        raise AttributeError(f"{type(self).__name__} n'a pas d'attribut {item!r}")

    def _noised_emission_matrix(self) -> Array:
        """E_gamma : chaque ligne meprisee vers l'uniforme (processus Moore)."""
        e = np.asarray(self.wrapped.emission_matrix(), dtype=np.float64)
        u = np.full_like(e, 1.0 / e.shape[1])
        return (1.0 - self.gamma) * e + self.gamma * u

    def _noised_edge_tensor(self) -> Array:
        """W_gamma : distribution d'arete meprisee vers l'uniforme (processus Mealy).

        La mixture est conditionnelle a l'arete : pour chaque couple
        ``(s, s')`` de masse ``m > 0``, la distribution sur ``y`` devient
        ``(1 - gamma) * W[s, s', :]/m + gamma * uniforme``, donc la masse de
        l'arete -- et la matrice de transition somme -- est inchangee.
        """
        w = np.asarray(self.wrapped.edge_tensor(), dtype=np.float64)
        out = w.copy()
        u = 1.0 / w.shape[2]
        for i in range(w.shape[0]):
            for j in range(w.shape[1]):
                m = w[i, j, :].sum()
                if m > 0.0:
                    out[i, j, :] = (1.0 - self.gamma) * w[i, j, :] + self.gamma * m * u
        return out

    def transition_matrix(self) -> Array:
        """Deleguee : le canal bruite ne touche pas aux transitions."""
        return np.asarray(self.wrapped.transition_matrix(), dtype=np.float64)

    def stationary(self) -> Array:
        return np.asarray(self.wrapped.stationary(), dtype=np.float64)

    def sample(self, n: int, seed: int) -> Tuple[Array, Array]:
        """Echantillonne le processus bruite : dynamique d'origine, emissions degradees.

        Moore : ``s ~ pi``, ``y ~ E_gamma[s]``, ``s' ~ T[s]``.
        Mealy : ``s ~ pi``, puis ``(s', y) ~ W_gamma[s]`` tire conjointement.
        En ``gamma = 0`` la LOI est celle du processus d'origine (les tirages
        diffèrent, l'echantillonneur etant natif).
        """
        if n < 1:
            raise ProcessError("NoisedChannel.sample attend n >= 1")
        rng = np.random.default_rng(seed)
        states = np.empty(n, dtype=np.int64)
        obs = np.empty(n, dtype=np.int64)
        pi = self.stationary()
        if self._is_moore():
            t = self.transition_matrix()
            e = self.emission_matrix()
            s = rng.choice(self.n_states, p=pi / pi.sum())
            for k in range(n):
                states[k] = s
                obs[k] = rng.choice(e.shape[1], p=e[s])
                s = rng.choice(self.n_states, p=t[s])
        else:
            w = self.edge_tensor()
            s = rng.choice(self.n_states, p=pi / pi.sum())
            for k in range(n):
                line = w[s].reshape(-1)
                flat = rng.choice(line.size, p=line / line.sum())
                obs[k] = flat % w.shape[2]
                s = flat // w.shape[2]
                states[k] = s  # etat d'ARRIVEE par pas, convention RRXOR
        return states, obs

    def beliefs(self, obs: Array) -> Array:
        """Filtration forward exacte SUR LES EMISSIONS DEGRADEES.

        Moore : ``b_k ∝ (b_{k-1} T) * E_gamma[:, y_k]``.
        Mealy : ``b_k ∝ b_{k-1} @ W_gamma[:, :, y_k]`` (etat d'arrivee).
        Le filtre utilise le modele bruite -- c'est le meilleur filtre du
        processus bruite, pas une approximation du filtre d'origine.
        """
        if obs.ndim != 1:
            raise ProcessError("NoisedChannel.beliefs attend une serie 1D")
        t = self.transition_matrix()
        out = np.empty((len(obs), self.n_states))
        if self._is_moore():
            e = self.emission_matrix()
            if not np.all(np.isin(obs, np.arange(e.shape[1]))):
                raise ProcessError(f"observations hors alphabet {{0..{e.shape[1] - 1}}}")
            b = self.stationary()
            for k in range(len(obs)):
                pred = b @ t if k > 0 else b
                w = pred * e[:, int(obs[k])]
                z = w.sum()
                if z <= 0.0:
                    raise ProcessError(f"vraisemblance nulle au pas {k}")
                b = w / z
                out[k] = b
        else:
            w = self.edge_tensor()
            if not np.all(np.isin(obs, np.arange(w.shape[2]))):
                raise ProcessError(f"observations hors alphabet {{0..{w.shape[2] - 1}}}")
            b = self.stationary()
            for k in range(len(obs)):
                v = b @ w[:, :, int(obs[k])]
                z = v.sum()
                if z <= 0.0:
                    raise ProcessError(f"vraisemblance nulle au pas {k}")
                b = v / z
                out[k] = b
        return out


@dataclass
class FactoredBench:
    """Banc a deux facteurs independants, factorisation latente connue.

    Chaque pas produit l'observation jointe ``(obs_A[t], obs_B[t])``. Les
    beliefs joints exacts sont le produit des beliefs marginaux (independance
    des generateurs) : ``P(s_A, s_B | o_{0..t}) = P(s_A|o_A) P(s_B|o_B)``.
    """

    factor_a: object
    factor_b: object
    name: str = "bench"

    def __post_init__(self) -> None:
        requis = ("sample", "beliefs", "n_states", "name")
        for p in (self.factor_a, self.factor_b):
            for attr in requis:
                if not hasattr(p, attr):
                    raise ProcessError(
                        f"{type(p).__name__} n'expose pas '{attr}' : generateur incompatible"
                    )

    # --- generation jointe --------------------------------------------------
    def sample(self, n: int, seed_a: int, seed_b: int) -> Dict[str, Array]:
        """Echantillonne les deux facteurs independamment ; trajectoires et observations jointes."""
        sa, oa = self.factor_a.sample(n, seed_a)
        sb, ob = self.factor_b.sample(n, seed_b)
        return {
            "states_a": sa,
            "states_b": sb,
            "obs_a": oa,
            "obs_b": ob,
            "obs_joint": np.stack([oa, ob], axis=1),
        }

    def beliefs(self, obs_a: Array, obs_b: Array) -> Dict[str, Array]:
        """Beliefs marginaux exacts par facteur, et belief joint = produit (independance)."""
        ba = self.factor_a.beliefs(obs_a)
        bb = self.factor_b.beliefs(obs_b)
        joint = (ba[:, :, None] * bb[:, None, :]).reshape(len(ba), -1)
        return {"belief_a": ba, "belief_b": bb, "belief_joint": joint}

    # --- protocole vary-one ---------------------------------------------------
    def vary_one(
        self,
        n: int,
        frozen: str,
        seed_frozen: int,
        seeds_varying: Sequence[int],
    ) -> Dict[str, object]:
        """Jeu vary-one : la trajectoire du facteur gele est identique sur toutes
        les repliques, celle du facteur libre varie par seed.

        ``frozen`` vaut ``"a"`` ou ``"b"`` ; retourne la trajectoire gelee et la
        liste des trajectoires libres.
        """
        if frozen not in ("a", "b"):
            raise ProcessError(f"frozen doit valoir 'a' ou 'b', recu {frozen!r}")
        frozen_proc = self.factor_a if frozen == "a" else self.factor_b
        varying_proc = self.factor_b if frozen == "a" else self.factor_a
        fixed_states, fixed_obs = frozen_proc.sample(n, seed_frozen)
        reps = [varying_proc.sample(n, s) for s in seeds_varying]
        return {
            "frozen": frozen,
            "fixed_states": fixed_states,
            "fixed_obs": fixed_obs,
            "varying_states": [r[0] for r in reps],
            "varying_obs": [r[1] for r in reps],
            "seeds_varying": list(seeds_varying),
        }


@dataclass(frozen=True)
class ConditionalBench:
    """Banc a deux facteurs DEPENDANTS PAR LA DONNEE (regime generatif, #20071).

    Le token du facteur PARENT selectionne la variante d'emission du facteur
    ENFANT, a MARGINALES APPARIEES exactement :

    - le parent (canal A) est un generateur quelconque, NON MODIFIE ;
    - l'enfant (canal B) est un processus MOORE dont la matrice d'emission
      prend ``q`` variantes -- une par symbole du parent -- construites par
      ROTATION CYCLIQUE de la perturbation ``Delta`` :

          E_v = E + kappa * roll(Delta, v, colonnes),   v = 0..q-1,

      ou ``Delta`` deplace de la masse du symbole ``(i+2) % q`` vers le
      symbole voisin ``(i+1) % q`` de chaque ligne ``i``. Les ``q``
      rotations d'une ligne de somme nulle s'annulent : ``somme_v E_v = q E``
      EXACTEMENT ;
    - au pas ``t``, la variante active est ``E_{v_t}`` avec ``v_t = obs_a[t]``
      -- le TOKEN OBSERVE du parent, pas son etat cache : la selection est
      donc lisible depuis la seule donnee.

    Appariement exact des marginales : si les tokens du parent sont
    equiprobables (verifie a la construction), le melange des variantes
    reconstruit ``E`` au sens exact -- la marginal de l'enfant, prise seule,
    est IDENTIQUE a celle du banc independant, sans approximation
    asymptotique. Toute la difference vit dans la loi JOINTE : l'enfant est
    pleinement lisible qu'a travers le token du parent, et un modele qui
    encode la dependance obtient un ``additivity_gap`` strictement negatif la
    ou un modele aveugle aux variants plafonne a zero. C'est l'objet du
    critere « structure generative conditionnelle » (#15478, suivi #20071).

    Contraintes de construction : parent a tokens equiprobables SUR LE MEME
    ALPHABET que l'enfant (le token doit indexer les variantes), enfant Moore
    parametre, ``kappa`` assez petit pour que chaque variante reste
    stochastique.
    """

    parent: object
    child: object
    kappa: float = 0.2
    name: str = "bench_conditionnel"

    def __post_init__(self) -> None:
        for attr in ("sample", "beliefs", "n_states", "name"):
            if not hasattr(self.parent, attr):
                raise ProcessError(
                    f"parent {type(self.parent).__name__} n'expose pas '{attr}' : incompatible"
                )
        for attr in ("sample", "beliefs", "n_states", "name", "transition_matrix", "stationary", "emission_matrix"):
            if not hasattr(self.child, attr):
                raise ProcessError(
                    f"enfant {type(self.child).__name__} n'expose pas '{attr}' : "
                    "ConditionalBench exige un processus Moore parametre"
                )
        e = np.asarray(self.child.emission_matrix(), dtype=np.float64)
        if e.shape[1] < 3:
            raise ProcessError(
                f"perturbation cyclique definie pour au moins 3 symboles, recu {e.shape[1]}"
            )
        for v in self.emission_variants():
            if (v < -1e-12).any() or (v > 1.0 + 1e-12).any():
                raise ProcessError(
                    f"kappa={self.kappa} invalide : une variante n'est pas stochastique "
                    "(bornes [0, 1] hors de portee)"
                )
        # condition d'appariement exact : tokens du parent equiprobables.
        pi_tok = _token_marginal(self.parent)
        q = e.shape[1]
        if not np.allclose(pi_tok, 1.0 / pi_tok.size, atol=1e-9):
            raise ProcessError(
                "marginales appariees exigees : les tokens du parent ne sont pas "
                f"equiprobables ({np.round(pi_tok, 4).tolist()})"
            )
        if pi_tok.size != q:
            raise ProcessError(
                f"parent ({pi_tok.size} symboles) et enfant ({q} symboles) : "
                "le token parent doit indexer les variantes de l'enfant"
            )

    @property
    def n_states(self) -> int:
        """Nombre d'etats caches JOINT (parent x enfant), comme FactoredBench."""
        return self.parent.n_states * self.child.n_states

    def emission_variants(self) -> Tuple[Array, ...]:
        """Les ``q`` matrices d'emission de l'enfant (une par token parent)."""
        e = np.asarray(self.child.emission_matrix(), dtype=np.float64)
        delta = cyclic_perturbation(e.shape[1])
        return tuple(e + self.kappa * np.roll(delta, v, axis=1) for v in range(e.shape[1]))

    def marginal_child(self) -> Array:
        """E reconstruite par melange uniforme des variantes : egalite exacte."""
        variants = self.emission_variants()
        return np.mean(np.stack(variants, axis=0), axis=0)

    def sample(self, n: int, seed_parent: int, seed_child: int) -> Dict[str, Array]:
        """Trajectoire jointe : parent non modifie, enfant redessine par variant.

        Les etats caches de l'enfant suivent SES PROPRES transitions (la
        chaine n'est pas touchee) ; seule l'emission depend du token parent :
        ``obs_b[t] ~ E_{obs_a[t]}[states_b[t], :]``. La loi de l'enfant prise
        seule est celle du banc independant ; la loi jointe porte la
        dependance.
        """
        if n < 1:
            raise ProcessError("ConditionalBench.sample attend n >= 1")
        _, obs_a = self.parent.sample(n, seed_parent)
        states_b, _ = self.child.sample(n, seed_child)
        variants = self.emission_variants()
        rng = np.random.default_rng(seed_child + 10_003)
        obs_b = np.empty(n, dtype=np.int64)
        for t in range(n):
            v = int(obs_a[t])
            obs_b[t] = rng.choice(variants[v].shape[1], p=variants[v][states_b[t]])
        return {
            "obs_a": obs_a,
            "obs_b": obs_b,
            "states_a": None,
            "states_b": states_b,
            "variant_tokens": obs_a.copy(),
        }

    def beliefs(self, obs_a: Array, obs_b: Array) -> Dict[str, Array]:
        """Beliefs EXACTS des deux facteurs.

        Parent : filtration propre, inchangee (le parent ignore l'enfant).
        Enfant : filtration forward a EMISSION VARIANT TEMPS-VARIABLE -- la
        variante ``v_t = obs_a[t]`` est OBSERVEE, donc le filtre

            b_t ∝ (b_{t-1} T_enfant) * E_{v_t}[:, y_t]

        est exact, sans approximation : c'est le meilleur filtre du processus
        conditionnel, celui que le plancher de Bayes mesure.
        """
        if obs_a.ndim != 1 or obs_b.ndim != 1 or len(obs_a) != len(obs_b):
            raise ProcessError("beliefs attend deux series 1D de meme longueur")
        if not np.all(np.isin(obs_a, np.arange(len(self.emission_variants())))):
            raise ProcessError("tokens parents hors alphabet des variants")
        belief_a = self.parent.beliefs(obs_a)
        variants = self.emission_variants()
        t_child = np.asarray(self.child.transition_matrix(), dtype=np.float64)
        if not np.all(np.isin(obs_b, np.arange(variants[0].shape[1]))):
            raise ProcessError(f"observations enfant hors alphabet {{0..{variants[0].shape[1] - 1}}}")
        b = np.asarray(self.child.stationary(), dtype=np.float64)
        out = np.empty((len(obs_b), self.child.n_states))
        for k in range(len(obs_b)):
            pred = b @ t_child if k > 0 else b
            v = int(obs_a[k])
            w = pred * variants[v][:, int(obs_b[k])]
            z = w.sum()
            if z <= 0.0:
                raise ProcessError(f"vraisemblance nulle au pas {k}")
            b = w / z
            out[k] = b
        joint = np.einsum("ti,tj->tij", belief_a, out)
        return {"belief_a": belief_a, "belief_b": out, "belief_joint": joint}


def cyclic_perturbation(n_symbols: int) -> Array:
    """Perturbation cyclique a lignes de somme nulle, de taille (q, q).

    ``Delta[i, j] = +1`` si ``j = (i+1) % q``, ``-1`` si ``j = (i+2) % q``,
    nul sinon : chaque ligne deplace de la masse d'un symbole vers son voisin
    cyclique. Les ``q`` rotations cycliques de COLONNES de ``Delta``
    s'annulent exactement -- c'est elles qui forment les variantes de
    :class:`ConditionalBench`.
    """
    if n_symbols < 3:
        raise ProcessError(f"perturbation cyclique definie pour q >= 3, recu {n_symbols}")
    d = np.zeros((n_symbols, n_symbols))
    for i in range(n_symbols):
        d[i, (i + 1) % n_symbols] = 1.0
        d[i, (i + 2) % n_symbols] = -1.0
    return d


def _token_marginal(process: object) -> Array:
    """Marginal des TOKENS d'un generateur (pi @ P(y|s)), Moore ou Mealy."""
    pi = np.asarray(process.stationary(), dtype=np.float64)
    if hasattr(process, "emission_matrix"):
        return pi @ np.asarray(process.emission_matrix(), dtype=np.float64)
    if hasattr(process, "edge_tensor"):
        w = np.asarray(process.edge_tensor(), dtype=np.float64)
        return pi @ w.sum(axis=1)
    raise ProcessError("processus sans emission parametree : marginal de tokens incalculable")


def conditional_child_floor(
    obs_b: Array,
    parent_tokens: Array,
    transition: Array,
    variants: Tuple[Array, ...],
    stationary: Array,
    burn: int = 0,
) -> float:
    """Plancher de Bayes de l'enfant CONDITIONNEL (emission variant temps-variable).

    Analogue exact de ``factor_geometry_trained.bayes_floor`` pour le regime
    conditionnel : perte logarithmique predictive du MEILLEUR filtre connaissant
    la variante observee ``v_t = parent_tokens[t]``,

        p_t = (b_{t-1} T) @ E_{v_t}[:, y_t],   b_t normalise apres coup,

    moyennee sur les pas posterieurs a ``burn``. Un filtre qui IGNORERAIT la
    variante (passer ``variants = (E, E, ...)``, l'emission marginale a
    chaque pas) rend une perte strictement plus grande : l'ecart entre les
    deux est la prime d'information conditionnelle, mesurable sur les memes
    donnees.
    """
    n = len(obs_b)
    if n < 1:
        raise ProcessError("conditional_child_floor attend une serie non vide")
    if not 0 <= burn < n:
        raise ProcessError(f"burn doit verifier 0 <= burn < {n}, recu {burn}")
    b = np.asarray(stationary, dtype=np.float64).copy()
    losses = []
    for t in range(n):
        v = int(parent_tokens[t]) % len(variants)
        pred = b @ transition if t > 0 else b
        p = pred @ variants[v][:, int(obs_b[t])]
        if t >= burn:
            losses.append(-np.log(max(p, 1e-300)))
        w = pred * variants[v][:, int(obs_b[t])]
        z = w.sum()
        if z <= 0.0:
            raise ProcessError(f"vraisemblance nulle au pas {t}")
        b = w / z
    return float(np.mean(losses))


def belief_simplex_coords(beliefs: Array) -> Array:
    """Coordonnees barycentriques 2D des beliefs d'un processus a 3 etats (triangle de Simon)."""
    if beliefs.shape[1] != 3:
        raise ProcessError("coordonnees simplexe definies pour 3 etats seulement")
    v = np.array([[0.0, 0.0], [1.0, 0.0], [0.5, np.sqrt(3.0) / 2.0]])
    return beliefs @ v
