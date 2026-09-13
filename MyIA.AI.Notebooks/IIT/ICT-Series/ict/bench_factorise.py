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
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Sequence, Tuple

import numpy as np

Array = np.ndarray


class ProcessError(ValueError):
    """Erreur de parametrage ou d'usage d'un generateur du banc."""


@dataclass(frozen=True)
class Mess3:
    """Mess3 : 3 etats caches en cycle, emissions gaussiennes 1D.

    Parametres par defaut : modes bien separees (ecart des moyennes >= 4
    ecarts-types) pour que la v1 ait une verite terrain lisible. Les
    etudes de superposition resserreront l'ecart ensuite.
    """

    stay: float = 0.95
    means: Tuple[float, float, float] = (-0.15, 0.0, 0.15)
    std: float = 0.05
    n_states: int = 3
    name: str = "mess3"

    def __post_init__(self) -> None:
        if not 0.0 < self.stay < 1.0:
            raise ProcessError(f"stay doit etre dans (0,1), recu {self.stay}")
        if self.std <= 0:
            raise ProcessError(f"std doit etre > 0, recu {self.std}")
        if len(self.means) != self.n_states:
            raise ProcessError("une moyenne par etat requise")

    # --- structure connue -------------------------------------------------
    def transition_matrix(self) -> Array:
        """Matrice T[i, j] = P(s_{t+1} = j | s_t = i) : rester, sinon avancer au suivant du cycle."""
        slip = 1.0 - self.stay
        t = np.zeros((self.n_states, self.n_states))
        for i in range(self.n_states):
            t[i, i] = self.stay
            t[i, (i + 1) % self.n_states] = slip
        return t

    def stationary(self) -> Array:
        """Loi stationnaire : uniforme par symetrie du cycle."""
        return np.full(self.n_states, 1.0 / self.n_states)

    def emission_loglik(self, obs: Array) -> Array:
        """Log-vraisemblance log P(obs | s) pour chaque etat, forme (T, n_states)."""
        means = np.asarray(self.means)[None, :]
        return -0.5 * ((obs[:, None] - means) / self.std) ** 2 - np.log(
            self.std * np.sqrt(2.0 * np.pi)
        )

    # --- generation --------------------------------------------------------
    def sample(self, n: int, seed: int) -> Tuple[Array, Array]:
        """Echantillonne n pas ; retourne (etats, observations), etat initial tiré selon la stationnaire."""
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

    # --- belief exact ------------------------------------------------------
    def beliefs(self, obs: Array) -> Array:
        """Filtration forward exacte : belief[k] = P(s_k | obs_{0..k}), forme (T, n_states)."""
        if obs.ndim != 1:
            raise ProcessError("Mess3.beliefs attend une serie 1D")
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
class RRXOR:
    """XOR recursif : bits iid ``b_t``, observation ``y_t = b_{t-1} XOR b_t``.

    Etat cache au pas t : la paire ``(b_{t-1}, b_t)``, 4 etats ordonnes
    ``00, 01, 10, 11``. L'observation etant deterministe dans l'etat, le
    belief exact apres observation vit sur les 2 etats coherents avec
    ``y_t``, uniformes (les entrees sont iid uniformes).
    """

    n_states: int = 4
    name: str = "rrxor"

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
        """Filtration forward exacte sur les 4 etats ; observation binaire deterministe.

        Le premier pas n'a pas d'observation antecedente : prior stationnaire
        (l'etat (b_{-1}, b_0) n'est jamais observable via y_0 seul).
        """
        if obs.ndim != 1 or not np.all(np.isin(obs, (0, 1))):
            raise ProcessError("RRXOR.beliefs attend une serie binaire 1D")
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


def belief_simplex_coords(beliefs: Array) -> Array:
    """Coordonnees barycentriques 2D des beliefs d'un processus a 3 etats (triangle de Simon)."""
    if beliefs.shape[1] != 3:
        raise ProcessError("coordonnees simplexe definies pour 3 etats seulement")
    v = np.array([[0.0, 0.0], [1.0, 0.0], [0.5, np.sqrt(3.0) / 2.0]])
    return beliefs @ v
