# _pl_verdict.py — contrat de verdict moteur pour la phase formelle (#22981)
#
# Le contrat d'appel de la phase formelle (`PROMPT_LOGIC_ANALYSIS`, dans
# `_runner.py`) exigeait l'APPEL de `StateManager-log_query_result`, pas un
# VERDICT de moteur : la valeur consignee pouvait etre n'importe quelle chaine.
# Mesure (#22981) : deux runs independants du carnet
# `Argumentation-08b-Executor-Python.ipynb`, sur deux generations de modele
# differentes, ont consigne 2 questions en langage naturel et 0 verdict.
#
# Ce module materialise le contrat : un verdict n'existe que s'il a ete EMIS
# par un moteur. Le registre memorise les verdicts produits par le solveur ;
# la garde (`GuardedStateManagerPlugin`, `_guarded_state.py`) refuse tout
# autre contenu — un rejet explicite, jamais un silence.

from __future__ import annotations

import re
import weakref
from typing import Dict, List, Optional, Tuple

ACCEPTED = "ACCEPTED"
REJECTED = "REJECTED"

_WHITESPACE = re.compile(r"\s+")


def normalize(text: str) -> str:
    """Normalisation de comparaison : espaces reduits, bordures retirees."""
    return _WHITESPACE.sub(" ", (text or "").strip())


def is_verdict(text: str) -> bool:
    """Vrai si la chaine commence par un marqueur de verdict moteur."""
    upper = (text or "").strip().upper()
    return upper.startswith(ACCEPTED) or upper.startswith(REJECTED)


def format_verdict(
    belief_set_id: str, query: str, entailed: bool, engine: str
) -> str:
    """Verdict canonique : lisible par machine (marqueur en tete) et par humain.

    Le marqueur `ACCEPTED:` / `REJECTED:` en tete est ce que le carnet
    `Argumentation-08b-Executor-Python.ipynb` recherche pour valider la
    phase formelle (`QUERIES_MEANINGFUL`) : il doit donc rester le premier
    token de la chaine.
    """
    status = ACCEPTED if entailed else REJECTED
    return (
        f"{status}: entail({query}) = {entailed} | belief_set={belief_set_id} "
        f"| moteur={engine}"
    )


class VerdictRegistry:
    """Verdicts reellement emis par un moteur, indexes par (belief_set, query).

    La cle porte le `belief_set_id` ET la requete : un verdict n'est
    reutilisable que pour la requete sur laquelle il a ete produit.
    """

    def __init__(self) -> None:
        self._verdicts: Dict[Tuple[str, str], str] = {}

    def record(self, belief_set_id: str, query: str, verdict: str) -> str:
        """Memorise un verdict emis par le moteur et le renvoie."""
        self._verdicts[(belief_set_id, normalize(query))] = verdict
        return verdict

    def get(self, belief_set_id: str, query: str) -> Optional[str]:
        """Verdict emis pour ce couple (belief_set, query), sinon None."""
        return self._verdicts.get((belief_set_id, normalize(query)))

    def is_engine_verdict(
        self, belief_set_id: str, query: str, raw_result: str
    ) -> bool:
        """Vrai si `raw_result` est un verdict emis par le moteur.

        Comparaison exacte sur le couple (belief_set, query) ; a defaut, on
        accepte un verdict deja emis pour ce meme belief set — le verdict
        canonique embarque l'identifiant du belief set et la requete, donc
        la correspondance reste verifiable a l'oeil.
        """
        expected = self.get(belief_set_id, query)
        if expected is not None and normalize(raw_result) == normalize(expected):
            return True
        target = normalize(raw_result)
        return any(
            normalize(verdict) == target
            for (bs_id, _query), verdict in self._verdicts.items()
            if bs_id == belief_set_id
        )

    def issued(self) -> List[Tuple[str, str, str]]:
        """Liste des verdicts emis : (belief_set_id, query, verdict)."""
        return [
            (bs_id, query, verdict)
            for (bs_id, query), verdict in self._verdicts.items()
        ]

    def clear(self) -> None:
        """Oublie tous les verdicts (tests, rejeu d'analyse)."""
        self._verdicts.clear()


_REGISTRIES: "weakref.WeakKeyDictionary" = weakref.WeakKeyDictionary()


def registry_for(state) -> VerdictRegistry:
    """Registre propre a un etat d'analyse.

    Les identifiants de belief set (`propositional_bs_1`) sont scopes a un
    etat : deux analyses successives dans le meme processus reutilisent les
    memes noms. Un registre par etat evite qu'un verdict d'une analyse
    vaille pour une autre.
    """
    registry = _REGISTRIES.get(state)
    if registry is None:
        registry = VerdictRegistry()
        _REGISTRIES[state] = registry
    return registry
