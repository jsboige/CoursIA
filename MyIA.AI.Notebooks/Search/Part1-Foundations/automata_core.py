"""Coeur reutilisable d'execution et d'operations sur automates finis deterministes.

Pli 0 v2 (#26511) : le carnet Search-10-SymbolicAutomata devient cours + TP +
service web. Ce module porte le contrat `POST /automata/run` partage par les
deux frontends (Kernel Gateway notebook-http sur le carnet, service FastAPI
`automata_service.py`). L'organe est `automata-lib` : construction, parcours
(`read_input_stepwise`) et operations (`complement` / `union` / `intersection`)
sont delegues a la lib, jamais reimplémentes ici.
"""

from __future__ import annotations

from typing import Any

from automata.base.exceptions import AutomatonException, RejectionException
from automata.fa.dfa import DFA


class AutomataInputError(ValueError):
    """Automate malforme, mot hors alphabet ou operation inconnue (status invalid)."""


class AutomataRunError(RuntimeError):
    """Echec inattendu pendant le parcours ou l'operation (status error)."""


ALLOWED_OPS = ("accepts", "complement", "intersection", "union")


def build_dfa(spec: Any) -> DFA:
    """Construit et valide un DFA depuis sa forme JSON (format automata-lib).

    Les cinq champs canoniques sont requis ; la validation structurelle est
    celle d'automata-lib (etats, transitions completes sur l'alphabet, etats
    finaux inclus dans les etats, etc.).
    """
    if not isinstance(spec, dict):
        raise AutomataInputError("l'automate doit etre un objet JSON")
    required = ("states", "input_symbols", "transitions", "initial_state", "final_states")
    missing = [name for name in required if name not in spec]
    if missing:
        raise AutomataInputError("champs manquants : " + ", ".join(missing))
    try:
        return DFA(
            states=set(spec["states"]),
            input_symbols=set(spec["input_symbols"]),
            transitions=dict(spec["transitions"]),
            initial_state=spec["initial_state"],
            final_states=set(spec["final_states"]),
        )
    except (TypeError, ValueError, AutomatonException) as exc:
        # AutomatonException (InvalidStateError, MissingSymbolError, ...) :
        # la validation structurelle d'automata-lib, relayee en status invalid.
        raise AutomataInputError("automate invalide : " + str(exc)) from exc


def check_word(dfa: DFA, word: Any) -> str:
    """Valide que le mot est une chaine sur l'alphabet de l'automate."""
    if not isinstance(word, str):
        raise AutomataInputError("le mot doit etre une chaine")
    outside = sorted({symbol for symbol in word if symbol not in dfa.input_symbols})
    if outside:
        raise AutomataInputError(
            "le mot utilise des symboles hors alphabet : " + ", ".join(outside)
        )
    return word


def _state_key(state: Any) -> str:
    """Cle JSON stable d'un etat (automata-lib renomme les etats en int apres operations)."""
    return str(state)


def _serialize(dfa: DFA) -> dict[str, Any]:
    """Serialise un DFA en forme JSON (frozenset -> listes triees de chaines)."""
    transitions = {
        _state_key(source): {
            str(symbol): _state_key(target) for symbol, target in sorted(transitions.items())
        }
        for source, transitions in dfa.transitions.items()
    }
    return {
        "states": sorted(_state_key(state) for state in dfa.states),
        "input_symbols": sorted(_state_key(symbol) for symbol in dfa.input_symbols),
        "transitions": transitions,
        "initial_state": _state_key(dfa.initial_state),
        "final_states": sorted(_state_key(state) for state in dfa.final_states),
    }


def run(payload: Any) -> dict[str, Any]:
    """Execute le contrat POST /automata/run et retourne le bloc ``data``.

    - ``op`` omis ou ``accepts`` : verdict d'acceptation + trace des etats
      parcourus (etat initial compris, un etat par symbole consomme).
    - ``complement`` / ``union`` / ``intersection`` : automate resultant,
      serialise dans le meme format que l'entree.
    """
    if not isinstance(payload, dict):
        raise AutomataInputError("le corps de la requete doit etre un objet JSON")
    op = payload.get("op", "accepts")
    if op not in ALLOWED_OPS:
        raise AutomataInputError(
            "operation inconnue : " + repr(op) + " (attendues : " + ", ".join(ALLOWED_OPS) + ")"
        )

    dfa = build_dfa(payload.get("automaton"))

    if op == "accepts":
        word = check_word(dfa, payload.get("word"))
        # read_input_stepwise rend l'etat initial compris et LEVE
        # RejectionException si l'etat d'arrivee n'est pas final : un mot
        # rejete est une reponse valide (accepted=False, trace complete),
        # pas un echec d'execution.
        trace: list[str] = []
        rejected = False
        try:
            for state in dfa.read_input_stepwise(word):
                trace.append(str(state))
        except RejectionException:
            rejected = True
        except Exception as exc:  # parcours inattendu (bug lib, transition cassee)
            raise AutomataRunError("echec du parcours : " + str(exc)) from exc
        return {"accepted": not rejected, "trace": trace}

    if op == "complement":
        try:
            result = dfa.complement()
        except Exception as exc:
            raise AutomataRunError("echec du complement : " + str(exc)) from exc
        return {"automaton": _serialize(result)}

    other = build_dfa(payload.get("other"))
    if other.input_symbols != dfa.input_symbols:
        raise AutomataInputError(
            "les deux automates doivent partager exactement le meme alphabet"
        )
    try:
        result = dfa.union(other) if op == "union" else dfa.intersection(other)
    except Exception as exc:
        raise AutomataRunError("echec de l'operation " + op + " : " + str(exc)) from exc
    return {"automaton": _serialize(result)}
