# -*- coding: utf-8 -*-
"""Protocoles de dialogue multi-agents — machine à états Walton-Krabbe, seule
implémentation vivante, exécutable sans JVM (EPIC #4960).

Généalogie : `1_2_7_argumentation_dialogique/local_db_arg` du dépôt étudiant
`jsboigeEpita/2025-Epita-Intelligence-Symbolique`. Mandat Triple Distillation
(EPIC #4960) : porter l'essence vivante « sans le bruit d'une année de
régressions et d'itérations ».

**Pourquoi il n'y a rien à distiller du tronc sur ce sujet** — et c'est ce fait
qui fonde ce port, mesuré sur le dépôt du tronc lui-même :

- le tronc a **adapté** ce vocabulaire, il ne l'a pas inventé
  (`argumentation_analysis/agents/core/debate/protocols.py`, en-tête :
  « Adapted from 1_2_7_argumentation_dialogique/local_db_arg/src/ ») ;
- puis il a **retiré** les trois classes de protocole — `DialogueProtocol`,
  `InquiryProtocol`, `PersuasionProtocol` — en **#2137**, qualifiées de « dead
  twins », la voie vivante du dialogue formel y étant le
  `logic/dialogue_handler.py` **JVM**. Le carnet du sas qui les mettait en
  scène survit comme artefact d'enseignement, mais ne peut plus être
  ré-exécuté contre ce code (garde de round-trip du tronc : le carnet « can no
  longer be re-run against this code », ses tests de rejeu étant partis avec
  les classes).

Ce port est donc **la seule implémentation vivante** de cette machine à états,
et il est **exécutable sans JVM** : module pur, stdlib uniquement, déterministe
par construction (aucun aléatoire dans le source porté).

Partie vivante retenue (qualification issuecomment-5770146198) :
- `core/models.py` : types de dialogue **Walton-Krabbe** (6) et 9 actes de
  parole formalisés (CLAIM, QUESTION, CHALLENGE, ARGUE, CONCEDE, RETRACT,
  SUPPORT, REFUTE, UNDERSTAND).
- `protocols/base_protocol.py` : `DialogueProtocol` = machine à états —
  transitions permises entre actes + conditions de terminaison.
- `protocols/inquiry_protocol.py` : dialogue d'enquête **collaboratif** —
  terminaison par compréhension mutuelle (3 UNDERSTAND/CONCEDE consécutifs)
  ou détection de boucle (même pattern d'actes 3 fois).
- `protocols/persuasion_protocol.py` : dialogue de persuasion
  **adversarial** — terminaison par CONCEDE ou double RETRACT.

Partie NON portée (bruit) : le monolithe `enhanced_argumentation_main.py`
(1496 lignes), les couches DB/CLI/serveur.

Divergences documentées (mesurées sur le source) :
1. `DialogueMove` du source porte `id`, `timestamp` (datetime + uuid) et un
   `content` typé `Proposition | Argument | str` : le port réduit à
   `(speaker, act, content, target)` en chaîne — la machine à états ne lit
   que `act`, l'horodatage ne joue aucun rôle dans les transitions ni la
   terminaison (vérifié : aucune condition ne le consulte).
2. Le registre `DialogueType` du source énumère 6 types Walton-Krabbe mais
   seuls INQUIRY et PERSUASION ont un protocole implémenté — porté tel quel
   (les 4 autres restent des noms, pas des machines).
3. `_detect_pattern_loop` du source compare des tuples d'actes 2 à 2 sur les
   6 derniers coups — porté à l'identique, y compris sa limite : une boucle
   de période 3 (ABC ABC) n'est pas détectée.
4. La terminaison « limite de longueur » (25 pour inquiry, 30 pour
   persuasion) est asymétrique dans le source sans justification — porté
   fidèle.
5. `_term_double_retract` du source teste deux RETRACT consécutifs — un état
   que sa propre table de transitions interdit : seul CHALLENGE mène à
   RETRACT, et RETRACT ne mène pas à RETRACT. La condition est vivante dans
   le code mais inatteignable par tout dialogue légal (code mort DANS le
   source) — découverte en écrivant les traces de démonstration du notebook,
   même nature que la simulation 2.1.6 qui n'appelait jamais ses méthodes
   de vote (cf governance_methods.py, divergence 1).

Le caractère pur est vérifié, pas déclaré : le module n'importe que la stdlib
(`__future__`, `dataclasses`, `enum`). Garde de structure :
`tests/test_dialogue_protocols.py` (13 tests, sans JVM).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum


class DialogueType(Enum):
    """Types de dialogues selon Walton-Krabbe (registre du source)."""

    INFORMATION_SEEKING = "information_seeking"
    INQUIRY = "inquiry"
    PERSUASION = "persuasion"
    NEGOTIATION = "negotiation"
    DELIBERATION = "deliberation"
    ERISTIC = "eristic"


class SpeechAct(Enum):
    """Actes de parole formalisés (9, du source)."""

    CLAIM = "claim"
    QUESTION = "question"
    CHALLENGE = "challenge"
    ARGUE = "argue"
    CONCEDE = "concede"
    RETRACT = "retract"
    SUPPORT = "support"
    REFUTE = "refute"
    UNDERSTAND = "understand"


@dataclass
class DialogueMove:
    """Mouvement de dialogue — le protocole ne lit que l'acte (divergence 1)."""

    speaker: str
    act: SpeechAct
    content: str = ""
    target: str | None = None


class DialogueProtocol:
    """Machine à états sur actes de langage (port de base_protocol.py)."""

    name = "abstract"

    def __init__(self):
        self.allowed_transitions: dict[SpeechAct, list[SpeechAct]] = {}
        self.termination_conditions = []
        self._setup_protocol()

    def _setup_protocol(self) -> None:
        raise NotImplementedError

    def is_valid_move(self, current_act: SpeechAct, next_act: SpeechAct) -> bool:
        """Une transition n'est valide que si elle figure dans la table."""
        return next_act in self.allowed_transitions.get(current_act, [])

    def is_terminal_state(self, history: list[DialogueMove]) -> bool:
        """Terminaison dès qu'une condition satisfaite."""
        return any(cond(history) for cond in self.termination_conditions)

    def get_allowed_responses(self, last_act: SpeechAct) -> list[SpeechAct]:
        return self.allowed_transitions.get(last_act, [])

    def validate_trace(self, moves: list[DialogueMove]) -> dict:
        """Valide une trace complète : chaque transition + terminaison.

        Retourne {valid, first_invalid (index), terminated, reason}.
        """
        first_invalid = None
        for i in range(1, len(moves)):
            if not self.is_valid_move(moves[i - 1].act, moves[i].act):
                first_invalid = i
                break
        terminated = self.is_terminal_state(moves)
        return {
            "valid": first_invalid is None,
            "first_invalid": first_invalid,
            "terminated": terminated,
            "reason": self._termination_reason(moves),
        }

    def _termination_reason(self, history: list[DialogueMove]) -> str | None:
        for cond in self.termination_conditions:
            if cond(history):
                return getattr(cond, "__name__", repr(cond))
        return None


class InquiryProtocol(DialogueProtocol):
    """Dialogue d'enquête collaborative (port fidèle)."""

    name = "inquiry"

    def _setup_protocol(self):
        S = SpeechAct
        self.allowed_transitions = {
            S.QUESTION: [S.CLAIM, S.ARGUE, S.QUESTION, S.SUPPORT],
            S.CLAIM: [S.SUPPORT, S.CHALLENGE, S.QUESTION, S.UNDERSTAND],
            S.SUPPORT: [S.QUESTION, S.UNDERSTAND, S.CHALLENGE],
            S.CHALLENGE: [S.ARGUE, S.SUPPORT, S.QUESTION],
            S.ARGUE: [S.CHALLENGE, S.UNDERSTAND, S.QUESTION, S.SUPPORT],
            S.UNDERSTAND: [S.QUESTION, S.UNDERSTAND, S.CLAIM],
            S.REFUTE: [S.ARGUE, S.QUESTION],
            S.CONCEDE: [S.QUESTION, S.UNDERSTAND],
        }
        self.termination_conditions = [
            self._term_mutual_understanding,
            self._term_length,
            self._term_converged,
            self._term_loop,
        ]

    @staticmethod
    def _term_mutual_understanding(h):
        S = SpeechAct
        return len(h) >= 3 and all(m.act in (S.UNDERSTAND, S.CONCEDE) for m in h[-3:])

    @staticmethod
    def _term_length(h):
        return len(h) > 25

    @staticmethod
    def _term_converged(h):
        return len(h) >= 4 and h[-1].act == h[-2].act == SpeechAct.UNDERSTAND

    @staticmethod
    def _term_loop(h):
        if len(h) < 6:
            return False
        recent = h[-6:]
        return (recent[0].act, recent[1].act) == (recent[2].act, recent[3].act) == (recent[4].act, recent[5].act)


class PersuasionProtocol(DialogueProtocol):
    """Dialogue de persuasion adversariale (port fidèle)."""

    name = "persuasion"

    def _setup_protocol(self):
        S = SpeechAct
        self.allowed_transitions = {
            S.CLAIM: [S.CHALLENGE, S.CONCEDE, S.QUESTION, S.SUPPORT],
            S.CHALLENGE: [S.ARGUE, S.RETRACT, S.SUPPORT],
            S.ARGUE: [S.CHALLENGE, S.CONCEDE, S.REFUTE, S.SUPPORT],
            S.QUESTION: [S.CLAIM, S.ARGUE, S.SUPPORT],
            S.REFUTE: [S.ARGUE, S.CONCEDE, S.CHALLENGE],
            S.SUPPORT: [S.UNDERSTAND, S.CHALLENGE, S.QUESTION],
            S.CONCEDE: [S.CLAIM, S.QUESTION],
            S.RETRACT: [S.CLAIM, S.QUESTION],
            S.UNDERSTAND: [S.CLAIM, S.QUESTION],
        }
        self.termination_conditions = [
            self._term_concede,
            self._term_length,
            self._term_double_retract,
        ]

    @staticmethod
    def _term_concede(h):
        return len(h) > 0 and h[-1].act == SpeechAct.CONCEDE

    @staticmethod
    def _term_length(h):
        return len(h) > 30

    @staticmethod
    def _term_double_retract(h):
        return len(h) > 2 and h[-1].act == h[-2].act == SpeechAct.RETRACT


PROTOCOLS: dict[str, type[DialogueProtocol]] = {
    "inquiry": InquiryProtocol,
    "persuasion": PersuasionProtocol,
}


def protocol_counts() -> dict:
    """Inventaire de l'organe (tests purs, sans exécution de trace)."""
    return {
        "walton_krabbe_types": len(DialogueType),
        "speech_acts": len(SpeechAct),
        "protocols": sorted(PROTOCOLS.keys()),
        "inquiry_transitions": sum(len(v) for v in InquiryProtocol().allowed_transitions.values()),
        "persuasion_transitions": sum(len(v) for v in PersuasionProtocol().allowed_transitions.values()),
    }
